---
name: feedback-olean-corruption-crash
description: "How to diagnose Lean exit code 3221225477 (0xC0000005) crashes — usually a corrupt mathlib olean, not your code"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-09-08T22:22:59.685Z
---

A Lean build failing with `Lean exited with code 3221225477` (= `0xC0000005`, Windows access violation) is almost always a **corrupt mathlib `.olean`**, NOT a bug in the declaration being elaborated.

**Why it's deceptive:** Lean loads oleans lazily (mmap). A corrupt region is only hit when the *specific* declaration referencing it is elaborated — so the crash can land deep inside your file (e.g. `[926/926] Building X (102s)`), looking exactly like "this declaration overflows the elaborator." I wasted a long session this way: I "definitively" blamed a new axiom, even removed it and saw a *clean* build — but that clean build was an **instant cached olean**, not a real recompile. The user caught it: a real `QML_Full_v8` compile takes ~10-12 min; anything instant is a stale-olean false positive.

**Why:** the root cause here was a single corrupt archive in the *download* cache — `~/.cache/mathlib/<hash>.ltar: Data corruption detected` — whose oleans never decompressed cleanly. Plain `lake exe cache get` reports "N already decompressed" and trusts existing (corrupt) oleans without re-verifying, so it does NOT fix it.

**How to apply — diagnostic + fix ladder:**
1. Run `lake exe cache get!` (force) and READ the full output. Look for `Data corruption detected` naming a specific `~/.cache/mathlib/<hash>.ltar`, then `leantar failed with error code 1`.
2. `rm` that specific corrupt `.ltar`, then `lake exe cache get` — re-downloads just that archive fresh and decompresses it.
3. Then `lake exe cache get!` **again** to force re-decompress ALL 8010 oleans (other decompressed oleans may also be corrupt from earlier interrupted `leantar` runs; `get` won't re-verify them, only `get!` re-decompresses). Confirm `Decompressing 8010 file(s) ... Completed successfully!` with NO corruption line.
4. Rebuild and **verify the time**: a genuine full compile of the target takes minutes. Instant "success" = cached olean, prove-nothing. Watch `date`/`time` around the build.

DON'T trust "removed the suspect code → it builds" unless that build actually took the real ~10 min. See [[feedback-polling]], [[project-vscode-extension-rollback]].

✅**THE RAM FIX IS CONFIRMED (user, 2026-09-08): ZERO crashes since.** The whole v11 build-out — Symbols/Terms/TermSubst/Rel/WFF/WFFSubst/Proof, including a dozen-plus `QML_v11_WFFSubst` elaborations at 13–16 min each and several full-chain rebuilds — ran without a single `3221225477`. So do NOT re-open the RAM hypothesis on this machine; if `3221225477` returns, work the other three modes (disk full → memory contention → corrupt olean) first.

⛔**FOURTH failure mode, and the one that wasted a whole session (found 2026-09-07): FAILING RAM.** One bad memory cell produced `3221225477` crashes that looked exactly like a code problem. **Signature = NON-DETERMINISM**: the same file, byte-identical, gave build / build / SEGFAULT across three runs; and `lake env lean` alone (no `-o`, no `-c`) also segfaulted, so it was never codegen. Confirmed with `Get-WinEvent -FilterHashtable @{LogName='System'; Id=1001}` → **BugCheck 0x1A (MEMORY_MANAGEMENT) subcode 0x41792 (corrupted PTE), three times over three weeks**; MemTest86 then found errors on a single cell. Fixed by putting that page in Windows' `badmemorylist` (`bcdedit /enum {badmemory}` — needs admin AND a reboot). Before: committed Part2b failed **5/5**. After: **4/4 green**, 306–371 s. ⚠️`mdsched.exe` found NOTHING — it is far too weak; use MemTest86.

⛔**THE RULE THIS BURNED IN: when the SAME input gives DIFFERENT results, stop and suspect the machine, not the code.** I produced FOUR confident, mutually inconsistent diagnoses of this one crash — "codegen can't compile WF recursion" (twice), "it's `diaCount_ctx_ext`", "it's the fuel wrapper" — each from single runs, each wrong, and each sent me redesigning working code. Check these BEFORE any bisection: (1) `df -h /c`; (2) rebuild the TRUE unmodified baseline — note "committed" ≠ "unmodified" if you committed earlier in the same session; (3) run the identical thing 3× and see whether results differ at all; (4) `Get-WinEvent … Id=1001` for bugchecks, `Get-CimInstance Win32_PhysicalMemory` for DIMMs. Also: **grepping output for "error" is NOT a pass/fail test** — a segfault prints no `error` line, so always check the EXIT CODE.

⭐**THIRD failure mode (found 2026-09-06): THE DISK IS FULL.** `C:` hit 0 bytes free (a stray 81 GB Dropbox folder). Lean crashes with `3221225477` when it cannot write the `.olean`, so the crash lands on whatever target was being built. It is *deceptively code-shaped*: `lake env lean <file>` often SUCCEEDS (it elaborates without writing an olean) while `lake build` crashes, which looks exactly like "codegen/serialisation chokes on my new definition".

**⚠️THE PROCESS LESSON — do this FIRST, before any diagnosis:** I "established" two conclusions from single runs of different code variants (that Lean's code generator segfaults on a well-founded `WFF.pairElim`, and that `simp only [WFF.pairElim]` overflows the stack on a nested-`have` arm), redesigned around them, and both evaporated when I finally built the **UNMODIFIED baseline**, which crashed identically. Variant-to-variant differences under a broken environment are NOISE. So:
1. **`df -h /c`** — check free space before anything else. Also `git status` failing with `sha1 file '.git/index.lock' write error. Out of diskspace` is a dead giveaway, as is any tool reporting `write error: No space left on device` (including `tail`/`head`, since this harness writes command output to disk).
2. **Build the unmodified baseline** (`git stash` your changes, `lake build <target>`). If HEAD crashes too, the environment is broken and NOTHING you conclude about your own code is trustworthy.
3. Only then work down the ladder below.

Cheap space wins on this machine: `powercfg /h off` reclaims `hiberfil.sys` (6.4 GB, reversible with `powercfg /h on`); `QML/.lake` is ~7 GB and rebuildable; `~/.cache/mathlib` ~0.4 GB. `du -sh` on top-level `C:` dirs works but `/c/Users` and `/c/Windows` need >400s each.

**SECOND failure mode for `3221225477` (found 2026-08-02, session 5): MEMORY CONTENTION, not olean corruption.** The machine has 16 GB RAM. The `lean-lsp` MCP server holds a resident `lean.exe` with mathlib loaded (~2.6 GB). Each `lake build` spawns ANOTHER ~2.6 GB mathlib `lean.exe`, and crashed builds LEAK orphaned `lean.exe`/`lake.exe` workers (~730 MB each). When free RAM drops (~4 GB), a build's allocation fails and surfaces as `3221225477` at a NON-deterministic source location (different line each run — that's the tell vs olean corruption, which is deterministic). Distinguishing signal: **the LSP `lean_diagnostic_messages` (full-file, no line filter) reports NO errors, but `lake build` crashes** → it's environment (memory), not code; TRUST the LSP (same elaborator, authoritative for correctness). FIX: `tasklist | grep -iE "lean|lake"` to find orphans, `taskkill //F //PID <pid>` the leftover build workers (keep the LSP's big `lean.exe` + `lean-lsp-mcp.exe`), check `wmic OS get FreePhysicalMemory` — freeing to ~7 GB lets the build complete. Kill orphans after every crashed build; don't run `lake build` concurrently with heavy LSP elaboration.
