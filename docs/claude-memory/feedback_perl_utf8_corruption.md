---
name: feedback-perl-utf8-corruption
description: "NEVER use perl \\x{NNNN} wide-char escapes when editing UTF-8 files in place — it double-encodes the WHOLE file"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-10-05T13:19:55.876Z
---

When editing a UTF-8 file with `perl -0pi -e 's/.../.../'`, **never put `\x{NNNN}` wide-character escapes in the replacement.** Perl reads the file as raw bytes; a single wide char in the replacement upgrades the entire string to character semantics, so on output every pre-existing UTF-8 byte gets re-encoded as UTF-8 again. The whole file is silently double-encoded (`—` becomes `Ã¢ÂÂ`). Perl warns `Wide character in print` — **treat that warning as "the file is now corrupt"**, not as cosmetic.

This happened twice in the QML project (2026-09-06): once on `QML_Full_v10_Part3.lean` (recovered with `git checkout`) and twice on `memory/reference_qml_eq_by_extensionality.md`, which is NOT in git and needed a hand-written repair.

**Why:** the corruption is silent for ASCII-only content, so it survives a `grep` spot-check; it only shows up when a non-ASCII line is read back.

**How to apply:**
- Prefer the **Edit tool** for any file containing non-ASCII — it is exact-string and encoding-safe.
- **Python 3.14 is installed (2026-10-05, user installed it for this).** For scripted multi-line or
  multi-file edits, prefer `python - <<'EOF' … EOF` with
  `io.open(path, encoding='utf-8', newline='')`, which round-trips UTF-8 and line endings, over
  perl.  It is also good for character-aware checks (line length > 100).
- If perl is genuinely needed, write non-ASCII as **byte escapes** (`\xe2\x86\x90` for `←`), never `\x{2190}`. Byte escapes keep the string in byte semantics.
- Heredocs (`cat >> file <<'EOF'`) are safe — they pass bytes through untouched. This is the right way to append large Lean blocks.
- Keep the file under git and commit often, so `git checkout -- <file>` is an escape hatch.

**Repair recipe** (if it happens again): loop `s/([\xC2\xC3])([\x80-\xBF])/chr(((ord($1)&0x1F)<<6)|(ord($2)&0x3F))/ge` until it stops matching — each pass strips one layer, and correct UTF-8 for characters ≥ U+0100 has no `C2`/`C3` lead byte so it is a no-op there. That over-collapses genuine U+0080–U+00FF characters, so follow it with a pass that walks the bytes and re-encodes any byte that does not start a valid UTF-8 sequence. Put the perl in a script file — `&` and `\` in `-e` one-liners fight with bash quoting. Related: [[project-qml-lean4]].
