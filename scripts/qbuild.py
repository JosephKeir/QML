"""Compact build report for the v12m files.

Usage (from the repo directory):
    python scripts/qbuild.py                  # the v12m top modules
    python scripts/qbuild.py SemBack Proof    # short names, or full QML.QML_v12m_X
    python scripts/qbuild.py -n 30 SemBack    # keep up to 30 lines per message

Prints each error, and each warning from a v12m file, cut to a few lines; skips the noisy
legacy files and CRLF-only `Leibniz` warnings; then reports v12m `sorry`s, lines over 100
characters, and one summary line.
"""
import glob
import io
import re
import subprocess
import sys

TOP = ["BCompactness", "Compactness", "StrongD", "LeibnizProof", "ArrowCheck", "BFairS", "BAliasW", "BDecodeLimit", "RetForget", "BLimitRet", "BBackTail", "BBackTruth", "BBackLimit"]
NOISE = ("✔", "⣿", "info:", "trace:", "Note: This linter")
HEAD = re.compile(r"^(error|warning): ")


def module(name):
    return name if name.startswith("QML.") else "QML.QML_v12m_" + name


def main(argv):
    sys.stdout.reconfigure(encoding="utf-8")
    keep = 8
    if argv[:1] == ["-n"]:
        keep, argv = int(argv[1]), argv[2:]
    mods = [module(m) for m in (argv or TOP)]
    proc = subprocess.run(["lake", "build", *mods], capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    lines = (proc.stdout + proc.stderr).splitlines()

    msgs, cur = [], None
    for line in lines:
        if line.startswith(NOISE) or not line.strip():
            continue
        if HEAD.match(line):
            cur = [line]
            msgs.append(cur)
        elif line.startswith(("✖", "⚠", "Build completed", "Some required",
                              "error: build failed", "- QML")):
            cur = None
        elif cur is not None:
            cur.append(line)

    shown = 0
    for m in msgs:
        head = m[0]
        if head.startswith("warning:") and ("QML_v12m_" not in head or "Leibniz.lean" in head):
            continue
        if "Lean exited with code" in head or head == "error: build failed":
            continue
        shown += 1
        print("\n".join(m[:keep]))
        if len(m) > keep:
            print(f"  ... ({len(m) - keep} more lines)")
    status = "OK" if proc.returncode == 0 else "FAILED"

    sorries, longs = [], []
    for path in sorted(glob.glob("QML/QML_v12m_*.lean")):
        text = io.open(path, encoding="utf-8", newline="").read()
        for i, l in enumerate(text.splitlines(), 1):
            if re.search(r"\bsorry\b", l) and not l.lstrip().startswith("--"):
                sorries.append(f"{path}:{i}")
            if len(l) > 100:
                longs.append(f"{path}:{i}")
    for s in sorries:
        print("sorry:", s)
    for s in longs:
        print("long line:", s)
    print(f"== {status}: {len(mods)} target(s), {shown} message(s), "
          f"{len(sorries)} sorry, {len(longs)} long line(s)")
    return proc.returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
