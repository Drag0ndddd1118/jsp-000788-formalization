"""Mechanical checks of this repository.

1. `lake build` must succeed.
2. `Submission.lean` must contain no `sorry`, no `admit` and no `axiom`.
3. The bridge

       example : jsp000788Statement := jsp_000788_solved

   must type-check, which is possible only if the submission proves exactly the
   proposition that `Challenge.lean` states.
4. The axiom audit of `jsp_000788_solved` must stay inside the allowed set.

Usage: python3 check.py
"""

import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.abspath(__file__))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BRIDGE = "example : jsp000788Statement := jsp_000788_solved"


def run(cmd):
    return subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


src = open(os.path.join(REPO, "Submission.lean")).read()
code = re.sub(r"/-.*?-/", "", src, flags=re.S)
code = re.sub(r"--[^\n]*", "", code)
for bad in ("sorry", "admit", "axiom", "opaque", "unsafe", "partial", "native_decide"):
    if re.search(r"\b" + bad + r"\b", code):
        fail("Submission.lean contains `" + bad + "`")

p = run(["lake", "build"])
if p.returncode != 0:
    print(p.stdout)
    print(p.stderr)
    fail("lake build failed")
print("build OK")

audit = os.path.join(REPO, "Verify.lean")
open(audit, "w").write("import Submission\n\nopen JSP000788\n\n" + BRIDGE + "\n" + "#print axioms jsp_000788_solved" + "\n")
try:
    p = run(["lake", "env", "lean", "Verify.lean"])
    out = p.stdout + p.stderr
    if p.returncode != 0 or "error" in out:
        print(out)
        fail("bridge or axiom audit failed")
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out, re.S)
    if m:
        used = {a.strip() for a in m.group(1).split(",") if a.strip()}
        extra = used - ALLOWED
        if extra:
            fail("axioms outside the allowed set: " + ", ".join(sorted(extra)))
        print("axioms OK:", ", ".join(sorted(used)))
    elif "does not depend on any axioms" in out:
        print("axioms OK: none")
    else:
        print(out)
        fail("could not read the axiom audit output")
finally:
    if os.path.exists(audit):
        os.remove(audit)
print("bridge OK:", BRIDGE)
