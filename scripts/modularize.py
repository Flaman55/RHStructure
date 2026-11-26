#!/usr/bin/env python3
"""Put Lean files under Lean's module system, mechanically and without touching proofs.

For every .lean file given (directories are searched recursively):
  * `module` is inserted as the first line (if the file is not already a module);
  * every `import X` line becomes `public import X`;
  * `@[expose] public section` is inserted after the last import line.
With --compat, the options `backward.proofsInPublic` and `backward.privateInPublic` are set
after the section header, which keeps the elaboration of proofs inside definitions as it was
before the module system (needed for grh-compact, which was written without it).
Used for the fork of grh-compact (src/) and for the files of this repository.
Usage: modularize.py [--compat] PATH...
"""
import os, re, sys

COMPAT = ["set_option backward.proofsInPublic true", "set_option backward.privateInPublic true"]

def add_compat(path):
    s = open(path, encoding="utf-8").read()
    if COMPAT[0] in s:
        return False
    s = s.replace("@[expose] public section", "@[expose] public section\n\n" + "\n".join(COMPAT), 1)
    open(path, "w", encoding="utf-8").write(s)
    return True

def modularize(path):
    s = open(path, encoding="utf-8").read()
    lines = s.split("\n")
    if any(l.strip() == "module" for l in lines[:40]):
        return False
    last_import = -1
    for i, l in enumerate(lines):
        m = re.match(r"^import\s+(.*)$", l)
        if m:
            lines[i] = "public import " + m.group(1)
            last_import = i
    if last_import >= 0:
        lines.insert(last_import + 1, "\n@[expose] public section")
    else:
        # no imports: open the public section after the leading comment block
        lines.insert(0, "@[expose] public section\n")
    lines.insert(0, "module\n")
    open(path, "w", encoding="utf-8").write("\n".join(lines))
    return True

def files(args):
    for a in args:
        if os.path.isdir(a):
            for root, _, fs in os.walk(a):
                if "/.lake" in root or root.endswith(".lake"):
                    continue
                for f in fs:
                    if f.endswith(".lean"):
                        yield os.path.join(root, f)
        else:
            yield a

if __name__ == "__main__":
    args = sys.argv[1:]
    compat = "--compat" in args
    args = [a for a in args if a != "--compat"]
    fs = list(files(args))
    n = sum(modularize(f) for f in fs)
    print(f"modularized {n} file(s)")
    if compat:
        print(f"compat options added to {sum(add_compat(f) for f in fs)} file(s)")
