#!/usr/bin/env python3
"""Copy PrimeNumberTheoremAnd files into PNTPort/, dropping the blueprint (Architect) layer.
Usage: port_pnt.py SRC_ROOT DST_ROOT module...   (module paths relative to PrimeNumberTheoremAnd/)"""
import sys, os, re

def skip_comment(s, i):
    # s[i:] starts with '/-'; nested block comments
    depth = 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; i += 2
        elif s.startswith('-/', i):
            depth -= 1; i += 2
            if depth == 0: return i
        else: i += 1
    raise ValueError('unterminated comment')

def skip_string(s, i):
    i += 1
    while s[i] != '"':
        i += 2 if s[i] == '\\' else 1
    return i + 1

def match_bracket(s, i):
    """s[i] is an opening bracket; return index after its match."""
    pairs = {'[': ']', '(': ')', '{': '}'}
    stack = [pairs[s[i]]]; i += 1
    while stack:
        if s.startswith('/-', i): i = skip_comment(s, i); continue
        if s.startswith('--', i): i = s.index('\n', i); continue
        c = s[i]
        if c == '"': i = skip_string(s, i); continue
        if c in pairs: stack.append(pairs[c])
        elif c == stack[-1]: stack.pop()
        i += 1
    return i

def split_attrs(body):
    """Split an attribute list body at top-level commas."""
    parts, depth, cur, i = [], 0, '', 0
    while i < len(body):
        if body.startswith('/-', i):
            j = skip_comment(body, i); cur += body[i:j]; i = j; continue
        c = body[i]
        if c == '"':
            j = skip_string(body, i); cur += body[i:j]; i = j; continue
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        if c == ',' and depth == 0: parts.append(cur); cur = ''
        else: cur += c
        i += 1
    parts.append(cur)
    return parts

def strip_blueprint(s):
    out, i = [], 0
    while True:
        j = s.find('@[', i)
        k = s.find('blueprint_comment', i)
        if j < 0 and k < 0:
            out.append(s[i:]); break
        if k >= 0 and (j < 0 or k < j):
            out.append(s[i:k])
            m = k + len('blueprint_comment')
            while s[m] in ' \n': m += 1
            assert s.startswith('/-', m), s[k:k+80]
            i = skip_comment(s, m)
            if i < len(s) and s[i] == '\n': i += 1
            continue
        out.append(s[i:j])
        end = match_bracket(s, j + 1)
        body = s[j + 2:end - 1]
        parts = [p for p in split_attrs(body) if not p.strip().startswith('blueprint')]
        if parts and any(p.strip() for p in parts):
            out.append('@[' + ','.join(p.strip() for p in parts) + ']')
            i = end
        else:
            i = end
            while i < len(s) and s[i] in ' \n': i += 1
    return ''.join(out)

def port(src_root, dst_root, mod):
    s = open(os.path.join(src_root, 'PrimeNumberTheoremAnd', mod + '.lean')).read()
    s = re.sub(r'^(public )?import Architect\n', '', s, flags=re.M)
    s = strip_blueprint(s)
    s = re.sub(r'\bPrimeNumberTheoremAnd\.', 'PNTPort.', s)
    # names renamed in Mathlib between 56a005855ea1 and fc4f59e (nnnorm -> nnNorm, enorm -> eNorm)
    s = re.sub(r"(?<=[A-Za-z_.])nnNorm|(?<![A-Za-z])nnNorm", 'nnnorm', s)
    s = re.sub(r"(?<=[A-Za-z_.])eNorm|(?<![A-Za-z])eNorm", 'enorm', s)
    hdr = ('/- Ported from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/'
           'PrimeNumberTheoremAnd, commit e9906138410f, Apache-2.0) to the Mathlib pinned by '
           'grh-compact. Changes: blueprint attributes removed, module paths renamed, and API '
           'adaptations listed in PORTING.md. -/\n')
    lines = s.split('\n', 1)
    s = lines[0] + '\n\n' + hdr + lines[1] if lines[0].strip() == 'module' else hdr + s
    dst = os.path.join(dst_root, 'PNTPort', mod + '.lean')
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write(s)

if __name__ == '__main__':
    for m in sys.argv[3:]: port(sys.argv[1], sys.argv[2], m)
