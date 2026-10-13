#!/usr/bin/env python3
"""Render docs/leanbugs.md from the run.sh outputs in ~/lean-ext/e85-work/lb (one directory per entry)."""
import os, re, sys, glob
LB = os.path.expanduser('~/lean-ext/e85-work/lb')
ENTRIES = [  # id, repro-on, note
 ('lean-0001','v4.32.1','proof of `False`: wrong-structure projection (lean4#14576)'),
 ('lean-0002','v4.33.0','proof of `False`: `is_def_eq` cache depended on the order of checks (lean4#14806)'),
 ('lean-0003','v4.33.1','FLT by `native_decide` (lean4#14684); the export declares `flt._native.native_decide.ax_1_1` as an axiom'),
 ('lean-0004','v4.33.0','`infer_let` wrong result (lean4#10475): the repro is a valid theorem the 4.24.0 kernel cannot type, so it is built on a fixed Lean and the question is whether the checkers accept it'),
 ('lean-0006','v4.32.1','proof of `False`: sorts not recognised as `Prop` up to universe normalisation (lean4#14613)'),
 ('lean-0008','v4.33.0','proof of `False`: `is_prop` did not require a sort (lean4#14807)'),
 ('lean-0012','v4.32.1','`mutB : Sort u → Sort u` with `u` undeclared (lean4#14608)'),
 ('lean-0014','v4.33.0','completeness: a valid inductive predicate in `Sort (imax 1 0)` the 4.32.1 kernel rejected (lean4#14615); built on a fixed Lean'),
]
def read(p):
    try: return open(p, encoding='utf-8', errors='ignore').read()
    except FileNotFoundError: return ''
def jvm(d):
    s = read(f'{d}/jvm.out')
    if not s: return ('pending','')
    rej = re.findall(r'^REJECTED .*', s, re.M)
    if rej: return ('rejects', rej[0][:140])
    ax = re.search(r'^axioms declared: (.*)$', s, re.M)
    return ('accepts', 'axioms declared: ' + ax.group(1)) if 'all declarations verified' in s else ('?', s[-200:])
def tenet(d):
    s = read(f'{d}/tenet.out')
    if not s: return ('pending','')
    last = [l for l in s.splitlines() if l.startswith(('OK:','FAILED:','DECLINED'))]
    v = last[-1] if last else s[-160:]
    fails = re.findall(r'^\s*[0-9.]+s\s+failed \d+\s+(\S+)', s, re.M)
    return ('rejects' if v.startswith('FAILED') else 'accepts' if v.startswith('OK') else 'declines', (fails[0] + ': ' if fails else '') + v[:120])
def hs(d):
    s = read(f'{d}/hs.out')
    if not s or not re.search(r'^(OK:|FAILED:|DECLINED)', s, re.M): return ('pending','')
    fails = re.findall(r'^FAIL (.*?) \(', s, re.M)
    last = [l for l in s.splitlines() if l.startswith(('OK:','FAILED:','DECLINED'))][-1]
    return ('rejects' if last.startswith('FAILED') else 'accepts' if last.startswith('OK') else 'declines', (fails[0] + ': ' if fails else '') + last[:120])
out = ['# The Lean bug corpus, checked by three independent kernels', '',
 'Results of running the repros of [leanbugs.com](https://leanbugs.com) (`sflean/leanbugs`) through Tenet (C#),',
 'tenet-hs (Haskell) and tenet-jvm (Java). Each repro is compiled with the Lean version the corpus says it',
 'reproduces on, exported with the matching `lean4export`, and given to each kernel. "rejects" means the',
 'kernel refused the bad declaration; "accepts" means it did not. The driver is `tools/leanbugs/run.sh`;',
 'this page is produced by `tools/leanbugs/report.py`. Entries without a `.lean` repro (0007, 0009, 0010,',
 '0011, 0013, 0015) and lean-0005 (a library `#eval`, nothing a kernel sees) are not run.', '',
 '| Entry | Built on | tenet-jvm | Tenet | tenet-hs |', '|---|---|---|---|---|']
details = []
for id_, ver, note in ENTRIES:
    d = f'{LB}/{id_}'
    r = {'tenet-jvm': jvm(d), 'Tenet': tenet(d), 'tenet-hs': hs(d)}
    out.append(f'| {id_} | {ver} | ' + ' | '.join(f'**{r[k][0]}**' for k in ('tenet-jvm','Tenet','tenet-hs')) + ' |')
    details.append(f'### {id_}\n\n{note}\n\n' + '\n'.join(f'- {k}: {v[0]}' + (f' — `{v[1]}`' if v[1] else '') for k, v in r.items()) + '\n')
out += ['', 'Four of the proofs of `False` (0001, 0002, 0006, 0008) are also in the Lean Kernel Arena\'s `bugs/` group',
 'as independent exports, where all three kernels reject them too.', '',
 '## What lean-0003 shows', '',
 'On Lean 4.33.1 `native_decide` does not reach the export as `Lean.ofReduceBool`; the compiler adds a',
 'per-proof **axiom** (`flt._native.native_decide.ax_1_1`) to the environment, and the export declares it',
 'exactly as it declares `propext`. A kernel that checks exports cannot tell the two apart. All three accept',
 'the file and list the axiom; whether that counts as "fooled" depends on whether anyone reads the axiom',
 'list, which is the corpus\'s `print-axioms` checker. A checker option that fails on any axiom outside the',
 'standard three would turn this into a rejection.', '', '## Per entry', ''] + details
open(os.path.expanduser('~/tenet-jvm/docs/leanbugs.md'), 'w').write('\n'.join(out))
print('\n'.join(out[9:19]))
