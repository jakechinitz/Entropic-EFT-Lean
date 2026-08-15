#!/usr/bin/env python3
from pathlib import Path
import re, sys
root=Path(__file__).resolve().parents[1]
fail=[]
for p in [root/'EntropicEFT.lean', *sorted((root/'EntropicEFT').rglob('*.lean'))]:
    s=p.read_text()
    # Strip nested-ish documentation/comments iteratively and line comments.
    old=None
    while old != s:
        old=s
        s=re.sub(r'/-[^/]*?-/', '', s, flags=re.S)
    s=re.sub(r'--.*','',s)
    # Strip strings conservatively.
    s=re.sub(r'"(?:\\.|[^"\\])*"','""',s)
    stack=[]; pairs={')':'(',']':'[','}':'{'}
    for i,ch in enumerate(s):
        if ch in '([{': stack.append((ch,i))
        elif ch in ')]}':
            if not stack or stack[-1][0]!=pairs[ch]:
                fail.append(f'{p}: delimiter mismatch near offset {i}')
                break
            stack.pop()
    else:
        if stack: fail.append(f'{p}: unclosed delimiter {stack[-1]}')
if fail:
    print('\n'.join(fail)); sys.exit(1)
print('delimiter sanity passed')
