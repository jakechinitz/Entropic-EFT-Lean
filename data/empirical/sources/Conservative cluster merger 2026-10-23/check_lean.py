from pathlib import Path
from datetime import datetime
import os,subprocess,json,re,hashlib,sys
sys.stdout.reconfigure(encoding='utf-8')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
base=ROOT/'02 Research/Unified closure 2026-10-21'
lib=base/'formalization/.lake/packages';env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in lib.iterdir()
                               if (p/'.lake/build/lib/lean').exists())
src=HERE/'formalization/MergerContact.lean';content=src.read_text(encoding='utf-8')
names=re.findall(r'^theorem\s+(\w+)',content,re.M)
stamp=datetime.now().strftime('%Y%m%d_%H%M%S');audit=HERE/'formalization'/f'Audit_{stamp}.lean'
audit.write_text(content+'\n'+''.join(f'#print axioms MergerContact.{n}\n' for n in names),encoding='utf-8')
p=subprocess.run([str(base/'toolchain/lean-4.19.0-windows/bin/lean.exe'),str(audit)],env=env,capture_output=True,encoding='utf-8',errors='replace')
log=HERE/'logs'/f'lean_{stamp}.log';log.write_text(p.stdout+p.stderr,encoding='utf-8')
record={'success':p.returncode==0,'theorems':len(names),'names':names,
 'compiler':'Lean/mathlib 4.19 standalone supplement; not a rebuild of upstream 4.35',
 'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log':str(log),
 'audit_source':str(audit),'contains_sorry':bool(re.search(r'\bsorry\b',content))}
(HERE/'results'/f'lean_{stamp}.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record),flush=True);print((p.stdout+p.stderr)[-12000:])
