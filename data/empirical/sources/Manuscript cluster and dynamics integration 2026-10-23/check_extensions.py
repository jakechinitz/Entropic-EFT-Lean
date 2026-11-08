from pathlib import Path
import json,subprocess,os,re,datetime,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'02 Research/Unified closure 2026-10-21'
LIB=BASE/'formalization'
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in (LIB/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').exists())
stamp=datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
out=HERE/'lean_checks'/stamp;out.mkdir(parents=True)
records=[]
for m in json.loads((HERE/'lean_modules.json').read_text()):
    if sys.argv[1:] and m['module'].split('.')[-1] not in sys.argv[1:]: continue
    src=LIB/m['path'];content=src.read_text(encoding='utf-8')
    namespace=re.search(r'^namespace\s+(\S+)',content,re.M).group(1)
    names=re.findall(r'^theorem\s+(\S+)',content,re.M)
    audit=out/src.name
    audit.write_text(content+'\n'+''.join(f'#print axioms {namespace}.{n}\n' for n in names),encoding='utf-8')
    p=subprocess.run([str(BASE/'toolchain/lean-4.19.0-windows/bin/lean.exe'),str(audit)],env=env,capture_output=True,encoding='utf-8',errors='replace')
    (out/(src.stem+'.log')).write_text(p.stdout+p.stderr,encoding='utf-8')
    axioms=set()
    for a in re.findall(r'depends on axioms: \[(.*?)\]',p.stdout,re.S): axioms.update(x.strip() for x in a.split(','))
    bad=axioms-{'propext','Classical.choice','Quot.sound',''}
    r={'module':m['module'],'theorems':len(names),'exit_code':p.returncode,'nonstandard_axioms':sorted(bad),'success':p.returncode==0 and not bad and 'sorryAx' not in p.stdout and "declaration uses 'sorry'" not in p.stdout}
    records.append(r);print(json.dumps(r),flush=True)
(out/'validation.json').write_text(json.dumps({'toolchain':'Lean/mathlib 4.19.0','passed':all(r['success'] for r in records),'records':records},indent=2),encoding='utf-8')
assert all(r['success'] for r in records)
