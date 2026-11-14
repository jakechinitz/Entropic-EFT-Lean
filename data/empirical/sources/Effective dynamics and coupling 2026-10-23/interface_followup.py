from pathlib import Path
import json,numpy as np
from interfaces import run
HERE=Path(__file__).resolve().parent
out=HERE/'results/interface_followup.json';assert not out.exists()
rows=[];arrays={}
for n,t in [(256,.1),(512,.1),(1024,.1),(2048,5.)]:
    r,a=run(n,t);rows.append(r)
    arrays.update({f'n{n}_t{t}_{k}':v for k,v in a.items()})
out.write_text(json.dumps({'reason':'The original long interface test loses resolved scalar energy as fronts steepen. Test the smooth early interval and refine the late interval before interpreting stability.','rows':rows},indent=2),encoding='utf-8')
np.savez_compressed(HERE/'results/interface_followup_traces.npz',**arrays)
