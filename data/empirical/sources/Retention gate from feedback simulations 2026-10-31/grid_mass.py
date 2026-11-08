import numpy as np, json, sys
from gate_mass import *
zre = float(sys.argv[1]); vpost = float(sys.argv[2]); out = sys.argv[3]
res = {}
for lM in np.round(np.arange(float(sys.argv[4]) if len(sys.argv)>4 else 6.5, 9.01 if len(sys.argv)<6 else float(sys.argv[5]), 0.1), 2):
    FZ = first_entry_M(float(lM), zre=zre, v_post=vpost)
    r = irel_all(FZ); res[str(lM)] = {k: v[0] for k, v in r.items()}; res[str(lM)]['F0'] = list(r.values())[0][1]
    print(lM, round(np.mean([v[0] for v in r.values()]), 1), flush=True)
json.dump(res, open(out, 'w'), indent=1)
