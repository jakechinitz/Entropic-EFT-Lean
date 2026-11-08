from pathlib import Path
import json,numpy as np
from thermal_interfaces import run
HERE=Path(__file__).resolve().parent
out=HERE/'results/thermal_refinement.json';assert not out.exists()
rows=[];data={}
for N in [1024,2048]:
    row,a=run(N);rows.append(row)
    data.update({f'n{N}_{key}':value for key,value in a.items()})
out.write_text(json.dumps({'purpose':'Resolve the heat and profile dependence of the conservative thermal extension at finer grids.','rows':rows},indent=2),encoding='utf-8')
np.savez_compressed(HERE/'results/thermal_refinement_traces.npz',**data)
