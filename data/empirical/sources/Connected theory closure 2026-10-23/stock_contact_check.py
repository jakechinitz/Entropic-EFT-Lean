from pathlib import Path
import json
import numpy as np
from boundary_completion import background,ETA
HERE=Path(__file__).resolve().parent
bg=background(80000);x,a,C,V,H,T,state,potential=bg
z=2.3;xx=-np.log1p(z)
Ci=state(xx)[1];Hi=state(xx)[3]
mass_ratio=C[-1]/(Ci*np.exp(3*xx))
report={
 'scope':'Adiabatic homologous, isolated, self-gravitating stock with conserved canonical orbital actions; baryon mass held fixed. Not a theorem for arbitrary mergers or scalar gradients.',
 'start_redshift':z,'mass_ratio':mass_ratio,
 'adiabatic_radius_ratio':mass_ratio**(-3),
 'adiabatic_speed_ratio':mass_ratio**2,
 'implied_a0_ratio_from_v4':mass_ratio**8,
 'required_H_tracking_a0_ratio':H[-1]/Hi,
 'mass_ratio_needed_in_this_model':(H[-1]/Hi)**(1/8),
 'smallest_a0_ratio_from_any_full_one_unit_release':np.exp(-8*ETA),
 'conclusion':'Cosmological mass loss alone does not produce the required equilibrium tracking in this controlled model. A physical redistribution/response contact is required.',
 'conversion_identity':'D f_u=-Gamma f_u; D f_R=+Gamma f_u implies D(f_u+f_R)=0 for a common Hamiltonian. Relabeling alone changes no total gravitational source.'
}
out=HERE/'results/stock_contact.json'
if out.exists():raise RuntimeError('Preserve previous result')
out.write_text(json.dumps(report,indent=2),encoding='utf-8');print(json.dumps(report))
