from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,html
import numpy as np
from scipy.optimize import brentq
from model import clock_homogeneous
from hermitian_contact import speed
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def read(n):return json.loads((HERE/'results'/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write_new(path,data):
    with path.open('x',encoding='utf-8') as f:f.write(data)

old=ROOT/'02 Research/Connected theory closure 2026-10-23'
manifest=json.loads((old/'source_records/input_manifest.json').read_text(encoding='utf-8'))
assert all(sha(ROOT/r['path'])==r['sha256'] for r in manifest['inputs'])
inputs=list(manifest['inputs'])
for rel in ['Research note/main.tex','Research note/main.pdf','formalization/ConnectedClosure.lean','results/adaptive_boundary_refined.json']:
    p=old/rel;inputs.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p)})
for rel in ['stock_model.py','fixed_L_z25_smooth.json','fixed_L_z25_smooth.npz','smooth_independent_results.json']:
    p=ROOT/'02 Research/Stock adjustment resolution 2026-10-21'/rel
    inputs.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p)})
write_new(HERE/'source_records/input_manifest.json',json.dumps({'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'prior_inputs_verified':len(manifest['inputs']),'inputs':inputs,
 'other_chat_read':'01a15c78-1f27-77c1-87c4-38214489f51b; latest assessment of the source-clock floor',
 'upstream_head_from_prior_audit':manifest['github_head']},indent=2))
cell=read('closed_cell.json');orb=read('local_contact.json');joint=read('hermitian_contact.json')
interface=read('interfaces.json');follow=read('interface_followup.json');ham=read('positive_hamiltonian.json')
lean=read(sorted(p.name for p in (HERE/'results').glob('lean_*.json'))[-1])
log=Path(lean['log']).read_text(encoding='utf-8')
assert lean['success'] and lean['theorems']==28 and 'sorryAx' not in log
assert sha(HERE/'formalization/EffectiveContact.lean')==lean['source_sha256']
assert len(re.findall('depends on axioms:',log))==28
assert max(r['max_absolute_total_energy_error'] for r in cell['rows'])<3e-11
assert all(abs(r['final_weight']-r['predicted_endpoint'])<1e-10 for r in cell['rows'])
assert all(r['target_radial_CDF_KS_error']<.007 for r in orb['rows'])
assert all(r['contact_energy_identity_error']<1e-12 for r in orb['rows'])
assert all(r['minimum_clock_energy_above_floor']>=0 for r in joint['rows'])
assert joint['rows'][-1]['radial_CDF_KS_from_requested_target']<.015
assert joint['rows'][-2]['radial_CDF_KS_from_requested_target']>.4
assert ham['minimum_interaction_eigenvalue']>-1e-12
assert ham['minimum_full_hamiltonian_eigenvalue']>=ham['free_floor']-1e-12
assert ham['bare_energy_commutator_max']==0 and max(ham['angular_commutators_max'])==0
assert ham['floor_coupling_max']==0
early=[r for r in follow['rows'] if r['final_time']==.1]
early_order=np.log2(early[0]['max_fractional_total_energy_change']/early[-1]['max_fractional_total_energy_change'])/2
assert 1.8<early_order<2.2
late=follow['rows'][-1]
assert late['max_fractional_total_energy_change']>.003
assert all(r['minimum_J']>=0 and r['minimum_X']>=0 for r in interface['rows']+follow['rows'])
speed_error=[]
for energy in np.r_[1+np.geomspace(1e-8,.1,100),np.linspace(1.1,2.5,100)]:
    j=brentq(lambda j:clock_homogeneous(j)[2]-energy,0,5,xtol=1e-13)
    speed_error.append(abs(speed(energy)-clock_homogeneous(j)[0]))
assert max(speed_error)<1e-6
report={'checked_utc':datetime.now(timezone.utc).isoformat(),'checks_passed':True,
 'input_files_recorded':len(inputs),'prior_input_hashes_unchanged':len(manifest['inputs']),
 'Lean':lean,'early_interface_energy_convergence_order':early_order,
 'late_interface_fractional_energy_deficit':late['max_fractional_total_energy_change'],
 'late_interface_conservative_closure_accepted':False,
 'max_clock_speed_interpolation_error_on_tested_energy_domain':max(speed_error),
 'coupled_fine_step_max_energy_error':max(r['max_absolute_energy_ledger_error'] for r in joint['rows'] if r['dt']==.005),
 'new_empirical_fit':False,'full_multistream_action_derived':False,'physical_rate_selected':False,
 'target_distribution_predicted':False,'positive_hamiltonian_witness_verified':True}
write_new(HERE/'VALIDATION.json',json.dumps(report,indent=2))
connections=[
 {'prior':'ConnectedClosure.current_factorization and regular_rate_positivity',
  'new':'gated_current_regular; power_gate_factor; insufficient_supply_bound',
  'scope':'A bounded work coefficient multiplying v squared preserves the regular positive-current form.'},
 {'prior':'Main paper O.3 retained radial update; RetainedRelaxation.lean',
  'new':'Local velocity kernel and actual Hamiltonian transport; local_population_conserved and central_impulse_angular',
  'scope':'A supplied orbital target has a local positive velocity transition with protected angular data; no target selection is proved.'},
 {'prior':'ConnectedClosure noise-delay and rate-rescaling results',
  'new':'Joint work/bath Hamiltonian, symmetric_edge_gate and joint_transition_energy',
  'scope':'An explicit effective energy-conserving interaction exists. Bath spectrum and physical rate remain open.'},
 {'prior':'Positive scalar floor in the preceding note',
  'new':'positive_edge_form and least_trace_positive_completion',
  'scope':'The selected positive Hamiltonian interaction does not lower the free lower bound. Spatial stress completion remains open.'}
]
write_new(HERE/'source_records/theorem_connections.json',json.dumps(connections,indent=2))
css='''body{font:17px/1.55 system-ui,sans-serif;color:#172d3d;background:#f4f7f9;margin:0}main{max-width:1080px;margin:auto;padding:40px 28px}h1{font-size:36px;line-height:1.15}h2{font-size:25px;margin-top:35px}a{color:#12619a}img{max-width:100%;border:1px solid #d7e0e6;background:white}.box{padding:20px;background:white;border-left:5px solid #2f7180}.warn{border-left-color:#ab742a}.formula{font:23px/1.6 Georgia,serif;text-align:center;background:white;padding:16px}.small{font-size:14px;color:#455b6b}.links{display:flex;gap:20px;flex-wrap:wrap}li{margin:8px 0}'''
page=f'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Effective stock dynamics and clock coupling</title><style>{css}</style><main>
<p class="small">SOL AND FABLE · RESEARCH CONSTRUCTION · 23 OCTOBER 2026</p>
<h1>A local redistribution contact with a finite work supply</h1>
<p>The new construction links actual orbital motion, retained angular information and the clock's self-limiting depletion phase. It specifies a possible interaction and its accounting; it does not select the physical halo target or rate.</p>
<p class="links"><a href="Research%20note/main.pdf"><strong>Derivation note (PDF)</strong></a><a href="VALIDATION.json">Verification record</a><a href="formalization/EffectiveContact.lean">Lean certificates</a><a href="REPRODUCE.txt">Reproduction guide</a></p>
<div class="box"><strong>New result:</strong> an energy-conserving effective interaction can redistribute orbital stock, preserve the stated angular labels, and become inactive at the resting floor. A positive diagonal completion also prevents the interaction from lowering the free energy bound. The source clock remains a scalar relative to proper time.</div>
<h2>The clock controls available work</h2><div class="formula">P = v² B<br>j̇ = −[θ + V<sub>φ</sub>A j/λ² + B/λ] j</div>
<p>For bounded B, the fractional drain stays regular as the current approaches zero. A contact with inadequate work stops short of its target. The floor is not an unlimited power supply.</p>
<img src="figures/closed_cell.png" alt="Two-state work demand with sufficient and insufficient clock energy">
<h2>Particles move under a local interaction</h2>
<p>Hamiltonian motion transports the particles. The contact changes radial velocities at their current positions; it does not move density instantly between radii. Radial impulses preserve angular momentum, and the finite carrier must carry the opposite linear impulse. The existing positive orbit weights can supply a target through the orbital density of states.</p>
<img src="figures/local_contact.png" alt="Particle distribution approaches a declared orbital target with a checked work and heat ledger">
<h2>An explicit joint Hamiltonian</h2>
<p>Each transition changes the orbit, draws W = ΔE + Q from a work register, and transfers Q to a bath. Its clock amplitude is symmetric between the initial and final register energies. The rate factor is v(U)v(U−W); unavailable transitions have zero amplitude.</p>
<p>A positive rank-one completion of every exchange edge preserves the free lower bound. The 72-state Hamiltonian test checks Hermiticity, energy and all three angular commutators, the decoupled floor, and the full spectrum. This finite closed-bath witness is not a Markov or microscopic bath derivation.</p>
<img src="figures/hermitian_contact.png" alt="Finite-event symmetric contact reaches or fails to reach its target depending on available work">
<p class="small">The finer coupled test uses 12,000 particles. Its largest energy-ledger error is {report['coupled_fine_step_max_energy_error']:.3g}. The low-supply state remains far from the requested distribution. All units and targets here are illustrative; no new galaxy fit was performed.</p>
<h2>The spatial test exposes the next missing part</h2>
<div class="box warn"><strong>Sharp-front closure is not accepted.</strong> Smooth early evolution has energy-error convergence of order {early_order:.2f}. The late scalar-only run retains a {100*late['max_fractional_total_energy_change']:.3f}% resolved-energy deficit at 2048 cells. Current and the local floor remain positive, but the physical destination and feedback of unresolved energy need a kinetic or thermal stress model.</div>
<img src="figures/interface.png" alt="Depleted and undepleted regions drive waves and later compressive fronts">
<h2>Physical inputs still to select</h2><ul>
<li>The equilibrium orbital distribution and its self-consistency with an evolving halo.</li>
<li>The interaction matrix elements, bath spectrum and a common physical relaxation rate.</li>
<li>The common scalar, kinetic and bath stress, including interfaces and multistream inertia.</li>
</ul><p>The high-redshift a₀ tension remains unresolved. The supplied target and rate make this a testable effective completion hypothesis, not a unique consequence of the microstructure.</p>
<h2>Verification and preservation</h2>
<p><strong>28 new standalone Lean certificates passed</strong> with standard logical axioms only. They check the stated algebra and bounds; the simulations and Hamiltonian matrices have separate records. The available 4.19 runtime was used, without rebuilding upstream 4.35.</p>
<p class="small">{len(manifest['inputs'])} prior input hashes verified unchanged. Current publications and upstream proofs remain intact. Earlier one-sided gates, the exchange-only Hamiltonian and failed checks are preserved. <a href="source_records/theorem_connections.json">Connections to the previous proofs</a>.</p></main></html>'''
write_new(HERE/'START HERE.html',page)
print(json.dumps(report))
