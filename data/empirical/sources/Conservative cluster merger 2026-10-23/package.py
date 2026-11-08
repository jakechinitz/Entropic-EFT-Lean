"""Package existing science and verify the delivered note; no new simulations."""
from pathlib import Path
from datetime import datetime,timezone
from html.parser import HTMLParser
from urllib.parse import unquote,urlparse
import hashlib,json,re,subprocess,importlib.metadata
import numpy as np
import pymupdf
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
    with p.open('x',encoding='utf-8') as f:f.write(s)
r=json.loads((HERE/'ASSESSMENT.json').read_text(encoding='utf-8'))
assert r['checks_passed'] and r['completed_runs']==17 and r['Lean']['theorems']==8
checked=json.loads((HERE/'source_records/input_manifest.json').read_text())
assert all(sha(ROOT/x['path'])==x['sha256'] for x in checked['inputs'])
old=json.loads((ROOT/'02 Research/Effective dynamics and coupling 2026-10-23/source_records/input_manifest.json').read_text())
assert all(sha(ROOT/x['path'])==x['sha256'] for x in old['inputs'])
for name,data in r['runs'].items():
    p=HERE/'results'/name
    assert sha(p/'executed_source.py')==data['source_sha256']
    a=np.load(p/'initial.npz');b=np.load(p/'history.npz')
    assert np.array_equal(a['m'],b['m']) and np.array_equal(a['cohort'],b['cohort'])
assert r['Lean']['success'] and not r['Lean']['contains_sorry']
assert sha(HERE/'formalization/MergerContact.lean')==r['Lean']['source_sha256']
base=np.load(HERE/'results/baseline_optimized/history.npz');floor=np.load(HERE/'results/exact_floor/history.npz')
assert np.array_equal(base['v'],floor['v'])

css='''body{font:17px/1.55 system-ui,sans-serif;background:#f4f7f9;color:#1b3143;margin:0}main{max-width:1050px;margin:auto;padding:35px 28px}h1{font-size:35px;line-height:1.15}h2{font-size:24px;margin-top:32px}a{color:#175f91}img{max-width:100%;background:white}table{border-collapse:collapse;background:white;width:100%}th,td{padding:11px;text-align:left;border-bottom:1px solid #d8e0e8}.box{padding:20px;background:white;border-left:5px solid #277b88}.warning{border-left-color:#b17725}.small{font-size:14px;color:#496173}.links{display:flex;gap:20px;flex-wrap:wrap}'''
html=f'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Conservative cluster encounter</title><style>{css}</style><main>
<p class="small">SOL AND FABLE · RESEARCH CALCULATION · 23 OCTOBER 2026</p>
<h1>A live cluster encounter with finite local work exchange</h1>
<p>Stock, stellar tracers and baryonic gas evolve in one three-dimensional gravitational potential. A reciprocal contact exchanges radial velocity, work and heat. The initial profiles and rates were supplied before inspecting any final map.</p>
<p class="links"><a href="Research%20note/main.pdf"><strong>Read the derivation and results</strong></a><a href="ASSESSMENT.json">Complete assessment</a><a href="formalization/MergerContact.lean">Eight new Lean certificates</a><a href="REPRODUCE.txt">Reproduction guide</a><a href="DELIVERY_VALIDATION.json">Delivery checks</a></p>
<div class="box"><strong>Conditional result:</strong> weak contact allows stellar-associated mass concentrations to pass through while the gas is displaced. The feature survives the tested particle refinement and second sampling. The common gravitational source includes each component once.</div>
<h2>Seventeen completed runs</h2>
<img src="figures/merger_maps.png" alt="Four projected encounters compare no contact, weak contact, strong contact and nearly depleted registers">
<p class="small">Cyan: total projected mass. White: stellar tracers. Color: gas-emission proxy normalized separately in each panel. The first three panels use 2,688 elements; the depleted case uses 1,344. These are synthetic maps of a declared encounter, not observed lensing or X-ray reconstructions.</p>
<table><tr><th>Test</th><th>Result</th></tr>
<tr><td>Weak interaction</td><td>The smaller cluster retains stock–stellar alignment relative to its much larger stock–gas displacement.</td></tr>
<tr><td>Nearly depleted registers</td><td>61 accepted contacts versus 7,114 for the active case at the same nominal rate. The encounter closely follows the zero-contact control.</td></tr>
<tr><td>Exact floor</td><td>No accepted contact; particle trajectories are identical to the zero-contact control.</td></tr>
<tr><td>Energy and reaction</td><td>Worst energy drift is below 0.00684% of initial gravitational binding. Momentum and angular momentum remain conserved to numerical precision. The baseline timestep test has order 2.003.</td></tr>
<tr><td>Collisionless baryon control</td><td>The large gas-labelled component offset disappears when that component is given collisionless velocity support.</td></tr></table>
<h2>The equilibrium target now supplies a concrete constraint</h2>
<img src="figures/isolated_controls.png" alt="The strong contact contracts isolated stock and expands gas before an encounter occurs">
<div class="box warning"><strong>Strong contact does not preserve the declared starting halo.</strong> In the isolated control it contracts the stock median radius by about 27% and expands the gas radius by about 46% over six dynamical units. A merger-shaped map alone therefore cannot validate this target and rate. The physical interaction must preserve an intended equilibrium or predict its secular evolution.</div>
<p>Negative work can also recharge the clock registers. Depletion suppresses exchange, but a nonzero initial surplus is not a guarantee of monotonically declining activity. The exact resting gate remains absorbing.</p>
<h2>What is still being specified</h2>
<p>The contact uses a selected pair-relative velocity target, finite range, rate and initial work allocation. It extends the earlier single-carrier construction; its global stationary distribution is not established by that earlier theorem. Its effective heat coefficients are pair-channel dependent and do not define one global equilibrium bath.</p>
<p>The full spatial clock/floor-fluid stress is not evolved. Baryonic gas uses gamma = 5/3 SPH; stock remains kinetic. Register energies are internal to existing elements and their small gravitational mass correction is omitted at Newtonian order.</p>
<p>No observed cluster likelihood, galaxy/cluster common-rate fit, assembly prediction or high-redshift a₀ repair has been obtained here. The next physical calculation is the equilibrium and rate selection, followed by higher-resolution observational modeling.</p>
<h2>Preservation and checks</h2>
<p>All 17 completed runs retain their initial states, full sampled histories and executed sources. The interrupted slow baseline and the original record for one source-hash metadata repair are preserved. The eight new Lean statements check local identities with standard logical axioms; they do not certify the entire simulation. Earlier research and all current publications remain intact.</p>
</main></html>'''
write(HERE/'START HERE.html',html)
class Links(HTMLParser):
    def __init__(self):super().__init__();self.links=[]
    def handle_starttag(self,tag,attrs):self.links.extend(v for k,v in attrs if k in ('href','src'))
p=Links();p.feed(html)
for link in p.links:
    if not urlparse(link).scheme and link!='DELIVERY_VALIDATION.json':assert (HERE/unquote(link)).is_file()
doc=pymupdf.open(HERE/'Research note/main.pdf')
assert len(doc)==8 and '??' not in ''.join(page.get_text() for page in doc)
build=max((ROOT/'05 Build Files/PDF builds/main').glob('*/main.log'),key=lambda x:x.stat().st_mtime)
log=build.read_text(encoding='utf-8',errors='replace')
assert 'Overfull' not in log and 'undefined references' not in log and not re.search(r'^! ',log,re.M)
pub=subprocess.run(['python',str(ROOT/'.organization/publication_set.py'),'check'],cwd=ROOT,text=True,capture_output=True)
assert pub.returncode==0 and 'OK:' in pub.stdout
files=list(HERE.glob('*.py'))+[HERE/'Research note/main.tex',HERE/'Research note/main.pdf',HERE/'formalization/MergerContact.lean',HERE/'ASSESSMENT.json',HERE/'START HERE.html',HERE/'REPRODUCE.txt']
verification={'checked_utc':datetime.now(timezone.utc).isoformat(),'checks_passed':True,'completed_simulations':17,
    'publication_check':pub.stdout.strip(),'pdf_pages':len(doc),'visual_review':'All eight pages inspected in Review render 20261023_133849; equations, table, maps and captions checked.',
    'prior_unchanged_input_hashes':len(old['inputs']),'additional_inputs_checked':len(checked['inputs']),
    'source_snapshots_verified':len(r['runs']),'exact_floor_position_and_velocity_match':True,
    'Lean_statements':8,'Lean_scope':'Local algebra and conditional signs; no whole-simulation theorem.',
    'runtime_versions':{name:importlib.metadata.version(name) for name in ['numpy','scipy','numba','matplotlib','pymupdf']},
    'build_log':str(build.relative_to(ROOT)),
    'files':[{'path':str(f.relative_to(HERE)),'sha256':sha(f)} for f in files],
    'empirical_fit':False,'physical_rate_selected':False,'full_spatial_clock_stress_evolved':False}
write(HERE/'DELIVERY_VALIDATION.json',json.dumps(verification,indent=2))
print(json.dumps({k:verification[k] for k in ['checks_passed','completed_simulations','pdf_pages','prior_unchanged_input_hashes','Lean_statements']}))
