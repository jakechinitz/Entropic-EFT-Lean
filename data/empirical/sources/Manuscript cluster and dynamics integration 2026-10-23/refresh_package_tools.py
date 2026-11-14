from pathlib import Path
import shutil,datetime
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];base=ROOT/'01 Current Papers/Empirical Results'
dest=base/'Previous PDFs'/(datetime.datetime.now().strftime('%Y%m%d_%H%M%S')+'_metadata_and_reproducer');dest.mkdir()
for name in ['README.txt','manifest.json','current_verification.json','refresh_verified_results.py','06_interpretation_and_audit.tex']:
 shutil.copy2(base/name,dest/name)
p=base/'refresh_verified_results.py';s=p.read_text(encoding='utf-8')
s=s.replace("parser.add_argument('--workspace',type=Path,default=default_root)","parser.add_argument('--workspace',type=Path,default=default_root)\nparser.add_argument('--legacy-linear',action='store_true',help='Reproduce the preserved linear-depletion comparison instead of the current exponential fit')")
anchor="outputs=[HERE/'current_verification.json']"
insert='''# The current paper uses the saved exponential-allocation fit. Earlier
# benchmarks remain reproducible through --legacy-linear and the archived inputs.
LATEST=ROOT/'02 Research/Unified empirical program 2026-10-23/results/cosmology_final.json'
REGISTER=ROOT/'02 Research/Unified empirical program 2026-10-23/execution_register.json'
EXTENSIONS=ROOT/'02 Research/Manuscript cluster and dynamics integration 2026-10-23/lean_validation_integrated.json'
if not args.legacy_linear:
    latest=json.loads(LATEST.read_text(encoding='utf-8'))
    comp=dict(latest['verification'])
    comp['delta_AIC_conditional_five_vs_six']=comp['delta_AIC_conditional_parameter_counts_5_vs_6']
    geo={'model':'geodesic','allocation':'exponential','parameters':latest['fit_parameters'],
         'parts_higher_accuracy':comp['geodesic'],'Alens':1,'nonlinear':'none',
         'source':str(LATEST.relative_to(ROOT))}
    lcdm={'model':'lcdm','parameters':latest['lcdm_parameters'],
          'parts_higher_accuracy':comp['lcdm'],'Alens':1,'nonlinear':'none'}
    assert abs(comp['delta_chi2']-(comp['geodesic']['total']-comp['lcdm']['total']))<1e-10
    for model in ['geodesic','lcdm']:
        q=comp[model]
        assert abs(q['total']-sum(q[k] for k in ['cmb','bao','sn']))<1e-9

'''
assert s.count(anchor)==1;s=s.replace(anchor,insert+anchor)
s=s.replace("'positive_allocation_likelihood':'not performed'","'positive_allocation_likelihood':('archived linear comparison selected' if args.legacy_linear else 'completed; saved exponential fit imported')")
s=s.replace("'fit':'linear-depletion geodesic-clock background; linear lensing, Alens=1'","'fit':('linear-depletion' if args.legacy_linear else 'exponential-allocation')+' geodesic-clock background; linear lensing, Alens=1'")
anchor="(HERE/'current_verification.json').write_text"
extra='''if not args.legacy_linear:
    record['cross_sector_register']=json.loads(REGISTER.read_text(encoding='utf-8'))
    record['lean']['extensions_standalone']=json.loads(EXTENSIONS.read_text(encoding='utf-8'))
    record['lean']['extensions_pr']='https://github.com/jakechinitz/Entropic-EFT-Lean/pull/4'
    for source in [LATEST,REGISTER,EXTENSIONS]:
        record['source_hashes'][source.relative_to(ROOT).as_posix()]=hashlib.sha256(source.read_bytes()).hexdigest()
    record['scope']='Arithmetic recalculation and saved exponential-fit/result import; no new simulation or cosmological optimization. Standalone Lean checks were rerun during integration; pinned-build status is recorded separately.'
'''
assert s.count(anchor)==1;s=s.replace(anchor,extra+anchor)
p.write_text(s,encoding='utf-8')
p=base/'06_interpretation_and_audit.tex';s=p.read_text(encoding='utf-8')
a=s.index('The supplementary \\path{refresh_verified_results.py}');b=s.index('Build the publication',a)
s=s[:a]+r'''The supplementary \path{refresh_verified_results.py} updates the
unrounded redshift arithmetic and imports the saved exponential-allocation
fit. It preserves prior outputs before writing. Its
\texttt{-{}-legacy-linear} option reproduces the earlier matched benchmark.
The broader calculations and source records are identified by U1 and C5.
''' +s[b:]
p.write_text(s,encoding='utf-8')
print('Reproducer default updated; original bytes preserved at',dest)
