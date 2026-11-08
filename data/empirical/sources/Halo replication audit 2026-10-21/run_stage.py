"""Run an unchanged stage copy using the preserved shared numerical modules."""
from pathlib import Path
import runpy, sys
here = Path(__file__).resolve().parent
quiet = here.parent / 'Halo quiet realization 2026-10-21'
stage = sys.argv.pop(1)
assert stage in ['seed_exact.py', 'quiet_fit.py', 'live_quiet_fast.py']
sys.path.insert(0, str(quiet))
sys.path.insert(0, str(here))
sys.argv[0] = str(here / stage)
runpy.run_path(str(here / stage), run_name='__main__')
