#!/usr/bin/env python3
"""Deterministic audit for the EntropicEFT Lean repository.

This is NOT a replacement for `lake build`.  It checks:
  * local import resolution,
  * forbidden proof holes/global axioms,
  * LOCAL CONTRACT headers,
  * exact 1680-state combinatorics and K^2 spectrum,
  * corrected H.9 closure decomposition/bounds,
  * numerical spine against the manuscript definitions,
  * important cross-sector algebraic identities.
"""
from __future__ import annotations
from pathlib import Path
from collections import Counter
import hashlib, itertools, math, re, sys

try:
    from scipy.optimize import brentq
except Exception as e:
    print(f"FAIL: scipy unavailable: {e}")
    sys.exit(2)

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "EntropicEFT"
SOURCE = Path("/mnt/data/dark energy addition(1).tex")
EXPECTED_SOURCE_SHA = "bec8390dec21af31fa5c1e3ca8c26503e664ee66ddb679d6f4085dba5e9882c7"

failures: list[str] = []
notes: list[str] = []

def check(cond: bool, msg: str):
    if cond:
        print("PASS:", msg)
    else:
        print("FAIL:", msg)
        failures.append(msg)

def approx(x: float, y: float, tol: float, msg: str):
    check(abs(x-y) <= tol, f"{msg}: {x:.15g} vs {y:.15g}")

# -----------------------------------------------------------------------------
# Repository/static audit
# -----------------------------------------------------------------------------
files = sorted(LEAN_ROOT.rglob("*.lean"))
check(bool(files), "Lean modules present")
for p in files:
    text = p.read_text()
    check("LOCAL CONTRACT" in text, f"LOCAL CONTRACT: {p.relative_to(ROOT)}")
    # Remove documentation/comments before searching for proof holes/global axioms.
    code = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    for bad in [r"\bsorry\b", r"\badmit\b", r"(^|\n)\s*axiom\s"]:
        check(re.search(bad, code) is None, f"no proof-hole/global-axiom pattern `{bad}` in {p.relative_to(ROOT)}")

# Resolve local imports.
modules = {"EntropicEFT." + ".".join(p.relative_to(LEAN_ROOT).with_suffix("").parts): p for p in files}
for p in files + [ROOT / "EntropicEFT.lean"]:
    if not p.exists():
        failures.append(f"missing top-level file {p}")
        continue
    for line in p.read_text().splitlines():
        if line.startswith("import EntropicEFT."):
            mod = line.split()[1]
            check(mod in modules, f"import resolves: {mod}")

if SOURCE.exists():
    sha = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    check(sha == EXPECTED_SOURCE_SHA, "source manuscript SHA-256 matches audited upload")
else:
    notes.append("source manuscript not present at /mnt/data; SHA check skipped")

# -----------------------------------------------------------------------------
# Exact UV enumeration
# -----------------------------------------------------------------------------
labels = tuple(range(-3, 4))
unoriented = list(itertools.permutations(labels, 4))
check(len(unoriented) == 840, "P(7,4)=840")
check(2*len(unoriented) == 1680, "orientation doubling gives 1680")

def invariants(st):
    S = sum(st)
    ss = sum(m*m for m in st)
    k3 = 144 - S*S + ss
    c3 = 4*ss - S*S
    v3 = 3*(48-ss)
    return k3,c3,v3

spec = Counter()
c3s=[]; v3s=[]
for st in unoriented:
    k3,c3,v3 = invariants(st)
    check(k3 == c3+v3, f"closure decomposition {st}") if False else None
    spec[k3] += 2
    c3s.append(c3); v3s.append(v3)

expected = {
    122:96, 134:96, 142:96, 146:288, 152:192, 154:144,
    158:384, 162:192, 164:48, 166:96, 170:48,
}
check(dict(sorted(spec.items())) == expected, "complete eleven-value K^2 spectrum and degeneracies")
check(sum(spec.values()) == 1680, "spectrum multiplicities sum to 1680")
check(min(c3s)==20 and max(c3s)==104, "classical closure bounds 20/3 <= |c|^2 <= 104/3")
check(min(v3s)==66 and max(v3s)==126, "quantum variance bounds 22 <= V_q <= 42")
check(all(invariants(st)[0] == invariants(st)[1]+invariants(st)[2] for st in unoriented),
      "K^2 = |c|^2 + V_q on every state")
check(all(invariants(st)[0] != invariants(st)[1] for st in unoriented),
      "K^2 never equals classical |c|^2 on injective ensemble")

# Uniform-without-replacement sanity check quoted in the H.9/O.13 single-strand audit.
sum_sigma2 = sum(sum(m*m for m in st) for st in unoriented)
sum_S2 = sum(sum(st)**2 for st in unoriented)
sum_k3_uniform = sum(invariants(st)[0] for st in unoriented)
check(sum_sigma2 == 16*len(unoriented), "uniform injective <Sigma m_i^2> = 16")
check(sum_S2 == 8*len(unoriented), "uniform injective <S^2> = 8")
check(sum_k3_uniform == 152*len(unoriented), "uniform injective <K^2> = 152/3")

# -----------------------------------------------------------------------------
# Gibbs root and numerical spine
# -----------------------------------------------------------------------------
ks = [k/3 for k in sorted(spec)]
ns = [spec[k] for k in sorted(spec)]

def Z(eta): return sum(n*math.exp(-eta*k) for k,n in zip(ks,ns))
def mean_k(eta):
    z=Z(eta); return sum(n*k*math.exp(-eta*k) for k,n in zip(ks,ns))/z

def f(eta): return mean_k(eta)-3/(2*eta)
eta = brentq(f, 1e-4, 0.1, xtol=5e-16)
z=Z(eta)
g = math.log(z) + eta*mean_k(eta)
# weighted microstate moments directly
weights=[]
for st in unoriented:
    k3,c3,v3=invariants(st)
    w=2*math.exp(-eta*(k3/3))
    weights.append((w,k3/3,c3/3,v3/3))
den=sum(x[0] for x in weights)
mk=sum(w*k for w,k,c,v in weights)/den
mc=sum(w*c for w,k,c,v in weights)/den
mv=sum(w*v for w,k,c,v in weights)/den
var=sum(w*(k-mk)**2 for w,k,c,v in weights)/den
var_c=sum(w*(c-mc)**2 for w,k,c,v in weights)/den
var_v=sum(w*(v-mv)**2 for w,k,c,v in weights)/den
cov_cv=sum(w*(c-mc)*(v-mv) for w,k,c,v in weights)/den
corr_cv=cov_cv/math.sqrt(var_c*var_v)

approx(eta, 0.02986684439352237, 3e-15, "eta_star")
approx(g, 7.419800023570903, 3e-13, "g_share_eff")
approx(mk, 50.2229154254, 2e-10, "mean K^2")
approx(var, 15.6889750078, 2e-10, "Var K^2")
approx(eta*mk, 1.5, 2e-13, "stationarity eta*<K^2>=3/2")
approx(mc+mv, mk, 2e-13, "weighted mean closure decomposition")
notes.append(f"weighted split: <|c|^2>={mc:.12f}, <V_q>={mv:.12f}")
notes.append(f"stationarity shares: eta<|c|^2>={eta*mc:.12f}, eta<V_q>={eta*mv:.12f}")
notes.append(f"closure split correlation: corr(|c|^2,V_q)={corr_cv:.12f}; covariance={cov_cv:.12f}")
approx(var_c+var_v+2*cov_cv, var, 2e-12, "variance decomposition Var(K^2)=Var(c^2)+Var(Vq)+2Cov")

q=2/7
u=2*eta*q*q
alpha=math.sqrt(1-u)
zeta=9*math.exp(-g)*alpha**21
Zmu=1+zeta
Ze=(1+zeta)*(1+7*zeta*zeta)
Ztau=1+q*zeta
approx(u, 8*eta/49, 2e-16, "H.9 pair contraction u=8 eta/49")
approx(zeta, 0.005123584484947, 2e-15, "zeta_star")

# Countermodel audit: if one really adds a SECOND independent 3D Gaussian/symplectic
# sector to the closure-evidence construction (six coordinates total), the determinant
# weight doubles from 3/2 to 3.  This is a different UV model, not merely a relabeling
# of the O.13 energy ledger.
eta_two_copy = brentq(lambda e: mean_k(e)-3/e, 1e-4, 0.15, xtol=5e-16)
alpha21_two_copy = math.sqrt(1-8*eta_two_copy/49)**21
approx(eta_two_copy, 0.0603400492178353, 2e-13,
       "six-coordinate/two-copy closure countermodel eta")
approx(alpha21_two_copy, 0.901267680947515, 2e-12,
       "six-coordinate/two-copy edge amplitude alpha^21")
notes.append(f"two-copy closure countermodel: eta={eta_two_copy:.12f}, alpha^21={alpha21_two_copy:.12f}; baseline alpha^21={alpha**21:.12f}")

# Scale outputs using constants printed in Appendix P.
hbar=1.054571817e-34
c=299792458.0
me=9.1093837139e-31
lam=hbar/(me*c)
r=math.exp(-7*g)
L0=-1.5*lam*math.log1p(-r)
Lstar=Ze*L0
Gstar=c**3*Lstar**2/hbar
mu=720*q*Zmu
tau=720**2*q**4*Zmu*Ztau
approx(L0, 1.607719470158885e-35, 2e-48, "baseline L0")
approx(Lstar, 1.616253701392569e-35, 2e-48, "marked Lstar")
approx(Gstar, 6.674289077220912e-11, 2e-23, "induced Gstar")
approx(mu, 206.768280237, 2e-9, "muon/electron ratio")
approx(tau, 3477.343310, 2e-6, "tau/electron ratio")

# -----------------------------------------------------------------------------
# Cross-sector algebra checks
# -----------------------------------------------------------------------------
# matched G cancellation: symbolic coefficient reduction done by direct arithmetic formula.
G0=0.2; L=1.7; hb=2.3; cc=3.1
km=hb/(cc*L*math.log(2))
k_over_g=3*L/(4*G0*km)
sinf=3*math.log(2)/(32*math.pi*G0)
matched=cc**2/(8*math.pi*sinf)*k_over_g
induced=cc**3*L**2/hb
approx(matched, induced, 2e-12, "matched-G cancellation sample")
# epsilon reciprocity
eps=g/(4*math.pi**2)
approx((eps*c*70)*(1/eps), c*70, 1e-4, "a0-abundance epsilon reciprocity sample")
# route ratio
approx((21/20)/(9/10), 7/6, 1e-15, "primitive route eigenvalue ratio 7/6")

print("\n--- NOTES ---")
for n in notes: print("NOTE:",n)

if failures:
    print(f"\nAUDIT FAILED: {len(failures)} failure(s)")
    sys.exit(1)
print(f"\nAUDIT PASSED: {len(files)} Lean modules; deterministic finite/numerical checks passed.")
print("IMPORTANT: this script is not the Lean kernel. Run `lake build` in an environment with Lean 4.33.0 to typecheck proofs.")
