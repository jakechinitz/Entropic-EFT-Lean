"""Comparison figures for the Empirical Results paper (three-theory edition, 2026-11-08).
Inputs: the saved outputs of 02 Research/Three-theory comparison 2026-11-08 and numbers quoted in the paper."""
import argparse, json, numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from pathlib import Path
PAPER = Path(__file__).resolve().parents[1]
PACKAGED_DATA = PAPER / 'evidence' / 'three_theory'
WORKSPACE_DATA = PAPER.parents[1] / '02 Research' / 'Three-theory comparison 2026-11-08'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-root', type=Path, default=PACKAGED_DATA if PACKAGED_DATA.exists() else WORKSPACE_DATA)
parser.add_argument('--output-dir', type=Path, default=PAPER / 'figures')
args = parser.parse_args()
R = args.data_root.resolve()
OUT = args.output_dir.resolve()
OUT.mkdir(parents=True, exist_ok=True)
if not (R / 'sparc/sparc_prior_sens.json').is_file():
    raise FileNotFoundError(f'Saved comparison data missing: {R}; supply --data-root.')
ST, MO, LC, DA = '#0f7b7b', '#c8582a', '#4a6fa5', '#222222'      # stock, MOND, LCDM, data
plt.rcParams.update({'font.size': 9, 'axes.titlesize': 10, 'axes.spines.top': False, 'axes.spines.right': False,
                     'savefig.bbox': 'tight', 'pdf.fonttype': 42})

# ---------------------------------------------------------------- 1. scoreboard
P, T, F, N = 'pass', 'tension', 'fail', 'none'
rows = [
 ('Galaxies', None),
 ('Rotation curves (SPARC)', [(P, 'BIC best, floor 5'), (T, '260 halo params'), (T, 'a$_0$ fixed; +26–34')]),
 ('Value of a$_0$', [(N, 'free constant'), (N, 'not addressed'), (T, '1.25; fits 0.9–1.2')]),
 ('LMC mass, 30 kpc', [(F, '1.6 vs 4.9'), (P, '3.7–10.8'), (P, '5.0 vs 4.9')]),
 ('NGC 628 vertical gravity', [(F, '$\\chi^2$ 8.9, $-$2.9$\\sigma$'), (P, '$\\chi^2$ 2.0'), (P, '$\\chi^2$ 2.0')]),
 ('Crater II', [(P, 'predicted 2.1'), (T, 'cuspy NFW fails'), (P, '2.4 km/s')]),
 ('Antlia 2', [(F, '2.8 vs 6.0'), (P, 'low-c halo'), (T, '3.5 vs 6.0')]),
 ('Isolated-galaxy lensing', [(P, '$\\chi^2$ 110'), (T, '$\\chi^2$ 124 at c$\\times$0.4'), (T, '$\\chi^2$ 132–171')]),
 ('High-z acceleration scale', [(T, 'residual trend'), (N, 'rise ~3, simulated'), (T, 'residual trend')]),
 ('Large scales', None),
 ('Cluster mass at R$_{500}$', [(F, '0.66 of data'), (P, '0.94'), (P, '0.91')]),
 ('Group and BCG excess', [(F, 'a$_0\\times$17 needed'), (P, 'halos'), (P, 'support rule')]),
 ('CMB, BAO, supernovae', [(N, 'needs AeST fields'), (P, '6 parameters'), (P, '4 parameters')]),
 ('$\\Omega_\\Lambda$ and $H_0$', [(N, 'no prediction'), (N, 'fitted'), (P, '0.709 vs 0.707')]),
 ('Split the two', None),
 ('Wide binaries', [(N, '$\\sim$20% boost'), (N, 'null'), (N, 'null')]),
]
col = {P: ('#d9eedb', '#1d6b2a', '✓'), T: ('#fbefd2', '#8a5a00', '~'), F: ('#f6d9d6', '#9b2a20', '✗'), N: ('#f2f2f2', '#666666', '–')}
fig, ax = plt.subplots(figsize=(7.2, 5.6)); ax.axis('off')
x0, cw, rh = 0.0, 0.22, 1.0
heads = ['MOND', '$\\Lambda$CDM', 'Stock model']
y = 0
for j, h in enumerate(heads):
    ax.text(0.34 + j * cw + cw / 2, y, h, ha='center', va='center', fontsize=10, weight='bold', color=[MO, LC, ST][j])
y -= 1
for name, cells in rows:
    if cells is None:
        ax.text(0, y, name, ha='left', va='center', fontsize=9, style='italic', color='#555555'); y -= 0.8; continue
    ax.text(0, y, name, ha='left', va='center', fontsize=8.6)
    for j, (s, txt) in enumerate(cells):
        bg, fg, sym = col[s]
        ax.add_patch(Rectangle((0.34 + j * cw + 0.004, y - 0.42), cw - 0.008, 0.84, color=bg, lw=0, transform=ax.transData))
        if j == 2: ax.add_patch(Rectangle((0.34 + j * cw + 0.004, y - 0.42), cw - 0.008, 0.84, fill=False, ec=ST, lw=1.0))
        ax.text(0.34 + j * cw + 0.016, y, sym, ha='left', va='center', fontsize=10, color=fg, family='DejaVu Sans')
        ax.text(0.34 + j * cw + 0.045, y, txt, ha='left', va='center', fontsize=7.6, color=fg)
    y -= 1
ax.set_xlim(0, 1.0); ax.set_ylim(y + 0.3, 0.6)
fig.savefig(OUT / 'scoreboard.pdf'); fig.savefig(OUT / 'scoreboard.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 2. clusters
cl = json.load(open(R / 'clusters/cluster_mond.json'))
names = sorted(cl, key=lambda c: cl[c]['R500']['hydro_total_over_baryon'])
fig, ax = plt.subplots(figsize=(7.0, 3.0))
xs = np.arange(len(names))
for k, (key, c, m, lab) in enumerate([('MOND_simple_over_hydro', MO, 's', 'MOND (simple $\\nu$)'), ('LCDM_fb_over_hydro', LC, 'D', '$\\Lambda$CDM cosmic baryon fraction'),
                                    ('stock_cohort_over_hydro', ST, 'o', 'Stock cohort ratio')]):
    v = [cl[n]['R500'][key] for n in names]
    ax.plot(xs + (k - 1) * 0.18, v, m, color=c, ms=6, label=lab, mfc=c if k != 1 else 'white')
ax.axhline(1, color=DA, lw=0.8); ax.axhspan(0.9, 1.1, color='#e8e8e8', zorder=0)
ax.set_xticks(xs); ax.set_xticklabels([n + ('' if cl[n]['stars'] else '*') for n in names], rotation=40, fontsize=8)
ax.set_ylabel('Predicted / hydrostatic mass at $R_{500}$'); ax.set_ylim(0.4, 1.35)
ax.legend(frameon=False, fontsize=8, ncol=3, loc='upper center', bbox_to_anchor=(0.5, 1.16))
ax.text(len(names) - 0.5, 0.43, '* no stellar profile (gas only)', ha='right', fontsize=7, color='#555555')
fig.savefig(OUT / 'clusters_three.pdf'); fig.savefig(OUT / 'clusters_three.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 3. chi2 versus parameter count
N = 2448; lnN = np.log(N)
pts = [('$\\Lambda$CDM', 6, 0.0, LC, 'D'), ('Release, fitted mixing time', 5, 0.85, ST, 's'), ('Frozen history', 4, 1.07, ST, 'o'),
       ('Frozen history, low-$z$ offset configuration', 4, -0.28, ST, 'o')]
fig, ax = plt.subplots(figsize=(5.4, 3.4))
kk = np.linspace(3.5, 6.5, 50)
ax.plot(kk, 2 * (6 - kk), '--', color='#777777', lw=1, label='equal AIC')
ax.plot(kk, lnN * (6 - kk), ':', color='#333333', lw=1.2, label='equal BIC ($N=2448$)')
ax.fill_between(kk, -5, np.minimum(2 * (6 - kk), 20), where=kk < 6, color=ST, alpha=0.07)
for lab, k, d, c, m in pts:
    ax.plot(k, d, m, color=c, ms=8, mfc=c if 'low' not in lab else 'white', label=lab)
ax.set_xlabel('Cosmological parameters fitted'); ax.set_ylabel('$\\chi^2 - \\chi^2_{\\Lambda\\mathrm{CDM}}$')
ax.set_xlim(3.5, 6.5); ax.set_ylim(-3, 17); ax.set_xticks([4, 5, 6])
ax.legend(frameon=False, fontsize=7.2, loc='upper right')
fig.savefig(OUT / 'cosmo_params.pdf'); fig.savefig(OUT / 'cosmo_params.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 4. Omega_Lambda against the retention gate
fig, (a1, a2) = plt.subplots(1, 2, figsize=(7.0, 2.9), sharey=True, gridspec_kw=dict(width_ratios=[1.25, 1]))
vg = [(9, .766, .775, 'run, $z$=9–15'), (10, .752, .761, 'run, $z$=6–9'), (12, .725, .736, 'cooling, neutral'), (14, .702, .713, 'likelihood-selected'), (17, .673, .685, 'cooling, ionized')]
for v, lo, hi, lab in vg:
    a1.plot([v, v], [lo, hi], color=ST if lab != 'likelihood-selected' else '#999999', lw=5, solid_capstyle='butt')
    a1.text(v + 0.25, (lo + hi) / 2, lab, fontsize=6.8, va='center')
a1.axhline(0.707, color=LC, lw=0.8)
a1.set_xlabel('Velocity gate before reionization (km s$^{-1}$)'); a1.set_ylabel('$\\Omega_\\Lambda$'); a1.set_xlim(8, 21.5)
mg = [(7.0, .78), (7.5, .73), (8.0, .68)]
a2.plot([m for m, _ in mg], [o for _, o in mg], 'o-', color='#999999', ms=5, label='sharp mass gate')
a2.errorbar([8.0], [0.709], yerr=[[0.019], [0.017]], fmt='o', color=ST, ms=7, capsize=3, label='feedback-resolved occupation\n(plotted at its half-occupation mass)')
a2.axhline(0.707, color=LC, lw=0.8, label='likelihood reference: 0.707')
a2.set_xlabel('log$_{10}$ halo mass gate ($M_\\odot$)'); a2.legend(frameon=False, fontsize=7, loc='lower left')
a2.text(7.72, 0.745, 'no input adjusted\nto $\\Omega_\\Lambda$', fontsize=7, color=ST, va='top')
fig.savefig(OUT / 'omegaL_gate.pdf'); fig.savefig(OUT / 'omegaL_gate.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 5. a0(z) three ways
z = np.linspace(0, 2.6, 200); E = np.sqrt(0.3038 * (1 + z)**3 + 0.6962)
fig, ax = plt.subplots(figsize=(5.4, 3.4))
ax.plot(z, 1.2494 * E, color=ST, lw=2, label='Stock relation, illustrative $H(z)$')
ax.plot(z, 1.2 * np.ones_like(z), color=MO, lw=2, ls='--', label='MOND, constant $a_0$')
ax.plot([2.3], [3.0 * 1.2], 'D', color=LC, mfc='white', ms=8, label='$\\Lambda$CDM simulation, about 3$\\times$ (Mayer et al.)')
zz = np.linspace(0.33, 1.44, 50); ax.fill_between(zz, (1.03 - 0.05) + (1.20 - 0.10) * zz, (1.03 + 0.05) + (1.20 + 0.10) * zz, color='#bbbbbb', alpha=0.5, lw=0, label='MUSE-DARK III line, $0.33<z<1.44$')
ax.set_xlabel('Redshift $z$'); ax.set_ylabel('$a_0$ ($10^{-10}$ m s$^{-2}$)'); ax.set_ylim(0, 5.2)
ax.legend(frameon=False, fontsize=7.2, loc='upper left')
fig.savefig(OUT / 'a0z_three.pdf'); fig.savefig(OUT / 'a0z_three.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 6. LMC three ways
G = 4.300917270e-6; RHO200 = 200 * 3 * (70 / 1000)**2 / (8 * np.pi * G)
def moster(lM):
    M1, Nn, b, g = 10**11.590, 0.0351, 1.376, 0.608; M = 10**lM
    return np.log10(2 * Nn * M / ((M / M1)**(-b) + (M / M1)**g))
grid = np.linspace(9, 14, 5001); lM0 = np.interp(np.log10(2.7e9), moster(grid), grid)
cdm = lambda lM: 10**(0.905 - 0.101 * (lM - 12 + np.log10(0.7)))
mu = lambda t: np.log1p(t) - t / (1 + t)
r = np.linspace(1, 70, 300)
def nfw(lM, c):
    M = 10**lM; r200 = (3 * M / (4 * np.pi * RHO200))**(1 / 3)
    return ((1 - 3e9 / M) * M * mu(c * r / r200) / mu(c) + 3e9) / 1e10
band = np.array([nfw(lM0 + dm, cdm(lM0 + dm) * 10**dc) for dm in (-0.3, 0, 0.3) for dc in (-0.11, 0, 0.11)])
rM = 1.84305; stock = np.minimum(3e9 / (1 - np.exp(-rM / r)), 34 * 3e9) / 1e10
fig, (ax, flux) = plt.subplots(1, 2, figsize=(7.2, 3.3), gridspec_kw={'width_ratios': [1.5, 1.0]})
ax.fill_between(r, band.min(0), band.max(0), color=LC, alpha=0.15, lw=0, label='$\\Lambda$CDM abundance-matched NFW, $\\pm$0.3 dex')
ax.plot(r, nfw(lM0, cdm(lM0)), color=LC, lw=1.2, ls='-.')
ax.plot(r, stock, color=ST, lw=2, label='Stock model (no halo-mass freedom)')
qr = [10, 17, 20, 23, 30, 35]; qm = [1.42, 1.57, 1.60, 1.63, 1.68, 1.71]
ax.plot(qr, qm, 's--', color=MO, ms=4, label='QUMOND with Milky Way field')
ax.errorbar([30], [4.9], yerr=[[0.2], [0.2]], fmt='o', color=DA, capsize=3, label='Orphan–Chenab stream')
ax.errorbar([50], [8.76], yerr=[[1.77], [1.94]], fmt='s', color=DA, mfc='white', capsize=3, label='outer-halo kinematics')
ax.set_xlabel('Radius (kpc)'); ax.set_ylabel('$M(<r)$ ($10^{10}M_\\odot$)'); ax.set_xlim(0, 70); ax.set_ylim(0, 17)
ax.legend(frameon=False, fontsize=6, loc='upper left')
ax.set_title('Enclosed mass profiles', fontsize=9)
flux.axvspan(4.7, 5.1, color='#dddddd', zorder=0)
flux.barh([3, 2, 1, 0], [5.035, 1.679, 1.681, 1.539],
          color=[ST, MO, MO, MO], height=0.58)
flux.set_yticks([3, 2, 1, 0])
flux.set_yticklabels(['Stock', 'QUMOND RAR', 'QUMOND simple', 'QUMOND standard'], fontsize=7)
flux.set_xlim(0, 5.6)
flux.set_xlabel('$M(<30\\,\\mathrm{kpc})$ ($10^{10}M_\\odot$)', fontsize=8)
flux.set_title('External-field flux tests', fontsize=9)
for y, v in zip([3, 2, 1, 0], [5.035, 1.679, 1.681, 1.539]):
    flux.text(v + 0.07, y, f'{v:.2f}', va='center', fontsize=7)
fig.tight_layout(w_pad=1.5)
fig.savefig(OUT / 'lmc_three.pdf'); fig.savefig(OUT / 'lmc_three.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 7. KiDS isolated lenses
fig, ax = plt.subplots(figsize=(5.4, 3.0))
cats = ['standard\nconcentration', 'concentration\n$\\times$0.6', 'best-fit\nconcentration']
nfw_v = [252.1, 154.1, 124.3]; st_v = [171.0, 146.6, 131.7]
x = np.arange(3)
ax.bar(x - 0.18, nfw_v, 0.34, color=LC, label='$\\Lambda$CDM NFW')
ax.bar(x + 0.18, st_v, 0.34, color=ST, label='Stock model, support-limited')
ax.axhline(110.5, color=MO, lw=1.8, ls='--', label='MOND, no halo freedom')
for xi, v in zip(x - 0.18, nfw_v): ax.text(xi, v + 3, f'{v:.0f}', ha='center', fontsize=7.5)
for xi, v in zip(x + 0.18, st_v): ax.text(xi, v + 3, f'{v:.0f}', ha='center', fontsize=7.5)
ax.set_xticks(x); ax.set_xticklabels(cats, fontsize=8); ax.set_ylabel('$\\chi^2$ (60 points)'); ax.set_ylim(0, 280)
ax.legend(frameon=False, fontsize=7.5, loc='upper right')
fig.savefig(OUT / 'kids_three.pdf'); fig.savefig(OUT / 'kids_three.png', dpi=200); plt.close(fig)

# ---------------------------------------------------------------- 8. SPARC a0 by variant and class
ps = json.load(open(R / 'sparc/sparc_prior_sens.json')); sp = json.load(open(R / 'sparc/sparc_split.json'))
labels = {'baseline (U_disk 0.5, 0.1 dex)': 'baseline priors', 'M/L prior 0.3 dex (near free)': 'M/L prior 0.3 dex', 'all priors x2': 'all priors $\\times$2',
          'absolute distances only (TRGB/Cepheid/SN)': '38 absolute distances'}
cls = {'Vflat<80': '$V_f<80$', '80-150': '$80\\leq V_f<150$', 'Vflat>=150': '$V_f\\geq150$', 'no Vflat': 'rising curves'}
fig, ax = plt.subplots(figsize=(6.4, 3.0))
items = []
for k, lab in labels.items():
    for fl in (0.0, 5.0):
        r_ = [x for x in ps if x['variant'] == k and x['floor'] == fl][0]; items.append((lab, fl, r_['a0_best'] * 1e10, r_['a0_sigma_scaled_dex']))
for k, lab in cls.items():
    for fl in (0.0, 5.0):
        r_ = [x for x in sp if x['group'] == k and x['floor'] == fl][0]; items.append((lab, fl, r_['a0_best'] * 1e10, None))
xl = []
for i, (lab, fl, a, s) in enumerate(items):
    xi = i // 2 + (0.15 if fl else -0.15) + (0.6 if i >= 8 else 0)
    yerr = None if s is None else [[a - a * 10**-s], [a * 10**s - a]]
    ax.errorbar([xi], [a], yerr=yerr, fmt='o' if fl == 0 else 's', color='#555555' if i < 8 else '#999999', mfc='white' if fl else None, ms=5, capsize=2)
    if fl == 0: xl.append((i // 2 + (0.6 if i >= 8 else 0), lab))
ax.axhline(1.2494, color=ST, lw=1.5, label='stock model, from cosmology')
ax.axhline(1.2, color=MO, lw=1, ls='--', label='MOND canonical')
ax.set_xticks([p for p, _ in xl]); ax.set_xticklabels([l for _, l in xl], rotation=35, ha='right', fontsize=7.5)
ax.axvline(3.8, color='#cccccc', lw=0.8)
ax.text(1.5, 1.85, 'prior variants', ha='center', fontsize=8, color='#444444'); ax.text(6.1, 1.85, 'galaxy classes', ha='center', fontsize=8, color='#444444')
ax.set_ylabel('best-fit $a_0$ ($10^{-10}$ m s$^{-2}$)'); ax.set_ylim(0.3, 1.95)
ax.plot([], [], 'o', color='#555555', label='no velocity floor'); ax.plot([], [], 's', color='#555555', mfc='white', label='5 km s$^{-1}$ floor')
ax.legend(frameon=False, fontsize=7, loc='lower left', ncol=2)
fig.savefig(OUT / 'sparc_a0.pdf'); fig.savefig(OUT / 'sparc_a0.png', dpi=200); plt.close(fig)
print('ok')
