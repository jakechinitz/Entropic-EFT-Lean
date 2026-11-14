import sys, json, time, numpy as np
exec(open('nuis.py').read().split("res = {}")[0])
def hyb(dlm, cf):
    out = np.zeros(60)
    for b in range(4):
        acc = np.zeros(F.NR)
        for j in kj:
            M = 10**(F.LMH[j] + dlm); r200 = F.R200[j] * 10**(dlm / 3); rsp = F.RSP[j] * 10**(dlm / 3); c = F.CONC[j] * cf
            MN = (1 - F.FB) * M * mu(np.minimum(RG, rsp) / (r200 / c)) / mu(c)
            Mhot = FH * F.FB * M
            for i in ki:
                w = W[b][i, j]
                if w < 1e-12: continue
                Mb = 10**LMG[i]; ex = Mb * (nu_exp(F.G * Mb / RG**2 / F.A0_MPC) - 1)
                rs = min(r200 * Mb / Mhot, rsp); MNs = np.interp(rs, RG, MN)
                h = np.where(RG < rs, np.minimum(ex, MNs), MN)
                acc += w * (F.esd_from_menc(h + Mhot * np.minimum(RG / r200, 1.0)) + Mb / (np.pi * F.RAD**2) / 1e12)
        out[b * F.NR:(b + 1) * F.NR] = acc
    return out
res = {}
print('HYB rigid', chi2_env(hyb(0, 1)), flush=True)
for dlm in (0.0, 0.1, 0.2, 0.3):
    for cf in (1.0, 0.6, 0.4):
        res[f'{dlm}_{cf}'] = chi2_env(hyb(dlm, cf)); print('HYB', dlm, cf, res[f'{dlm}_{cf}'], flush=True)
        json.dump(res, open('kids_hyb_grid.json', 'w'), indent=1)
