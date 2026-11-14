exec(open('hyb_nuis.py').read().split("print('HYB rigid'")[0])
import json
res = json.load(open('kids_hyb_grid.json'))
for dlm, cf in [(0.2, 0.3), (0.25, 0.35), (0.2, 0.35), (0.25, 0.4)]:
    res[f'{dlm}_{cf}'] = chi2_env(hyb(dlm, cf)); print('HYB', dlm, cf, res[f'{dlm}_{cf}'], flush=True)
    json.dump(res, open('kids_hyb_grid.json', 'w'), indent=1)
# NFW on the same extended grid for like-for-like
for dlm in (0.0, 0.1, 0.2, 0.25, 0.3):
    for cf in (1.0, 0.6, 0.4, 0.35, 0.3):
        res[f'NFW_{dlm}_{cf}'] = chi2_env(nfw_profile(dlm, cf))
json.dump(res, open('kids_hyb_grid.json', 'w'), indent=1)
print('NFW grid min', min((v, k) for k, v in res.items() if k.startswith('NFW')), flush=True)
print('HYB grid min', min((v, k) for k, v in res.items() if not k.startswith('NFW')), flush=True)
