# Registered dwarf predictions and a 22-dwarf test of the satellite support rule (2026-10-28)

## Files

- **`predict.py`**: models, inputs and sources, stated in its docstring.
- **`registered_predictions.json`**: the frozen predictions. SHA-256 is in the first line of `predict_output.txt`.
- **`predict_output.txt`**: the comparison with existing data.
- **Inputs:**
  - Local Volume Database (Pace; github apace7/local_volume_database, dwarf_all.csv): stellar masses (V-band M/L = 2), circularized half-light radii, distances and Wolf masses.
  - Star-formation durations:
    - Weisz et al. 2015 (tau_90);
    - Monelli et al. 2010a for Cetus (no stars formed in the last 8 Gyr) and 2010b for Tucana (burst about 13 Gyr ago, at most about 1 Gyr long);
    - Gallart et al. 2021 for Eridanus II (burst at the earliest epoch, FWHM 500 Myr);
    - Read+19 for Sextans.

## Models

None of the models is fitted to the masses being tested.

| Model | Content |
|---|---|
| NFW | LCDM halo from the abundance-matching relation through the eight Read+19 dwarfs, with Dutton & Maccio concentration |
| HEAT | NFW plus coreNFW supernova heating at the published calibration |
| RULE | Retained NFW where the host's law field exceeds the dwarf's own at r_1/2; otherwise the relaxed law plus 0.08 dex (the median offset of the relaxed runs) |

Every model carries 0.20 dex of model uncertainty.

## Result on the existing Wolf masses M(<r_1/2)

This is a postdiction for these dwarfs.

| Model | chi^2 (22 dwarfs) |
|---|---|
| LCDM + heating | 24.0 |
| NFW | 30.0 |
| Rule | 31.0 |
| Law everywhere | 43.9 |

Six dwarfs have predictions that differ by more than 0.14 dex between the rule and heating:

| Dwarf | sigma predicted, rule (km/s) | sigma predicted, heating (km/s) | sigma observed (km/s) | Favours |
|---|---|---|---|---|
| Tucana (isolated) | 6.3 | 8.2 | 6.2 ± 1.5 (Taibi+20; Gregory+19 find ~14) | rule |
| Cetus (isolated) | 9.2 | 12.7 | 8.3 ± 1.0 | rule |
| Andromeda II | 10.4 | 15.1 | 7.8 ± 1.1 | rule |
| Eridanus II | 3.6 | 6.6 | 6.9 ± 1.0 | heating |
| Canes Venatici I | 5.2 | 8.5 | 7.7 ± 0.4 | heating |
| Canes Venatici II | 2.3 | 3.2 | 5.3 ± 1.1 | heating |

On these six, chi^2 is 11.6 for heating against 15.5 for the rule.

## Verdict

The broader sample favours LCDM + heating over the support rule by Delta chi^2 ≈ 7 over 22 dwarfs. The rule's edge on the eight classical GravSphere densities does not carry over to masses at the half-light radius in the wider sample.

The pattern is specific:
- The two truly isolated dwarfs, Tucana and Cetus, come out low as the rule predicts. So does the diffuse M31 satellite Andromeda II.
- The self-dominated Milky-Way satellites at 160–370 kpc (Eridanus II, Canes Venatici I and II) are as dense as CDM predicts and denser than the relaxed law.

The rule as stated takes the present-day field. An orbit-history version, in which a satellite is host-dominated at pericentre, could change those three classifications. Introducing it now would be fitted after the fact, so it is not adopted here.

## Registered tests

- **Tucana.** The rule predicts sigma ≈ 6.3 km/s; heating predicts 8.2 km/s. The two published values, 6.2 and about 14 km/s, bracket both, so a larger spectroscopic sample decides.
- **Cetus and Andromeda II.** Central densities from GravSphere-quality data. The rule predicts relaxed, cored profiles; heating predicts only partial cores, given their star-formation durations.
- **Eridanus II, Canes Venatici I and II.** Orbits from Gaia proper motions. If their pericentres place them in the host-dominated class, the orbit-history version of the rule becomes testable. If not, these three count against the rule.
