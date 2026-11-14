# Independent review of the first draft, and responses

An adversarial reviewer (separate agent, given the code and results, not the conclusions)
checked the first draft. Main findings and what changed:

1. **Carried stock was circular.** The first rule bound particles to a potential that
   already contained the galactic-law stock. *Changed:* binding now uses the carrier's
   3D stellar mass plus the stock it currently carries, iterated from the stars alone
   (`labeled2.py`). The result holds: carried stock relaxes from 1.1-4.3x to 0.57-0.85x
   the law value; the core keeps 94-105% inside r_d.
2. **R500 protection is by construction once the support is accepted.** *Accepted:* the
   note now says the runs confirm rather than test the outer result; their content is in
   the core.
3. **Core results were single-snapshot and under-resolved.** *Changed:* N = 16000,
   8-10 Gyr time averages of core counts, Poisson errors quoted (6-14%). One seed.
4. **Register = cell energy is a fourth identification; the galaxy runs spent
   0.15-0.20 V_f^2, not "half the reservoir".** *Accepted and corrected.*
5. **Provenance; projected stellar mass used as 3D.** *Changed:* `make_inputs.py`
   regenerates all inputs and the galaxy reservoir table; dynamics now use 3D stellar mass;
   r_d and the cell energy still use projected mass (upper bounds, stated).
6. **Physics objections:** X-ray ellipticals on the RAR with hot gas counted (Lelli et al.
   2017); weak lensing flat to ~1 Mpc; the cooling threshold is ~1e12 Msun, not group
   scale; the ICM keeps records in other senses; history dependence. *All stated in the
   note as tests or open problems.* The Milky Way support edge is quoted as 115-490 kpc.

What the reviewer confirmed: the reservoir algebra and V_f^2 limit, the quoted ratios
against the result files, the A1795 reproduction of GPT's run, momentum conservation, and
that the code implements the stated rules without disabling contacts.
