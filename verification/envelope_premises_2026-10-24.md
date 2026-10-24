Envelope premises and derivation (2026-10-24)

Input: GPT's "Microstructure and 3D envelope 2026-10-24" note. It proves a 3D
energy bound for the isentropic halo envelope P = zeta rho^2 with a fixed core,
and states that no existing theorem selects the pressure law or the halo state.
This note splits that open item into separate premises, derives what can be
derived, and checks the result against weak lensing.

Lean: Entropic/EnvelopePremises.lean (new) and GPT's MicroEnvelope3D.lean,
ported to the pinned Lean 4.35 library. Every closed form is checked numerically
in check_envelope.py.


1. THREE THINGS THE ENVELOPE ASSUMES

The envelope needs three separate inputs. Calling them all "the halo pressure
law" hides that two of them have very different answers.

  (E) the exponent: P proportional to rho^2 (gamma = 2);
  (Z) the coefficient: one value zeta across the envelope, different for each halo;
  (M) the matching radius a where the envelope joins the inner RAR stock.

The results below show that (E) reduces to an extremal choice inside the
paper's own warm family. (Z) cannot come from any universal pair interaction.
(M) and (Z) together reduce to one astrophysical number per galaxy, the
retained stock-to-baryon ratio S. That number is bounded from below by weak
lensing.


2. THE EXPONENT: THE STIFFEST CAUSAL MEMBER OF THE WARM FAMILY

The manuscript's warm extension allows e_T = z n^gamma with 1 < gamma <= 2.
Take total energy eps = m n + z n^gamma with m, z > 0. Then

  P = n eps' - eps = (gamma - 1) z n^gamma,
  c_s^2 = dP/deps = (gamma - 1) x / (1 + x),   x = gamma z n^(gamma-1) / m.

  - cs2_lt: c_s^2 < gamma - 1 at every density, and approaches gamma - 1 at
    high density.
  - causal_iff: c_s^2 < 1 at every density exactly when gamma <= 2.
  - stiff_limit: at gamma = 2, P / eps -> 1. This is the stiff, Zel'dovich limit.

So the upper end of the paper's range, gamma <= 2, is the causality bound, and
the envelope uses its endpoint. gamma = 2 is the unique power-law interaction
energy that stays subluminal at every density while reaching the light-speed
limit asymptotically. GPT found that the clock's vacuum-adjacent depletion
branch reaches the same limit, c_s -> 1. A premise that would select gamma = 2
is "the retained stock's interaction stress is maximally stiff subject to
causality". That premise is extremal and natural, but it is not derived here.
The alternatives are not excluded by anything in the paper. An ideal
nonrelativistic gas gives gamma = 5/3, and a thermal gas at constant
temperature gives a coefficient proportional to 1/rho (GPT, section 2).


3. THE COEFFICIENT IS A STATE LABEL, NOT A COUPLING

GPT showed that a constant pair kernel leaves zeta unfixed by normalization. A
stronger statement holds.

  - pair_coefficient_bounds: for any composition p, the mean-field coefficient
    sum p_a p_b kappa_ab lies between the least and greatest kernel entries.
  - pair_coefficient_ratio: across any two halos it changes by at most
    kappa_max / kappa_min.

The matched coefficient is zeta = pi G (1 + eta) a^2 with a = r_M / (2 eta) and
r_M = sqrt(G M_b / a0). Hence

  zeta = [pi (1 + eta) / (4 eta^2)] G^2 M_b / a0.

At fixed eta this is proportional to M_b. Over the RAR sample, M_b spans about
10^7 to 10^11.5 Msun. A universal two-body interaction would therefore need
kernel integrals that themselves span four to five decades and are selected
in step with M_b. This is a no-go for the "pair interaction" route as an
explanation of the envelope family. It does not exclude a pair interaction
that sets gamma while a separate state variable sets zeta. In the warm
extension the label z = zeta plays that role: an advected, entropy-like
quantity carried by the stock.


4. MATCHING REDUCES THE STATE TO ONE NUMBER

The rest is derived, not assumed. Take compact baryons and the deep-RAR inner
stock, with M_R(r) = A r - M_b/2 and G A^2 = M_b a0. Slope and hydrostatic
matching at r = a give zeta = pi G (1 + eta) a^2 with eta = M_b / (2 A a)
(GPT). Two facts follow.

  - matching_acceleration: g(a) = 2 eta (1 + eta) a0. The join sits at the
    acceleration a0 exactly when eta = (sqrt 3 - 1)/2 = 0.366
    (matching_at_a0_iff).
  - envelope_ode, envelope_mass, envelope_mass_matched: outside the sources the
    envelope is rho = D sin(k r - phi) / r with k^2 = 2 pi G / zeta, q = k a.
    In closed form its edge and stock are

      R / a = 1 + arctan(q) / q,      q^2 = 2 / (1 + eta),
      M_env / M_b = (1 / (2 eta)) sqrt(1 + q^2) / q^3
                    [arctan q + q - 2 q / sqrt(1 + q^2)].

  The inner stock is M_R(a) / M_b = (1 - eta) / (2 eta). So the total stock
  ratio S(eta) is an explicit, monotone function. Inverting it, the retained
  stock ratio S fixes eta, a, R and zeta with nothing left free:

      S      eta      a/r_M   R/r_M
      5.18   0.129    3.9     6.6     (coextensive cohort, k_C)
      11.5   0.061    8.2     13.9    (GPT's saved benchmark)
      29     0.025    20      34
      100    0.0072   69      116

  To a good approximation R = 1.2 S r_M.

  For the lensing-compatible values of section 5 (S >= 25), g(a) = 2 eta (1 + eta) a0
  is below 0.06 a0. The join therefore sits deep in the low-acceleration regime,
  not at a0, and a rule "match where g = a0" (eta = 0.366, S = 1.5) is excluded.

The formation history enters only through S. In this theory S = k_C / f_ret
when the galaxy keeps its stock and retains a fraction f_ret of its ancestral
baryons. The "state selection" problem for the envelope is therefore the
galaxy's baryon retention, an astrophysical quantity that can be measured. No
new microscopic constant is needed. The plateau itself (constant zeta outside
a) still needs a premise. Marginal convective stability would supply one: the
inner RAR stock has K = P / rho^2 rising as r^2, which is convectively stable,
and mixing in the outer region drives dK/dr -> 0. That premise is standard for
mixed atmospheres but is not derived for the stock.


5. WEAK LENSING BOUNDS S, AND THE SAVED BENCHMARK FAILS IT

Beyond R the stock ends and the rotation speed falls as r^(-1/2). Mistele et
al. 2024 stack about 127,000 isolated KiDS lenses in four baryonic-mass bins.
They find flat circular speeds out to about 1 Mpc, and call the result
conservatively reliable to at least 300 kpc.

  - stock_ratio_lower_bound (Lean, rigorous, uses R <= 2a): a stock that
    reaches L needs S >= (L / r_M - 1) / 2.

The sharper closed-form inversion (check_envelope.py) gives:

  log M_b   r_M (kpc)   S for R >= 300 kpc (f_ret max)   S for R >= 1 Mpc (f_ret max)
  9.75      2.5         102  (0.051)                      343  (0.015)
  10.65     7.1         36   (0.14)                       121  (0.043)
  10.95     10.1        25   (0.20)                       86   (0.060)
  11.30     15.0        17   (0.31)                       57   (0.091)

GPT's benchmark has Milky Way-like baryons, M_b = 6.9e10 Msun with
r_M = 8.8 kpc, and S = 11.5. Its edge is at R = 124 kpc. With 8.6e11 Msun
inside, the circular speed is 173 km/s at R, 111 km/s at 300 kpc and
61 km/s at 1 Mpc. The flat value for this mass is 183 km/s (BTFR). At
300 kpc the benchmark is 39% low; at 1 Mpc it is 67% low. If the lensing
result holds to 300 kpc, the benchmark envelope is excluded. A Milky
Way-mass envelope needs S of about 25 or more, i.e. f_ret <= 0.2. If the
lensing result holds to 1 Mpc, S >= 86 and f_ret <= 0.06.

Two caveats weaken the bound. Stacked lensing beyond a few hundred kpc
includes neighbours and the surrounding large-scale stock, which an isolation
cut removes only in part. And GPT's benchmark uses extended baryons, while the
closed forms here assume compact baryons. Neither is likely to close the
factor of 2.7 in enclosed mass that separates the benchmark from a flat curve at
300 kpc.

These retention values sit in the same range as the galaxy baryon deficits
inferred from abundance matching and circumgalactic surveys. So the bound is
demanding but not obviously fatal. It does make the critic's point
quantitative: an isolated Milky Way-mass galaxy has to carry 25 to 90 times
its baryonic mass in stock. Separately, the model predicts a lensing break at
R = 1.2 (k_C / f_ret) r_M, beyond which the stacked circular speed falls as
r^(-1/2). That break radius scales with sqrt(M_b) / f_ret(M_b). Stacked
lensing by baryonic-mass bin can test it.


6. WHAT REMAINS

  (E) a derivation that the stock's interaction stress is maximally stiff
      (gamma = 2), or another exponent with its own stability analysis;
  (Z) the identification of zeta with an advected entropy-like label, and the
      mixing that makes it uniform beyond a;
  (S) the galaxy's retained stock ratio, i.e. f_ret(M_b) together with
      k_C. This is measurable, and weak lensing already bounds it from below;
  (F) a 3D formation calculation that produces the matched profile, with the
      work register and a live core.

Matching, the closed-form envelope, the stock integral, the causal exponent
bound, the pair-kernel range bound and the lensing lower bound are proved in
Lean. The continuum harmonic expansion and PDE energy argument remain as in
GPT's note.


7. FOLLOW-UP: THE OUTER BOUNDARY IS COSMOLOGICAL, AND THE OUTSKIRTS ARE UNRELAXED

(a) The extent bound does not depend on the exponent. gamma_scan.py repeats the
matching for gamma = 2, 1.8, 5/3, 1.5 and 1.4. The edge scales as
R = c(gamma) S r_M with c = 1.17, 1.25, 1.35, 1.61 and 2.04 for S between
30 and 100, and somewhat larger at S = 5. Softening the equation of state buys at most a factor of two. The
reason is kinematic: a flat curve to L needs enclosed mass A L, so S is close
to L / r_M whatever stress holds the stock up. A stiffer or softer envelope
only moves the edge a little.

(b) Lensing follows the RAR far beyond any envelope. The KiDS/GAMA lensing RAR
(Brouwer et al. 2021) reaches g_bar of about 1e-15 m/s^2. For isolated
late-type lenses it agrees with the RAR extrapolation, and is reliable to about
300 kpc in KiDS-bright and further in GAMA. Inside an envelope the density
falls as sin(k r)/r, steeper than 1/r^2, so the curve drops below the RAR. The
matching radius a must therefore lie beyond the lensing reach, not at
70 kpc. For an isolated Milky Way-mass galaxy the RAR stock density at 1 Mpc
is about 18 times the mean matter density, in the infall zone. A candidate
outer condition is matching to the cosmological stock background there,
instead of a zero-density surface at R <= 2a. The vacuum surface is the
premise to reconsider. Its stability bound still holds in the interior but
needs boundary terms for a background-matched edge.

(c) With a supplied edge radius R and the RAR continued to it, the stock ratio
is S = R / r_M - 1/2 (isothermal_stock_ratio). This moves the unknown to R; it
does not derive S. Matching at 200 times the mean density is one more
condition, not a consequence of the theory. With full stock retention, the
fraction of ancestral baryons a galaxy keeps is f_ret = k_C / S
(retained_fraction). McGaugh et al.'s detected baryon fraction is a different
quantity, f_d = M_b / (f_b M_tot) = (1 + k_C)/(1 + S) with f_b = 1/(1 + k_C)
(detected_fraction_formula). It is larger whenever S > k_C
(retained_lt_detected). An earlier version of this note identified the two;
that was wrong. At the 200-mean-density radius, f_ret runs from 0.09 at
log M_b = 9.75 to 0.22 at 11.3.

(d) Orbit counts do not settle the relaxation question. At 300 kpc a Milky
Way-mass galaxy completes about 1.5 orbits in 13.8 Gyr, but the crossing time
r/v is only about 1.5 Gyr. Collisionless violent relaxation acts over a few
crossing times, and a parcel's present radius and speed do not describe its
whole history. An earlier version of this note, and a Lean theorem now
removed, used the fixed-radius orbit count to argue that infall must set the
outer profile. That inference does not follow. Infall is one candidate for the
outer profile, not a result.

What this changes. The compact, vacuum-bounded envelope is in tension with
stacked lensing, since its edge at 124 kpc gives 111 km/s at 300 kpc against
183 km/s. GPT's stability result stands as a conditional result for its stated
boundary conditions. The next step is to test an extended, cosmologically
embedded stock distribution, and to derive its profile and normalization from
the theory rather than supplying an edge radius.

Sources
  Mistele, McGaugh, Lelli, Schombert, Li 2024, ApJL, "Indefinitely flat
  circular velocities and the baryonic Tully-Fisher relation from weak
  lensing", arXiv:2406.09685.
  Brouwer et al. 2021, A&A, "The weak lensing radial acceleration relation",
  arXiv:2106.11677.
  McGaugh, Schombert, de Blok, Zagursky 2010, ApJL, "The baryon content of
  cosmic structures", arXiv:0911.2700.
  "A comprehensive assessment of weak-lensing inferred circular velocity
  profiles of isolated galaxies", arXiv:2609.14085 (isolation validated to
  300 kpc).
