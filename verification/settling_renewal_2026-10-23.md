Stock settling and finite renewal (2026-10-23)

Two open items from the external review of the Lean package:

  1. Cluster momentum. The reciprocity repair uses an inertial stock. The review asked
     for the mechanism that settles the stock into the galactic equilibrium in galaxies
     but not in clusters, and for a momentum check of that settling.
  2. History capacity. The Newton-constant and charged-lepton chains are stated with
     exact memoryless renewal. The review asked whether the numbers survive a finite
     reversible dynamics.

Lean: Entropic/FiniteRenewal.lean and Entropic/StockSettling.lean in the pinned Lean
4.35 library (repository branch settling-renewal). No sorry, no custom axioms; the
axiom audit covers 2,992 theorems.
Manuscript text: manuscript_dropin_2026-10-23.tex (P.9, I.1, Section 18). The live
manuscript was not edited.

An independent review of a first draft of this note found overclaims in both parts.
The text below is the corrected version; the corrections are listed at the end.


SUMMARY

Item 2. The charged-lepton shell load 720^N survives any finite reversible dynamics
exactly: it is Kac's return-time identity, which needs no independence between ticks.
The G_* chain does not transfer as derived. Every finite reversible renewal is periodic
and has entropy rate zero, so the maximum-entropy-rate selection of H.4 rejects it, and
the almost-sure return asymptotics (App. D) and the survival-transfer gap (Sec. 13.3)
need unbounded windows. A finite register can match the statistics on windows up to
its length, but at the needed length it stores about 1e24 nats of retrievable state per
cell, far above the de Sitter capacity. The manuscript's choice of an unbounded,
non-geometric history factor is the consistent one; the reviewer's point stands for
the G_* chain and fails for the lepton shell load.

Item 1. Momentum is not an obstacle: any schedule of central pair contacts conserves
linear and angular momentum, and a stock-only force requires the opposite carrier
recoil. Selection remains open. A finite clock supply with work per transition growing
as sigma^2 gives a candidate branch in which cold stock settles and hot stock does not.
Its two scalings are hypotheses, and current X-ray data do not fix its threshold.


ITEM 2. FINITE RENEWAL

Proved (FiniteRenewal; HistoryCapacity for periodicity):
  kac_sum                  Kac's identity for any permutation of a finite set: if every
                           orbit meets A, the first-return times over A sum to |Omega|.
  stepEquiv, pow_apply     A register of W cells over a finite set M. One tick shifts
                           the cells and applies a fixed permutation tau to the cell that
                           wraps around; a bijection; reading at t is tau^(t/W) of cell
                           t mod W.
  window_count, label_window_count, consecutive_pair_count
                           Over the uniform ensemble of register states, every window of
                           at most W readings has the product law.
  label_kac, meanReturn_eq, arithmetic_return_load, geometric_return_load
                           With tau a single cycle: E[T_b | b] = 1/p_b; sum p_b E[T_b|b] =
                           number of supported labels; sum p_b log E[T_b|b] = H(p).
  reading_periodic         Readings periodic with period W * orderOf tau.
  HistoryCapacity.finite_reversible_recurs
                           Every permutation of a finite set has a positive power equal to
                           the identity; hence every finite reversible renewal is periodic
                           and has entropy rate zero.

What carries over.
  - Lepton shell load. I.1 derives E[T_b | b] = 1/p_b from geometric return times under
    memoryless renewal. Kac's identity gives the same value for any stationary dynamics
    in which each orbit visits each shell state, including every finite reversible one
    with that property. The arithmetic load 720 per shell is exact for every marginal.
  - Window statistics. For windows of at most W ticks, the ensemble law of a register
    matches exact renewal, for rational label weights. p_eta* is irrational and is
    matched only to a chosen precision.

What does not carry over.
  - H.4 selects complete renewal by maximum entropy rate. Every finite reversible
    renewal has entropy rate zero, so that principle rejects all of them.
  - H.8 applies faithful resolution to every finite temporal block. In a register,
    readings W ticks apart are deterministically related (B_{t+W} = tau(B_t)).
  - App. D selects H_1 over H_2 through the Wyner-Ziv / Ornstein-Weiss almost-sure
    return theorem, which needs positive entropy rate on long blocks. Kac's identity does
    not replace it: the same return times give ln 720 arithmetically and H_1
    geometrically, so the choice of the geometric statistic is a separate premise.
  - Sec. 13.3 reads the survival transfer T_surv = 1 - r through its spectral gap, a
    statement about unbounded composition. The window product law gives T^n only for
    n <= W. No theorem here covers the gap.
  - Capacity. A register holds its future readings, so its content is retrievable
    present information. P.9 exempts the closure registers because renewal resets them
    independently of the state; that reason does not apply to a register. At
    W >= e^{7g} = 3.6e22 the register holds at least 7 g e^{7g} = 1.9e24 nats per cell
    (more, since ln|M| >= 7 ln 1680 and approximating p_eta* enlarges M). Over 2.6e183
    cells this is about 5e207 nats against S_dS = 3.3e122.
  - Recurrence. With |M| = 1680^7 = 3.8e22 and W = 3.6e22 the period W|M| is about 1.4e45
    ticks, of order a minute at tau_* = 5.4e-44 s. A period longer than a Hubble time
    needs W|M| above about 1e61, which enlarging M provides at logarithmic capacity cost.

Scope. Window statements are ensemble statements over the register state. Along one
orbit of the formalized register the one-time label frequencies and the Kac return times
are exact, and the two-tick frequencies are not the product law. A single-orbit version
needs a register whose readings form a de Bruijn sequence; that is not formalized.


ITEM 1. STOCK SETTLING

Proved (StockSettling):
  contact_momentum, contact_angular, schedule_conserves
        Central pair contacts at fixed positions conserve total linear and angular
        momentum, for any finite schedule of pairs and strengths. Section 18 already
        states this for one impulse; the schedule version is a direct extension.
  central_forces_balance, streaming_angular_rate
        Symmetric central pair forces have zero resultant and zero total torque, and the
        kinetic term of dL/dt vanishes. These are rate statements; the composition of
        streaming with contacts is not formalized as one theorem.
  recoil_required
        A force on the stock alone conserves momentum only if its resultant vanishes;
        otherwise the carriers must take the opposite resultant.
  reversible_no_concentration, casimir_invariant
        Fine-grained statements: a reversible map sends exactly |T| states into T and
        preserves every Casimir sum. Coarse-grained relaxation by phase mixing and
        violent relaxation can reach equilibria; these theorems do not show that the
        contact is required.
  endpoint_rate_free, endpoint_spends_supply
        Effective-dynamics contact on a signed ledger (work W per net transition, refunded
        on downward transitions), supply D short of the target: the population at
        exhaustion is w0 + D/W for every rate nu > 0, and the work spent is D. The time
        to exhaustion depends on nu. A ledger charging every event without refund gives a
        rate-dependent endpoint below w0 + D/W and is not covered.
  settled_fraction_eq, settles_iff_below_threshold, settled_fraction_above
        With W = kappa sigma^2 and supply d per unit stock, the settled part of the
        population gap is min(1, sigma_c^2 / sigma^2), sigma_c^2 = d / (kappa (p - w0)).
  cluster_fraction_bounds
        Illustration: if sigma_c <= 320 km/s, at most 21% settles at 700 km/s and at most
        10.3% at 1000 km/s.

Hypotheses of the budget branch.
  (H1) Work per transition proportional to sigma^2. The orbital part E_j - E_i is of
       order sigma^2; the bath part Theta ln(h_j/h_i) is so only if Theta scales with
       sigma^2.
  (H2) Fixed supply per unit stock. Plausible if the clock's available energy per volume
       is universal and settled systems share a common overdensity; not derived.
  The galactic target distribution itself remains an input.

What the branch would and would not give.
  - Cold stock settles fully, hot stock retains a collisionless fraction 1 - F.
  - Assembly history matters: stock from settled progenitors keeps any unspent supply,
    so a cluster's settled fraction depends on its merger tree. The formula F(sigma)
    applies to stock that has not settled before.
  - The Bullet offset is protected only to the extent that the remaining supply is
    small; with F(700 km/s) up to 21%, that has to be checked in the merger runs.

Data (first pass).
  - Isolated and noncentral early-type galaxies follow the galactic RAR; central
    galaxies of groups, subclusters and clusters depart from it, with a switching radius
    that shrinks with host mass (A&A 2026, arXiv:2603.23591).
  - Brightest cluster galaxies (stellar dispersions about 190-335 km/s) follow a relation
    with an acceleration scale about 17 times the galactic one (arXiv:2402.12016).
  - Angus, Famaey and Buote 2008 (arXiv:0709.0108): X-ray groups and clusters from about
    0.5 to 9 keV need mass beyond MOND, including NGC 720 (about 0.6 keV) and NGC 4125
    (about 0.5 keV). 0.5 keV is the floor of their sample, not a measured transition.
  - Milgrom 2012 (arXiv:1205.1308) finds NGC 720 and NGC 1521 consistent with MOND.
    The two analyses disagree on NGC 720.
  - Low-dispersion optical groups (54-187 km/s) were reported to depart from the MOND
    baryonic Faber-Jackson relation (arXiv:2402.13320), with declining profiles and
    unrelaxed members. If this holds for relaxed groups, a pure dispersion threshold is
    contradicted.
  - Conversion for mu = 0.6: 0.5 keV = 283 km/s, 0.6 keV = 310 km/s, 1 keV = 400 km/s.
  Reading: the environment pattern (centrals deviate, isolated and noncentral galaxies do
  not) is what the branch predicts if the host sets the local stock dispersion; it is
  also what collisionless dark matter predicts. The data do not fix sigma_c.

Next test. Compute the switching radius of group centrals from the host's unsettled
stock and the galaxy's settled stock with one sigma_c, and compare with arXiv:2603.23591.


CORRECTIONS FROM THE INDEPENDENT REVIEW
  - The first draft said the coefficient chains need only windowed statistics. H.4, H.8,
    App. D and Sec. 13.3 use unbounded windows; corrected above.
  - The first draft called the register's recurrence a far-future issue. At the minimal
    size it recurs in about a minute.
  - The first draft carried the de Sitter exemption of the closure registers over to the
    register. The exemption rests on state-independent reset and does not apply.
  - The first draft said a register reproduces the survival composition exactly. No
    theorem covers that; removed.
  - The first draft said selection requires the contact, from a fine-grained theorem.
    Removed.
  - The first draft stated rate independence without the signed-ledger condition, and a
    sigma_c range of 250-300 km/s from data that do not support it. Corrected.
