# O.13 single-strand record-energy patch

This note accompanies `EntropicEFT/Marked/SingleStrandRecord.lean`.

## Recommended manuscript replacement

The repaired renewed amplitude contains exactly one three-component Hubbard--Stratonovich
auxiliary per renewal event,

\[
A_*(b)\propto e^{-\eta_*V_q(b)/2}
\int \frac{d^3\xi}{(2\pi)^{3/2}}
 e^{-\xi^2/2+i\sqrt{\eta_*}\,\xi\cdot c(b)}.
\]

For the selected minimal record realization, this auxiliary is canonically completed to one
unit-frequency three-mode response strand.  Its coordinate kernel `exp(-xi^2/2)` is the
unnormalized oscillator vacuum wavefunction, so the strand contains three canonical pairs and
has stationary zero-point ledger

\[
\langle H_{\rm rec}\rangle
=\frac12\sum_{a=1}^3\langle \pi_a^2+\xi_a^2\rangle
=\frac32.
\]

The nine-state marked register is the operator doubling of this same strand.  At first level it
is spanned by matrix units

\[
|a\rangle\langle b|\sim a_a^\dagger|0\rangle\langle0|a_b,
\qquad a,b=1,2,3,
\]

and therefore carries `V_1 \otimes V_1^*`, which in three spatial dimensions is equivalent to
`V_1 \otimes V_1` and decomposes as `V_0 \oplus V_1 \oplus V_2`.  The matrix-unit
Hilbert--Schmidt Gram is `I_9`.  The history index is thus the dual/operator end of one response
strand, not a second independently energized oscillator sector.  Correspondingly the record
dynamics uses the difference-sign Liouvillian `L=[H,·]`; on the degenerate first-excitation
triplet these transition labels have zero Liouvillian eigenvalue.  They label which transition
is recorded and do not add an occupied quantum to the stationary energy ledger.

A literal two-deposit model would instead introduce a second independent three-mode canonical
phase space.  It would have six canonical pairs and zero-point ledger `3`; this is a different
model, not an alternative count inside the displayed one-strand realization.  The selected
`W_*` realization further prepares a fresh response strand at each renewal vertex.  An
amortized chain model that reuses one strand across consecutive vertices is a separate
countermodel and carries an adjacent-record-correlation obligation.

With the one-strand realization selected, the mathematical ledger is therefore

\[
\langle H_{\rm rec}\rangle=\frac32,
\qquad
\eta_*\langle K^2\rangle_{\eta_*}=\frac32,
\]

and hence

\[
\frac{\langle H_{\rm rec}\rangle}{\langle K^2\rangle_{\eta_*}}=\eta_*.
\]

The final interpretation of this ratio as the physical late-time released-energy fraction still
uses the already stated infrared conversion and release-selection bridges.

## Logical grade

The finite count `3 pairs -> 3/2`, the nine operator labels, identity coordinate Gram, the
zero difference-sign Liouvillian on the degenerate triplet, and the `6 pairs -> 3` two-copy
control are exact finite mathematics in the Lean model.  The step from the HS auxiliary to a
physical canonical oscillator strand, the operator-dual reading of history, the specific
`W_*` Liouvillian implementation, and fresh-per-vertex preparation are the selected model
realization.  Hubbard--Stratonovich integration alone does not prove those physical
identifications.

A Tomita--Takesaki formulation may provide a deeper infinite-dimensional realization, but it
is not needed for the finite theorem and is not claimed until the algebra/state and
cyclic-separating hypotheses are specified.
