import Mathlib

/-! Native bridge selection audit. The integer coordinate data below are exact
snapshots of Pass2.Intertwiner.IF and LF, and their bridge compressions.
write_lean.py and check_native.py check provenance against the active sources.
These proofs certify the displayed finite data and conditional algebra. They do
not construct Haar measure, establish a physical SU(9) average, a Coulomb phase,
or a fine-structure constant. The ladder coordinates need not be orthonormal;
traces are similarity invariant. Haar averaging uses the orthonormal Q fiber.
-/
namespace Entropic.Electromagnetism.NativeSelection
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def embedding12 : Fin 16 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-12, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -18, 0, -6, 0, 0, 0, 0, 0],
    ![0, 0, -19, 0, -8, 0, -1, 0, 0],
    ![12, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 6, 0, -6, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, -16, 0, -5, 0, 0],
    ![0, 0, 0, 0, 0, -27, 0, -9, 0],
    ![0, 6, 0, 18, 0, 0, 0, 0, 0],
    ![0, 0, 5, 0, 16, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 12, 0, -12, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -36],
    ![0, 0, 1, 0, 8, 0, 19, 0, 0],
    ![0, 0, 0, 0, 0, 9, 0, 27, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 36],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0]]

def retraction60 : Fin 9 → Fin 16 → ℤ := ![![0, -30, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -33, 0, 0, 24, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -38, 0, 0, 16, 0, 0, -4, 0, 0, 2, 0, 0, 0],
    ![0, 0, 3, 0, 0, -24, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 5, 0, 0, -25, 0, 0, 25, 0, 0, -5, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -22, 0, 0, 12, 0, 0, -2, 0, 0],
    ![0, 0, 0, -2, 0, 0, 4, 0, 0, -16, 0, 0, 38, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -12, 0, 0, 22, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 10, 0]]

def bridgeR720 : Fin 9 → Fin 9 → ℤ := ![![1440, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -504, 0, -504, 0, 0, 0, 0, 0],
    ![0, 0, -2196, 0, -672, 0, 84, 0, 0],
    ![0, 504, 0, 1944, 0, 0, 0, 0, 0],
    ![0, 0, 420, 0, 0, 0, -420, 0, 0],
    ![0, 0, 0, 0, 0, -1944, 0, -504, 0],
    ![0, 0, -84, 0, 672, 0, 2196, 0, 0],
    ![0, 0, 0, 0, 0, 504, 0, 504, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1440]]

def bridgeL720 : Fin 9 → Fin 9 → ℤ := ![![1440, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1944, 0, 504, 0, 0, 0, 0, 0],
    ![0, 0, 2196, 0, 672, 0, -84, 0, 0],
    ![0, -504, 0, -504, 0, 0, 0, 0, 0],
    ![0, 0, -420, 0, 0, 0, 420, 0, 0],
    ![0, 0, 0, 0, 0, 504, 0, 504, 0],
    ![0, 0, 84, 0, -672, 0, -2196, 0, 0],
    ![0, 0, 0, 0, 0, -504, 0, -1944, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1440]]


def diagonalCompression (right : Bool) (i j : Fin 9) : ℤ :=
  (List.ofFn fun k : Fin 16 => retraction60 i k *
    (3 - 2 * ((if right then k.val % 4 else k.val / 4 : ℕ) : ℤ)) *
    embedding12 k j).sum

theorem bridge_compression_data :
    (∀ i j, diagonalCompression true i j = bridgeR720 i j) ∧
    (∀ i j, diagonalCompression false i j = bridgeL720 i j) := by decide

def traceData (A : Fin 9 → Fin 9 → ℤ) : ℤ :=
  (List.ofFn fun i => A i i).sum

def traceProductData (A B : Fin 9 → Fin 9 → ℤ) : ℤ :=
  (List.ofFn fun i => (List.ofFn fun j => A i j * B j i).sum).sum

theorem native_bridge_traces :
    traceData bridgeR720 = 0 ∧ traceData bridgeL720 = 0 ∧
    traceProductData bridgeR720 bridgeR720 = 38*720^2 ∧
    traceProductData bridgeL720 bridgeL720 = 38*720^2 ∧
    traceProductData bridgeR720 bridgeL720 = -14*720^2 := by decide

/-- Once the U tensor U commutant and trace preservation have been supplied,
the two trace constraints uniquely determine the identity and swap coefficients.
The group-integral theorem is deliberately not hidden in these hypotheses. -/
theorem common_twirl_coefficients (a b : ℝ)
    (htrace : 81*a+9*b=0) (hswap : 9*a+81*b = -14) :
    a=7/360 ∧ b = -7/40 := by constructor <;> linarith

theorem common_twirl_product_energy (eta overlapSquared : ℝ) :
    eta*(7/360-7/40*overlapSquared) =
      -(7*eta/40)*overlapSquared+7*eta/360 := by ring

theorem positive_bridge_favors_alignment (eta p : ℝ)
    (heta : 0 ≤ eta) (hp : p ≤ 1) :
    eta*(7/360-7/40) ≤ eta*(7/360-7/40*p) := by
  apply mul_le_mul_of_nonneg_left _ heta
  linarith

theorem spatial_twirl_residual : (1444:ℚ)/3-49/20 = 28733/60 := by norm_num
theorem spatial_twirl_residual_positive : (0:ℚ) < 28733/60 := by norm_num

def swapPair {n : Type*} (v : n × n → ℂ) : n × n → ℂ :=
  fun p => v (p.2,p.1)

theorem swapPair_involution {n : Type*} (v : n × n → ℂ) :
    swapPair (swapPair v) = v := by rfl

theorem swap_aligned_tensor {n : Type*} (z : n → ℂ) :
    swapPair (fun p => z p.1*z p.2) = (fun p => z p.1*z p.2) := by
  funext p
  exact mul_comm _ _

theorem alignment_bond_annihilates_product {n : Type*} (z : n → ℂ) :
    (fun p => z p.1*z p.2) - swapPair (fun p => z p.1*z p.2) = 0 := by
  rw [swap_aligned_tensor]
  exact sub_self _

theorem exchange_cost_nonnegative (J p : ℝ) (hJ : 0 ≤ J) (hp : p ≤ 1) :
    0 ≤ J*(1-p) := mul_nonneg hJ (sub_nonneg.mpr hp)

/-- The cubic one-flip dispersion is quadratic at zero momentum. This concerns
the averaged exchange Hamiltonian, not the full native interacting theory. -/
theorem exchange_dispersion_zero_slope (J a : ℝ) :
    HasDerivAt (fun k : ℝ => 4*J*(Real.sin (k*a/2))^2) 0 0 := by
  have ha : HasDerivAt (fun k : ℝ => k*a/2) (a/2) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const a).div_const 2
  have hh := ((ha.sin).pow 2).const_mul (4*J)
  simpa using hh

/-- Every normally ordered number-preserving bilinear annihilates a vector
annihilated by all annihilation maps. Positivity and a Fock representation are
separate obligations, established analytically for the stated free completion. -/
theorem normal_ordered_vacuum {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (ann cre : ι → V →ₗ[ℂ] V)
    (h : ι → ι → ℂ) (vac : V) (hv : ∀ j, ann j vac = 0) :
    (∑ i, ∑ j, h i j • cre i (ann j vac)) = 0 := by
  simp [hv]

end Entropic.Electromagnetism.NativeSelection
