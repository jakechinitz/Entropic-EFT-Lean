import Entropic.AppP.Records
import Entropic.AppO.Numerics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.NumberTheory.Niven
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-! Appendix P, numbers and gluing geometry: the isotropic Fubini–Study angle (C14-16), trial
budget and energy scale (C14-26, C14-27), electron-anchor record energy (C14-46), mean closure energy
(C14-58), thermal thresholds and de Sitter numbers (C14-61 … C14-64), the Hubble-volume register
(C14-66), the no-event Kraus operator (C14-72a), the K² floor over injective assignments (C14-74),
mirror gluings and the product angle (C14-77), irrationality of the gluing angle (C14-78). -/

noncomputable section
namespace Entropic.AppP.Num
open Real Matrix

set_option maxHeartbeats 2000000 in
/-- cos 0.387595 > √(6/7). -/
theorem cos_A : (0.9258207057822832 : ℝ) ≤ Real.cos 0.387595 := by
  have hb := Real.cos_bound (x := (0.00151404296875 : ℝ)) (by norm_num [abs_le])
  rw [abs_le, abs_of_pos (by norm_num : (0.00151404296875 : ℝ) > 0)] at hb
  have L0 : (0.9999988538366707 : ℝ) ≤ Real.cos (0.00151404296875 : ℝ) := by linarith [hb.1]
  have U0 : Real.cos (0.00151404296875 : ℝ) ≤ (0.9999988538372181 : ℝ) := by linarith [hb.2]
  have e1 : Real.cos (0.0030280859375 : ℝ) = 2 * Real.cos (0.00151404296875 : ℝ) ^ 2 - 1 := by
    rw [show (0.0030280859375 : ℝ) = 2 * (0.00151404296875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L1 : (0.9999954153493101 : ℝ) ≤ Real.cos (0.0030280859375 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul L0 L0 (by norm_num) (by linarith)]
  have U1 : Real.cos (0.0030280859375 : ℝ) ≤ (0.9999954153514998 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul U0 U0 (by linarith) (by linarith)]
  have e2 : Real.cos (0.006056171875 : ℝ) = 2 * Real.cos (0.0030280859375 : ℝ) ^ 2 - 1 := by
    rw [show (0.006056171875 : ℝ) = 2 * (0.0030280859375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L2 : (0.9999816614392784 : ℝ) ≤ Real.cos (0.006056171875 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul L1 L1 (by norm_num) (by linarith)]
  have U2 : Real.cos (0.006056171875 : ℝ) ≤ (0.9999816614480373 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul U1 U1 (by linarith) (by linarith)]
  have e3 : Real.cos (0.01211234375 : ℝ) = 2 * Real.cos (0.006056171875 : ℝ) ^ 2 - 1 := by
    rw [show (0.01211234375 : ℝ) = 2 * (0.006056171875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L3 : (0.9999266464297192 : ℝ) ≤ Real.cos (0.01211234375 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul L2 L2 (by norm_num) (by linarith)]
  have U3 : Real.cos (0.01211234375 : ℝ) ≤ (0.9999266464647542 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul U2 U2 (by linarith) (by linarith)]
  have e4 : Real.cos (0.0242246875 : ℝ) = 2 * Real.cos (0.01211234375 : ℝ) ^ 2 - 1 := by
    rw [show (0.0242246875 : ℝ) = 2 * (0.01211234375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L4 : (0.9997065964803693 : ℝ) ≤ Real.cos (0.0242246875 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul L3 L3 (by norm_num) (by linarith)]
  have U4 : Real.cos (0.0242246875 : ℝ) ≤ (0.9997065966204991 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul U3 U3 (by linarith) (by linarith)]
  have e5 : Real.cos (0.048449375 : ℝ) = 2 * Real.cos (0.0242246875 : ℝ) ^ 2 - 1 := by
    rw [show (0.048449375 : ℝ) = 2 * (0.0242246875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L5 : (0.9988265580927278 : ℝ) ≤ Real.cos (0.048449375 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul L4 L4 (by norm_num) (by linarith)]
  have U5 : Real.cos (0.048449375 : ℝ) ≤ (0.9988265586530827 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul U4 U4 (by linarith) (by linarith)]
  have e6 : Real.cos (0.09689875 : ℝ) = 2 * Real.cos (0.048449375 : ℝ) ^ 2 - 1 := by
    rw [show (0.09689875 : ℝ) = 2 * (0.048449375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L6 : (0.9953089863027306 : ℝ) ≤ Real.cos (0.09689875 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul L5 L5 (by norm_num) (by linarith)]
  have U6 : Real.cos (0.09689875 : ℝ) ≤ (0.9953089885415202 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul U5 U5 (by linarith) (by linarith)]
  have e7 : Real.cos (0.1937975 : ℝ) = 2 * Real.cos (0.09689875 : ℝ) ^ 2 - 1 := by
    rw [show (0.1937975 : ℝ) = 2 * (0.09689875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L7 : (0.9812799564299383 : ℝ) ≤ Real.cos (0.1937975 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul L6 L6 (by norm_num) (by linarith)]
  have U7 : Real.cos (0.1937975 : ℝ) ≤ (0.9812799653430880 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul U6 U6 (by linarith) (by linarith)]
  have e8 : Real.cos (0.387595 : ℝ) = 2 * Real.cos (0.1937975 : ℝ) ^ 2 - 1 := by
    rw [show (0.387595 : ℝ) = 2 * (0.1937975 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L8 : (0.9258207057822832 : ℝ) ≤ Real.cos (0.387595 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul L7 L7 (by norm_num) (by linarith)]
  have U8 : Real.cos (0.387595 : ℝ) ≤ (0.9258207407674640 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul U7 U7 (by linarith) (by linarith)]
  exact L8

set_option maxHeartbeats 2000000 in
theorem cos_B : Real.cos 0.387605 ≤ (0.9258169610951363 : ℝ) := by
  have hb := Real.cos_bound (x := (0.00151408203125 : ℝ)) (by norm_num [abs_le])
  rw [abs_le, abs_of_pos (by norm_num : (0.00151408203125 : ℝ) > 0)] at hb
  have L0 : (0.9999988537775276 : ℝ) ≤ Real.cos (0.00151408203125 : ℝ) := by linarith [hb.1]
  have U0 : Real.cos (0.00151408203125 : ℝ) ≤ (0.9999988537780751 : ℝ) := by linarith [hb.2]
  have e1 : Real.cos (0.0030281640625 : ℝ) = 2 * Real.cos (0.00151408203125 : ℝ) ^ 2 - 1 := by
    rw [show (0.0030281640625 : ℝ) = 2 * (0.00151408203125 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L1 : (0.9999954151127380 : ℝ) ≤ Real.cos (0.0030281640625 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul L0 L0 (by norm_num) (by linarith)]
  have U1 : Real.cos (0.0030281640625 : ℝ) ≤ (0.9999954151149281 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul U0 U0 (by linarith) (by linarith)]
  have e2 : Real.cos (0.006056328125 : ℝ) = 2 * Real.cos (0.0030281640625 : ℝ) ^ 2 - 1 := by
    rw [show (0.006056328125 : ℝ) = 2 * (0.0030281640625 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L2 : (0.9999816604929943 : ℝ) ≤ Real.cos (0.006056328125 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul L1 L1 (by norm_num) (by linarith)]
  have U2 : Real.cos (0.006056328125 : ℝ) ≤ (0.9999816605017548 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul U1 U1 (by linarith) (by linarith)]
  have e3 : Real.cos (0.01211265625 : ℝ) = 2 * Real.cos (0.006056328125 : ℝ) ^ 2 - 1 := by
    rw [show (0.01211265625 : ℝ) = 2 * (0.006056328125 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L3 : (0.9999266426446522 : ℝ) ≤ Real.cos (0.01211265625 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul L2 L2 (by norm_num) (by linarith)]
  have U3 : Real.cos (0.01211265625 : ℝ) ≤ (0.9999266426796936 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul U2 U2 (by linarith) (by linarith)]
  have e4 : Real.cos (0.0242253125 : ℝ) = 2 * Real.cos (0.01211265625 : ℝ) ^ 2 - 1 := by
    rw [show (0.0242253125 : ℝ) = 2 * (0.01211265625 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L4 : (0.9997065813412119 : ℝ) ≤ Real.cos (0.0242253125 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul L3 L3 (by norm_num) (by linarith)]
  have U4 : Real.cos (0.0242253125 : ℝ) ≤ (0.9997065814813673 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul U3 U3 (by linarith) (by linarith)]
  have e5 : Real.cos (0.048450625 : ℝ) = 2 * Real.cos (0.0242253125 : ℝ) ^ 2 - 1 := by
    rw [show (0.048450625 : ℝ) = 2 * (0.0242253125 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L5 : (0.9988264975538662 : ℝ) ≤ Real.cos (0.048450625 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul L4 L4 (by norm_num) (by linarith)]
  have U5 : Real.cos (0.048450625 : ℝ) ≤ (0.9988264981143234 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul U4 U4 (by linarith) (by linarith)]
  have e6 : Real.cos (0.09690125 : ℝ) = 2 * Real.cos (0.048450625 : ℝ) ^ 2 - 1 := by
    rw [show (0.09690125 : ℝ) = 2 * (0.048450625 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L6 : (0.9953087444314469 : ℝ) ≤ Real.cos (0.09690125 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul L5 L5 (by norm_num) (by linarith)]
  have U6 : Real.cos (0.09690125 : ℝ) ≤ (0.9953087466706450 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul U5 U5 (by linarith) (by linarith)]
  have e7 : Real.cos (0.1938025 : ℝ) = 2 * Real.cos (0.09690125 : ℝ) ^ 2 - 1 := by
    rw [show (0.1938025 : ℝ) = 2 * (0.09690125 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L7 : (0.9812789934834065 : ℝ) ≤ Real.cos (0.1938025 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul L6 L6 (by norm_num) (by linarith)]
  have U7 : Real.cos (0.1938025 : ℝ) ≤ (0.9812790023981804 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul U6 U6 (by linarith) (by linarith)]
  have e8 : Real.cos (0.387605 : ℝ) = 2 * Real.cos (0.1938025 : ℝ) ^ 2 - 1 := by
    rw [show (0.387605 : ℝ) = 2 * (0.1938025 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L8 : (0.9258169261036146 : ℝ) ≤ Real.cos (0.387605 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul L7 L7 (by norm_num) (by linarith)]
  have U8 : Real.cos (0.387605 : ℝ) ≤ (0.9258169610951363 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul U7 U7 (by linarith) (by linarith)]
  exact U8

set_option maxHeartbeats 2000000 in
theorem cos_C : (-0.7777659675676808 : ℝ) ≤ Real.cos 2.4618787 := by
  have hb := Real.cos_bound (x := (0.009616713671875 : ℝ)) (by norm_num [abs_le])
  rw [abs_le, abs_of_pos (by norm_num : (0.009616713671875 : ℝ) > 0)] at hb
  have L0 : (0.9999537589636198 : ℝ) ≤ Real.cos (0.009616713671875 : ℝ) := by linarith [hb.1]
  have U0 : Real.cos (0.009616713671875 : ℝ) ≤ (0.9999537598545334 : ℝ) := by linarith [hb.2]
  have e1 : Real.cos (0.01923342734375 : ℝ) = 2 * Real.cos (0.009616713671875 : ℝ) ^ 2 - 1 := by
    rw [show (0.01923342734375 : ℝ) = 2 * (0.009616713671875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L1 : (0.9998150401309460 : ℝ) ≤ Real.cos (0.01923342734375 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul L0 L0 (by norm_num) (by linarith)]
  have U1 : Real.cos (0.01923342734375 : ℝ) ≤ (0.9998150436944358 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul U0 U0 (by linarith) (by linarith)]
  have e2 : Real.cos (0.0384668546875 : ℝ) = 2 * Real.cos (0.01923342734375 : ℝ) ^ 2 - 1 := by
    rw [show (0.0384668546875 : ℝ) = 2 * (0.01923342734375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L2 : (0.9992602289440903 : ℝ) ≤ Real.cos (0.0384668546875 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul L1 L1 (by norm_num) (by linarith)]
  have U2 : Real.cos (0.0384668546875 : ℝ) ≤ (0.9992602431954132 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul U1 U1 (by linarith) (by linarith)]
  have e3 : Real.cos (0.076933709375 : ℝ) = 2 * Real.cos (0.0384668546875 : ℝ) ^ 2 - 1 := by
    rw [show (0.076933709375 : ℝ) = 2 * (0.0384668546875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L3 : (0.9970420102987915 : ℝ) ≤ Real.cos (0.076933709375 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul L2 L2 (by norm_num) (by linarith)]
  have U3 : Real.cos (0.076933709375 : ℝ) ≤ (0.9970420672619127 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul U2 U2 (by linarith) (by linarith)]
  have e4 : Real.cos (0.15386741875 : ℝ) = 2 * Real.cos (0.076933709375 : ℝ) ^ 2 - 1 := by
    rw [show (0.15386741875 : ℝ) = 2 * (0.076933709375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L4 : (0.9881855406013109 : ℝ) ≤ Real.cos (0.15386741875 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul L3 L3 (by norm_num) (by linarith)]
  have U4 : Real.cos (0.15386741875 : ℝ) ≤ (0.9881857677798169 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul U3 U3 (by linarith) (by linarith)]
  have e5 : Real.cos (0.3077348375 : ℝ) = 2 * Real.cos (0.15386741875 : ℝ) ^ 2 - 1 := by
    rw [show (0.3077348375 : ℝ) = 2 * (0.15386741875 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L5 : (0.9530213253070101 : ℝ) ≤ Real.cos (0.3077348375 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul L4 L4 (by norm_num) (by linarith)]
  have U5 : Real.cos (0.3077348375 : ℝ) ≤ (0.9530222232851725 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul U4 U4 (by linarith) (by linarith)]
  have e6 : Real.cos (0.615469675 : ℝ) = 2 * Real.cos (0.3077348375 : ℝ) ^ 2 - 1 := by
    rw [show (0.615469675 : ℝ) = 2 * (0.3077348375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L6 : (0.8164992929798599 : ℝ) ≤ Real.cos (0.615469675 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul L5 L5 (by norm_num) (by linarith)]
  have U6 : Real.cos (0.615469675 : ℝ) ≤ (0.8165027161508264 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul U5 U5 (by linarith) (by linarith)]
  have e7 : Real.cos (1.23093935 : ℝ) = 2 * Real.cos (0.615469675 : ℝ) ^ 2 - 1 := by
    rw [show (1.23093935 : ℝ) = 2 * (0.615469675 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L7 : (0.3333421908732221 : ℝ) ≤ Real.cos (1.23093935 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul L6 L6 (by norm_num) (by linarith)]
  have U7 : Real.cos (1.23093935 : ℝ) ≤ (0.3333533709633540 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul U6 U6 (by linarith) (by linarith)]
  have e8 : Real.cos (2.4618787 : ℝ) = 2 * Real.cos (1.23093935 : ℝ) ^ 2 - 1 := by
    rw [show (2.4618787 : ℝ) = 2 * (1.23093935 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L8 : (-0.7777659675676808 : ℝ) ≤ Real.cos (2.4618787 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul L7 L7 (by norm_num) (by linarith)]
  have U8 : Real.cos (2.4618787 : ℝ) ≤ (-0.7777510601347369 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul U7 U7 (by linarith) (by linarith)]
  exact L8

set_option maxHeartbeats 2000000 in
theorem cos_D : Real.cos 2.462048 ≤ (-0.7778574659922727 : ℝ) := by
  have hb := Real.cos_bound (x := (0.009617375 : ℝ)) (by norm_num [abs_le])
  rw [abs_le, abs_of_pos (by norm_num : (0.009617375 : ℝ) > 0)] at hb
  have L0 : (0.9999537526034754 : ℝ) ≤ Real.cos (0.009617375 : ℝ) := by linarith [hb.1]
  have U0 : Real.cos (0.009617375 : ℝ) ≤ (0.9999537534946340 : ℝ) := by linarith [hb.2]
  have e1 : Real.cos (0.01923475 : ℝ) = 2 * Real.cos (0.009617375 : ℝ) ^ 2 - 1 := by
    rw [show (0.01923475 : ℝ) = 2 * (0.009617375 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L1 : (0.9998150146915449 : ℝ) ≤ Real.cos (0.01923475 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul L0 L0 (by norm_num) (by linarith)]
  have U1 : Real.cos (0.01923475 : ℝ) ≤ (0.9998150182560146 : ℝ) := by
    rw [e1, sq]; linarith [mul_le_mul U0 U0 (by linarith) (by linarith)]
  have e2 : Real.cos (0.0384695 : ℝ) = 2 * Real.cos (0.01923475 : ℝ) ^ 2 - 1 := by
    rw [show (0.0384695 : ℝ) = 2 * (0.01923475 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L2 : (0.9992601272053082 : ℝ) ≤ Real.cos (0.0384695 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul L1 L1 (by norm_num) (by linarith)]
  have U2 : Real.cos (0.0384695 : ℝ) ≤ (0.9992601414605497 : ℝ) := by
    rw [e2, sq]; linarith [mul_le_mul U1 U1 (by linarith) (by linarith)]
  have e3 : Real.cos (0.076939 : ℝ) = 2 * Real.cos (0.0384695 : ℝ) ^ 2 - 1 := by
    rw [show (0.076939 : ℝ) = 2 * (0.0384695 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L3 : (0.9970416036447374 : ℝ) ≤ Real.cos (0.076939 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul L2 L2 (by norm_num) (by linarith)]
  have U3 : Real.cos (0.076939 : ℝ) ≤ (0.9970416606235156 : ℝ) := by
    rw [e3, sq]; linarith [mul_le_mul U2 U2 (by linarith) (by linarith)]
  have e4 : Real.cos (0.153878 : ℝ) = 2 * Real.cos (0.076939 : ℝ) ^ 2 - 1 := by
    rw [show (0.153878 : ℝ) = 2 * (0.076939 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L4 : (0.9881839187969392 : ℝ) ≤ Real.cos (0.153878 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul L3 L3 (by norm_num) (by linarith)]
  have U4 : Real.cos (0.153878 : ℝ) ≤ (0.9881841460377954 : ℝ) := by
    rw [e4, sq]; linarith [mul_le_mul U3 U3 (by linarith) (by linarith)]
  have e5 : Real.cos (0.307756 : ℝ) = 2 * Real.cos (0.153878 : ℝ) ^ 2 - 1 := by
    rw [show (0.307756 : ℝ) = 2 * (0.153878 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L5 : (0.9530149147377514 : ℝ) ≤ Real.cos (0.307756 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul L4 L4 (by norm_num) (by linarith)]
  have U5 : Real.cos (0.307756 : ℝ) ≤ (0.9530158129608939 : ℝ) := by
    rw [e5, sq]; linarith [mul_le_mul U4 U4 (by linarith) (by linarith)]
  have e6 : Real.cos (0.615512 : ℝ) = 2 * Real.cos (0.307756 : ℝ) ^ 2 - 1 := by
    rw [show (0.615512 : ℝ) = 2 * (0.307756 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L6 : (0.8164748554252071 : ℝ) ≤ Real.cos (0.615512 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul L5 L5 (by norm_num) (by linarith)]
  have U6 : Real.cos (0.615512 : ℝ) ≤ (0.8164782795070271 : ℝ) := by
    rw [e6, sq]; linarith [mul_le_mul U5 U5 (by linarith) (by linarith)]
  have e7 : Real.cos (1.231024 : ℝ) = 2 * Real.cos (0.615512 : ℝ) ^ 2 - 1 := by
    rw [show (1.231024 : ℝ) = 2 * (0.615512 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L7 : (0.3332623790832256 : ℝ) ≤ Real.cos (1.231024 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul L6 L6 (by norm_num) (by linarith)]
  have U7 : Real.cos (1.231024 : ℝ) ≤ (0.3332735618135102 : ℝ) := by
    rw [e7, sq]; linarith [mul_le_mul U6 U6 (by linarith) (by linarith)]
  have e8 : Real.cos (2.462048 : ℝ) = 2 * Real.cos (1.231024 : ℝ) ^ 2 - 1 := by
    rw [show (2.462048 : ℝ) = 2 * (1.231024 : ℝ) by norm_num]; exact Real.cos_two_mul _
  have L8 : (-0.7778723733755769 : ℝ) ≤ Real.cos (2.462048 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul L7 L7 (by norm_num) (by linarith)]
  have U8 : Real.cos (2.462048 : ℝ) ≤ (-0.7778574659922727 : ℝ) := by
    rw [e8, sq]; linarith [mul_le_mul U7 U7 (by linarith) (by linarith)]
  exact U8

/-- a < arccos c < b from cos b < c < cos a with 0 ≤ a < b ≤ π. -/
theorem arccos_between {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) (hab : a ≤ b) (hc1 : -1 ≤ c) (hc2 : c ≤ 1)
    (h1 : Real.cos b < c) (h2 : c < Real.cos a) : a < Real.arccos c ∧ Real.arccos c < b := by
  constructor
  · have := Real.arccos_lt_arccos hc1 h2 (Real.cos_le_one a)
    rwa [Real.arccos_cos ha (by linarith)] at this
  · have := Real.arccos_lt_arccos (Real.neg_one_le_cos b) h1 hc2
    rwa [Real.arccos_cos (by linarith) hb] at this

/-- C14-16: arccos √(6/7) = 0.38760 to five significant digits (0.387595 < θ < 0.387605). -/
theorem isotropic_angle :
    0.387595 < Real.arccos (Real.sqrt (6/7)) ∧ Real.arccos (Real.sqrt (6/7)) < 0.387605 := by
  have hs : Real.sqrt (6/7) ^ 2 = 6/7 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (6/7) := Real.sqrt_nonneg _
  have hlo : (0.9258169610951363 : ℝ) < Real.sqrt (6/7) := by nlinarith
  have hhi : Real.sqrt (6/7) < (0.9258207057822832 : ℝ) := by nlinarith
  have hpi := Real.pi_gt_three
  exact arccos_between (by norm_num) (by linarith) (by norm_num) (by linarith) (by nlinarith)
    (lt_of_le_of_lt cos_B hlo) (lt_of_lt_of_le hhi cos_A)

/-- C14-77 (degrees): arccos(−7/9) = 141.06° (141.055 < θ·180/π < 141.065). -/
theorem gluing_angle_degrees :
    141.055 < Real.arccos (-7/9) * 180 / π ∧ Real.arccos (-7/9) * 180 / π < 141.065 := by
  have hpi1 := Real.pi_gt_d6; have hpi2 := Real.pi_lt_d6
  obtain ⟨h1, h2⟩ := arccos_between (a := 2.4618787) (b := 2.462048) (c := -7/9) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_le_of_lt cos_D (by norm_num)) (lt_of_lt_of_le (by norm_num) cos_C)
  have hp : 0 < π := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- C14-78: arccos(−7/9)/π is irrational (Niven: the rational values of cos at rational multiples of π
are 0, ±1/2, ±1). -/
theorem gluing_angle_irrational : ¬ ∃ r : ℚ, Real.arccos (-7/9) = r * π := by
  intro hr
  have h := niven hr ⟨-7/9, by rw [Real.cos_arccos (by norm_num) (by norm_num)]; push_cast; ring⟩
  rw [Real.cos_arccos (by norm_num) (by norm_num)] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h <;> norm_num at h

/-! ### C14-77: mirror gluings -/

/-- R = 2nnᵀ − I for a unit vector n. -/
def mirror (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2:ℝ) • (Matrix.replicateCol Unit n * Matrix.replicateRow Unit n) - 1

/-- C14-77 (a): for n·n = 1, R = 2nnᵀ − I is symmetric, R² = I (so RᵀR = I), det R = 1, Rn = n. -/
theorem mirror_rotation (n : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) :
    (mirror n)ᵀ = mirror n ∧ mirror n * mirror n = 1 ∧ (mirror n).det = 1 ∧ mirror n *ᵥ n = n := by
  have hn' : ∑ x, n x * n x = 1 := hn
  have hP : (Matrix.replicateCol Unit n * Matrix.replicateRow Unit n) *
      (Matrix.replicateCol Unit n * Matrix.replicateRow Unit n) =
      Matrix.replicateCol Unit n * Matrix.replicateRow Unit n := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    calc ∑ x, n i * n x * (n x * n j) = n i * n j * ∑ x, n x * n x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = n i * n j := by rw [hn', mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [mirror, Matrix.mul_apply, Matrix.one_apply, eq_comm]; ring
  · simp only [mirror, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP,
      Matrix.one_mul, Matrix.mul_one, smul_smul]
    module
  · have e : mirror n = -(1 + Matrix.replicateCol Unit ((-2:ℝ) • n) * Matrix.replicateRow Unit n) := by
      ext i j; simp [mirror, Matrix.mul_apply]; ring
    rw [e, Matrix.det_neg, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct_smul, hn]; norm_num
  · ext i
    have hs : ∀ j, (mirror n) i j = 2 * (n i * n j) - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      intro j; simp [mirror, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, hs, sub_mul, Finset.sum_sub_distrib]
    have h1 : ∑ x, 2 * (n i * n x) * n x = 2 * n i := by
      rw [show ∑ x, 2 * (n i * n x) * n x = 2 * n i * ∑ x, n x * n x by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring), hn', mul_one]
    have h2 : ∑ x, (1 : Matrix (Fin 3) (Fin 3) ℝ) i x * n x = n i := by
      simp [Matrix.one_apply]
    rw [h1, h2]; ring

/-- C14-77 (b): tr(R₀R₁) = 4(n₀·n₁)² − 1, so cos θ = (tr − 1)/2 = 2(n₀·n₁)² − 1 = −7/9 when n₀·n₁ = −1/3. -/
theorem product_angle (n0 n1 : Fin 3 → ℝ) (h0 : n0 ⬝ᵥ n0 = 1) (h1 : n1 ⬝ᵥ n1 = 1) :
    (mirror n0 * mirror n1).trace = 4 * (n0 ⬝ᵥ n1) ^ 2 - 1 ∧
      (n0 ⬝ᵥ n1 = -1/3 → ((mirror n0 * mirror n1).trace - 1) / 2 = -7/9) := by
  have ht : (mirror n0 * mirror n1).trace = 4 * (n0 ⬝ᵥ n1) ^ 2 - 1 := by
    simp only [dotProduct, Fin.sum_univ_three] at h0 h1 ⊢
    simp [mirror, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.sub_apply]
    nlinarith [h0, h1]
  refine ⟨ht, fun h => by rw [ht, h]; norm_num⟩

/-! ### Physical numbers -/

/-- C14-26: e^{560} lies between 10^{243} and 10^{244} (ln N ≃ 5.6·10² nats ⇒ N ≈ 10^{243}). -/
theorem trial_budget : (10:ℝ) ^ 243 < Real.exp 560 ∧ Real.exp 560 < (10:ℝ) ^ 244 := by
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have a1 := Real.log_two_gt_d9; have a2 := Real.log_two_lt_d9
  have b1 := Real.log_five_gt_d9; have b2 := Real.log_five_lt_d9
  have e : ∀ k : ℕ, (10:ℝ) ^ k = Real.exp (k * Real.log 10) := fun k => by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e, e]
  constructor <;> (apply Real.exp_lt_exp.mpr; push_cast; nlinarith)

/-- C14-27: K_crit·ε_rec = 560 × 0.737 MeV = 412.72 MeV ≈ 0.41 GeV. -/
theorem critical_energy : (560 : ℝ) * 0.737 = 412.72 := by norm_num

/-- C14-46: ε_rec = m_ec²/ln 2 = 0.51099895 MeV / ln 2 ∈ (0.73721, 0.73722) MeV/nat. -/
theorem electron_record_energy :
    0.73721 < (0.51099895 : ℝ) / Real.log 2 ∧ (0.51099895 : ℝ) / Real.log 2 < 0.73722 := by
  have a1 := Real.log_two_gt_d9; have a2 := Real.log_two_lt_d9
  have hp : 0 < Real.log 2 := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- C14-58: ⟨K²⟩ at η* equals 3/(2η*) ∈ (50.2229154252, 50.2229154257) (the tenth decimal is not fixed
by the certified η* bracket). -/
theorem mean_closure_energy {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    50.2229154252 < Entropic.FiniteModel.meanK2 η ∧ Entropic.FiniteModel.meanK2 η < 50.2229154257 := by
  obtain ⟨e1, e2⟩ := Entropic.ClosureRoot.stationary_bracket h
  obtain ⟨h0, hm⟩ := h
  unfold Entropic.ClosureRoot.etaLo at e1; unfold Entropic.ClosureRoot.etaHi at e2
  rw [hm]
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- C14-61, C14-62: E_nat/k_B = 0.737 MeV/k_B ∈ (8.55, 8.56)·10⁹ K; E_nat/k_B(2.7 K) ∈ (3.16, 3.17)·10⁹;
E_nat/k_BT_dS ∈ (3.88, 3.89)·10³⁹; 2m_ec²/k_BT_dS ∈ (5.39, 5.40)·10³⁹ (T_dS = 2.2·10⁻³⁰ K). -/
theorem thermal_thresholds :
    8.55e9 < (0.737e6 * 1.602176634e-19 / 1.380649e-23 : ℝ) ∧ (0.737e6 * 1.602176634e-19 / 1.380649e-23 : ℝ) < 8.56e9 ∧
      3.16e9 < (0.737e6 * 1.602176634e-19 / 1.380649e-23 / 2.7 : ℝ) ∧
      (0.737e6 * 1.602176634e-19 / 1.380649e-23 / 2.7 : ℝ) < 3.17e9 ∧
      3.88e39 < (0.737e6 * 1.602176634e-19 / 1.380649e-23 / 2.2e-30 : ℝ) ∧
      (0.737e6 * 1.602176634e-19 / 1.380649e-23 / 2.2e-30 : ℝ) < 3.89e39 ∧
      5.39e39 < (2 * 0.51099895e6 * 1.602176634e-19 / 1.380649e-23 / 2.2e-30 : ℝ) ∧
      (2 * 0.51099895e6 * 1.602176634e-19 / 1.380649e-23 / 2.2e-30 : ℝ) < 5.40e39 := by
  norm_num

/-- C14-63: with Planck-2018 H₀ = 67.36 km/s/Mpc and Ω_Λ = 0.6847 (H_Λ² = H₀²Ω_Λ), S_dS = πc⁵/(GħH_Λ²)
∈ (3.31, 3.32)·10¹²² and T_dS = ħH_Λ/(2πk_B) ∈ (2.19, 2.20)·10⁻³⁰ K. -/
theorem de_sitter_numbers :
    let H0 : ℝ := 67.36e3 / 3.0856775814913673e22
    3.31e122 < π * 299792458 ^ 5 / (6.67430e-11 * 1.054571817e-34 * (H0 ^ 2 * 0.6847)) ∧
      π * 299792458 ^ 5 / (6.67430e-11 * 1.054571817e-34 * (H0 ^ 2 * 0.6847)) < 3.32e122 ∧
      2.19e-30 < 1.054571817e-34 * (H0 * Real.sqrt 0.6847) / (2 * π * 1.380649e-23) ∧
      1.054571817e-34 * (H0 * Real.sqrt 0.6847) / (2 * π * 1.380649e-23) < 2.20e-30 := by
  intro H0
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6
  have s1 : (0.8274 : ℝ) < Real.sqrt 0.6847 := by
    rw [show (0.8274:ℝ) = Real.sqrt (0.8274 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s2 : Real.sqrt 0.6847 < (0.8275 : ℝ) := by
    rw [show (0.8275:ℝ) = Real.sqrt (0.8275 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hH : H0 = 67.36e3 / 3.0856775814913673e22 := rfl
  have hp : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by rw [hH]; positivity), hH]; nlinarith
  · rw [div_lt_iff₀ (by rw [hH]; positivity), hH]; nlinarith
  · rw [lt_div_iff₀ (by positivity), hH]; nlinarith
  · rw [div_lt_iff₀ (by positivity), hH]; nlinarith

/-- C14-64 (b): 10²⁴³/(3.3·10¹²²) ∈ (3.0, 3.1)·10¹²⁰, which is below 10¹²¹: the text's "exceeds by at
least 10¹²¹" overstates the ratio by a factor of about 3. -/
theorem history_vs_desitter :
    3.0e120 < (10:ℝ) ^ 243 / 3.3e122 ∧ (10:ℝ) ^ 243 / 3.3e122 < 3.1e120 ∧ (10:ℝ) ^ 243 / 3.3e122 < 1e121 := by
  norm_num

/-- C14-66: 2.6·10¹⁸³ × g_share,eff ∈ (1.92, 1.93)·10¹⁸⁴ at the closure root. -/
theorem hubble_register {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    1.92e184 < 2.6e183 * Entropic.ClosureRoot.gshare η ∧ 2.6e183 * Entropic.ClosureRoot.gshare η < 1.93e184 := by
  obtain ⟨g1, g2⟩ := Entropic.ClosureRoot.gshare_bracket h
  unfold Entropic.ClosureRoot.gLo at g1; unfold Entropic.ClosureRoot.gHi at g2
  constructor <;> nlinarith

/-- C14-72 (a): u = 8η*/49 ∈ (0.0048762, 0.0048763), α = √(1 − u) ∈ (0.99755885, 0.99755895); the
no-event operator diag(α, 1) is positive definite. -/
theorem no_event_kraus {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    0.0048762 < 8 * η / 49 ∧ 8 * η / 49 < 0.0048763 ∧
      0.99755885 < Real.sqrt (1 - 8 * η / 49) ∧ Real.sqrt (1 - 8 * η / 49) < 0.99755895 ∧
      0 < Real.sqrt (1 - 8 * η / 49) := by
  obtain ⟨e1, e2⟩ := Entropic.ClosureRoot.stationary_bracket h
  unfold Entropic.ClosureRoot.etaLo at e1; unfold Entropic.ClosureRoot.etaHi at e2
  have hu : 0 < 1 - 8 * η / 49 := by nlinarith
  have hs := Real.sq_sqrt hu.le
  have hs0 := Real.sqrt_nonneg (1 - 8 * η / 49)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, Real.sqrt_pos.mpr hu⟩

/-- Pair sum Σ_{i<k} m_im_k for four labels. -/
def pairSum (a b c d : ℤ) : ℤ := a * b + a * c + a * d + b * c + b * d + c * d

/-- C14-74: for four distinct labels in {−3,…,3}, Σ_{i<k} m_im_k ≤ 11, so
K² = 48 − (2/3)Σ m_im_k ≥ 122/3, with equality at {0,1,2,3} and {−3,−2,−1,0}. -/
def okB (a b c d : Fin 7) : Bool :=
  a == b || a == c || a == d || b == c || b == d || c == d ||
    decide (pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) ≤ 11)

theorem okB_all : ∀ a b c d : Fin 7, okB a b c d = true := by decide +kernel

theorem pair_sum_le (a b c d : Fin 7) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) ≤ 11 := by
  have := okB_all a b c d
  simp [okB, hab, hac, had, hbc, hbd, hcd] at this
  exact this

theorem K2_floor (a b c d : Fin 7) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    (122:ℝ) / 3 ≤ 48 - 2 / 3 * (pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) : ℝ) ∧
      (48:ℝ) - 2 / 3 * (pairSum 0 1 2 3 : ℝ) = 122 / 3 ∧ (48:ℝ) - 2 / 3 * (pairSum (-3) (-2) (-1) 0 : ℝ) = 122 / 3 := by
  have h := pair_sum_le a b c d hab hac had hbc hbd hcd
  have h' : (pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) : ℝ) ≤ 11 := by
    exact_mod_cast h
  refine ⟨by linarith, by norm_num [pairSum], by norm_num [pairSum]⟩

end Entropic.AppP.Num
