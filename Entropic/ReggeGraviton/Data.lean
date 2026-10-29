import Mathlib

/-!
# Linearized Regge calculus on the Freudenthal–Kuhn triangulation: lattice data

The hypercubic lattice `ℤ⁴` with each unit hypercube cut into the 24 path simplices
`0 → e_{π1} → e_{π1}+e_{π2} → e_{π1}+e_{π2}+e_{π3} → (1,1,1,1)`. This is the subdivision
`{0, 2^i, 2^i+2^j, 2^i+2^j+2^k, 15}` used for the length-Regge reference case in Dittrich et al.,
arXiv:2105.10808, who attribute the length-Regge Hessian on this lattice to Roček and Williams. It is
not the centrally subdivided lattice of the symbol cited in Appendix H.10. Edge types are the 15
nonzero vectors of `{0,1}⁴`.

`hzL` is 48 times the flat-space Hessian `∂²(∑_t A_t ε_t)/∂sₑ∂s_f` of one 4-simplex in the squared
edge lengths `s`, at the flat Kuhn simplex (squared length `j − i` between chain vertices `i < j`).
It is computed in exact arithmetic from the dihedral-angle derivatives through the Schläfli identity
`∂²S = ∑_t ∇A_t ∇ε_tᵀ` (`tools/regge_simplex_hessian.py`); it is the one numerical input of this
module group and is not derived in Lean. The assembly over the lattice, the moments and all limits
are kernel-checked. Two modelling choices are definitions: metric perturbations are placed at edge
midpoints (`DA`, `DB`), and `δs_v = v^μ v^ν h_μν` on the edges that carry metric data.
-/

namespace Entropic.ReggeGraviton

abbrev V4 := ℤ × ℤ × ℤ × ℤ

/-- The 24 axis orders (permutations of `0..3`). -/
def permList : List (List ℕ) :=
  [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
   [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
   [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
   [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]

def unit : ℕ → V4
  | 0 => (1, 0, 0, 0) | 1 => (0, 1, 0, 0) | 2 => (0, 0, 1, 0) | _ => (0, 0, 0, 1)

/-- Vertex `m` (`0 ≤ m ≤ 4`) of the path simplex `p`: the sum of the first `m` axis vectors. -/
def vert (p : ℕ) (m : ℕ) : V4 :=
  ((permList.getD p []).take m).foldr (fun i v => unit i + v) 0

/-- Edge `e` of a 4-simplex as a vertex pair `(i, j)`, `i < j`. -/
def edgeEnds : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- For each of the 24 simplices, its ten edges as (edge type, base vertex), in the order of
`edgeEnds`. Tabulated for fast kernel evaluation; `simplexData_kuhn` proves the table. -/
def simplexData : List (List (V4 × V4)) :=
  [[((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 0, 0)), ((0, 1, 1, 0), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 0)), ((0, 0, 1, 1), (1, 1, 0, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 0, 0)), ((0, 1, 0, 1), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 0, 0, 1), (1, 1, 0, 0)), ((0, 0, 1, 1), (1, 1, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 0, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (1, 0, 0, 0)), ((0, 1, 1, 0), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 1, 0)), ((0, 1, 0, 1), (1, 0, 1, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 0, 1, 0), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (1, 0, 0, 0)), ((0, 0, 1, 1), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 0, 0, 1), (1, 0, 1, 0)), ((0, 1, 0, 1), (1, 0, 1, 0)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 0, 0, 1), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (1, 0, 0, 0)), ((0, 1, 0, 1), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 1, 0, 0), (1, 0, 0, 1)), ((0, 1, 1, 0), (1, 0, 0, 1)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((1, 0, 0, 0), (0, 0, 0, 0)), ((1, 0, 0, 1), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (1, 0, 0, 0)), ((0, 0, 1, 1), (1, 0, 0, 0)), ((0, 1, 1, 1), (1, 0, 0, 0)), ((0, 0, 1, 0), (1, 0, 0, 1)), ((0, 1, 1, 0), (1, 0, 0, 1)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 1, 0, 0)), ((1, 0, 1, 0), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 0)), ((0, 0, 1, 1), (1, 1, 0, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 0), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 1, 0, 0)), ((1, 0, 0, 1), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((0, 0, 0, 1), (1, 1, 0, 0)), ((0, 0, 1, 1), (1, 1, 0, 0)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((0, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 1, 0, 0)), ((1, 0, 1, 0), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((1, 0, 0, 0), (0, 1, 1, 0)), ((1, 0, 0, 1), (0, 1, 1, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((0, 1, 1, 0), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 1, 0, 0)), ((0, 0, 1, 1), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((0, 0, 0, 1), (0, 1, 1, 0)), ((1, 0, 0, 1), (0, 1, 1, 0)), ((1, 0, 0, 0), (0, 1, 1, 1))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((0, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 1, 0, 0)), ((1, 0, 0, 1), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((1, 0, 0, 0), (0, 1, 0, 1)), ((1, 0, 1, 0), (0, 1, 0, 1)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((0, 1, 0, 0), (0, 0, 0, 0)), ((0, 1, 0, 1), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 1, 0, 0)), ((0, 0, 1, 1), (0, 1, 0, 0)), ((1, 0, 1, 1), (0, 1, 0, 0)), ((0, 0, 1, 0), (0, 1, 0, 1)), ((1, 0, 1, 0), (0, 1, 0, 1)), ((1, 0, 0, 0), (0, 1, 1, 1))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((1, 0, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 0, 1, 0)), ((1, 1, 0, 0), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((0, 1, 0, 0), (1, 0, 1, 0)), ((0, 1, 0, 1), (1, 0, 1, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((1, 0, 1, 0), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 0, 1, 0)), ((1, 0, 0, 1), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((0, 0, 0, 1), (1, 0, 1, 0)), ((0, 1, 0, 1), (1, 0, 1, 0)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((0, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 0), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (0, 0, 1, 0)), ((1, 1, 0, 0), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((1, 0, 0, 0), (0, 1, 1, 0)), ((1, 0, 0, 1), (0, 1, 1, 0)), ((0, 0, 0, 1), (1, 1, 1, 0))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((0, 1, 1, 0), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (0, 0, 1, 0)), ((0, 1, 0, 1), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((0, 0, 0, 1), (0, 1, 1, 0)), ((1, 0, 0, 1), (0, 1, 1, 0)), ((1, 0, 0, 0), (0, 1, 1, 1))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((0, 0, 1, 1), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 0, 1, 0)), ((1, 0, 0, 1), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((1, 0, 0, 0), (0, 0, 1, 1)), ((1, 1, 0, 0), (0, 0, 1, 1)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((0, 0, 1, 0), (0, 0, 0, 0)), ((0, 0, 1, 1), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 0, 1, 0)), ((0, 1, 0, 1), (0, 0, 1, 0)), ((1, 1, 0, 1), (0, 0, 1, 0)), ((0, 1, 0, 0), (0, 0, 1, 1)), ((1, 1, 0, 0), (0, 0, 1, 1)), ((1, 0, 0, 0), (0, 1, 1, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((1, 0, 0, 1), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 0, 0, 1)), ((1, 1, 0, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((0, 1, 0, 0), (1, 0, 0, 1)), ((0, 1, 1, 0), (1, 0, 0, 1)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((1, 0, 0, 1), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((1, 0, 0, 0), (0, 0, 0, 1)), ((1, 0, 1, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((0, 0, 1, 0), (1, 0, 0, 1)), ((0, 1, 1, 0), (1, 0, 0, 1)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 0, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (0, 0, 0, 1)), ((1, 1, 0, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((1, 0, 0, 0), (0, 1, 0, 1)), ((1, 0, 1, 0), (0, 1, 0, 1)), ((0, 0, 1, 0), (1, 1, 0, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 1, 0, 1), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 1, 0, 0), (0, 0, 0, 1)), ((0, 1, 1, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((0, 0, 1, 0), (0, 1, 0, 1)), ((1, 0, 1, 0), (0, 1, 0, 1)), ((1, 0, 0, 0), (0, 1, 1, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 1, 1), (0, 0, 0, 0)), ((1, 0, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 0, 0, 1)), ((1, 0, 1, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((1, 0, 0, 0), (0, 0, 1, 1)), ((1, 1, 0, 0), (0, 0, 1, 1)), ((0, 1, 0, 0), (1, 0, 1, 1))],
   [((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 1, 1), (0, 0, 0, 0)), ((0, 1, 1, 1), (0, 0, 0, 0)), ((1, 1, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 0, 0, 1)), ((0, 1, 1, 0), (0, 0, 0, 1)), ((1, 1, 1, 0), (0, 0, 0, 1)), ((0, 1, 0, 0), (0, 0, 1, 1)), ((1, 1, 0, 0), (0, 0, 1, 1)), ((1, 0, 0, 0), (0, 1, 1, 1))]]

theorem simplexData_kuhn : simplexData = (List.range 24).map fun p => edgeEnds.map fun (i, j) =>
    (vert p j - vert p i, vert p i) := by decide

/-- 48 × flat Hessian of the Regge action of one Kuhn simplex (edge order `edgeEnds`). -/
def hzL : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 3, 0, -6, 0, 0],
   [0, -3, 3, 0, 6, -6, 0, 3, 0, 0],
   [0, 3, -2, 0, -6, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 6, -6, 0, -6, 6, 0, 0, 3, -6],
   [3, -6, 3, 0, 6, -6, 3, 6, -6, 3],
   [0, 0, 0, 0, 0, 3, -2, -6, 3, 0],
   [-6, 3, 0, 0, 0, 6, -6, -6, 6, 0],
   [0, 0, 0, 0, 3, -6, 3, 6, -3, 0],
   [0, 0, 0, 0, -6, 3, 0, 0, 0, 0]]

def typ (p : Fin 24) (e : Fin 10) : V4 := ((simplexData.getD p.val []).getD e.val (0, 0)).1
def base (p : Fin 24) (e : Fin 10) : V4 := ((simplexData.getD p.val []).getD e.val (0, 0)).2
def hz (e f : Fin 10) : ℤ := (hzL.getD e.val []).getD f.val 0

theorem hz_symm : ∀ e f, hz e f = hz f e := by decide

def comp (v : V4) : Fin 4 → ℤ := ![v.1, v.2.1, v.2.2.1, v.2.2.2]

def weight (v : V4) : ℤ := v.1 + v.2.1 + v.2.2.1 + v.2.2.2

/-- The ten metric components `(μ, ν)`, `μ ≤ ν`. -/
def symIdx : Fin 10 → Fin 4 × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]

/-- `δs_v = v^μ v^ν h_μν`: coefficient of metric component `c` in the squared length of `v`,
for the edges carrying metric data (weight ≤ 3; the hyper-diagonal row of the Hessian vanishes). -/
def ec (v : V4) (c : Fin 10) : ℤ :=
  if weight v ≤ 3 then
    comp v (symIdx c).1 * comp v (symIdx c).2 * (if (symIdx c).1 = (symIdx c).2 then 1 else 2)
  else 0

/-- The four body diagonals (weight-3 edge types), integrated out. -/
def body : Fin 4 → V4 := ![(0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1), (1, 1, 1, 0)]

/-- Doubled phase displacements: metric–metric `−a + 2(b_f − b_e) + b`, metric–body `−a + 2(b_f − b_e)`. -/
def DA (a ba b bb : V4) : V4 := -a + 2 • (bb - ba) + b
def DB (a ba bb : V4) : V4 := -a + 2 • (bb - ba)

def dA (p : Fin 24) (e f : Fin 10) : V4 := DA (typ p e) (base p e) (typ p f) (base p f)
def dB (p : Fin 24) (e f : Fin 10) : V4 := DB (typ p e) (base p e) (base p f)

/-- Coefficient (×48) of the metric–metric term. -/
def GA (c d : Fin 10) (a b : V4) (x : ℤ) : ℤ := if x = 0 then 0 else x * ec a c * ec b d
/-- Coefficient (×48) of the metric–body term for body diagonal `j`. -/
def GB (c : Fin 10) (j : Fin 4) (a b : V4) (x : ℤ) : ℤ :=
  if x = 0 then 0 else if b = body j then x * ec a c else 0

def cA (c d : Fin 10) (p : Fin 24) (e f : Fin 10) : ℤ := GA c d (typ p e) (typ p f) (hz e f)
def cB (c : Fin 10) (j : Fin 4) (p : Fin 24) (e f : Fin 10) : ℤ := GB c j (typ p e) (typ p f) (hz e f)

/-- Sum of `G(type_e, base_e, type_f, base_f, hz_ef)` over all simplices and edge pairs, by
sequential traversal (fast in the kernel). `fastSum_eq` identifies it with the indexed sum. -/
def fastSum (G : V4 → V4 → V4 → V4 → ℤ → ℤ) : ℤ :=
  (simplexData.map fun S => ((S.zip hzL).map fun (e, row) =>
    ((S.zip row).map fun (f, x) => G e.1 e.2 f.1 f.2 x).sum).sum).sum


/-! ### `fastSum` is the indexed sum -/

theorem list_sum_eq_fin {α : Type*} (d : α) (f : α → ℤ) :
    ∀ (l : List α) (n : ℕ), l.length = n → (l.map f).sum = ∑ i : Fin n, f (l.getD i.val d)
  | [], n, h => by subst h; simp
  | _ :: _, 0, h => by simp at h
  | a :: l, n + 1, h => by
    rw [List.map_cons, List.sum_cons, Fin.sum_univ_succ,
      list_sum_eq_fin d f l n (by simpa using h)]
    simp

theorem zip_sum_eq_fin {α β : Type*} (d₁ : α) (d₂ : β) (g : α × β → ℤ) :
    ∀ (l₁ : List α) (l₂ : List β) (n : ℕ), l₁.length = n → l₂.length = n →
      ((l₁.zip l₂).map g).sum = ∑ i : Fin n, g (l₁.getD i.val d₁, l₂.getD i.val d₂)
  | [], _, n, h₁, _ => by subst h₁; simp
  | _ :: _, _, 0, h₁, _ => by simp at h₁
  | _ :: _, [], _ + 1, _, h₂ => by simp at h₂
  | a :: l₁, b :: l₂, n + 1, h₁, h₂ => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, Fin.sum_univ_succ,
      zip_sum_eq_fin d₁ d₂ g l₁ l₂ n (by simpa using h₁) (by simpa using h₂)]
    simp

theorem simplexData_length : simplexData.length = 24 := by decide
theorem simplexData_rows : ∀ p : Fin 24, (simplexData.getD p.val []).length = 10 := by decide
theorem hzL_length : hzL.length = 10 := by decide
theorem hzL_rows : ∀ e : Fin 10, (hzL.getD e.val []).length = 10 := by decide

theorem fastSum_eq (G : V4 → V4 → V4 → V4 → ℤ → ℤ) :
    fastSum G = ∑ p : Fin 24, ∑ e : Fin 10, ∑ f : Fin 10,
      G (typ p e) (base p e) (typ p f) (base p f) (hz e f) := by
  rw [fastSum, list_sum_eq_fin [] _ simplexData 24 simplexData_length]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [zip_sum_eq_fin (0, 0) [] _ _ hzL 10 (simplexData_rows p) hzL_length]
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp only
  rw [zip_sum_eq_fin (0, 0) 0 _ _ _ 10 (simplexData_rows p) (hzL_rows e)]
  rfl

/-! ### Moments (computed by the kernel in `Moments*`) -/

def momA0 (c d : Fin 10) : ℤ := fastSum fun a _ b _ x => GA c d a b x
def momA1 (c d : Fin 10) (i : Fin 4) : ℤ :=
  fastSum fun a ba b bb x => GA c d a b x * comp (DA a ba b bb) i
def momA2 (c d : Fin 10) (i l : Fin 4) : ℤ :=
  fastSum fun a ba b bb x => GA c d a b x * comp (DA a ba b bb) i * comp (DA a ba b bb) l
def momB0 (c : Fin 10) (j : Fin 4) : ℤ := fastSum fun a _ b _ x => GB c j a b x
def momB1 (c : Fin 10) (j : Fin 4) (i : Fin 4) : ℤ :=
  fastSum fun a ba b bb x => GB c j a b x * comp (DB a ba bb) i

/-- The body-diagonal block of the lattice Hessian (×48) and its displacement support.
With `bodyC j j' = −24 δ` and `bodyD = 0`, `C(q) = −½ I` for all `q`. -/
def bodyC (j j' : Fin 4) : ℤ :=
  fastSum fun a _ b _ x => if a = body j ∧ b = body j' then x else 0
def bodyD (j j' : Fin 4) : ℤ :=
  fastSum fun a ba b bb x => if x ≠ 0 ∧ a = body j ∧ b = body j' ∧ bb - ba ≠ 0 then 1 else 0

end Entropic.ReggeGraviton
