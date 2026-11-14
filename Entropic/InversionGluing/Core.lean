/-!
# Inversion gluing of four-port cells: integer core

Ledger: C07-101, C10-48 (girth and closed words), C07-100 (counts), C14-78 (integer form).
No imports. Units: the four bond vectors are `(±1, ±1, ±1)`, so cell centres are integer points.
The neighbour of a cell across face `j` is its point inversion through the face centre,
`p ↦ tet j - p` for the base cell.

Contents
* `develop`: the cells reached by composing inversions are the pairs (class, centre) with the
  neighbour rule `nbr`; `nbr` is the diamond adjacency.
* `closed_iff_balanced`: a word closes exactly when every port is used equally often from the two
  classes (Theorem A of DIAMOND_DERIVATION_2026-11-14).
* `no_two_ring`, `no_four_ring`, `six_ring_iff`, `hexagon`: the shortest closed reduced words are
  exactly the three-port words `(i, k, j, i, k, j)`.
* `closed_everywhere`: every cell is equivalent to the base cell.
* `cheb_ne_pow`: `3^n cos(n arccos(1/3))` is never `3^n` for `n ≥ 1` (integer form of: no ring of
  regular mirror-glued cells closes with zero deficit).
* `inversion_moves_face_vertices`, `mirror_fixes_face_vertices`: a flat triangular face is glued
  vertex to vertex by the mirror and never by the inversion.
* `halfturn_moves_star`: the half turn of the mirror gluing moves the other three labelled normals.
-/

namespace Entropic.InversionGluing

/-- Integer vectors. -/
structure V3 where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

namespace V3
def zero : V3 := ⟨0, 0, 0⟩
instance : Add V3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub V3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg V3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩
def smul (c : Int) (a : V3) : V3 := ⟨c * a.x, c * a.y, c * a.z⟩
def dot (a b : V3) : Int := a.x * b.x + a.y * b.y + a.z * b.z

@[simp] theorem add_x (a b : V3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : V3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : V3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : V3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : V3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : V3) : (a - b).z = a.z - b.z := rfl
@[simp] theorem neg_x (a : V3) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : V3) : (-a).y = -a.y := rfl
@[simp] theorem neg_z (a : V3) : (-a).z = -a.z := rfl
@[simp] theorem zero_x : zero.x = 0 := rfl
@[simp] theorem zero_y : zero.y = 0 := rfl
@[simp] theorem zero_z : zero.z = 0 := rfl

theorem eq_iff (a b : V3) : a = b ↔ a.x = b.x ∧ a.y = b.y ∧ a.z = b.z := by
  cases a; cases b; simp
end V3

open V3

/-- Componentwise linear integer arithmetic on vector identities. -/
macro "v3_arith" : tactic =>
  `(tactic| (simp only [V3.eq_iff, V3.add_x, V3.add_y, V3.add_z, V3.sub_x, V3.sub_y, V3.sub_z,
      V3.neg_x, V3.neg_y, V3.neg_z, V3.zero_x, V3.zero_y, V3.zero_z] <;> omega))

/-- The four bond vectors (outward face normals of the base cell, times `√3`). -/
def tet : Fin 4 → V3
  | 0 => ⟨1, 1, 1⟩
  | 1 => ⟨1, -1, -1⟩
  | 2 => ⟨-1, 1, -1⟩
  | 3 => ⟨-1, -1, 1⟩

theorem tet_sum : tet 0 + tet 1 + tet 2 + tet 3 = V3.zero := by decide

theorem tet_dot : ∀ i j : Fin 4, dot (tet i) (tet j) = if i = j then 3 else -1 := by decide

/-! ### The inversions and the group they generate -/

/-- Inversion of the base cell through the centre `tet j / 2` of its face `j`. -/
def inv (j : Fin 4) (p : V3) : V3 := tet j - p

theorem inv_inv (j : Fin 4) (p : V3) : inv j (inv j p) = p := by
  unfold inv; v3_arith

/-- Two inversions compose to a translation. -/
theorem inv_comp (i j : Fin 4) (p : V3) : inv i (inv j p) = p + (tet i - tet j) := by
  unfold inv; v3_arith

/-- `(I_i I_k I_j)^2 = 1`. -/
theorem inv_hexagon (i k j : Fin 4) (p : V3) :
    inv i (inv k (inv j (inv i (inv k (inv j p))))) = p := by
  unfold inv; v3_arith

/-- The maps `p ↦ p + t` (`flip = false`) and `p ↦ t - p` (`flip = true`). -/
structure Iso where
  flip : Bool
  shift : V3
deriving DecidableEq

def Iso.act (g : Iso) (p : V3) : V3 :=
  match g.flip with
  | false => p + g.shift
  | true => g.shift - p

/-- Composition `g ∘ h`. -/
def Iso.comp (g h : Iso) : Iso :=
  match g.flip with
  | false => ⟨h.flip, h.shift + g.shift⟩
  | true => ⟨!h.flip, g.shift - h.shift⟩

def invIso (j : Fin 4) : Iso := ⟨true, tet j⟩

theorem invIso_act (j : Fin 4) (p : V3) : (invIso j).act p = inv j p := rfl

theorem comp_act (g h : Iso) (p : V3) : (g.comp h).act p = g.act (h.act p) := by
  cases g with | mk gf gs => cases h with | mk hf hs =>
  cases gf <;> cases hf <;> simp only [Iso.comp, Iso.act, Bool.not_true, Bool.not_false] <;> v3_arith

/-! ### The developed complex -/

/-- A cell: orientation class and centre. -/
structure Cell where
  odd : Bool
  pos : V3
deriving DecidableEq, Repr

def base : Cell := ⟨false, V3.zero⟩

/-- Neighbour across port `j`: the bond vector is `+tet j` from an even cell and `-tet j` from an
odd cell. This is the diamond adjacency. -/
def nbr (c : Cell) (j : Fin 4) : Cell :=
  match c.odd with
  | false => ⟨true, c.pos + tet j⟩
  | true => ⟨false, c.pos - tet j⟩

/-- The cell `g(base)`: class of `g` and centre `g(0)`. -/
def Iso.cell (g : Iso) : Cell := ⟨g.flip, g.shift⟩

/-- **Development.** The neighbour of `g(base)` across its face `j` is `(g ∘ I_j)(base)`. -/
theorem develop (g : Iso) (j : Fin 4) : (g.comp (invIso j)).cell = nbr g.cell j := by
  cases g with | mk gf gs =>
  cases gf <;> simp only [Iso.comp, invIso, Iso.cell, nbr, Bool.not_true, Cell.mk.injEq, true_and] <;>
    v3_arith

theorem nbr_odd (c : Cell) (j : Fin 4) : (nbr c j).odd = !c.odd := by
  cases c with | mk b p => cases b <;> rfl

/-- Crossing the same face twice returns to the cell. -/
theorem nbr_nbr (c : Cell) (j : Fin 4) : nbr (nbr c j) j = c := by
  cases c with | mk b p =>
  cases b <;> simp only [nbr, Cell.mk.injEq, true_and] <;> v3_arith

def walk : List (Fin 4) → Cell → Cell
  | [], c => c
  | j :: w, c => walk w (nbr c j)

/-- Every three-port word `(i, k, j, i, k, j)` closes, from every cell. -/
theorem hexagon (i k j : Fin 4) (c : Cell) : walk [i, k, j, i, k, j] c = c := by
  cases c with | mk b p =>
  cases b <;> simp only [walk, nbr, Cell.mk.injEq, true_and] <;> v3_arith

/-- No closed reduced word of length two. -/
theorem no_two_ring : ∀ i j : Fin 4, i ≠ j → walk [i, j] base ≠ base := by decide

/-- No closed reduced word of length four. -/
theorem no_four_ring : ∀ i j k l : Fin 4, i ≠ j → j ≠ k → k ≠ l → l ≠ i →
    walk [i, j, k, l] base ≠ base := by decide

set_option maxRecDepth 100000 in
/-- The closed reduced words of length six are exactly the words `(a, b, c, a, b, c)`. -/
theorem six_ring_iff : ∀ a b c d e f : Fin 4, a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ f → f ≠ a →
    (walk [a, b, c, d, e, f] base = base ↔ (d = a ∧ e = b ∧ f = c)) := by decide

/-! ### Every cell is equivalent to the base cell -/

def Cell.translate (t : V3) (c : Cell) : Cell := ⟨c.odd, c.pos + t⟩
/-- Central inversion of the whole complex; it exchanges the two classes. -/
def Cell.invert (c : Cell) : Cell := ⟨!c.odd, -c.pos⟩

theorem nbr_translate (t : V3) (c : Cell) (j : Fin 4) :
    nbr (c.translate t) j = (nbr c j).translate t := by
  cases c with | mk b p =>
  cases b <;> simp only [nbr, Cell.translate, Cell.mk.injEq, true_and] <;> v3_arith

theorem nbr_invert (c : Cell) (j : Fin 4) : nbr c.invert j = (nbr c j).invert := by
  cases c with | mk b p =>
  cases b <;> simp only [nbr, Cell.invert, Bool.not_true, Bool.not_false, Cell.mk.injEq, true_and] <;>
    v3_arith

theorem walk_translate (t : V3) : ∀ (w : List (Fin 4)) (c : Cell),
    walk w (c.translate t) = (walk w c).translate t
  | [], _ => rfl
  | j :: w, c => by simp only [walk]; rw [nbr_translate]; exact walk_translate t w (nbr c j)

theorem walk_invert : ∀ (w : List (Fin 4)) (c : Cell), walk w c.invert = (walk w c).invert
  | [], _ => rfl
  | j :: w, c => by simp only [walk]; rw [nbr_invert]; exact walk_invert w (nbr c j)

theorem translate_inj (t : V3) (a b : Cell) : a.translate t = b.translate t ↔ a = b := by
  cases a with | mk ab ap => cases b with | mk bb bp =>
  simp only [Cell.translate, Cell.mk.injEq]
  constructor
  · intro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; revert h2; v3_arith
  · intro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩

theorem invert_inj (a b : Cell) : a.invert = b.invert ↔ a = b := by
  cases a with | mk ab ap => cases b with | mk bb bp =>
  simp only [Cell.invert, Cell.mk.injEq]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨by cases ab <;> cases bb <;> simp_all, ?_⟩
    revert h2; v3_arith
  · intro ⟨h1, h2⟩; exact ⟨by rw [h1], by rw [h2]⟩

/-- A word closes from a cell exactly when it closes from the base cell. -/
theorem closed_everywhere (w : List (Fin 4)) (c : Cell) : walk w c = c ↔ walk w base = base := by
  cases c with | mk b p =>
  cases b
  · have h : (⟨false, p⟩ : Cell) = base.translate p := by
      simp only [Cell.translate, base, Cell.mk.injEq, true_and]; v3_arith
    rw [h, walk_translate, translate_inj]
  · have h : (⟨true, p⟩ : Cell) = (base.invert).translate p := by
      simp only [Cell.translate, Cell.invert, base, Bool.not_false, Cell.mk.injEq, true_and]; v3_arith
    rw [h, walk_translate, walk_invert, translate_inj, invert_inj]

/-! ### Theorem A: a word closes exactly when it is balanced -/

def sgn (b : Bool) : Int := match b with | false => 1 | true => -1

/-- Signed count of port `j`: `+1` for a step from an even cell, `-1` from an odd cell. -/
def cnt (j : Fin 4) : List (Fin 4) → Bool → Int
  | [], _ => 0
  | i :: w, b => (if i = j then sgn b else 0) + cnt j w (!b)

/-- Class reached after a word. -/
def par : List (Fin 4) → Bool → Bool
  | [], b => b
  | _ :: w, b => par w (!b)

theorem walk_odd : ∀ (w : List (Fin 4)) (c : Cell), (walk w c).odd = par w c.odd
  | [], _ => rfl
  | j :: w, c => by simp only [walk, par]; rw [walk_odd w (nbr c j), nbr_odd]

theorem delta_x : ∀ i : Fin 4, (tet i).x = (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0)
    - (if i = 2 then 1 else 0) - (if i = 3 then (1 : Int) else 0) := by decide
theorem delta_y : ∀ i : Fin 4, (tet i).y = (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)
    + (if i = 2 then 1 else 0) - (if i = 3 then (1 : Int) else 0) := by decide
theorem delta_z : ∀ i : Fin 4, (tet i).z = (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)
    - (if i = 2 then 1 else 0) + (if i = 3 then (1 : Int) else 0) := by decide
theorem delta_one : ∀ i : Fin 4, (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0)
    + (if i = 2 then 1 else 0) + (if i = 3 then (1 : Int) else 0) = 1 := by decide

theorem walk_pos : ∀ (w : List (Fin 4)) (c : Cell),
    (walk w c).pos.x = c.pos.x + cnt 0 w c.odd + cnt 1 w c.odd - cnt 2 w c.odd - cnt 3 w c.odd ∧
    (walk w c).pos.y = c.pos.y + cnt 0 w c.odd - cnt 1 w c.odd + cnt 2 w c.odd - cnt 3 w c.odd ∧
    (walk w c).pos.z = c.pos.z + cnt 0 w c.odd - cnt 1 w c.odd - cnt 2 w c.odd + cnt 3 w c.odd
  | [], c => by simp [walk, cnt]
  | i :: w, c => by
    have ih := walk_pos w (nbr c i)
    have hx := delta_x i; have hy := delta_y i; have hz := delta_z i
    cases c with | mk b p =>
    cases b <;> simp only [walk, cnt, nbr, sgn, Bool.not_true, Bool.not_false, V3.add_x, V3.add_y,
      V3.add_z, V3.sub_x, V3.sub_y, V3.sub_z] at ih ⊢ <;>
      (repeat' split at hx) <;> (repeat' split at hy) <;> (repeat' split at hz) <;>
      simp_all <;> omega

theorem cnt_sum : ∀ (w : List (Fin 4)) (b : Bool),
    cnt 0 w b + cnt 1 w b + cnt 2 w b + cnt 3 w b = if par w b = b then 0 else sgn b
  | [], b => by simp [cnt, par]
  | i :: w, b => by
    have ih := cnt_sum w (!b)
    have h1 := delta_one i
    cases b <;> simp only [cnt, par, sgn, Bool.not_true, Bool.not_false] at ih ⊢ <;>
      (repeat' split at h1) <;> (repeat' split at ih) <;> simp_all <;> omega

/-- **Theorem A.** A word returns to its starting cell exactly when every port is used equally
often from the two classes. -/
theorem closed_iff_balanced (w : List (Fin 4)) (c : Cell) :
    walk w c = c ↔
      (cnt 0 w c.odd = 0 ∧ cnt 1 w c.odd = 0 ∧ cnt 2 w c.odd = 0 ∧ cnt 3 w c.odd = 0) := by
  have hp := walk_pos w c
  have ho := walk_odd w c
  have hs := cnt_sum w c.odd
  constructor
  · intro h
    rw [h] at hp ho
    rw [← ho] at hs
    simp only [ite_true] at hs
    omega
  · intro ⟨h0, h1, h2, h3⟩
    rw [h0, h1, h2, h3] at hp hs
    have hpar : par w c.odd = c.odd := by
      cases hc : c.odd <;> rw [hc] at hs <;> simp only [sgn] at hs <;> split at hs <;> simp_all
    cases hw : walk w c with | mk wb wp =>
    cases c with | mk b p =>
    rw [hw] at hp ho
    simp only [Cell.mk.injEq, V3.eq_iff]
    simp only at hp ho hpar
    refine ⟨by rw [ho, hpar], ?_⟩
    omega

/-! ### Counts of the complex -/

/-- Per primitive cell: 2 hinge end points, 4 hinges, 4 faces, 2 cells. -/
theorem euler_inversion_complex : (2 : Int) - 4 + 4 - 2 = 0 := by decide

/-- With twelve hinges per cell and six cells around every hinge, hinges = 2 × cells, and Euler's
relation `V - E + F - T = 0` with `F = 2T` gives one hinge end point per cell. -/
theorem one_end_point_per_cell (V E T : Int) (hE : 6 * E = 12 * T) (hEuler : V - E + 2 * T - T = 0) :
    V = T := by omega

/-- Simplicial count for comparison: six edges per cell and `E = V + T`, `V ≥ 1`, force the mean
number of cells around an edge below six. -/
theorem simplicial_mean_below_six (V T : Int) (hV : 1 ≤ V) : 6 * T < 6 * (V + T) := by omega

/-! ### Mirror gluing of regular cells -/

/-- `cheb n = 3^n cos(n θ)` for `cos θ = 1/3`, by `cos((n+2)θ) = 2 cos θ cos((n+1)θ) - cos(nθ)`. -/
def cheb : Nat → Int
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * cheb (n + 1) - 9 * cheb n

theorem cheb_succ_succ (n : Nat) : cheb (n + 2) = 2 * cheb (n + 1) - 9 * cheb n := by
  simp [cheb]

theorem cheb_not_div3 : ∀ n : Nat, cheb (n + 1) % 3 ≠ 0
  | 0 => by decide
  | n + 1 => by
    have ih := cheb_not_div3 n
    have h : cheb (n + 1 + 1) = 2 * cheb (n + 1) - 9 * cheb n := cheb_succ_succ n
    omega

/-- `cos(n arccos(1/3)) ≠ 1` for `n ≥ 1`, in integers: a ring of `n` regular cells glued by plane
reflections has total dihedral angle `n arccos(1/3)`, never a multiple of `2π`. -/
theorem cheb_ne_pow (n : Nat) (hn : 1 ≤ n) : cheb n ≠ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := cheb_not_div3 m
  have h2 : (3 : Int) ^ (m + 1) = 3 ^ m * 3 := Int.pow_succ 3 m
  intro h
  rw [h, h2] at h1
  omega

/-- Vertices of the base cell are `-3 tet i`; face `j` has centroid `tet j`. The inversion through
that centroid sends no vertex of the face to a vertex of the face. -/
theorem inversion_moves_face_vertices : ∀ j i k : Fin 4, i ≠ j → k ≠ j →
    smul 2 (tet j) - smul (-3) (tet i) ≠ smul (-3) (tet k) := by decide

/-- The vertices of face `j` lie on the mirror plane `tet j · p = 3`, so the reflection fixes them. -/
theorem mirror_fixes_face_vertices : ∀ j i : Fin 4, i ≠ j → dot (tet j) (smul (-3) (tet i)) = 3 := by
  decide

/-- Three times the half turn about `tet j`: `3 C_j v = 2 (tet j · v) tet j - 3 v`. -/
def halfturn3 (j : Fin 4) (v : V3) : V3 := smul (2 * dot (tet j) v) (tet j) - smul 3 v

theorem halfturn_fixes_normal : ∀ j : Fin 4, halfturn3 j (tet j) = smul 3 (tet j) := by decide

/-- The half turn sends each of the other three normals to a vector that is not a normal of the
star: the mirror-glued neighbour does not carry the star of the cell. -/
theorem halfturn_moves_star : ∀ j i k : Fin 4, i ≠ j → halfturn3 j (tet i) ≠ smul 3 (tet k) := by
  decide

end Entropic.InversionGluing
