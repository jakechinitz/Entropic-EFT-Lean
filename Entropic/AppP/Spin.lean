import Entropic.AppP.Records
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Appendix P, spin-3/2 pair algebra in the ladder basis (C14-38, C14-48, C14-49 partial).

The ladder basis rescales the standard |3/2, m⟩ basis by a positive diagonal matrix so that J₊ has unit
entries; then J₋ has entries 3, 4, 3 and H = 2J_z = diag(3, 1, −1, −3). Every statement below is
invariant under that diagonal similarity (spectra, traces, polynomial identities), and I ⊗ H, H ⊗ I are
unchanged by it. Integer matrices are compared entrywise by kernel evaluation. -/

noncomputable section
namespace Entropic.AppP.Spin
open Matrix
open scoped Kronecker

def HsF : Fin 4 → Fin 4 → ℤ := ![![3,0,0,0],![0,1,0,0],![0,0,-1,0],![0,0,0,-3]]
def JpF : Fin 4 → Fin 4 → ℤ := ![![0,1,0,0],![0,0,1,0],![0,0,0,1],![0,0,0,0]]
def JmF : Fin 4 → Fin 4 → ℤ := ![![0,0,0,0],![3,0,0,0],![0,4,0,0],![0,0,3,0]]
def IdF : Fin 4 → Fin 4 → ℤ := fun i j => if i = j then 1 else 0
def Hs : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of HsF
def Jp : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of JpF
def Jm : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of JmF

def hi (i : Fin 16) : Fin 4 := ⟨i.val / 4, by omega⟩
def lo (i : Fin 16) : Fin 4 := ⟨i.val % 4, by omega⟩

/-- Kronecker product on Fin 16 = Fin 4 × Fin 4 (index 4a + b). -/
def krF (A B : Fin 4 → Fin 4 → ℤ) : Fin 16 → Fin 16 → ℤ := fun i j => A (hi i) (hi j) * B (lo i) (lo j)

def kr (A B : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun i j => A (hi i) (hi j) * B (lo i) (lo j)

theorem kr_eq (A B : Matrix (Fin 4) (Fin 4) ℤ) :
    kr A B = Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) := by
  ext i j
  simp only [kr, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.kroneckerMap_apply]
  congr 1 <;> congr 1 <;> ext <;> simp [hi, lo, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem mul4 (A B : Matrix (Fin 4) (Fin 4) ℤ) (i j : Fin 4) :
    (A * B) i j = (List.ofFn fun k => A i k * B k j).sum := by rw [Matrix.mul_apply, List.sum_ofFn]

theorem mul16 (A B : Matrix (Fin 16) (Fin 16) ℤ) (i j : Fin 16) :
    (A * B) i j = (List.ofFn fun k => A i k * B k j).sum := by rw [Matrix.mul_apply, List.sum_ofFn]

theorem tr16 (A : Matrix (Fin 16) (Fin 16) ℤ) : A.trace = (List.ofFn fun k => A k k).sum := by
  rw [Matrix.trace, List.sum_ofFn]; rfl

/-- [J₊, J₋] = 2J_z = H in the ladder basis. -/
theorem ladder_chk : ∀ i j : Fin 4,
    (List.ofFn fun k => JpF i k * JmF k j).sum - (List.ofFn fun k => JmF i k * JpF k j).sum = HsF i j := by
  decide +kernel

theorem ladder_comm : Jp * Jm - Jm * Jp = Hs := by
  ext i j; rw [Matrix.sub_apply, mul4, mul4]; exact ladder_chk i j

/-- 4 Q_f(1) = 9I − 4J_L·J_R = 9I − H⊗H − 2(J₊⊗J₋ + J₋⊗J₊). -/
def MzF : Fin 16 → Fin 16 → ℤ := fun i j =>
  (if i = j then 9 else 0) - krF HsF HsF i j - 2 * (krF JpF JmF i j + krF JmF JpF i j)
def Mz : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of MzF

theorem Mz_eq : Mz = (9:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - kr Hs Hs - (2:ℤ) • (kr Jp Jm + kr Jm Jp) := by
  ext i j
  simp only [Mz, MzF, krF, kr, Hs, Jp, Jm, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- 4J² for the total spin of the pair: (H⊗I + I⊗H)² + 2(J₊ᵗJ₋ᵗ + J₋ᵗJ₊ᵗ). -/
def HtF : Fin 16 → Fin 16 → ℤ := fun i j => krF HsF IdF i j + krF IdF HsF i j
def JptF : Fin 16 → Fin 16 → ℤ := fun i j => krF JpF IdF i j + krF IdF JpF i j
def JmtF : Fin 16 → Fin 16 → ℤ := fun i j => krF JmF IdF i j + krF IdF JmF i j
def Htot : Matrix (Fin 16) (Fin 16) ℤ := kr Hs 1 + kr 1 Hs
def Jpt : Matrix (Fin 16) (Fin 16) ℤ := kr Jp 1 + kr 1 Jp
def Jmt : Matrix (Fin 16) (Fin 16) ℤ := kr Jm 1 + kr 1 Jm

def M2F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 72, 0, 0, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 192, 0, 0, -160, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 360, 0, 0, -168, 0, 0, 48, 0, 0, 0, 0, 0, 0],
    ![0, -72, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -120, 0, 0, 160, 0, 0, -120, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -168, 0, 0, 200, 0, 0, -160, 0, 0, 48, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 192, 0, 0, -120, 0, 0, 48, 0, 0],
    ![0, 0, 48, 0, 0, -160, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 48, 0, 0, -160, 0, 0, 200, 0, 0, -168, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -160, 0, 0, 160, 0, 0, -160, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, -72, 0],
    ![0, 0, 0, 0, 0, 0, 48, 0, 0, -168, 0, 0, 360, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 48, 0, 0, -120, 0, 0, 192, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -72, 0, 0, 72, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def M2 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of M2F

def M3F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 864, 0, 0, -864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3264, 0, 0, -3200, 0, 0, 1536, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 7488, 0, 0, -4224, 0, 0, 1824, 0, 0, -288, 0, 0, 0],
    ![0, -864, 0, 0, 864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2400, 0, 0, 3200, 0, 0, -2400, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -4224, 0, 0, 4288, 0, 0, -3488, 0, 0, 1824, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 3264, 0, 0, -2400, 0, 0, 1536, 0, 0],
    ![0, 0, 1536, 0, 0, -3200, 0, 0, 3264, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1824, 0, 0, -3488, 0, 0, 4288, 0, 0, -4224, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -3200, 0, 0, 3200, 0, 0, -3200, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 864, 0, 0, -864, 0],
    ![0, 0, 0, -288, 0, 0, 1824, 0, 0, -4224, 0, 0, 7488, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1536, 0, 0, -2400, 0, 0, 3264, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -864, 0, 0, 864, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def M3 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of M3F

def NmF : Fin 16 → Fin 16 → ℤ :=
  ![![-5760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -2880, 0, 0, -2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1152, 0, 0, -2304, 0, 0, -1152, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -288, 0, 0, -864, 0, 0, -864, 0, 0, -288, 0, 0, 0],
    ![0, -2880, 0, 0, -2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1728, 0, 0, -3456, 0, 0, -1728, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -864, 0, 0, -2592, 0, 0, -2592, 0, 0, -864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1152, 0, 0, -1728, 0, 0, -1152, 0, 0],
    ![0, 0, -1152, 0, 0, -2304, 0, 0, -1152, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -864, 0, 0, -2592, 0, 0, -2592, 0, 0, -864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2304, 0, 0, -3456, 0, 0, -2304, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2880, 0, 0, -2880, 0],
    ![0, 0, 0, -288, 0, 0, -864, 0, 0, -864, 0, 0, -288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1152, 0, 0, -1728, 0, 0, -1152, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2880, 0, 0, -2880, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5760]]

def Nm : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of NmF

def ZRF : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 33177600, 0, 0, -33177600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -13271040, 0, 0, 13271040, 0, 0, -6635520, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -89579520, 0, 0, 19906560, 0, 0, 9953280, 0, 0, 0, 0, 0, 0],
    ![0, -33177600, 0, 0, 33177600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 9953280, 0, 0, 13271040, 0, 0, -29859840, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 19906560, 0, 0, -3317760, 0, 0, 0, 0, 0, -9953280, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -66355200, 0, 0, 29859840, 0, 0, 6635520, 0, 0],
    ![0, 0, -6635520, 0, 0, -39813120, 0, 0, 66355200, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 9953280, 0, 0, 0, 0, 0, 3317760, 0, 0, -19906560, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 39813120, 0, 0, -13271040, 0, 0, -13271040, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -33177600, 0, 0, 33177600, 0],
    ![0, 0, 0, 0, 0, 0, -9953280, 0, 0, -19906560, 0, 0, 89579520, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 6635520, 0, 0, -9953280, 0, 0, 13271040, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33177600, 0, 0, -33177600, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZR : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZRF

def ZLF : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 33177600, 0, 0, -33177600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 66355200, 0, 0, -39813120, 0, 0, -6635520, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 89579520, 0, 0, -19906560, 0, 0, -9953280, 0, 0, 0, 0, 0, 0],
    ![0, -33177600, 0, 0, 33177600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -29859840, 0, 0, 13271040, 0, 0, 9953280, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -19906560, 0, 0, 3317760, 0, 0, 0, 0, 0, 9953280, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 13271040, 0, 0, -9953280, 0, 0, 6635520, 0, 0],
    ![0, 0, -6635520, 0, 0, 13271040, 0, 0, -13271040, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -9953280, 0, 0, 0, 0, 0, -3317760, 0, 0, 19906560, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -13271040, 0, 0, -13271040, 0, 0, 39813120, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -33177600, 0, 0, 33177600, 0],
    ![0, 0, 0, 0, 0, 0, 9953280, 0, 0, 19906560, 0, 0, -89579520, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 6635520, 0, 0, 29859840, 0, 0, -66355200, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33177600, 0, 0, -33177600, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZL : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZLF

def ZR2F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2201506283520000, 0, 0, -2201506283520000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 352241005363200, 0, 0, 264180754022400, 0, 0, -748512136396800, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 8519829317222400, 0, 0, -1849265278156800, 0, 0, -858587450572800, 0, 0, -396271131033600, 0, 0, 0],
    ![0, -2201506283520000, 0, 0, 2201506283520000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 198135565516800, 0, 0, 1497024272793600, 0, 0, -2443671974707200, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1849265278156800, 0, 0, 506346445209600, 0, 0, 396271131033600, 0, 0, -858587450572800, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5635856085811200, 0, 0, -2443671974707200, 0, 0, -748512136396800, 0, 0],
    ![0, 0, -748512136396800, 0, 0, -3258229299609600, 0, 0, 5635856085811200, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -858587450572800, 0, 0, 396271131033600, 0, 0, 506346445209600, 0, 0, -1849265278156800, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -3258229299609600, 0, 0, 1497024272793600, 0, 0, 264180754022400, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2201506283520000, 0, 0, -2201506283520000, 0],
    ![0, 0, 0, -396271131033600, 0, 0, -858587450572800, 0, 0, -1849265278156800, 0, 0, 8519829317222400, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -748512136396800, 0, 0, 198135565516800, 0, 0, 352241005363200, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2201506283520000, 0, 0, 2201506283520000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZR2 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZR2F

def ZR4F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 9693259832756085247180800000000, 0, 0, -9693259832756085247180800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 736687747289462478785740800000, 0, 0, 2927364469492337744648601600000, 0, 0, -5127734451527969095758643200000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 76901476883170402308508876800000, 0, 0, -16691793432005978795645337600000, 0, 0, -7749761236288490155121049600000, 0, 0, -3576812878286995456209715200000, 0, 0, 0],
    ![0, -9693259832756085247180800000000, 0, 0, 9693259832756085247180800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2195523352119253308486451200000, 0, 0, 10255468903055938191517286400000, 0, 0, -17578726706703160595762380800000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -16691793432005978795645337600000, 0, 0, 4570372011144494194045747200000, 0, 0, 3576812878286995456209715200000, 0, 0, -7749761236288490155121049600000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 40285187864934290287283404800000, 0, 0, -17578726706703160595762380800000, 0, 0, -5127734451527969095758643200000, 0, 0],
    ![0, 0, -5127734451527969095758643200000, 0, 0, -23438302275604214127683174400000, 0, 0, 40285187864934290287283404800000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -7749761236288490155121049600000, 0, 0, 3576812878286995456209715200000, 0, 0, 4570372011144494194045747200000, 0, 0, -16691793432005978795645337600000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -23438302275604214127683174400000, 0, 0, 10255468903055938191517286400000, 0, 0, 2927364469492337744648601600000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9693259832756085247180800000000, 0, 0, -9693259832756085247180800000000, 0],
    ![0, 0, 0, -3576812878286995456209715200000, 0, 0, -7749761236288490155121049600000, 0, 0, -16691793432005978795645337600000, 0, 0, 76901476883170402308508876800000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -5127734451527969095758643200000, 0, 0, 2195523352119253308486451200000, 0, 0, 736687747289462478785740800000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -9693259832756085247180800000000, 0, 0, 9693259832756085247180800000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZR4 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZR4F

def WR1F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -766927296157188096000000, 0, 0, 766927296157188096000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 613541836925750476800000, 0, 0, -409027891283833651200000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 766927296157188096000000, 0, 0, -766927296157188096000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -306770918462875238400000, 0, 0, 0, 0, 0, 306770918462875238400000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 613541836925750476800000, 0, 0, -306770918462875238400000, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 409027891283833651200000, 0, 0, -613541836925750476800000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -409027891283833651200000, 0, 0, 0, 0, 0, 409027891283833651200000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 766927296157188096000000, 0, 0, -766927296157188096000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 306770918462875238400000, 0, 0, -613541836925750476800000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -766927296157188096000000, 0, 0, 766927296157188096000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def WR1 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of WR1F

def WR2F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2566360797469441385296988366438400000000, 0, 0, 1350716209194442834366835982336000000000, 0, 0, 540286483677777133746734392934400000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1013037156895832125775126986752000000000, 0, 0, -1080572967355554267493468785868800000000, 0, 0, 607822294137499275465076192051200000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1755931071952775684676886777036800000000, 0, 0, -607822294137499275465076192051200000000, 0, 0, -540286483677777133746734392934400000000, 0, 0],
    ![0, 0, 540286483677777133746734392934400000000, 0, 0, 810429725516665700620101589401600000000, 0, 0, -1755931071952775684676886777036800000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -810429725516665700620101589401600000000, 0, 0, 1080572967355554267493468785868800000000, 0, 0, -1350716209194442834366835982336000000000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -540286483677777133746734392934400000000, 0, 0, -1013037156895832125775126986752000000000, 0, 0, 2566360797469441385296988366438400000000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def WR2 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of WR2F

def ZL2F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2201506283520000, 0, 0, -2201506283520000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 5635856085811200, 0, 0, -3258229299609600, 0, 0, -748512136396800, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 8519829317222400, 0, 0, -1849265278156800, 0, 0, -858587450572800, 0, 0, -396271131033600, 0, 0, 0],
    ![0, -2201506283520000, 0, 0, 2201506283520000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2443671974707200, 0, 0, 1497024272793600, 0, 0, 198135565516800, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1849265278156800, 0, 0, 506346445209600, 0, 0, 396271131033600, 0, 0, -858587450572800, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 352241005363200, 0, 0, 198135565516800, 0, 0, -748512136396800, 0, 0],
    ![0, 0, -748512136396800, 0, 0, 264180754022400, 0, 0, 352241005363200, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -858587450572800, 0, 0, 396271131033600, 0, 0, 506346445209600, 0, 0, -1849265278156800, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 264180754022400, 0, 0, 1497024272793600, 0, 0, -3258229299609600, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2201506283520000, 0, 0, -2201506283520000, 0],
    ![0, 0, 0, -396271131033600, 0, 0, -858587450572800, 0, 0, -1849265278156800, 0, 0, 8519829317222400, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -748512136396800, 0, 0, -2443671974707200, 0, 0, 5635856085811200, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2201506283520000, 0, 0, 2201506283520000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZL2 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZL2F

def ZL4F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 9693259832756085247180800000000, 0, 0, -9693259832756085247180800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 40285187864934290287283404800000, 0, 0, -23438302275604214127683174400000, 0, 0, -5127734451527969095758643200000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 76901476883170402308508876800000, 0, 0, -16691793432005978795645337600000, 0, 0, -7749761236288490155121049600000, 0, 0, -3576812878286995456209715200000, 0, 0, 0],
    ![0, -9693259832756085247180800000000, 0, 0, 9693259832756085247180800000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -17578726706703160595762380800000, 0, 0, 10255468903055938191517286400000, 0, 0, 2195523352119253308486451200000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -16691793432005978795645337600000, 0, 0, 4570372011144494194045747200000, 0, 0, 3576812878286995456209715200000, 0, 0, -7749761236288490155121049600000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 736687747289462478785740800000, 0, 0, 2195523352119253308486451200000, 0, 0, -5127734451527969095758643200000, 0, 0],
    ![0, 0, -5127734451527969095758643200000, 0, 0, 2927364469492337744648601600000, 0, 0, 736687747289462478785740800000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -7749761236288490155121049600000, 0, 0, 3576812878286995456209715200000, 0, 0, 4570372011144494194045747200000, 0, 0, -16691793432005978795645337600000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2927364469492337744648601600000, 0, 0, 10255468903055938191517286400000, 0, 0, -23438302275604214127683174400000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9693259832756085247180800000000, 0, 0, -9693259832756085247180800000000, 0],
    ![0, 0, 0, -3576812878286995456209715200000, 0, 0, -7749761236288490155121049600000, 0, 0, -16691793432005978795645337600000, 0, 0, 76901476883170402308508876800000, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -5127734451527969095758643200000, 0, 0, -17578726706703160595762380800000, 0, 0, 40285187864934290287283404800000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -9693259832756085247180800000000, 0, 0, 9693259832756085247180800000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def ZL4 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of ZL4F

def WL1F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -766927296157188096000000, 0, 0, 766927296157188096000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -613541836925750476800000, 0, 0, 409027891283833651200000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 766927296157188096000000, 0, 0, -766927296157188096000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 306770918462875238400000, 0, 0, 0, 0, 0, -306770918462875238400000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -613541836925750476800000, 0, 0, 306770918462875238400000, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -409027891283833651200000, 0, 0, 613541836925750476800000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 409027891283833651200000, 0, 0, 0, 0, 0, -409027891283833651200000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 766927296157188096000000, 0, 0, -766927296157188096000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -306770918462875238400000, 0, 0, 613541836925750476800000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -766927296157188096000000, 0, 0, 766927296157188096000000, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def WL1 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of WL1F

def WL2F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1755931071952775684676886777036800000000, 0, 0, 810429725516665700620101589401600000000, 0, 0, 540286483677777133746734392934400000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 607822294137499275465076192051200000000, 0, 0, -1080572967355554267493468785868800000000, 0, 0, 1013037156895832125775126986752000000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2566360797469441385296988366438400000000, 0, 0, -1013037156895832125775126986752000000000, 0, 0, -540286483677777133746734392934400000000, 0, 0],
    ![0, 0, 540286483677777133746734392934400000000, 0, 0, 1350716209194442834366835982336000000000, 0, 0, -2566360797469441385296988366438400000000, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1350716209194442834366835982336000000000, 0, 0, 1080572967355554267493468785868800000000, 0, 0, -810429725516665700620101589401600000000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -540286483677777133746734392934400000000, 0, 0, -607822294137499275465076192051200000000, 0, 0, 1755931071952775684676886777036800000000, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def WL2 : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of WL2F

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem M2_chk : ∀ i j : Fin 16, (List.ofFn fun k => MzF i k * MzF k j).sum = M2F i j := by decide +kernel

theorem M2_eq : Mz * Mz = M2 := by ext i j; rw [mul16]; exact M2_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem M3_chk : ∀ i j : Fin 16, (List.ofFn fun k => M2F i k * MzF k j).sum = M3F i j := by decide +kernel

theorem M3_eq : M2 * Mz = M3 := by ext i j; rw [mul16]; exact M3_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem N_chk : ∀ i j : Fin 16, NmF i j = M3F i j - 56 * M2F i j + 1008 * MzF i j - 5760 * (if i = j then 1 else 0) := by
  decide +kernel

theorem N_eq : Nm = M3 - (56:ℤ) • M2 + (1008:ℤ) • Mz - (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  exact N_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem MN_chk : ∀ i j : Fin 16, (List.ofFn fun k => MzF i k * NmF k j).sum = 0 := by decide +kernel

theorem MN_zero : Mz * Nm = 0 := by ext i j; rw [mul16]; exact MN_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem traces_chk : (List.ofFn fun k => MzF k k).sum = 144 ∧ (List.ofFn fun k => M2F k k).sum = 2496 ∧
    (List.ofFn fun k => M3F k k).sum = 46464 ∧ (List.ofFn fun k => NmF k k).sum = -40320 := by decide +kernel

theorem traces : Mz.trace = 144 ∧ M2.trace = 2496 ∧ M3.trace = 46464 ∧ Nm.trace = -40320 := by
  rw [tr16, tr16, tr16, tr16]; exact traces_chk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- 4J²_tot = 48·I − 2·(4Q): J² = 12 − 2Q, so Q = 6, 5, 3, 0 ↔ J(J+1) = 0, 2, 6, 12 (J = 0, 1, 2, 3). -/
theorem total_chk : ∀ i j : Fin 16, (List.ofFn fun k => HtF i k * HtF k j).sum +
    2 * ((List.ofFn fun k => JptF i k * JmtF k j).sum + (List.ofFn fun k => JmtF i k * JptF k j).sum) =
    48 * (if i = j then 1 else 0) - 2 * MzF i j := by decide +kernel

theorem total_spin : Htot * Htot + (2:ℤ) • (Jpt * Jmt + Jmt * Jpt) =
    (48:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - (2:ℤ) • Mz := by
  have e1 : Htot = Matrix.of HtF := by ext i j; simp [Htot, HtF, kr, krF, Hs, IdF, Matrix.one_apply]
  have e2 : Jpt = Matrix.of JptF := by ext i j; simp [Jpt, JptF, kr, krF, Jp, IdF, Matrix.one_apply]
  have e3 : Jmt = Matrix.of JmtF := by ext i j; simp [Jmt, JmtF, kr, krF, Jm, IdF, Matrix.one_apply]
  rw [e1, e2, e3]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul16, Matrix.one_apply]
  exact total_chk i j

theorem num16 (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Matrix (Fin 16) (Fin 16) ℤ) = ((OfNat.ofNat n : ℤ)) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  rw [zsmul_eq_mul, mul_one]; norm_cast

/-- C14-38: the minimal polynomial M(M − 12)(M − 20)(M − 24) = 0 (eigenvalues 4·{0, 3, 5, 6}). -/
theorem minpoly_M : Mz * (Mz - 12) * (Mz - 20) * (Mz - 24) = 0 := by
  have e : (Mz - 12) * (Mz - 20) * (Mz - 24) = Nm := by
    rw [N_eq, num16 12, num16 20, num16 24, ← M3_eq, ← M2_eq]; noncomm_ring
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Mz - 12), e, MN_zero]

/-- Lagrange numerators: L₀ = −(M−12)(M−20)(M−24) (J = 3), L₁₂ = M(M−20)(M−24) (J = 2),
L₂₀ = −M(M−12)(M−24) (J = 1), L₂₄ = M(M−12)(M−20) (J = 0); P_λ = L_λ/d_λ with d = 5760, 1152, 640, 1152. -/
def L0 : Matrix (Fin 16) (Fin 16) ℤ := -((Mz - 12) * (Mz - 20) * (Mz - 24))
def L12 : Matrix (Fin 16) (Fin 16) ℤ := Mz * (Mz - 20) * (Mz - 24)
def L20 : Matrix (Fin 16) (Fin 16) ℤ := -(Mz * (Mz - 12) * (Mz - 24))
def L24 : Matrix (Fin 16) (Fin 16) ℤ := Mz * (Mz - 12) * (Mz - 20)

/-- C14-38: Σ_λ (5760/d_λ) L_λ = 5760·I and Σ_λ λ(5760/d_λ) L_λ = 5760·M (resolution of the identity and
spectral form 4Q = 0·P₃ + 12P₂ + 20P₁ + 24P₀, i.e. Q = 3P₂ + 5P₁ + 6P₀ on the retained part). -/
theorem resolution :
    L0 + (5:ℤ) • L12 + (9:ℤ) • L20 + (5:ℤ) • L24 = (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) ∧
      (60:ℤ) • L12 + (180:ℤ) • L20 + (120:ℤ) • L24 = (5760:ℤ) • Mz := by
  simp only [L0, L12, L20, L24, num16 12, num16 20, num16 24]
  constructor <;> noncomm_ring

/-- C14-38: M·L_λ = λ·L_λ for each λ. -/
theorem eigen_relations :
    Mz * L0 = 0 ∧ Mz * L12 = (12:ℤ) • L12 ∧ Mz * L20 = (20:ℤ) • L20 ∧ Mz * L24 = (24:ℤ) • L24 := by
  have h := minpoly_M
  simp only [L0, L12, L20, L24, num16 12, num16 20, num16 24] at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show Mz * -((Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1)) =
      -(Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1)) by noncomm_ring, h, neg_zero]
  · rw [← sub_eq_zero, show Mz * (Mz * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1)) -
      (12:ℤ) • (Mz * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1)) =
      Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1) by noncomm_ring, h]
  · rw [← sub_eq_zero, show Mz * -(Mz * (Mz - (12:ℤ) • 1) * (Mz - (24:ℤ) • 1)) -
      (20:ℤ) • -(Mz * (Mz - (12:ℤ) • 1) * (Mz - (24:ℤ) • 1)) =
      -(Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1)) by noncomm_ring, h, neg_zero]
  · rw [← sub_eq_zero, show Mz * (Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1)) -
      (24:ℤ) • (Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1)) =
      Mz * (Mz - (12:ℤ) • 1) * (Mz - (20:ℤ) • 1) * (Mz - (24:ℤ) • 1) by noncomm_ring, h]

/-- C14-38: multiplicities: Tr P₃ = 7, Tr P₂ = 5, Tr P₁ = 3, Tr P₀ = 1 (Tr L_λ = mult·d_λ). -/
theorem multiplicities :
    L0.trace = 7 * 5760 ∧ L12.trace = 5 * 1152 ∧ L20.trace = 3 * 640 ∧ L24.trace = 1 * 1152 := by
  obtain ⟨t1, t2, t3, _⟩ := traces
  have e0 : L0 = -(M3 - (56:ℤ) • M2 + (1008:ℤ) • Mz - (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) := by
    simp only [L0, num16 12, num16 20, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  have e12 : L12 = M3 - (44:ℤ) • M2 + (480:ℤ) • Mz := by
    simp only [L12, num16 20, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  have e20 : L20 = -(M3 - (36:ℤ) • M2 + (288:ℤ) • Mz) := by
    simp only [L20, num16 12, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  have e24 : L24 = M3 - (32:ℤ) • M2 + (240:ℤ) • Mz := by
    simp only [L24, num16 12, num16 20]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  simp only [e0, e12, e20, e24, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, t1, t2, t3, smul_eq_mul, Fintype.card_fin]
  norm_num

/-! ### C14-48: the projected bridge factors A_R = P_Q(I⊗H)P_Q, A_L = P_Q(H⊗I)P_Q -/

/-- Y = 5760·P_Q = 5760·I + N (P_Q = I − P₃ = I + N/5760). -/
def Y : Matrix (Fin 16) (Fin 16) ℤ := (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) + Nm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def YF : Fin 16 → Fin 16 → ℤ := fun i j => 5760 * (if i = j then 1 else 0) + NmF i j

theorem Y_of : Y = Matrix.of YF := by
  ext i j
  simp only [Y, YF, Nm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

theorem Y_chk : ∀ i j : Fin 16, (List.ofFn fun k => YF i k * YF k j).sum = 5760 * YF i j := by decide +kernel

theorem Y_idem : Y * Y = (5760:ℤ) • Y := by
  rw [Y_of]; ext i j; rw [mul16]; simp only [Matrix.smul_apply, smul_eq_mul]; exact Y_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Y_trace : Y.trace = 9 * 5760 := by
  rw [Y_of, tr16]; show (List.ofFn fun k => YF k k).sum = 9 * 5760; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ZR_chk : ∀ i j : Fin 16,
    (List.ofFn fun k => (List.ofFn fun l => YF i l * krF IdF HsF l k).sum * YF k j).sum = ZRF i j := by decide +kernel

theorem kr_of (A B : Fin 4 → Fin 4 → ℤ) : kr (Matrix.of A) (Matrix.of B) = Matrix.of (krF A B) := rfl

theorem one4 : (1 : Matrix (Fin 4) (Fin 4) ℤ) = Matrix.of IdF := by ext i j; simp [IdF, Matrix.one_apply]

theorem ZR_eq : Y * kr 1 Hs * Y = ZR := by
  rw [Y_of, one4, Hs, kr_of]; ext i j; rw [mul16]; simp only [mul16]; exact ZR_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ZL_chk : ∀ i j : Fin 16,
    (List.ofFn fun k => (List.ofFn fun l => YF i l * krF HsF IdF l k).sum * YF k j).sum = ZLF i j := by decide +kernel

theorem ZL_eq : Y * kr Hs 1 * Y = ZL := by
  rw [Y_of, one4, Hs, kr_of]; ext i j; rw [mul16]; simp only [mul16]; exact ZL_chk i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Z_chk : (List.ofFn fun k => ZRF k k).sum = 0 ∧ (List.ofFn fun k => ZLF k k).sum = 0 ∧
    (List.ofFn fun k => (List.ofFn fun l => ZRF k l * ZRF l k).sum).sum = 38 * 5760 ^ 4 ∧
    (List.ofFn fun k => (List.ofFn fun l => ZLF k l * ZLF l k).sum).sum = 38 * 5760 ^ 4 := by decide +kernel

theorem Z_traces : ZR.trace = 0 ∧ ZL.trace = 0 ∧ (ZR * ZR).trace = 38 * 5760 ^ 4 ∧
    (ZL * ZL).trace = 38 * 5760 ^ 4 := by
  rw [tr16, tr16, tr16, tr16]; simp only [mul16]; exact Z_chk

/-- C14-48: P_Q is a rank-9 projector (P_Q² = P_Q, Tr P_Q = 9), and A_R = P_Q(I⊗H)P_Q,
A_L = P_Q(H⊗I)P_Q have Tr A = 0 and Tr A² = 38 (rational form). -/
theorem bridge_traces :
    let PQ : Matrix (Fin 16) (Fin 16) ℚ := (1/5760 : ℚ) • Y.map (Int.castRingHom ℚ)
    let AR := PQ * (kr 1 Hs).map (Int.castRingHom ℚ) * PQ
    let AL := PQ * (kr Hs 1).map (Int.castRingHom ℚ) * PQ
    PQ * PQ = PQ ∧ PQ.trace = 9 ∧ AR.trace = 0 ∧ AL.trace = 0 ∧ (AR * AR).trace = 38 ∧ (AL * AL).trace = 38 := by
  intro PQ AR AL
  have hmap : ∀ A B : Matrix (Fin 16) (Fin 16) ℤ,
      (A * B).map (Int.castRingHom ℚ) = A.map (Int.castRingHom ℚ) * B.map (Int.castRingHom ℚ) :=
    fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)
  have htr : ∀ A : Matrix (Fin 16) (Fin 16) ℤ, (A.map (Int.castRingHom ℚ)).trace = (A.trace : ℚ) := by
    intro A; simp [Matrix.trace, Matrix.diag]
  have eR : AR = (1/5760 : ℚ) ^ 2 • ZR.map (Int.castRingHom ℚ) := by
    simp only [AR, PQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hmap, ZR_eq]; ring_nf
  have eL : AL = (1/5760 : ℚ) ^ 2 • ZL.map (Int.castRingHom ℚ) := by
    simp only [AL, PQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hmap, ZL_eq]; ring_nf
  obtain ⟨z1, z2, z3, z4⟩ := Z_traces
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h5 : ((5760:ℤ) • Y).map (Int.castRingHom ℚ) = (5760:ℚ) • Y.map (Int.castRingHom ℚ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, eq_intCast]; push_cast; ring
    simp only [PQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hmap, Y_idem, h5]
    norm_num
  · simp only [PQ, Matrix.trace_smul, htr, Y_trace]; norm_num
  · rw [eR, Matrix.trace_smul, htr, z1]; simp
  · rw [eL, Matrix.trace_smul, htr, z2]; simp
  · rw [eR, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hmap, Matrix.trace_smul, htr, z3]; norm_num
  · rw [eL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hmap, Matrix.trace_smul, htr, z4]; norm_num

/-! ### C14-49 (partial): an annihilating polynomial for A_R and A_L -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ZR_chk2 : (∀ i j : Fin 16, (List.ofFn fun k => ZRF i k * ZRF k j).sum = ZR2F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => ZR2F i k * ZR2F k j).sum = ZR4F i j) := by decide +kernel

theorem ZR_pows : ZR * ZR = ZR2 ∧ ZR2 * ZR2 = ZR4 := by
  constructor
  · ext i j; rw [mul16]; exact ZR_chk2.1 i j
  · ext i j; rw [mul16]; exact ZR_chk2.2 i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ZL_chk2 : (∀ i j : Fin 16, (List.ofFn fun k => ZLF i k * ZLF k j).sum = ZL2F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => ZL2F i k * ZL2F k j).sum = ZL4F i j) := by decide +kernel

theorem ZL_pows : ZL * ZL = ZL2 ∧ ZL2 * ZL2 = ZL4 := by
  constructor
  · ext i j; rw [mul16]; exact ZL_chk2.1 i j
  · ext i j; rw [mul16]; exact ZL_chk2.2 i j

def sq5760 : ℤ := 5760 ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem WR_chk : (∀ i j : Fin 16, (List.ofFn fun k => ZRF i k * (5 * ZR2F k j - 41 * sq5760 ^ 2 * (if k = j then 1 else 0))).sum = WR1F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => WR1F i k * (ZR2F k j - 4 * sq5760 ^ 2 * (if k = j then 1 else 0))).sum = WR2F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => WR2F i k * (25 * ZR4F k j - 170 * sq5760 ^ 2 * ZR2F k j + 49 * sq5760 ^ 4 * (if k = j then 1 else 0))).sum = 0) := by
  decide +kernel

theorem WR_chain : ZR * ((5:ℤ) • ZR2 - (41 * sq5760 ^ 2 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = WR1 ∧
    WR1 * (ZR2 - (4 * sq5760 ^ 2 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = WR2 ∧
    WR2 * ((25:ℤ) • ZR4 - (170 * sq5760 ^ 2 : ℤ) • ZR2 + (49 * sq5760 ^ 4 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = 0 := by
  obtain ⟨c1, c2, c3⟩ := WR_chk
  refine ⟨?_, ?_, ?_⟩
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]; exact c1 i j
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]; exact c2 i j
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.zero_apply]; exact c3 i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem WL_chk : (∀ i j : Fin 16, (List.ofFn fun k => ZLF i k * (5 * ZL2F k j - 41 * sq5760 ^ 2 * (if k = j then 1 else 0))).sum = WL1F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => WL1F i k * (ZL2F k j - 4 * sq5760 ^ 2 * (if k = j then 1 else 0))).sum = WL2F i j) ∧
    (∀ i j : Fin 16, (List.ofFn fun k => WL2F i k * (25 * ZL4F k j - 170 * sq5760 ^ 2 * ZL2F k j + 49 * sq5760 ^ 4 * (if k = j then 1 else 0))).sum = 0) := by
  decide +kernel

theorem WL_chain : ZL * ((5:ℤ) • ZL2 - (41 * sq5760 ^ 2 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = WL1 ∧
    WL1 * (ZL2 - (4 * sq5760 ^ 2 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = WL2 ∧
    WL2 * ((25:ℤ) • ZL4 - (170 * sq5760 ^ 2 : ℤ) • ZL2 + (49 * sq5760 ^ 4 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) = 0 := by
  obtain ⟨c1, c2, c3⟩ := WL_chk
  refine ⟨?_, ?_, ?_⟩
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]; exact c1 i j
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]; exact c2 i j
  · ext i j; rw [mul16]; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.zero_apply]; exact c3 i j

/-- C14-49 (spectral bound): every eigenvalue μ of A = Z/5760² satisfies
μ(5μ² − 41)(μ² − 4)(25μ⁴ − 170μ² + 49) = 0, hence μ² ≤ 41/5 (‖A‖ ≤ √(41/5), so ‖A_R ⊗ A_L‖ ≤ 41/5). -/
theorem eigen_root_bound (μ : ℝ) (h : μ * (5 * μ ^ 2 - 41) * (μ ^ 2 - 4) * (25 * μ ^ 4 - 170 * μ ^ 2 + 49) = 0) :
    μ ^ 2 ≤ 41 / 5 := by
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rw [h]; norm_num
      · linarith
    · nlinarith
  · nlinarith [sq_nonneg (μ ^ 2 - 17/5)]

/-- C14-48: if A, B are traceless and nonzero then A ⊗ B is not of the form X ⊗ I + I ⊗ Y + cI with
X, Y traceless (it is not a sum of local terms). -/
theorem not_local {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n] [Nonempty m]
    (A X : Matrix n n ℚ) (B Y : Matrix m m ℚ) (c : ℚ) (hB : B.trace = 0) (hA : A.trace = 0)
    (hX : X.trace = 0) (hY : Y.trace = 0) (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    A ⊗ₖ B ≠ X ⊗ₖ (1 : Matrix m m ℚ) + (1 : Matrix n n ℚ) ⊗ₖ Y + c • 1 := by
  intro h
  have entry : ∀ i j k l, A i j * B k l = X i j * (if k = l then 1 else 0) +
      (if i = j then 1 else 0) * Y k l + (if i = j then 1 else 0) * ((if k = l then 1 else 0) * c) := by
    intro i j k l
    have := congrFun (congrFun h (i, k)) (j, l)
    simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul] at this
    rw [this]; split_ifs <;> simp_all
  have cm : (0:ℚ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have cn : (0:ℚ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hBt : ∑ k, B k k = 0 := hB
  have hAt : ∑ i, A i i = 0 := hA
  have hXt : ∑ i, X i i = 0 := hX
  have hYt : ∑ k, Y k k = 0 := hY
  have p2 : ∀ i j, X i j * Fintype.card m + (if i = j then 1 else 0) * (Fintype.card m * c) = 0 := by
    intro i j
    have := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => entry i j k k)
    simp only [ite_true, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, hBt, mul_zero, hYt,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    linarith
  have hXc : ∀ i j, X i j = -(if i = j then c else 0) := by
    intro i j
    have h2 := p2 i j
    by_cases hij : i = j
    · simp only [hij, ite_true, one_mul] at h2 ⊢
      have : (X j j + c) * Fintype.card m = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · simp only [hij, ite_false, zero_mul, add_zero, neg_zero] at h2 ⊢
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · linarith
  have hc : c = 0 := by
    have : ∑ i, X i i = -(Fintype.card n * c) := by
      simp only [hXc, ite_true, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hXt] at this
    have : (Fintype.card n : ℚ) * c = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hX0 : ∀ i j, X i j = 0 := fun i j => by rw [hXc, hc]; simp
  have hY0 : ∀ k l, Y k l = 0 := by
    intro k l
    have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => entry i i k l)
    simp only [ite_true, one_mul, hX0, zero_mul, zero_add, ← Finset.sum_mul, hAt, hc, mul_zero,
      add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, zero_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · linarith
    · exact h
  apply hA0
  ext i j
  by_contra hij
  apply hB0
  ext k l
  have := entry i j k l
  rw [hX0, hY0, hc] at this
  simp only [zero_mul, mul_zero, add_zero] at this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hij
  · simpa using h

end Entropic.AppP.Spin
