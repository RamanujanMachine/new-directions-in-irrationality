/-
# The dual endpoint: the rational function `F_n` and its residue rows (END01, END03)

`F_n(s) = (s+1)_{10n+1} (s+1-n)_{9n+1} / [(2n-s)_{10n+2} (1/3-s)_{6n+2} (2n+1/2-s)_{3n+2}]`.

Its poles are simple: the integer poles `2n + j` (`j < 10n+2`), the third poles `1/3 + j`
(`j < 6n+2`) and the half poles `2n + 1/2 + j` (`j < 3n+2`).  For a pole `ρ` put
`v_ρ = -Res_{s=ρ} F_n(s)`; the rows (columns `k = 0,1,2`) are

* `B_T,k = ∑_{third} v_ρ ρ^k`, `B_H,k = ∑_{half} v_ρ ρ^k`, `B_I,k = ∑_{integer} v_ρ ρ^k`,
* `B_0,k = -∑_ρ v_ρ h(ρ) ρ^k` with the harmonic weights `h`.

All objects are defined over an arbitrary field `K` of characteristic zero so that they can be
used both over `ℚ` (arithmetic) and over `ℝ` (analysis).
-/
import Zeta2L2Chi3.Matrices

open Finset

namespace Zeta2L2Chi3

variable {K : Type*} [Field K]

/-- Rising factorial `(x)_m = x (x+1) ⋯ (x+m-1)`. -/
def rf {R : Type*} [CommRing R] (x : R) (m : ℕ) : R := ∏ i ∈ range m, (x + i)

/-- Numerator of `F_n`. -/
def FNum (n : ℕ) (s : K) : K := rf (s + 1) (10 * n + 1) * rf (s + 1 - n) (9 * n + 1)

/-- Denominator of `F_n`. -/
def FDen (n : ℕ) (s : K) : K :=
  rf (2 * n - s) (10 * n + 2) * rf (1 / 3 - s) (6 * n + 2) * rf (2 * n + 1 / 2 - s) (3 * n + 2)

/-- The dual endpoint rational function `F_n(s)`. -/
def F (n : ℕ) (s : K) : K := FNum n s / FDen n s

/-! ### Poles and residues -/

/-- third poles `1/3 + j` -/
def tP (j : ℕ) : K := 1 / 3 + j
/-- half poles `2n + 1/2 + j` -/
def hP (n j : ℕ) : K := 2 * n + 1 / 2 + j
/-- integer poles `2n + j` -/
def iP (n j : ℕ) : K := 2 * n + j

/-- `Res_{s = 1/3 + j} F_n(s)`. -/
def resT (n j : ℕ) : K :=
  -FNum n ((tP (K := K) j)) / (rf (2 * n - (tP (K := K) j)) (10 * n + 2) *
    (∏ i ∈ (range (6 * n + 2)).erase j, (1 / 3 + i - (tP (K := K) j))) * rf (2 * n + 1 / 2 - (tP (K := K) j)) (3 * n + 2))

/-- `Res_{s = 2n + 1/2 + j} F_n(s)`. -/
def resH (n j : ℕ) : K :=
  -FNum n ((hP (K := K) n j)) / (rf (2 * n - (hP (K := K) n j)) (10 * n + 2) * rf (1 / 3 - (hP (K := K) n j)) (6 * n + 2) *
    ∏ i ∈ (range (3 * n + 2)).erase j, (2 * n + 1 / 2 + i - (hP (K := K) n j)))

/-- `Res_{s = 2n + j} F_n(s)`. -/
def resI (n j : ℕ) : K :=
  -FNum n ((iP (K := K) n j)) / ((∏ i ∈ (range (10 * n + 2)).erase j, (2 * n + i - (iP (K := K) n j))) *
    rf (1 / 3 - (iP (K := K) n j)) (6 * n + 2) * rf (2 * n + 1 / 2 - (iP (K := K) n j)) (3 * n + 2))

/-! ### Harmonic weights -/

/-- `h_{1/3}(j) = ∑_{l=0}^{j} (l + 1/3)^{-2}` -/
def hwT (j : ℕ) : K := ∑ l ∈ range (j + 1), 1 / ((l : K) + 1 / 3) ^ 2
/-- `h_{1/2}(2n+j) = ∑_{l=0}^{2n+j} (l + 1/2)^{-2}` -/
def hwH (n j : ℕ) : K := ∑ l ∈ range (2 * n + j + 1), 1 / ((l : K) + 1 / 2) ^ 2
/-- `h_0(2n+j) = ∑_{l=1}^{2n+j} l^{-2}` -/
def hwI (n j : ℕ) : K := ∑ l ∈ range (2 * n + j), 1 / ((l : K) + 1) ^ 2

/-! ### The residue rows -/

/-- `B_T,k = ∑_{third ρ} v_ρ ρ^k`, `v = -Res`. -/
def BT (n k : ℕ) : K := ∑ j ∈ range (6 * n + 2), -resT n j * (tP (K := K) j) ^ k
/-- `B_H,k` -/
def BH (n k : ℕ) : K := ∑ j ∈ range (3 * n + 2), -resH n j * (hP (K := K) n j) ^ k
/-- `B_I,k` -/
def BI (n k : ℕ) : K := ∑ j ∈ range (10 * n + 2), -resI n j * (iP (K := K) n j) ^ k
/-- `B_0,k = -∑ v_ρ h(ρ) ρ^k = ∑ Res_ρ · h(ρ) ρ^k`. -/
def B0 (n k : ℕ) : K :=
  (∑ j ∈ range (6 * n + 2), resT n j * hwT j * (tP (K := K) j) ^ k) +
  (∑ j ∈ range (3 * n + 2), resH n j * hwH n j * (hP (K := K) n j) ^ k) +
  (∑ j ∈ range (10 * n + 2), resI n j * hwI n j * (iP (K := K) n j) ^ k)

/-- The residue-defined endpoint matrix `B̂_n` (rows `B₀, B_T, B_H`; columns `0,1,2`). -/
def Bres (n : ℕ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of ![![B0 n 0, B0 n 1, B0 n 2], ![BT n 0, BT n 1, BT n 2], ![BH n 0, BH n 1, BH n 2]]

/-- The initial residue matrix is the stated `B̂₀`. -/
theorem Bres_zero_entries (i j : Fin 3) : (Bres 0 : Matrix (Fin 3) (Fin 3) ℚ) i j = Bhat0 i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem Bres_zero : (Bres 0 : Matrix (Fin 3) (Fin 3) ℚ) = Bhat0 := by
  ext i j; exact Bres_zero_entries i j

end Zeta2L2Chi3
