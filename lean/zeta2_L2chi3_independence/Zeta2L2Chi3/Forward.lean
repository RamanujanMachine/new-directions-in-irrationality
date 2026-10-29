/-
# The forward (5F4) presentation: definitions (FWD01)

`R_n(t) = (t+2n+1)_{10n+1} (t+4/3)_{6n+1} (t+2n+3/2)_{3n+1} / [(t-10n-1)_{10n+2} (t-8n-1)_{9n+2}]`
has double poles at `0, …, 8n+1` and simple poles at `-n, …, -1` and `8n+2, …, 10n+1`.
For `j ≤ 3`, `t^j R_n` is written in partial-fraction form `q_j + ∑_k (a_k/(t-k)^2 + b_k/(t-k))`
(`fdata`).  The forward functionals are

* `DP = ∑_k a_k` (sum of double-pole coefficients),
* `p_ρ^{(m)} = ∑_k [a_k H^{(2)}_ρ(k+m) - b_k H^{(1)}_ρ(k+m)] - ∑_j q_j (-1)^j ζ(-j, ρ+m)`,
  `ζ(-j,x) = -B_{j+1}(x)/(j+1)`, with the signed finite harmonic sums `H`,

and the forward rows are `φ¹ = DP`, `φᵀ = p_{1/3}^{(1)} - p_1^{(2n)}`, `φᴴ = p_{1/2}^{(2n+1)} - p_1^{(2n)}`
applied to `t^j R_n`.  The forward vector is `f_n = (φ¹, φᵀ, φᴴ) · K(n) e₀`.
-/
import Zeta2L2Chi3.PartialFrac2
import Zeta2L2Chi3.Dual

open Polynomial Finset

noncomputable section

namespace Zeta2L2Chi3

/-- numerator of `R_n` -/
def RNum (n : ℕ) (t : ℝ) : ℝ :=
  rf (t + 2 * n + 1) (10 * n + 1) * rf (t + 4 / 3) (6 * n + 1) * rf (t + 2 * n + 3 / 2) (3 * n + 1)

/-- denominator of `R_n` -/
def RDen (n : ℕ) (t : ℝ) : ℝ := rf (t - 10 * n - 1) (10 * n + 2) * rf (t - 8 * n - 1) (9 * n + 2)

/-- the forward kernel `R_n` -/
def Rk (n : ℕ) (t : ℝ) : ℝ := RNum n t / RDen n t

/-- the poles of `R_n` -/
def KF (n : ℕ) : Finset ℝ := (Finset.Icc (-(n : ℤ)) (10 * n + 1)).image (fun k : ℤ => (k : ℝ))

/-- pole orders -/
def eF (n : ℕ) (k : ℝ) : ℕ := if 0 ≤ k ∧ k ≤ 8 * n + 1 then 2 else 1

/-- numerator polynomial of `R_n` -/
def RNumPoly (n : ℕ) : ℝ[X] :=
  (∏ i ∈ range (10 * n + 1), (X + Polynomial.C (2 * (n : ℝ) + 1 + i))) *
  (∏ i ∈ range (6 * n + 1), (X + Polynomial.C (4 / 3 + (i : ℝ)))) *
  (∏ i ∈ range (3 * n + 1), (X + Polynomial.C (2 * (n : ℝ) + 3 / 2 + i)))

lemma fdata_exists (n j : ℕ) :
    ∃ (q : ℝ[X]) (a b : ℝ → ℝ), (∀ k ∈ KF n, eF n k ≤ 1 → a k = 0) ∧
      (∀ k ∈ KF n, eF n k = 0 → b k = 0) ∧
      ∀ t ∉ KF n, (X ^ j * RNumPoly n).eval t / ∏ k ∈ KF n, (t - k) ^ eF n k = pfEval (KF n) q a b t :=
  pf_exists (KF n) (eF n) (fun k _ => by unfold eF; split_ifs <;> omega) _

/-- partial-fraction data of `t^j R_n` -/
def fq (n j : ℕ) : ℝ[X] := Classical.choose (fdata_exists n j)
def fa (n j : ℕ) : ℝ → ℝ := Classical.choose (Classical.choose_spec (fdata_exists n j))
def fb (n j : ℕ) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (fdata_exists n j)))

lemma fdata_spec (n j : ℕ) (t : ℝ) (ht : t ∉ KF n) :
    (X ^ j * RNumPoly n).eval t / ∏ k ∈ KF n, (t - k) ^ eF n k = pfEval (KF n) (fq n j) (fa n j) (fb n j) t :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (fdata_exists n j)))).2.2 t ht

/-! ### The functionals -/

/-- signed finite harmonic sums `H^{(j)}_ρ(m)` -/
def Hsig (j : ℕ) (ρ : ℝ) (m : ℤ) : ℝ :=
  if 0 ≤ m then ∑ l ∈ range m.toNat, 1 / (ρ + l) ^ j
  else -∑ l ∈ range (-m).toNat, 1 / (ρ + m + l) ^ j

/-- `ζ(-j, x) = -B_{j+1}(x)/(j+1)` -/
def zetaNeg (j : ℕ) (x : ℝ) : ℝ := -((Polynomial.bernoulli (j + 1)).map (algebraMap ℚ ℝ)).eval x / (j + 1)

/-- the Bernoulli (polynomial-part) term `∑_j q_j (-1)^j ζ(-j, x)` -/
def Ubern (q : ℝ[X]) (x : ℝ) : ℝ :=
  ∑ j ∈ range (q.natDegree + 1), q.coeff j * (-1) ^ j * zetaNeg j x

/-- `p_ρ^{(m)}` on partial-fraction data with integer poles -/
def pfun (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (ρ : ℝ) (m : ℤ) : ℝ :=
  ∑ k ∈ K, (a k * Hsig 2 ρ (⌊k⌋ + m) - b k * Hsig 1 ρ (⌊k⌋ + m)) - Ubern q (ρ + m)

/-- the forward rows (functionals applied to `t^j R_n`, `j = 0,…,3`) -/
def phi1 (n j : ℕ) : ℝ := ∑ k ∈ KF n, fa n j k
def phiT (n j : ℕ) : ℝ :=
  pfun (KF n) (fq n j) (fa n j) (fb n j) (1 / 3) 1 - pfun (KF n) (fq n j) (fa n j) (fb n j) 1 (2 * n)
def phiH (n j : ℕ) : ℝ :=
  pfun (KF n) (fq n j) (fa n j) (fb n j) (1 / 2) (2 * n + 1) -
    pfun (KF n) (fq n j) (fa n j) (fb n j) 1 (2 * n)

/-- `K(n)` (forward/dual pairing matrix), real -/
def Kmat (n : ℕ) : Matrix (Fin 4) (Fin 3) ℝ :=
  fun i j => hornerR (Data.Knum i j) (n : ℝ) / Data.Kden i j

/-- the forward vector `f_n = (φ¹, φᵀ, φᴴ) · K(n) e₀` -/
def fvec (n : ℕ) : Fin 3 → ℝ :=
  ![∑ j : Fin 4, phi1 n j * Kmat n j 0, ∑ j : Fin 4, phiT n j * Kmat n j 0,
    ∑ j : Fin 4, phiH n j * Kmat n j 0]

end Zeta2L2Chi3
