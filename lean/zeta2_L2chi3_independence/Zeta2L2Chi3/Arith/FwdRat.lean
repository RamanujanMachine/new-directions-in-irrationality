/-
# The forward vector as an explicit rational number

`fvecE n` is `f_n` written with the explicit partial-fraction data (`aQ`, `bQ`, `qc`), the rational
signed harmonic sums `HsigQ`, the explicit values `zQ i x = ζ(-i, x)` (`i ≤ 2`) and `K(n) e₀`.
`fvec_eq_cast : fvec n i = fvecE n i`.
-/
import Zeta2L2Chi3.Arith.FwdPoly
import Zeta2L2Chi3.FInit

open Polynomial Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

/-- signed finite harmonic sums over `ℚ` -/
def HsigQ (j : ℕ) (ρ : ℚ) (m : ℤ) : ℚ :=
  if 0 ≤ m then ∑ l ∈ range m.toNat, 1 / (ρ + l) ^ j
  else -∑ l ∈ range (-m).toNat, 1 / (ρ + m + l) ^ j

/-- `ζ(-i, x) = -B_{i+1}(x)/(i+1)` for `i ≤ 2` -/
def zQ (i : ℕ) (x : ℚ) : ℚ :=
  match i with
  | 0 => 1 / 2 - x
  | 1 => -(x ^ 2 - x + 1 / 6) / 2
  | _ => -(x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x) / 3

/-- the Bernoulli term of `q_j` -/
def UQ (n j : ℕ) (x : ℚ) : ℚ := ∑ i ∈ range 3, qc n j i * (-1) ^ i * zQ i x

/-- `p_ρ^{(m)}` applied to `t^j R_n` -/
def pfunQ (n j : ℕ) (ρ : ℚ) (m : ℤ) : ℚ :=
  ∑ k ∈ KZ n, (aQ n j k * HsigQ 2 ρ (k + m) - bQ n j k * HsigQ 1 ρ (k + m)) - UQ n j (ρ + m)

def phi1Q (n j : ℕ) : ℚ := ∑ k ∈ KZ n, aQ n j k
def phiTQ (n j : ℕ) : ℚ := pfunQ n j (1 / 3) 1 - pfunQ n j 1 (2 * n)
def phiHQ (n j : ℕ) : ℚ := pfunQ n j (1 / 2) (2 * n + 1) - pfunQ n j 1 (2 * n)

/-- `K(n) e₀` -/
def KQ (n : ℕ) (j : Fin 4) : ℚ := hornerR (Data.Knum j 0) (n : ℚ) / Data.Kden j 0

/-- the explicit rational forward vector -/
def fvecE (n : ℕ) : Fin 3 → ℚ :=
  ![∑ j : Fin 4, phi1Q n j * KQ n j, ∑ j : Fin 4, phiTQ n j * KQ n j,
    ∑ j : Fin 4, phiHQ n j * KQ n j]

/-! ### Casts -/

lemma HsigQ_cast (j : ℕ) (ρ : ℚ) (m : ℤ) : ((HsigQ j ρ m : ℚ) : ℝ) = Hsig j (ρ : ℝ) m := by
  unfold HsigQ Hsig
  split_ifs <;> push_cast <;> rfl

lemma zQ_cast (i : ℕ) (hi : i < 3) (x : ℚ) : ((zQ i x : ℚ) : ℝ) = zetaNeg i (x : ℝ) := by
  interval_cases i
  · rw [zetaNeg_zero]; simp [zQ]
  · rw [zetaNeg_one]; simp [zQ]
  · rw [zetaNeg_two]; simp [zQ]

lemma qQ_natDegree (n j : ℕ) : ((qQ n j).map (algebraMap ℚ ℝ)).natDegree < 3 := by
  refine lt_of_le_of_lt (natDegree_map_le) ?_
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2) fun i hi => ?_) (by norm_num)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := mem_range.1 hi; omega

lemma qQ_coeff (n j i : ℕ) (hi : i < 3) :
    ((qQ n j).map (algebraMap ℚ ℝ)).coeff i = ((qc n j i : ℚ) : ℝ) := by
  rw [coeff_map, qQ, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (mem_range.2 hi) h)]
  simp

lemma Ubern_eq (q : ℝ[X]) (hq : q.natDegree < 3) (x : ℝ) :
    Ubern q x = ∑ i ∈ range 3, q.coeff i * (-1) ^ i * zetaNeg i x := by
  unfold Ubern
  refine sum_subset (fun i hi => by simp only [mem_range] at hi ⊢; omega) fun i _ hi => ?_
  rw [coeff_eq_zero_of_natDegree_lt (by simp only [mem_range] at hi; omega)]
  ring

lemma Ubern_fq (n j : ℕ) (hj : j ≤ 3) (x : ℚ) : Ubern (fq n j) (x : ℝ) = ((UQ n j x : ℚ) : ℝ) := by
  rw [fq_eq n j hj, Ubern_eq _ (qQ_natDegree n j), UQ]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  rw [qQ_coeff n j i (mem_range.1 hi), zQ_cast i (mem_range.1 hi)]

lemma pfun_cast (n j : ℕ) (hj : j ≤ 3) (ρ : ℚ) (m : ℤ) :
    pfun (KF n) (fq n j) (fa n j) (fb n j) (ρ : ℝ) m = ((pfunQ n j ρ m : ℚ) : ℝ) := by
  unfold pfun pfunQ
  rw [sum_KF, show (ρ : ℝ) + (m : ℝ) = ((ρ + m : ℚ) : ℝ) by push_cast; ring, Ubern_fq n j hj]
  push_cast
  congr 1
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨ha, hb⟩ := fa_fb_eq n j k hk
  rw [Int.floor_intCast, ha, hb, HsigQ_cast, HsigQ_cast]

lemma phi1_cast (n j : ℕ) : phi1 n j = ((phi1Q n j : ℚ) : ℝ) := by
  unfold phi1 phi1Q
  rw [sum_KF]
  push_cast
  exact sum_congr rfl fun k hk => (fa_fb_eq n j k hk).1

lemma phiT_cast (n j : ℕ) (hj : j ≤ 3) : phiT n j = ((phiTQ n j : ℚ) : ℝ) := by
  unfold phiT phiTQ
  rw [show (1 / 3 : ℝ) = ((1 / 3 : ℚ) : ℝ) by push_cast; ring, show (1 : ℝ) = ((1 : ℚ) : ℝ) by simp,
    pfun_cast n j hj, pfun_cast n j hj]
  push_cast; ring

lemma phiH_cast (n j : ℕ) (hj : j ≤ 3) : phiH n j = ((phiHQ n j : ℚ) : ℝ) := by
  unfold phiH phiHQ
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by push_cast; ring, show (1 : ℝ) = ((1 : ℚ) : ℝ) by simp,
    pfun_cast n j hj, pfun_cast n j hj]
  push_cast; ring

lemma Kmat_cast (n : ℕ) (j : Fin 4) : Kmat n j 0 = ((KQ n j : ℚ) : ℝ) := by
  unfold Kmat KQ
  have h := hornerR_map (Rat.castHom ℝ) (Data.Knum j 0) (n : ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at h
  push_cast
  rw [h]

theorem fvec_eq_cast (n : ℕ) (i : Fin 3) : fvec n i = ((fvecE n i : ℚ) : ℝ) := by
  have hj : ∀ j : Fin 4, (j : ℕ) ≤ 3 := fun j => by omega
  fin_cases i <;>
    simp [fvec, fvecE, phi1_cast, phiT_cast _ _ (hj _), phiH_cast _ _ (hj _), Kmat_cast]

end Zeta2L2Chi3.Arith
