/-
# The forward cofactor `q^f_n = fvecQ n 0` as a positive-weight sum

`fvecQ n 0 = Σ_{k=0}^{8n+1} w(n,k) P_n(k)` with `w(n,k) = N(k)/D_k(k)`,
`D_k(k) = k! (10n+1-k)! (k+n)! (8n+1-k)!` and the explicit cubic `P_n` (from `K(n) e₀`).
Elementary Stirling bounds give `|log w(n,k) - n φ(k/n)| ≤ 30 (log (20n+3) + 1)` for `k ≤ 7n`.
-/
import Zeta2L2Chi3.Arith.FwdVal
import Zeta2L2Chi3.Target2.PhiNum

namespace Zeta2L2Chi3.Arith

open Real Finset Filter

/-! ### The representation -/

/-- `P_n(t) = Σ_j t^j K(n)_{j0}` -/
def Pcub (n : ℕ) (t : ℚ) : ℚ := ∑ j : Fin 4, t ^ (j : ℕ) * KQ n j

lemma Pcub_eq (n : ℕ) (t : ℚ) : Pcub n t =
    (19440 * n ^ 4 + 13812 * n ^ 3 + 3219 * n ^ 2 + 308 * n + 11) / 3 -
      (4320 * n ^ 3 + 4410 * n ^ 2 + 1045 * n + 69) * t / 6 - (1080 * n ^ 2 + 315 * n + 7) * t ^ 2 / 6 +
      3 * t ^ 3 := by
  simp [Pcub, Fin.sum_univ_four, KQ, hornerR, Data.Knum, Data.Kden]
  ring

/-- the double-pole weight `N(k)/D_k(k)` -/
def wQ (n k : ℕ) : ℚ := NF n (((k : ℤ) : ℚ)) / DF n (k : ℤ) (((k : ℤ) : ℚ))

lemma image_range_sub_KZ (n : ℕ) : (range (8 * n + 2)).image (fun m : ℕ => (m : ℤ)) ⊆ KZ n := by
  intro x hx
  simp only [mem_image, mem_range] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  rw [mem_KZ]; omega

theorem fvecQ_zero_eq (n : ℕ) : fvecQ n 0 = ∑ k ∈ range (8 * n + 2), wQ n k * Pcub n k := by
  show fvecE n 0 = _
  simp only [fvecE, Matrix.cons_val_zero, phi1Q, sum_mul]
  rw [sum_comm]
  have hterm : ∀ k ∈ KZ n, ∑ j : Fin 4, aQ n j k * KQ n j =
      if eZ n k = 2 then NF n (k : ℚ) / DF n k (k : ℚ) * Pcub n k else 0 := by
    intro k _
    unfold aQ gQ Pcub
    split_ifs
    · rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    · simp
  rw [sum_congr rfl hterm]
  rw [← sum_subset (image_range_sub_KZ n)]
  · rw [sum_image (fun a _ b _ h => by exact_mod_cast h)]
    refine sum_congr rfl fun m hm => ?_
    have := mem_range.1 hm
    rw [if_pos (by unfold eZ; split_ifs with h; rfl; exfalso; exact h ⟨by omega, by omega⟩)]
    simp [wQ]
  · intro k hk hk'
    rw [if_neg]
    unfold eZ
    split_ifs with h
    · exfalso; apply hk'
      simp only [mem_image, mem_range]
      exact ⟨k.toNat, by omega, by omega⟩
    · simp

/-! ### The closed form of `D_k(k)` -/

lemma prod_skip (K M : ℕ) (hK : K < M) :
    ∏ i ∈ range M, (if (i : ℤ) = (K : ℤ) then (1 : ℚ) else ((K : ℚ) - (i : ℚ))) =
      (-1) ^ (M - 1 - K) * (K.factorial : ℚ) * ((M - 1 - K).factorial : ℚ) := by
  rw [← prod_range_mul_prod_Ico _ (show K + 1 ≤ M by omega), prod_range_succ, if_pos rfl, mul_one]
  have h1 : ∏ i ∈ range K, (if (i : ℤ) = (K : ℤ) then (1 : ℚ) else ((K : ℚ) - (i : ℚ))) =
      (K.factorial : ℚ) := by
    rw [prod_congr rfl fun i hi => if_neg (by have := mem_range.1 hi; omega)]
    rw [← prod_range_reflect, ← prod_range_add_one_eq_factorial, Nat.cast_prod]
    refine prod_congr rfl fun i hi => ?_
    have := mem_range.1 hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have h2 : ∏ i ∈ Ico (K + 1) M, (if (i : ℤ) = (K : ℤ) then (1 : ℚ) else ((K : ℚ) - (i : ℚ))) =
      (-1) ^ (M - 1 - K) * ((M - 1 - K).factorial : ℚ) := by
    rw [prod_Ico_eq_prod_range, show M - (K + 1) = M - 1 - K by omega,
      ← prod_range_add_one_eq_factorial, Nat.cast_prod, ← card_range (M - 1 - K), ← prod_const,
      card_range, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [if_neg (by omega)]
    push_cast; ring
  rw [h1, h2]; ring

theorem DF_nat (n k : ℕ) (hk : k ≤ 8 * n + 1) :
    DF n (k : ℤ) (((k : ℤ) : ℚ)) = (k.factorial : ℚ) * ((10 * n + 1 - k).factorial : ℚ) *
      ((k + n).factorial : ℚ) * ((8 * n + 1 - k).factorial : ℚ) := by
  rw [DF_fam n k (by rw [mem_KZ]; omega)]
  have e0 : (∏ i ∈ range (famP0.len n), (if famP0.al * n + (i : ℤ) = (k : ℤ) then (1 : ℚ) else
      (((k : ℤ) : ℚ) - ((famP0.al * n + i : ℤ) : ℚ)))) =
      ∏ i ∈ range (10 * n + 2), (if (i : ℤ) = (k : ℤ) then (1 : ℚ) else ((k : ℚ) - (i : ℚ))) := by
    rw [show famP0.len n = 10 * n + 2 from rfl]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℤ) = k
    · rw [if_pos h, if_pos (by simp [famP0, h])]
    · rw [if_neg h, if_neg (by simpa [famP0] using h)]; simp [famP0]
  have e1 : (∏ i ∈ range (famP1.len n), (if famP1.al * n + (i : ℤ) = (k : ℤ) then (1 : ℚ) else
      (((k : ℤ) : ℚ) - ((famP1.al * n + i : ℤ) : ℚ)))) =
      ∏ i ∈ range (9 * n + 2),
        (if (i : ℤ) = ((k + n : ℕ) : ℤ) then (1 : ℚ) else (((k + n : ℕ) : ℚ) - (i : ℚ))) := by
    rw [show famP1.len n = 9 * n + 2 from rfl]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℤ) = ((k + n : ℕ) : ℤ)
    · rw [if_pos (by simp only [famP1]; push_cast at h ⊢; omega), if_pos h]
    · rw [if_neg (by simp only [famP1]; push_cast at h ⊢; omega), if_neg h]
      simp only [famP1]; push_cast; ring
  rw [e0, e1, prod_skip k (10 * n + 2) (by omega), prod_skip (k + n) (9 * n + 2) (by omega),
    show 10 * n + 2 - 1 - k = 10 * n + 1 - k by omega, show 9 * n + 2 - 1 - (k + n) = 8 * n + 1 - k by omega]
  have hs : ((-1 : ℚ) ^ (10 * n + 1 - k)) * (-1) ^ (8 * n + 1 - k) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨9 * n + 1 - k, by omega⟩
  linear_combination ((k.factorial : ℚ) * ((10 * n + 1 - k).factorial : ℚ) *
      ((k + n).factorial : ℚ) * ((8 * n + 1 - k).factorial : ℚ)) * hs

/-! ### Real form and positivity -/

lemma NF_real (n k : ℕ) : NF n (k : ℝ) = (∏ i ∈ range (10 * n + 1), ((k : ℝ) + 2 * n + 1 + i)) *
    (∏ i ∈ range (6 * n + 1), ((k : ℝ) + 4 / 3 + i)) *
    (∏ i ∈ range (3 * n + 1), ((k : ℝ) + 2 * n + 3 / 2 + i)) := rfl

lemma fact_real (m : ℕ) : ((m.factorial : ℕ) : ℝ) = ∏ i ∈ range m, ((1 : ℝ) + i) := by
  rw [← prod_range_add_one_eq_factorial, Nat.cast_prod]
  exact prod_congr rfl fun i _ => by push_cast; ring

lemma wQ_real (n k : ℕ) (hk : k ≤ 8 * n + 1) : ((wQ n k : ℚ) : ℝ) = NF n (k : ℝ) /
    (((k.factorial : ℕ) : ℝ) * ((10 * n + 1 - k).factorial : ℕ) * ((k + n).factorial : ℕ) *
      ((8 * n + 1 - k).factorial : ℕ)) := by
  unfold wQ
  rw [DF_nat n k hk, Rat.cast_div, NF_cast]
  push_cast
  rfl

lemma NF_real_pos (n k : ℕ) : 0 < NF n (k : ℝ) := by
  rw [NF_real]
  refine mul_pos (mul_pos ?_ ?_) ?_ <;> exact prod_pos fun i _ => by positivity

lemma wQ_pos (n k : ℕ) (hk : k ≤ 8 * n + 1) : 0 < ((wQ n k : ℚ) : ℝ) := by
  rw [wQ_real n k hk]
  have := NF_real_pos n k
  positivity

end Zeta2L2Chi3.Arith
