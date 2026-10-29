/-
# The telescoping identity for the dual transport (END02, part 1)

For `k ∈ {0,1,2}` put
`f_k(s) = s^k F_{n+1}(s) + ∑_j Q_{jk}(n) s^j F_n(s)` and
`G_k(s) = F_n(s) N_k(n,s) / (12 (3n+1) D_Q(n) rden(n,s))`.
Then `f_k(s) = G_k(s) - G_k(s-1)` at every `s` where the finitely many denominators involved are
nonzero (`f_eq_G_sub_G`).
-/
import Zeta2L2Chi3.Cert0
import Zeta2L2Chi3.Cert1
import Zeta2L2Chi3.Cert2
import Zeta2L2Chi3.DualShift

open Finset

namespace Zeta2L2Chi3

variable {K : Type*} [Field K] [CharZero K]

/-- The certificate polynomials. -/
def Ncert : Fin 3 → PE := ![Ncert0, Ncert1, Ncert2]

theorem Ncert_check (k : Fin 3) : ∃ B, (certPE k (Ncert k)).check B := by
  fin_cases k
  · exact ⟨_, cert0_check⟩
  · exact ⟨_, cert1_check⟩
  · exact ⟨_, cert2_check⟩

/-- `Q_{jk}(n)` over `K`. -/
def Qk (n : ℕ) (j k : Fin 3) : K := hornerR (Data.Qnum j k) (n : K) / hornerR Data.Qden (n : K)

lemma Qk_rat (n : ℕ) (j k : Fin 3) : (Qk n j k : ℚ) = Q n j k := rfl

lemma Qk_cast (n : ℕ) (j k : Fin 3) : (Qk n j k : ℝ) = ((Q n j k : ℚ) : ℝ) := by
  have h1 := hornerR_map (Rat.castHom ℝ) (Data.Qnum j k) (n : ℚ)
  have h2 := hornerR_map (Rat.castHom ℝ) Data.Qden (n : ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at h1 h2
  show hornerR (Data.Qnum j k) (n : ℝ) / hornerR Data.Qden (n : ℝ) =
    ((hornerR (Data.Qnum j k) (n : ℚ) / hornerR Data.Qden (n : ℚ) : ℚ) : ℝ)
  rw [Rat.cast_div, h1, h2]

/-- `f_k(s)`. -/
def fk (n : ℕ) (k : Fin 3) (s : K) : K :=
  s ^ (k : ℕ) * F (n + 1) s + ∑ j : Fin 3, Qk n j k * s ^ (j : ℕ) * F n s

/-- `G_k(s)`. -/
def Gk (n : ℕ) (k : Fin 3) (s : K) : K :=
  F n s * (Ncert k).val (n : K) s / (12 * (3 * n + 1) * hornerR Data.Qden (n : K) * rdenR (n : K) s)

lemma rdenS_eq (n : ℕ) (s : K) : rdenS n s = rdenR (n : K) s := rfl

lemma rnumR_eq (n : ℕ) (s : K) :
    rnumR (n : K) s = rnumA n s *
      ((2 * n - s) * (2 * n + 1 - s) * (2 * n + 1 / 2 - s) * (2 * n + 3 / 2 - s)) := by
  simp only [rnumR, rnumA]

/-- `F_{n+1} = F_n · rnum/rden`. -/
lemma F_succ (n : ℕ) (s : K) (h1 : FDen n s ≠ 0) (h2 : rdenR (n : K) s ≠ 0) :
    F (n + 1) s = F n s * rnumR (n : K) s / rdenR (n : K) s := by
  have hs := FDen_succ (K := K) n s
  rw [rdenS_eq] at hs
  have h3 : FDen (n + 1) s ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs; exact mul_ne_zero h1 h2 hs.symm
  rw [show F n s * rnumR (n : K) s / rdenR (n : K) s
      = FNum n s * rnumR (n : K) s / (FDen n s * rdenR (n : K) s) by simp only [F]; ring]
  rw [F, div_eq_div_iff h3 (mul_ne_zero h1 h2), FNum_succ, rnumR_eq]
  linear_combination (-(FNum n s * rnumA n s)) * hs

/-- `F_n(s-1) A(s-1) = F_n(s) B(s-1)`. -/
lemma F_shift (n : ℕ) (s : K) (h0 : FDen n s ≠ 0) (h1 : FDen n (s - 1) ≠ 0) :
    F n (s - 1) * AR (n : K) (s - 1) = F n s * BR (n : K) (s - 1) := by
  have a := FNum_shift (K := K) n s
  have b := FDen_shift (K := K) n s
  have hA : AR (n : K) (s - 1) = ((s + 10 * n + 1) * (s + 8 * n + 1)) *
      ((12 * n + 2 - s) * (6 * n + 7 / 3 - s) * (5 * n + 5 / 2 - s)) := by simp only [AR]; ring
  have hB : BR (n : K) (s - 1) = (s * (s - n)) * ((2 * n - s) * (1 / 3 - s) * (2 * n + 1 / 2 - s)) := by
    simp only [BR]; ring
  rw [hA, hB, F, F, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff h1 h0]
  linear_combination (((12 * n + 2 - s) * (6 * n + 7 / 3 - s) * (5 * n + 5 / 2 - s)) * FDen n s) * a
    - (FNum n s * (s * (s - n))) * b

/-- **The telescoping identity.** -/
theorem f_eq_G_sub_G (n : ℕ) (k : Fin 3) (s : K)
    (h0 : FDen n s ≠ 0) (h1 : FDen n (s - 1) ≠ 0) (h2 : rdenR (n : K) s ≠ 0)
    (h3 : rdenR (n : K) (s - 1) ≠ 0) (h4 : AR (n : K) (s - 1) ≠ 0) :
    fk n k s = Gk n k s - Gk n k (s - 1) := by
  obtain ⟨B, hB⟩ := Ncert_check k
  have hc := cert_identity (R := K) k (Ncert k) B hB (n : K) s
  have hD : hornerR Data.Qden (n : K) ≠ 0 := by
    have hq := Qden_pos (n : ℚ) (by positivity)
    have h' := hornerR_map (Rat.castHom K) Data.Qden (n : ℚ)
    simp only [Rat.coe_castHom, Rat.cast_natCast] at h'
    rw [← h']; exact_mod_cast hq.ne'
  have h31 : (3 * (n : K) + 1) ≠ 0 := by
    have : (3 * (n : K) + 1) = ((3 * n + 1 : ℕ) : K) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 3 * n + 1 ≠ 0)
  have hP1 : F n (s - 1) = F n s * BR (n : K) (s - 1) / AR (n : K) (s - 1) := by
    rw [eq_div_iff h4]; exact F_shift n s h0 h1
  have hF1 := F_succ n s h0 h2
  simp only [fk, Gk, Fin.sum_univ_three, Qk]
  rw [hP1, hF1]
  generalize (Ncert k).val (n : K) s = N at hc ⊢
  generalize (Ncert k).val (n : K) (s - 1) = N1 at hc ⊢
  generalize F n s = P
  generalize rdenR (n : K) s = rd at hc h2 ⊢
  generalize rdenR (n : K) (s - 1) = rd1 at hc h3 ⊢
  generalize AR (n : K) (s - 1) = A1 at hc h4 ⊢
  generalize BR (n : K) (s - 1) = B1 at hc ⊢
  generalize rnumR (n : K) s = rn at hc ⊢
  generalize hornerR Data.Qden (n : K) = Qd at hc hD ⊢
  generalize hornerR (Data.Qnum 0 k) (n : K) = q0 at hc ⊢
  generalize hornerR (Data.Qnum 1 k) (n : K) = q1 at hc ⊢
  generalize hornerR (Data.Qnum 2 k) (n : K) = q2 at hc ⊢
  generalize (n : K) = x at hc h31 ⊢
  have E1 : P * N / (12 * (3 * x + 1) * Qd * rd) - P * B1 / A1 * N1 / (12 * (3 * x + 1) * Qd * rd1)
      = P * (N * (rd1 * A1) - B1 * rd * N1) / (12 * (3 * x + 1) * Qd * rd * (rd1 * A1)) := by
    field_simp
  rw [E1, hc]
  field_simp
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  ring

end Zeta2L2Chi3
