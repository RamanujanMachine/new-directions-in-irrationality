/-
# Positive rational content of a rational vector and the reduced denominator (END03, END04)

For `w ∈ ℚ³`, `L = lcm(den w_i)`, `g = gcd(L w_i)`, `cont w = g / L`, `prim w = L w / g ∈ ℤ³`.
Then `w = cont w • prim w`, `prim w` is a primitive integer vector, and for the readout
`r = 2[(A+B) w₁ - 3B w₂] / (9 w₀)` we get `r = P/Q` with integers
`Q = 9 u₀`, `P = 2[(A+B)u₁ - 3B u₂]`, `u = prim w`; the reduced denominator divides `Q`.
-/
import Mathlib

namespace Zeta2L2Chi3

/-- `lcm` of the denominators -/
def contL (w : Fin 3 → ℚ) : ℕ := Nat.lcm (w 0).den (Nat.lcm (w 1).den (w 2).den)

lemma contL_pos (w : Fin 3 → ℚ) : 0 < contL w := by
  unfold contL
  exact Nat.lcm_pos (w 0).den_pos (Nat.lcm_pos (w 1).den_pos (w 2).den_pos)

lemma den_dvd_contL (w : Fin 3 → ℚ) (i : Fin 3) : (w i).den ∣ contL w := by
  unfold contL
  fin_cases i
  · exact Nat.dvd_lcm_left _ _
  · exact (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
  · exact (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)

/-- `L w` as an integer vector -/
def intVec (w : Fin 3 → ℚ) : Fin 3 → ℤ := fun i => (w i * contL w).num

lemma intVec_spec (w : Fin 3 → ℚ) (i : Fin 3) : ((intVec w i : ℤ) : ℚ) = w i * contL w := by
  have hden : (w i * contL w).den = 1 := by
    obtain ⟨k, hk⟩ := den_dvd_contL w i
    rw [hk]
    have : w i * ((w i).den * k : ℕ) = ((w i).num * k : ℤ) := by
      push_cast; rw [← mul_assoc, Rat.mul_den_eq_num]
    rw [this]; exact Rat.den_intCast _
  have := Rat.num_div_den (w i * contL w)
  rw [hden] at this; simp only [Nat.cast_one, div_one] at this
  simp only [intVec]; exact this

/-- `gcd` of the integer vector -/
def contG (w : Fin 3 → ℚ) : ℕ :=
  Nat.gcd (intVec w 0).natAbs (Nat.gcd (intVec w 1).natAbs (intVec w 2).natAbs)

/-- the positive rational content -/
def cont (w : Fin 3 → ℚ) : ℚ := contG w / contL w

/-- the primitive integer vector `w / cont w` -/
def prim (w : Fin 3 → ℚ) : Fin 3 → ℤ := fun i => intVec w i / contG w

lemma contG_dvd (w : Fin 3 → ℚ) (i : Fin 3) : (contG w : ℤ) ∣ intVec w i := by
  rw [Int.natCast_dvd]
  unfold contG
  fin_cases i
  · exact Nat.gcd_dvd_left _ _
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

lemma contG_ne_zero (w : Fin 3 → ℚ) (hw : w ≠ 0) : contG w ≠ 0 := by
  intro h
  apply hw
  ext i
  have hi : intVec w i = 0 := by
    have := contG_dvd w i; rw [h] at this; simpa using this
  have := intVec_spec w i
  rw [hi] at this
  have hL : (contL w : ℚ) ≠ 0 := by exact_mod_cast (contL_pos w).ne'
  simp only [Int.cast_zero] at this
  simpa [hL] using this.symm

lemma cont_pos (w : Fin 3 → ℚ) (hw : w ≠ 0) : 0 < cont w := by
  unfold cont
  have := contG_ne_zero w hw
  have := contL_pos w
  positivity

/-- `w = cont w • prim w` -/
lemma w_eq_cont_prim (w : Fin 3 → ℚ) (hw : w ≠ 0) (i : Fin 3) : w i = cont w * prim w i := by
  have hG : (contG w : ℚ) ≠ 0 := by exact_mod_cast contG_ne_zero w hw
  have hL : (contL w : ℚ) ≠ 0 := by exact_mod_cast (contL_pos w).ne'
  have hdiv : ((prim w i : ℤ) : ℚ) = (intVec w i : ℚ) / contG w := by
    simp only [prim]
    rw [Int.cast_div (contG_dvd w i) (by exact_mod_cast contG_ne_zero w hw)]
    simp
  rw [hdiv, intVec_spec, cont]
  field_simp

/-- the reduced denominator of `P/Q` divides `Q` -/
lemma den_div_dvd (P Q : ℤ) : ((P / Q : ℚ).den : ℤ) ∣ Q := by
  rw [← Rat.divInt_eq_div]; exact Rat.den_dvd P Q

/-- `|den(P/Q) α - num(P/Q)| ≤ |Q α - P|` -/
lemma abs_den_mul_sub_num_le (P Q : ℤ) (hQ : Q ≠ 0) (α : ℝ) :
    |((P / Q : ℚ).den : ℝ) * α - (P / Q : ℚ).num| ≤ |(Q : ℝ) * α - P| := by
  obtain ⟨k, hk⟩ := den_div_dvd P Q
  generalize hr : (P / Q : ℚ) = r at hk ⊢
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hQ hk
  have hnum : (r.num : ℝ) = ((P : ℝ) / Q) * r.den := by
    have h1 : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
    have h2 : ((r : ℚ) : ℝ) = (P : ℝ) / Q := by rw [← hr]; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at this; rw [this, h2]
  have hQr : (Q : ℝ) = r.den * k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
  have hden' : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  rw [hnum, hQr]
  have : (r.den : ℝ) * α - P / (r.den * k) * r.den = ((r.den * k : ℝ) * α - P) / k := by
    field_simp
  rw [this, abs_div]
  exact div_le_self (abs_nonneg _) hk1

lemma den_div_le (P Q : ℤ) (hQ : Q ≠ 0) : ((P / Q : ℚ).den : ℝ) ≤ |(Q : ℝ)| := by
  obtain ⟨k, hk⟩ := den_div_dvd P Q
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hQ hk
  have : (Q : ℝ) = (P / Q : ℚ).den * k := by exact_mod_cast hk
  rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((P / Q : ℚ).den : ℝ))]
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
  nlinarith [(by positivity : (0 : ℝ) ≤ ((P / Q : ℚ).den : ℝ))]

end Zeta2L2Chi3
