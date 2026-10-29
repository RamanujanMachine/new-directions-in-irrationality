/-
# Gauge normalization of the recurrence (ASY01)

With `D_g(n) = diag(1, n⁻¹, n⁻²)` and `Q₀₀(n) → s∞ = 156660580321280`,
`A(n) = D_g(n)⁻¹ Q(n) D_g(n+1) / Q₀₀(n)` has entries `Q_{ij}(n) n^i / ((n+1)^j Q₀₀(n))`, and
`A(n) → T` entrywise, where `T` is the exact rational limit matrix.
-/
import Zeta2L2Chi3.Matrices

open Filter Topology Polynomial

noncomputable section

namespace Zeta2L2Chi3

/-! ### Polynomials from coefficient lists -/

/-- last coefficient of a list (`0` for the empty list) -/
def lastCoeff : List ℤ → ℤ
  | [] => 0
  | [c] => c
  | _ :: c :: cs => lastCoeff (c :: cs)

lemma toPoly_natDegree_leadingCoeff (l : List ℤ) (h : lastCoeff l ≠ 0) :
    (toPoly l).natDegree = l.length - 1 ∧ (toPoly l).leadingCoeff = lastCoeff l := by
  induction l with
  | nil => simp [lastCoeff] at h
  | cons c cs ih =>
    cases cs with
    | nil =>
      refine ⟨by simp [toPoly], ?_⟩
      simp only [toPoly, mul_zero, add_zero, lastCoeff, leadingCoeff_C]
    | cons d ds =>
      have h' : lastCoeff (d :: ds) ≠ 0 := by simpa [lastCoeff] using h
      obtain ⟨h1, h2⟩ := ih h'
      have hne : toPoly (d :: ds) ≠ 0 := by
        intro h0; rw [h0, leadingCoeff_zero] at h2; exact h' h2.symm
      have hdeg : (Polynomial.C c : ℤ[X]).natDegree < (X * toPoly (d :: ds)).natDegree := by
        rw [natDegree_X_mul hne]; simp
      have e : toPoly (c :: d :: ds) = Polynomial.C c + X * toPoly (d :: ds) := rfl
      rw [e]
      constructor
      · rw [add_comm, natDegree_add_eq_left_of_natDegree_lt hdeg, natDegree_X_mul hne, h1]
        simp
      · rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hdeg), leadingCoeff_mul, leadingCoeff_X, one_mul, h2]
        simp [lastCoeff]

/-- the real polynomial of a coefficient list -/
def toPolyR (l : List ℤ) : ℝ[X] := (toPoly l).map (Int.castRingHom ℝ)

lemma eval_toPolyR (l : List ℤ) (x : ℝ) : (toPolyR l).eval x = hornerR l x := by
  rw [toPolyR, eval_map, eval₂_toPoly]

lemma toPolyR_natDegree_leadingCoeff (l : List ℤ) (h : lastCoeff l ≠ 0) :
    (toPolyR l).natDegree = l.length - 1 ∧ (toPolyR l).leadingCoeff = lastCoeff l := by
  obtain ⟨h1, h2⟩ := toPoly_natDegree_leadingCoeff l h
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  refine ⟨?_, ?_⟩
  · rw [toPolyR, natDegree_map_eq_of_injective hinj, h1]
  · rw [toPolyR, leadingCoeff_map_of_injective hinj, h2]; simp

/-- Rational function limit: `p(x) x^i / ((x+1)^j q(x)) → lc p / lc q` when degrees match. -/
lemma tendsto_ratio_lists (p q : List ℤ) (i j : ℕ) (hp : lastCoeff p ≠ 0) (hq : lastCoeff q ≠ 0)
    (hdeg : p.length - 1 + i = q.length - 1 + j) :
    Tendsto (fun n : ℕ => hornerR p (n : ℝ) * (n : ℝ) ^ i / (((n : ℝ) + 1) ^ j * hornerR q (n : ℝ)))
      atTop (𝓝 ((lastCoeff p : ℝ) / lastCoeff q)) := by
  obtain ⟨hp1, hp2⟩ := toPolyR_natDegree_leadingCoeff p hp
  obtain ⟨hq1, hq2⟩ := toPolyR_natDegree_leadingCoeff q hq
  set P := toPolyR p * X ^ i
  set R := (X + 1) ^ j * toPolyR q
  have hP0 : toPolyR p ≠ 0 := by intro h0; rw [h0, leadingCoeff_zero] at hp2; exact hp (by exact_mod_cast hp2.symm)
  have hR0 : toPolyR q ≠ 0 := by intro h0; rw [h0, leadingCoeff_zero] at hq2; exact hq (by exact_mod_cast hq2.symm)
  have hPdeg : P.natDegree = p.length - 1 + i := by
    simp only [P]
    rw [natDegree_mul hP0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow, hp1]
  have hX1 : (X + 1 : ℝ[X]) = X + Polynomial.C 1 := by simp
  have hRdeg : R.natDegree = j + (q.length - 1) := by
    simp only [R]
    rw [hX1, natDegree_mul (pow_ne_zero _ (X_add_C_ne_zero 1)) hR0, natDegree_pow, natDegree_X_add_C,
      hq1]; ring
  have hPlc : P.leadingCoeff = lastCoeff p := by
    simp only [P]
    rw [leadingCoeff_mul, leadingCoeff_X_pow, mul_one, hp2]
  have hRlc : R.leadingCoeff = lastCoeff q := by
    simp only [R]
    rw [leadingCoeff_mul, leadingCoeff_pow, hX1, leadingCoeff_X_add_C, one_pow, one_mul, hq2]
  have hR0' : R ≠ 0 := by simp only [R]; rw [hX1]; exact mul_ne_zero (pow_ne_zero _ (X_add_C_ne_zero 1)) hR0
  have hP0' : P ≠ 0 := mul_ne_zero hP0 (pow_ne_zero _ X_ne_zero)
  have hdeg' : P.degree = R.degree := by
    rw [degree_eq_natDegree hP0', degree_eq_natDegree hR0', hPdeg, hRdeg]; congr 1; omega
  have := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P R hdeg').comp
    tendsto_natCast_atTop_atTop
  rw [hPlc, hRlc] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, P, R, eval_mul, eval_pow, eval_X, eval_add, eval_one,
    eval_toPolyR]

/-! ### The limit matrix and the scalar -/

/-- `s∞ = lim Q₀₀(n)` -/
def sInf : ℚ := 156660580321280

/-- the exact limit matrix `T` of the normalized recurrence -/
def Tlim : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 67935889627/15298884797, 288899710760/15298884797;
     -4289038063/611955391880, 532385237/611955391880, 419064958/2185554971;
     -67935889627/2447821567520, -7222492769/61195539188, -288367325523/611955391880]

/-- the normalized matrices `A(n)` (real) -/
def Anorm (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (Q n i j : ℝ) * (n : ℝ) ^ (i : ℕ) / (((n : ℝ) + 1) ^ (j : ℕ) * (Q n 0 0 : ℝ))

lemma Q_cast (n : ℕ) (i j : Fin 3) :
    (Q n i j : ℝ) = hornerR (Data.Qnum i j) (n : ℝ) / hornerR Data.Qden (n : ℝ) := by
  have h1 := hornerR_map (Rat.castHom ℝ) (Data.Qnum i j) (n : ℚ)
  have h2 := hornerR_map (Rat.castHom ℝ) Data.Qden (n : ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at h1 h2
  simp only [Q, Rat.cast_div, h1, h2]

lemma Qden_pos_real (n : ℕ) : 0 < hornerR Data.Qden (n : ℝ) := by
  have h2 := hornerR_map (Rat.castHom ℝ) Data.Qden (n : ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at h2
  rw [← h2]; exact_mod_cast Qden_pos (n : ℚ) (by positivity)

theorem lastCoeff_facts :
    (∀ i j : Fin 3, lastCoeff (Data.Qnum i j) ≠ 0) ∧ lastCoeff Data.Qden ≠ 0 ∧
    (∀ i j : Fin 3, (Data.Qnum i j).length - 1 + (i : ℕ) = (Data.Qnum 0 0).length - 1 + (j : ℕ)) ∧
    (Data.Qnum 0 0).length = Data.Qden.length := by
  decide +kernel

theorem Tlim_eq (i j : Fin 3) :
    (lastCoeff (Data.Qnum i j) : ℚ) / lastCoeff (Data.Qnum 0 0) = Tlim i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem sInf_eq : (lastCoeff (Data.Qnum 0 0) : ℚ) / lastCoeff Data.Qden = sInf := by
  decide +kernel

theorem tendsto_Anorm (i j : Fin 3) :
    Tendsto (fun n => Anorm n i j) atTop (𝓝 ((Tlim i j : ℚ) : ℝ)) := by
  obtain ⟨h1, -, h3, -⟩ := lastCoeff_facts
  have := tendsto_ratio_lists (Data.Qnum i j) (Data.Qnum 0 0) i j (h1 i j) (h1 0 0) (h3 i j)
  rw [← Tlim_eq i j]; push_cast
  refine this.congr fun n => ?_
  have hD := (Qden_pos_real n).ne'
  simp only [Anorm, Q_cast]
  field_simp

theorem tendsto_Q00 : Tendsto (fun n => (Q n 0 0 : ℝ)) atTop (𝓝 ((sInf : ℚ) : ℝ)) := by
  obtain ⟨h1, h2, -, h4⟩ := lastCoeff_facts
  have := tendsto_ratio_lists (Data.Qnum 0 0) Data.Qden 0 0 (h1 0 0) h2 (by rw [h4])
  rw [← sInf_eq]; push_cast
  refine this.congr fun n => ?_
  simp [Q_cast]

end Zeta2L2Chi3
