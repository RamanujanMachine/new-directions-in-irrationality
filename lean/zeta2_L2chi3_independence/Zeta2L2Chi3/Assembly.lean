/-
# Assembly: from the three rate inputs to the final statements (NV02, FIN01–FIN03)

The special state `γ_k(n) = S n k = ξ · (column k of B̂_n)`, `ξ = (1, 9C/2+3Z, 2Z)`, and the
cofactor vector `w_n` satisfy the exact identity (`key_identity`)

`9 w₀ α - 2[(A+B) w₁ - 3B w₂] = -2(A+B)(γ₂ B̂₂₁ - γ₁ B̂₂₂) - 6B(γ₂ B̂₁₁ - γ₁ B̂₁₂)`,

so with `u = w / cont w` the integer linear form `9u₀ α - 2[(A+B)u₁ - 3Bu₂]` is bounded by
`|γ| ‖B̂‖ / cont`.  The rate inputs (`RateHyp`) are

* decay of the special state:   `|S n k| ≤ e^{(Lg+ε) n}`,
* growth of the endpoint matrix: `|B̂_n(i,j)| ≤ e^{(LB+ε) n}`,
* the content lower bound:       `cont(w_n) ≥ e^{(β-ε) n}`.
-/
import Zeta2L2Chi3.DualTransport
import Zeta2L2Chi3.NV
import Zeta2L2Chi3.Generic
import Zeta2L2Chi3.Content

open Filter Real Topology Matrix

noncomputable section

namespace Zeta2L2Chi3

/-- `ξ₁ = ψ₁(1/3) - Z = 9C/2 + 3Z`, `ξ₂ = ψ₁(1/2) - Z = 2Z` -/
def ξ1 : ℝ := 9 * C / 2 + 3 * Z
def ξ2 : ℝ := 2 * Z

lemma alpha_eq_xi (A B : ℤ) : alpha A B = 2 / 9 * (A + B : ℝ) * ξ1 - 2 / 3 * (B : ℝ) * ξ2 := by
  rw [alpha_eq]; unfold ξ1 ξ2; ring

/-- the special state is `ξ · B̂_n` -/
lemma S_eq_Bhat (n : ℕ) (k : Fin 3) :
    S n k = ((Bhat n 0 k : ℚ) : ℝ) + ξ1 * ((Bhat n 1 k : ℚ) : ℝ) + ξ2 * ((Bhat n 2 k : ℚ) : ℝ) := by
  rw [← Bres_eq_Bhat, S_eq n k (by omega)]
  unfold ξ1 ξ2
  fin_cases k <;> simp [Bres]

/-- the exact error identity -/
lemma key_identity (B : Matrix (Fin 3) (Fin 3) ℝ) (a b x1 x2 : ℝ) :
    9 * (B 1 1 * B 2 2 - B 2 1 * B 1 2) * (2 / 9 * (a + b) * x1 - 2 / 3 * b * x2)
      - 2 * ((a + b) * (B 2 1 * B 0 2 - B 0 1 * B 2 2) - 3 * b * (B 0 1 * B 1 2 - B 1 1 * B 0 2)) =
    -2 * (a + b) * ((B 0 2 + x1 * B 1 2 + x2 * B 2 2) * B 2 1 - (B 0 1 + x1 * B 1 1 + x2 * B 2 1) * B 2 2)
      - 6 * b * ((B 0 2 + x1 * B 1 2 + x2 * B 2 2) * B 1 1 - (B 0 1 + x1 * B 1 1 + x2 * B 2 1) * B 1 2) := by
  ring

/-- `w_n ≠ 0` -/
lemma w_ne_zero (n : ℕ) : w n ≠ 0 := by
  intro h
  have hv : v n ≠ 0 := by
    intro hv0
    have : (W n)ᵀ⁻¹ *ᵥ e0 = 0 := hv0
    have hdet : ((W n)ᵀ⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']
      exact inv_ne_zero (det_W_ne n)
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet this
    have h1 := congrFun this 0
    simp [e0] at h1
  have hc : ((-1944 / 35 : ℚ) * Δ n) ≠ 0 := mul_ne_zero (by norm_num) (det_W_ne n)
  have h2 : A0 *ᵥ v n = 0 := by
    have := w_eq_A0_v n
    rw [h] at this
    funext i
    have hi := congrFun this i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.1 hi.symm).resolve_left hc
  have hdetA : A0.det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [A0]; norm_num
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hdetA h2)

/-! ### Integer linear forms -/

/-- primitive integer cofactor vector -/
def u (n : ℕ) : Fin 3 → ℤ := prim (w n)

def Qd (n : ℕ) : ℤ := 9 * u n 0
def Pd (n : ℕ) (A B : ℤ) : ℤ := 2 * ((A + B) * u n 1 - 3 * B * u n 2)

lemma w_eq_u (n : ℕ) (i : Fin 3) : w n i = cont (w n) * u n i :=
  w_eq_cont_prim (w n) (w_ne_zero n) i

lemma linform_eq (n : ℕ) (A B : ℤ) :
    ((Qd n : ℝ) * alpha A B - Pd n A B) * (cont (w n) : ℝ) =
      9 * ((w n 0 : ℚ) : ℝ) * alpha A B - 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ)) := by
  simp only [w_eq_u n, Qd, Pd]; push_cast; ring

/-- the bound for the integer linear form -/
lemma linform_bound (n : ℕ) (A B : ℤ) (Γ M : ℝ) (hΓ : ∀ k : Fin 3, |S n k| ≤ Γ)
    (hM : ∀ i j : Fin 3, |((Bhat n i j : ℚ) : ℝ)| ≤ M) :
    |9 * ((w n 0 : ℚ) : ℝ) * alpha A B - 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ))|
      ≤ (4 * |(A + B : ℝ)| + 12 * |(B : ℝ)|) * (Γ * M) := by
  set Bm : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ((Bhat n i j : ℚ) : ℝ)
  have hw : ∀ i, ((w n i : ℚ) : ℝ) = ![Bm 1 1 * Bm 2 2 - Bm 2 1 * Bm 1 2,
      Bm 2 1 * Bm 0 2 - Bm 0 1 * Bm 2 2, Bm 0 1 * Bm 1 2 - Bm 1 1 * Bm 0 2] i := by
    intro i; fin_cases i <;> simp [w, Bm]
  have hS : ∀ k : Fin 3, S n k = Bm 0 k + ξ1 * Bm 1 k + ξ2 * Bm 2 k := fun k => S_eq_Bhat n k
  rw [hw 0, hw 1, hw 2, alpha_eq_xi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [key_identity Bm (A : ℝ) B ξ1 ξ2, ← hS 1, ← hS 2]
  have hΓ0 : 0 ≤ Γ := (abs_nonneg _).trans (hΓ 0)
  have h1 : |S n 2 * Bm 2 1 - S n 1 * Bm 2 2| ≤ 2 * (Γ * M) := by
    calc _ ≤ |S n 2| * |Bm 2 1| + |S n 1| * |Bm 2 2| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ Γ * M + Γ * M := by gcongr <;> [exact hΓ 2; exact hM 2 1; exact hΓ 1; exact hM 2 2]
      _ = _ := by ring
  have h2 : |S n 2 * Bm 1 1 - S n 1 * Bm 1 2| ≤ 2 * (Γ * M) := by
    calc _ ≤ |S n 2| * |Bm 1 1| + |S n 1| * |Bm 1 2| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ Γ * M + Γ * M := by gcongr <;> [exact hΓ 2; exact hM 1 1; exact hΓ 1; exact hM 1 2]
      _ = _ := by ring
  calc _ ≤ |-2 * (A + B : ℝ) * (S n 2 * Bm 2 1 - S n 1 * Bm 2 2)|
          + |6 * (B : ℝ) * (S n 2 * Bm 1 1 - S n 1 * Bm 1 2)| := by
        rw [show ∀ x y : ℝ, -2 * (A + B : ℝ) * x - 6 * B * y = -2 * (A + B : ℝ) * x + -(6 * B * y)
          from fun x y => by ring]
        exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_neg]; rfl))
    _ = 2 * |(A + B : ℝ)| * |S n 2 * Bm 2 1 - S n 1 * Bm 2 2|
          + 6 * |(B : ℝ)| * |S n 2 * Bm 1 1 - S n 1 * Bm 1 2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ 2 * |(A + B : ℝ)| * (2 * (Γ * M)) + 6 * |(B : ℝ)| * (2 * (Γ * M)) := by gcongr
    _ = _ := by ring

/-! ### The rate hypotheses -/

structure RateHyp (Lg LB β : ℝ) : Prop where
  decay : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : Fin 3, |S n k| ≤ exp ((Lg + ε) * n)
  growth : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i j : Fin 3, |((Bhat n i j : ℚ) : ℝ)| ≤ exp ((LB + ε) * n)
  content : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, exp ((β - ε) * n) ≤ ((cont (w n) : ℚ) : ℝ)

lemma eventually_const_le_exp (K ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, K ≤ exp (ε * n) := by
  have : Tendsto (fun n : ℕ => exp (ε * n)) atTop atTop :=
    tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hε tendsto_natCast_atTop_atTop)
  exact this.eventually_ge_atTop K

/-- the integer linear form decays at rate `β - Lg - LB` -/
theorem linform_decay {Lg LB β : ℝ} (h : RateHyp Lg LB β) (A B : ℤ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |(Qd n : ℝ) * alpha A B - Pd n A B| ≤ exp ((Lg + LB - β + ε) * n) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  filter_upwards [h.decay _ hε4, h.growth _ hε4, h.content _ hε4,
    eventually_const_le_exp (4 * |(A + B : ℝ)| + 12 * |(B : ℝ)| + 1) _ hε4] with n hd hg hc hK
  have hcpos : (0 : ℝ) < ((cont (w n) : ℚ) : ℝ) := by
    exact_mod_cast cont_pos (w n) (w_ne_zero n)
  have hb := linform_bound n A B _ _ hd hg
  rw [← linform_eq, abs_mul, abs_of_pos hcpos] at hb
  have hK0 : 0 ≤ 4 * |(A + B : ℝ)| + 12 * |(B : ℝ)| := by positivity
  have hprod : exp ((Lg + ε / 4) * n) * exp ((LB + ε / 4) * n) = exp ((Lg + LB + ε / 2) * n) := by
    rw [← exp_add]; ring_nf
  rw [hprod] at hb
  have hstep : |(Qd n : ℝ) * alpha A B - Pd n A B| ≤
      (4 * |(A + B : ℝ)| + 12 * |(B : ℝ)|) * exp ((Lg + LB + ε / 2) * n) / exp ((β - ε / 4) * n) := by
    rw [le_div_iff₀ (exp_pos _)]
    calc _ ≤ |(Qd n : ℝ) * alpha A B - Pd n A B| * ((cont (w n) : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ ≤ _ := hb
  refine hstep.trans ?_
  rw [div_le_iff₀ (exp_pos _)]
  calc (4 * |(A + B : ℝ)| + 12 * |(B : ℝ)|) * exp ((Lg + LB + ε / 2) * n)
      ≤ exp (ε / 4 * n) * exp ((Lg + LB + ε / 2) * n) := by gcongr; linarith
    _ = exp ((Lg + LB - β + ε) * n) * exp ((β - ε / 4) * n) := by
        rw [← exp_add, ← exp_add]; ring_nf

/-- **Eventually `D v_N ≠ 0`**, i.e. `w_{N,0} ≠ 0`. -/
theorem eventually_w0_ne {Lg LB β : ℝ} (h : RateHyp Lg LB β) (hE : Lg + LB < β) :
    ∀ᶠ n : ℕ in atTop, w n 0 ≠ 0 := by
  set η := (β - Lg - LB) / 2
  have hη : 0 < η := by simp only [η]; linarith
  have hsmall : ∀ᶠ n : ℕ in atTop, exp ((Lg + LB - β + η) * n) < 1 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : Lg + LB - β + η < 0 := by simp only [η]; linarith
    have h2 : (Lg + LB - β + η) * n < 0 := mul_neg_of_neg_of_pos this (by exact_mod_cast hn)
    calc exp ((Lg + LB - β + η) * n) < exp 0 := exp_lt_exp.2 h2
      _ = 1 := exp_zero
  filter_upwards [linform_decay h 1 0 η hη, linform_decay h 0 1 η hη, hsmall] with n h10 h01 hs h0
  have hu0 : u n 0 = 0 := by
    have := w_eq_u n 0
    rw [h0] at this
    have hc := cont_pos (w n) (w_ne_zero n)
    exact_mod_cast (mul_eq_zero.1 this.symm).resolve_left hc.ne'
  have hlt1 : |((Pd n 1 0 : ℤ) : ℝ)| < 1 := by
    have : (Qd n : ℝ) = 0 := by simp [Qd, hu0]
    rw [this, zero_mul, zero_sub, abs_neg] at h10; linarith
  have hlt2 : |((Pd n 0 1 : ℤ) : ℝ)| < 1 := by
    have : (Qd n : ℝ) = 0 := by simp [Qd, hu0]
    rw [this, zero_mul, zero_sub, abs_neg] at h01; linarith
  have hP1 : Pd n 1 0 = 0 := by
    have : |Pd n 1 0| < 1 := by exact_mod_cast hlt1
    exact Int.abs_lt_one_iff.mp this
  have hP2 : Pd n 0 1 = 0 := by
    have : |Pd n 0 1| < 1 := by exact_mod_cast hlt2
    exact Int.abs_lt_one_iff.mp this
  have hu1 : u n 1 = 0 := by simp [Pd] at hP1; omega
  have hu2 : u n 2 = 0 := by simp [Pd] at hP2; omega
  apply w_ne_zero n
  funext i
  rw [w_eq_u n i]
  fin_cases i <;> simp [hu0, hu1, hu2]

/-! ### The readout as a reduced fraction -/

lemma readout_eq_PQ (n : ℕ) (A B : ℤ) (h0 : w n 0 ≠ 0) :
    readout n A B = (Pd n A B : ℚ) / (Qd n : ℚ) := by
  rw [readout_eq_w]
  have hc := cont_pos (w n) (w_ne_zero n)
  simp only [w_eq_u n, Pd, Qd]
  push_cast
  field_simp

lemma Qd_ne (n : ℕ) (h0 : w n 0 ≠ 0) : Qd n ≠ 0 := by
  intro hq
  apply h0
  rw [w_eq_u n 0]
  have : u n 0 = 0 := by simp [Qd] at hq; exact hq
  simp [this]

/-! ### Nonvanishing of the error infinitely often -/

/-- the error row `ρ = 3αD - 3(A+B)X - 2(A-B)Y` -/
def errRow (A B : ℤ) : Fin 3 → ℝ := fun j =>
  3 * alpha A B * (rowD j : ℝ) - 3 * (A + B : ℝ) * (rowX j : ℝ) - 2 * (A - B : ℝ) * (rowY j : ℝ)

lemma errRow_ne (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) : errRow A B ≠ 0 := by
  intro h
  set c : Fin 3 → ℝ := ![3 * alpha A B, -3 * (A + B : ℝ), -2 * (A - B : ℝ)]
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![fun j => (rowD j : ℝ), fun j => (rowX j : ℝ),
    fun j => (rowY j : ℝ)]
  have hcM : c ᵥ* M = 0 := by
    funext j
    have := congrFun h j
    simp only [errRow, Pi.zero_apply] at this
    simp [c, M, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
    linarith
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [M, rowD, rowX, rowY]; norm_num
  have hc0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hcM
  have h1 := congrFun hc0 1
  have h2 := congrFun hc0 2
  simp [c] at h1 h2
  apply hAB
  have : (A : ℝ) + B = 0 := by linarith
  have : (A : ℝ) - B = 0 := by linarith
  have hA : A = 0 := by exact_mod_cast (by linarith : (A : ℝ) = 0)
  have hB : B = 0 := by exact_mod_cast (by linarith : (B : ℝ) = 0)
  simp [hA, hB]

lemma linform_dot (n : ℕ) (A B : ℤ) :
    9 * ((w n 0 : ℚ) : ℝ) * alpha A B - 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ))
      = ((-1944 / 35 : ℚ) * Δ n : ℚ) / 1296 * (errRow A B ⬝ᵥ castV (v n)) := by
  have hw := w_eq_A0_v n
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  have h2 := congrFun hw 2
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  have hdot : errRow A B ⬝ᵥ castV (v n) = 3 * alpha A B * ((rowD ⬝ᵥ v n : ℚ) : ℝ)
      - 3 * (A + B : ℝ) * ((rowX ⬝ᵥ v n : ℚ) : ℝ) - 2 * (A - B : ℝ) * ((rowY ⬝ᵥ v n : ℚ) : ℝ) := by
    simp only [errRow, dotProduct, castV, Fin.sum_univ_three]; push_cast; ring
  rw [hdot, rowD_v, rowX_v, rowY_v, h0, h1, h2]
  push_cast; ring

theorem frequently_linform_ne (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ᶠ n : ℕ in atTop, (Qd n : ℝ) * alpha A B ≠ Pd n A B := by
  refine (frequently_dot_v_ne (errRow A B) (errRow_ne A B hAB)).mono fun n hn => ?_
  intro heq
  apply hn
  have h := linform_eq n A B
  rw [heq, sub_self, zero_mul, linform_dot] at h
  have hc : ((-1944 / 35 : ℚ) * Δ n : ℚ) ≠ 0 := mul_ne_zero (by norm_num) (det_W_ne n)
  have hc' : (((-1944 / 35 : ℚ) * Δ n : ℚ) : ℝ) / 1296 ≠ 0 := by
    apply div_ne_zero _ (by norm_num); exact_mod_cast hc
  exact (mul_eq_zero.1 h.symm).resolve_left hc'

/-! ### The final statements, conditional on the rate inputs -/

theorem irrational_of_rates {Lg LB β : ℝ} (h : RateHyp Lg LB β) (hE : Lg + LB < β)
    (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) : Irrational (alpha A B) := by
  set η := (β - Lg - LB) / 2
  have hη : 0 < η := by simp only [η]; linarith
  refine irrational_of_linear_forms (alpha A B) (fun n => Pd n A B) Qd
    (fun n => exp ((Lg + LB - β + η) * n)) (linform_decay h A B η hη) ?_
    (frequently_linform_ne A B hAB)
  apply tendsto_exp_atBot.comp
  have : Lg + LB - β + η < 0 := by simp only [η]; linarith
  exact (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg this) |>.congr fun n => by ring

theorem linIndep_of_rates {Lg LB β : ℝ} (h : RateHyp Lg LB β) (hE : Lg + LB < β) :
    LinearIndependent ℚ ![(1 : ℝ), C, Z] :=
  linearIndependent_one_C_Z fun A B hAB => irrational_of_rates h hE A B hAB

lemma abs_w0_le (n : ℕ) (M : ℝ) (hM : ∀ i j : Fin 3, |((Bhat n i j : ℚ) : ℝ)| ≤ M) :
    |((w n 0 : ℚ) : ℝ)| ≤ 2 * M ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have : ((w n 0 : ℚ) : ℝ) = ((Bhat n 1 1 : ℚ) : ℝ) * ((Bhat n 2 2 : ℚ) : ℝ)
      - ((Bhat n 2 1 : ℚ) : ℝ) * ((Bhat n 1 2 : ℚ) : ℝ) := by simp [w]
  rw [this]
  calc _ ≤ |((Bhat n 1 1 : ℚ) : ℝ)| * |((Bhat n 2 2 : ℚ) : ℝ)|
        + |((Bhat n 2 1 : ℚ) : ℝ)| * |((Bhat n 1 2 : ℚ) : ℝ)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ M * M + M * M := by gcongr <;> [exact hM 1 1; exact hM 2 2; exact hM 2 1; exact hM 1 2]
    _ = 2 * M ^ 2 := by ring

/-- the reduced denominators grow at most at rate `2 LB - β` -/
theorem log_den_bound {Lg LB β : ℝ} (h : RateHyp Lg LB β) (A B : ℤ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, w n 0 ≠ 0 →
      Real.log ((readout n A B).den : ℝ) ≤ (2 * LB - β + ε) * n := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  filter_upwards [h.growth _ hε4, h.content _ hε4, eventually_const_le_exp 18 _ hε4]
    with n hg hc hK h0
  rw [readout_eq_PQ n A B h0]
  have hQ := Qd_ne n h0
  have hden := den_div_le (Pd n A B) (Qd n) hQ
  have hdpos : (0 : ℝ) < ((Pd n A B : ℚ) / (Qd n : ℚ)).den := by exact_mod_cast Rat.den_pos _
  have hcpos : (0 : ℝ) < ((cont (w n) : ℚ) : ℝ) := by exact_mod_cast cont_pos (w n) (w_ne_zero n)
  -- `|Q| = 9 |w₀| / cont`
  have hQw : |(Qd n : ℝ)| * ((cont (w n) : ℚ) : ℝ) = 9 * |((w n 0 : ℚ) : ℝ)| := by
    have := w_eq_u n 0
    have h' : ((w n 0 : ℚ) : ℝ) = ((cont (w n) : ℚ) : ℝ) * (u n 0 : ℝ) := by
      rw [this]; push_cast; ring
    rw [h', abs_mul, abs_of_pos hcpos]; simp [Qd, abs_mul]; ring
  have hw0 := abs_w0_le n _ hg
  have hexp : exp ((LB + ε / 4) * n) ^ 2 = exp (2 * (LB + ε / 4) * n) := by
    rw [← exp_nat_mul]; ring_nf
  have hQb : |(Qd n : ℝ)| ≤ 18 * exp (2 * (LB + ε / 4) * n) / exp ((β - ε / 4) * n) := by
    rw [le_div_iff₀ (exp_pos _)]
    calc |(Qd n : ℝ)| * exp ((β - ε / 4) * n) ≤ |(Qd n : ℝ)| * ((cont (w n) : ℚ) : ℝ) := by gcongr
      _ = 9 * |((w n 0 : ℚ) : ℝ)| := hQw
      _ ≤ 9 * (2 * exp ((LB + ε / 4) * n) ^ 2) := by gcongr
      _ = 18 * exp (2 * (LB + ε / 4) * n) := by rw [hexp]; ring
  have hfin : ((Pd n A B : ℚ) / (Qd n : ℚ)).den ≤ exp ((2 * LB - β + ε) * n) := by
    refine hden.trans (hQb.trans ?_)
    rw [div_le_iff₀ (exp_pos _)]
    calc 18 * exp (2 * (LB + ε / 4) * n) ≤ exp (ε / 4 * n) * exp (2 * (LB + ε / 4) * n) := by
          gcongr
      _ = exp ((2 * LB - β + ε) * n) * exp ((β - ε / 4) * n) := by
          rw [← exp_add, ← exp_add]; ring_nf
  calc Real.log _ ≤ Real.log (exp ((2 * LB - β + ε) * n)) := Real.log_le_log hdpos hfin
    _ = _ := Real.log_exp _

theorem delta_of_rates {Lg LB β : ℝ} (h : RateHyp Lg LB β) (hE : Lg + LB < β)
    (hH : β < 2 * LB) (hδ : 1 / 10000 < (β - Lg - LB) / (2 * LB - β))
    (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ c : ℝ, 1 / 10000 < c ∧ ∀ᶠ N : ℕ in atTop, c ≤ delta (alpha A B) (readout N A B) := by
  set E' := β - Lg - LB
  set H₀ := 2 * LB - β
  have hH₀ : 0 < H₀ := by simp only [H₀]; linarith
  have hd : 0 < E' - H₀ / 10000 := by
    rw [lt_div_iff₀ hH₀] at hδ; linarith
  set ε := (E' - H₀ / 10000) / 4
  have hε : 0 < ε := by positivity
  have ha : 0 < E' - ε := by
    have : 0 < E' := by simp only [E']; linarith
    have : ε < E' := by simp only [ε]; nlinarith
    linarith
  have hHε : 0 < H₀ + ε := by linarith
  refine ⟨(E' - ε) / (H₀ + ε), ?_, ?_⟩
  · rw [lt_div_iff₀ hHε]; simp only [ε]; nlinarith
  · have hirr := irrational_of_rates h hE A B hAB
    have herr : ∀ᶠ N : ℕ in atTop, |((readout N A B).den : ℝ) * alpha A B - (readout N A B).num|
        ≤ exp (-((E' - ε) * N)) := by
      filter_upwards [linform_decay h A B ε hε, eventually_w0_ne h hE] with N hN h0
      rw [readout_eq_PQ N A B h0]
      refine (abs_den_mul_sub_num_le _ _ (Qd_ne N h0) _).trans (hN.trans (le_of_eq ?_))
      congr 1; simp only [E']; ring
    have hden : ∀ᶠ N : ℕ in atTop, Real.log ((readout N A B).den : ℝ) ≤ (H₀ + ε) * N := by
      filter_upwards [log_den_bound h A B ε hε, eventually_w0_ne h hE] with N hN h0
      exact hN h0
    exact delta_lower_bound (alpha A B) hirr (fun N => readout N A B) _ _ ha hHε herr hden

end Zeta2L2Chi3
