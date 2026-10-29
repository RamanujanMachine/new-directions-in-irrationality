/-
# Nonvanishing (NV01, NV02)

`T(n) = Q(n)^{-T}`.  The determinant `det[e₀, T(n)e₀, T(n)T(n+1)e₀]` is, up to a nonzero scalar,
the value at `x = n` of a polynomial `P(x) = e(x, x+1)` which is nonzero at `x = 0`; hence it
vanishes for only finitely many `n` (NV01).  Consequently any nonzero real row `ρ` has
`ρ · v_N ≠ 0` for infinitely many `N` (NV02).
-/
import Zeta2L2Chi3.Matrices

open Matrix Filter Polynomial

namespace Zeta2L2Chi3

/-! ### Checker expressions for `3×3` matrix algebra -/

def adjPE (m : Fin 3 → Fin 3 → PE) : Fin 3 → Fin 3 → PE :=
  ![![PE.sub (PE.mul (m 1 1) (m 2 2)) (PE.mul (m 1 2) (m 2 1)),
      PE.sub (PE.mul (m 0 2) (m 2 1)) (PE.mul (m 0 1) (m 2 2)),
      PE.sub (PE.mul (m 0 1) (m 1 2)) (PE.mul (m 0 2) (m 1 1))],
    ![PE.sub (PE.mul (m 1 2) (m 2 0)) (PE.mul (m 1 0) (m 2 2)),
      PE.sub (PE.mul (m 0 0) (m 2 2)) (PE.mul (m 0 2) (m 2 0)),
      PE.sub (PE.mul (m 0 2) (m 1 0)) (PE.mul (m 0 0) (m 1 2))],
    ![PE.sub (PE.mul (m 1 0) (m 2 1)) (PE.mul (m 1 1) (m 2 0)),
      PE.sub (PE.mul (m 0 1) (m 2 0)) (PE.mul (m 0 0) (m 2 1)),
      PE.sub (PE.mul (m 0 0) (m 1 1)) (PE.mul (m 0 1) (m 1 0))]]

/-- `(Mᵀ v)_i = ∑_j M_{j i} v_j`. -/
def tMulVecPE (m : Fin 3 → Fin 3 → PE) (u : Fin 3 → PE) : Fin 3 → PE :=
  fun i => PE.add (PE.add (PE.mul (m 0 i) (u 0)) (PE.mul (m 1 i) (u 1))) (PE.mul (m 2 i) (u 2))

/-- determinant of the matrix with rows `a, b, c`. -/
def det3RowsPE (a b c : Fin 3 → PE) : PE :=
  PE.add (PE.sub (PE.mul (a 0) (PE.sub (PE.mul (b 1) (c 2)) (PE.mul (b 2) (c 1))))
    (PE.mul (a 1) (PE.sub (PE.mul (b 0) (c 2)) (PE.mul (b 2) (c 0)))))
    (PE.mul (a 2) (PE.sub (PE.mul (b 0) (c 1)) (PE.mul (b 1) (c 0))))

def evalMat {R : Type*} [CommRing R] (m : Fin 3 → Fin 3 → PE) (x s : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => (m i j).val x s

lemma adjPE_val {R : Type*} [CommRing R] (m : Fin 3 → Fin 3 → PE) (x s : R) (i j : Fin 3) :
    (adjPE m i j).val x s = (evalMat m x s).adjugate i j := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp [adjPE, evalMat, PE.val] <;> ring

lemma tMulVecPE_val {R : Type*} [CommRing R] (m : Fin 3 → Fin 3 → PE) (u : Fin 3 → PE) (x s : R)
    (i : Fin 3) :
    (tMulVecPE m u i).val x s = ((evalMat m x s)ᵀ *ᵥ fun j => (u j).val x s) i := by
  simp [tMulVecPE, PE.val, evalMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma det3RowsPE_val {R : Type*} [CommRing R] (a b c : Fin 3 → PE) (x s : R) :
    (det3RowsPE a b c).val x s =
      (Matrix.of ![fun j => (a j).val x s, fun j => (b j).val x s, fun j => (c j).val x s]).det := by
  rw [Matrix.det_fin_three]; simp [det3RowsPE, PE.val]; ring

/-! ### The polynomial `x ↦ e(x, x + c)` -/

noncomputable def toPolyQ (l : List ℤ) : ℚ[X] := (toPoly l).map (Int.castRingHom ℚ)

lemma eval_toPolyQ (l : List ℤ) (x : ℚ) : (toPolyQ l).eval x = hornerR l x := by
  rw [toPolyQ, eval_map, eval₂_toPoly]

noncomputable def litDiag : List (List ℤ) → ℤ → ℚ[X]
  | [], _ => 0
  | l :: ls, c => toPolyQ l + (X + Polynomial.C (c : ℚ)) * litDiag ls c

noncomputable def PE.polyDiag : PE → ℤ → ℚ[X]
  | .lit L, c => litDiag L c
  | .add a b, c => a.polyDiag c + b.polyDiag c
  | .sub a b, c => a.polyDiag c - b.polyDiag c
  | .mul a b, c => a.polyDiag c * b.polyDiag c
  | .shift a, c => a.polyDiag (c - 1)

lemma PE.eval_polyDiag (e : PE) (c : ℤ) (x : ℚ) : (e.polyDiag c).eval x = e.val x (x + c) := by
  induction e generalizing c with
  | lit L =>
    simp only [PE.polyDiag, PE.val]
    induction L with
    | nil => simp [litDiag, litVal]
    | cons l ls ih => simp [litDiag, litVal, ih, eval_toPolyQ]
  | add a b iha ihb => simp [PE.polyDiag, PE.val, iha, ihb]
  | sub a b iha ihb => simp [PE.polyDiag, PE.val, iha, ihb]
  | mul a b iha ihb => simp [PE.polyDiag, PE.val, iha, ihb]
  | shift a ih => simp [PE.polyDiag, PE.val, ih]; ring_nf

/-- A polynomial nonzero at one point is nonzero at all large naturals. -/
lemma eventually_eval_ne_zero (p : ℚ[X]) (x₀ : ℚ) (h : p.eval x₀ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, p.eval (N : ℚ) ≠ 0 := by
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have hfin : (p.roots.toFinset : Set ℚ).Finite := Finset.finite_toSet _
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine eventually_atTop.2 ⟨⌈M⌉₊ + 1, fun N hN hz => ?_⟩
  have hroot : (N : ℚ) ∈ (p.roots.toFinset : Set ℚ) := by
    simp [Multiset.mem_toFinset, mem_roots hp, IsRoot, hz]
  have := hM hroot
  have : (⌈M⌉₊ : ℚ) + 1 ≤ N := by exact_mod_cast hN
  have := Nat.le_ceil M
  linarith

/-! ### NV01 -/

/-- `T(n) = Q(n)^{-T}`. -/
noncomputable def T (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := (Q n)ᵀ⁻¹

/-- The numerator matrix `Q̃(n)`. -/
def Qt (n : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j => hornerR (Data.Qnum i j) n

lemma Q_eq_smul (n : ℕ) : Q n = (hornerR Data.Qden (n : ℚ))⁻¹ • Qt n := by
  ext i j; simp [Q, Qt, div_eq_inv_mul]

lemma det_Qt_ne (n : ℕ) : (Qt n).det ≠ 0 := (det_Qnum_pos n).ne'

lemma Qinv_eq (n : ℕ) :
    (Q n)⁻¹ = (hornerR Data.Qden (n : ℚ) / (Qt n).det) • (Qt n).adjugate := by
  have hD : hornerR Data.Qden (n : ℚ) ≠ 0 := (Qden_pos _ (by positivity)).ne'
  have hd := det_Qt_ne n
  apply Matrix.inv_eq_left_inv
  rw [Q_eq_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.adjugate_mul, smul_smul]
  have : hornerR Data.Qden (n : ℚ) / (Qt n).det * (hornerR Data.Qden (n : ℚ))⁻¹ * (Qt n).det = 1 := by
    field_simp
  rw [this, one_smul]

lemma T_eq (n : ℕ) : T n = (hornerR Data.Qden (n : ℚ) / (Qt n).det) • ((Qt n).adjugate)ᵀ := by
  rw [T, ← Matrix.transpose_nonsing_inv, Qinv_eq, Matrix.transpose_smul]

/-- Rows of the `Q̃(n)` (in `n`) and `Q̃(n+1)` (in the second variable) as expressions. -/
def QnPE : Fin 3 → Fin 3 → PE := fun i j => PE.lit [Data.Qnum i j]
def QsPE : Fin 3 → Fin 3 → PE := fun i j => PE.lit ((Data.Qnum i j).map fun c => [c])

lemma QnPE_val (x s : ℚ) (i j : Fin 3) : (QnPE i j).val x s = hornerR (Data.Qnum i j) x := by
  simp [QnPE, PE.val, litVal]

lemma litVal_map_singleton (l : List ℤ) (x s : ℚ) :
    litVal (l.map fun c => [c]) x s = hornerR l s := by
  induction l with
  | nil => simp [litVal, hornerR]
  | cons c cs ih => simp [litVal, hornerR, ih]

lemma QsPE_val (x s : ℚ) (i j : Fin 3) : (QsPE i j).val x s = hornerR (Data.Qnum i j) s := by
  simp [QsPE, PE.val, litVal_map_singleton]

def e0PE : Fin 3 → PE := ![PE.lit [[1]], PE.lit [[0]], PE.lit [[0]]]

/-- `det[e₀, adj(Q̃(x))ᵀe₀, adj(Q̃(x))ᵀ adj(Q̃(s))ᵀ e₀]`. -/
def nvPE : PE :=
  det3RowsPE e0PE (tMulVecPE (adjPE QnPE) e0PE)
    (tMulVecPE (adjPE QnPE) (tMulVecPE (adjPE QsPE) e0PE))

theorem nvPE_ne : nvPE.val (0 : ℤ) (1 : ℤ) ≠ 0 := by decide +kernel

lemma e0PE_val (x s : ℚ) : (fun j => (e0PE j).val x s) = e0 := by
  ext j; fin_cases j <;> simp [e0PE, e0, PE.val, litVal, hornerR]

lemma evalMat_QnPE (x s : ℚ) : evalMat QnPE x s = Qt x := by
  ext i j; simp [evalMat, QnPE_val, Qt]

lemma evalMat_QsPE (x s : ℚ) : evalMat QsPE x s = Qt s := by
  ext i j; simp [evalMat, QsPE_val, Qt]

lemma evalMat_adj_Qn (x s : ℚ) : evalMat (adjPE QnPE) x s = (Qt x).adjugate := by
  ext a b; simp only [evalMat, Matrix.of_apply]; rw [adjPE_val, evalMat_QnPE]

lemma evalMat_adj_Qs (x s : ℚ) : evalMat (adjPE QsPE) x s = (Qt s).adjugate := by
  ext a b; simp only [evalMat, Matrix.of_apply]; rw [adjPE_val, evalMat_QsPE]

lemma nvPE_val (x s : ℚ) :
    nvPE.val x s = (Matrix.of ![e0, ((Qt x).adjugate)ᵀ *ᵥ e0,
      ((Qt x).adjugate)ᵀ *ᵥ (((Qt s).adjugate)ᵀ *ᵥ e0)]).det := by
  have r1 : (fun j => (tMulVecPE (adjPE QnPE) e0PE j).val x s) = ((Qt x).adjugate)ᵀ *ᵥ e0 := by
    funext j; rw [tMulVecPE_val, evalMat_adj_Qn, e0PE_val]
  have r0 : (fun j => (tMulVecPE (adjPE QsPE) e0PE j).val x s) = ((Qt s).adjugate)ᵀ *ᵥ e0 := by
    funext j; rw [tMulVecPE_val, evalMat_adj_Qs, e0PE_val]
  have r2 : (fun j => (tMulVecPE (adjPE QnPE) (tMulVecPE (adjPE QsPE) e0PE) j).val x s) =
      ((Qt x).adjugate)ᵀ *ᵥ (((Qt s).adjugate)ᵀ *ᵥ e0) := by
    funext j; rw [tMulVecPE_val, evalMat_adj_Qn, r0]
  rw [nvPE, det3RowsPE_val, e0PE_val, r1, r2]

lemma det_rows_smul (u x y : Fin 3 → ℚ) (a b : ℚ) :
    (Matrix.of ![u, a • x, b • y]).det = a * b * (Matrix.of ![u, x, y]).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Pi.smul_apply, smul_eq_mul]
  ring

/-- The three-consecutive-column determinant. -/
noncomputable def nvDet (N : ℕ) : ℚ := (Matrix.of ![e0, T N *ᵥ e0, T N *ᵥ (T (N + 1) *ᵥ e0)]).det

lemma nvDet_eq (N : ℕ) : ∃ a : ℚ, a ≠ 0 ∧ nvDet N = a * nvPE.val (N : ℚ) ((N : ℚ) + 1) := by
  set a₀ := hornerR Data.Qden (N : ℚ) / (Qt N).det
  set a₁ := hornerR Data.Qden ((N + 1 : ℕ) : ℚ) / (Qt (N + 1 : ℕ)).det
  have ha₀ : a₀ ≠ 0 := div_ne_zero (Qden_pos _ (by positivity)).ne' (det_Qt_ne N)
  have ha₁ : a₁ ≠ 0 := div_ne_zero (Qden_pos _ (by positivity)).ne' (det_Qt_ne (N + 1))
  refine ⟨a₀ * a₀ * a₁, by positivity, ?_⟩
  rw [nvPE_val, nvDet, T_eq, T_eq]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  rw [det_rows_smul]
  have : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  simp only [a₀, a₁, this]
  ring

theorem nvDet_eventually_ne : ∀ᶠ N in atTop, nvDet N ≠ 0 := by
  have h0 : (nvPE.polyDiag 1).eval 0 ≠ 0 := by
    rw [PE.eval_polyDiag]
    have hq := PE.val_map (Int.castRingHom ℚ) nvPE 0 1
    simp only [map_zero, map_one, eq_intCast] at hq
    rw [show (0 : ℚ) + ((1 : ℤ) : ℚ) = 1 by norm_num, ← hq]
    exact_mod_cast nvPE_ne
  filter_upwards [eventually_eval_ne_zero _ 0 h0] with N hN
  obtain ⟨a, ha, he⟩ := nvDet_eq N
  rw [he]
  refine mul_ne_zero ha ?_
  rw [PE.eval_polyDiag] at hN
  simpa using hN

/-! ### NV02 -/

lemma v_succ (N : ℕ) : v (N + 1) = (W N)ᵀ⁻¹ *ᵥ (T N *ᵥ e0) := by
  rw [v, W, Matrix.transpose_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, T]

lemma v_succ_succ (N : ℕ) : v (N + 2) = (W N)ᵀ⁻¹ *ᵥ (T N *ᵥ (T (N + 1) *ᵥ e0)) := by
  rw [v, W, W, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mulVec_mulVec]
  rfl

/-- Real cast of a rational vector. -/
def castV (u : Fin 3 → ℚ) : Fin 3 → ℝ := fun j => (u j : ℝ)

lemma castV_mulVec (M : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 3 → ℚ) :
    castV (M *ᵥ u) = (M.map (Rat.cast : ℚ → ℝ)) *ᵥ castV u := by
  ext i; simp [castV, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **NV02.** A nonzero real row cannot annihilate `v_N` for all large `N`. -/
theorem frequently_dot_v_ne (ρ : Fin 3 → ℝ) (hρ : ρ ≠ 0) :
    ∃ᶠ N in atTop, ρ ⬝ᵥ castV (v N) ≠ 0 := by
  rw [Filter.Frequently]
  intro hall
  obtain ⟨N, hN⟩ := (hall.and (nvDet_eventually_ne)).exists_forall_of_atTop
  obtain ⟨h0, hdet⟩ := hN N le_rfl
  have h1 := (hN (N + 1) (by omega)).1
  have h2 := (hN (N + 2) (by omega)).1
  push Not at h0 h1 h2
  set A : Matrix (Fin 3) (Fin 3) ℝ := ((W N)ᵀ⁻¹).map (Rat.cast : ℚ → ℝ)
  set σ : Fin 3 → ℝ := ρ ᵥ* A
  have hv : ∀ u : Fin 3 → ℚ, ρ ⬝ᵥ castV ((W N)ᵀ⁻¹ *ᵥ u) = σ ⬝ᵥ castV u := by
    intro u; rw [castV_mulVec, Matrix.dotProduct_mulVec]
  rw [v] at h0; rw [v_succ] at h1; rw [v_succ_succ] at h2
  rw [hv] at h0 h1 h2
  -- the rows `e₀, T e₀, T T e₀` span, so `σ = 0`
  set M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![e0, T N *ᵥ e0, T N *ᵥ (T (N + 1) *ᵥ e0)]
  have hrow : ∀ i, ((M.map (Rat.cast : ℚ → ℝ)) *ᵥ σ) i = σ ⬝ᵥ castV (M i) := by
    intro i; simp [Matrix.mulVec, dotProduct, castV, mul_comm]
  have hMσ : (M.map (Rat.cast : ℚ → ℝ)) *ᵥ σ = 0 := by
    ext i; rw [hrow]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hMdet : (M.map (Rat.cast : ℚ → ℝ)).det ≠ 0 := by
    have := RingHom.map_det (Rat.castHom ℝ) M
    rw [show M.map (Rat.cast : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix M from rfl, ← this]
    simpa [nvDet, M] using hdet
  have hσ : σ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMσ
  have hAdet : A.det ≠ 0 := by
    have := RingHom.map_det (Rat.castHom ℝ) ((W N)ᵀ⁻¹)
    rw [show A = (Rat.castHom ℝ).mapMatrix ((W N)ᵀ⁻¹) from rfl, ← this]
    rw [Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']
    exact (_root_.map_ne_zero _).2 (inv_ne_zero (det_W_ne N))
  exact hρ (Matrix.eq_zero_of_vecMul_eq_zero hAdet hσ)

end Zeta2L2Chi3
