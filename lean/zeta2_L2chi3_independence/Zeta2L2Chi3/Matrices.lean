/-
# The fixed MG55 trajectory: exact matrices, products, cofactors and readouts (ALG01, ALG05, END04)

All exact objects live over `ℚ`.

* `Q n` is the restricted `3×3` trajectory matrix (`Data.Qnum / Data.Qden`), shown equal to the
  entrywise numerator/denominator form of `data/exact_rational_data.json` (`Q_eq_json`).
* `W N = Q 0 ⋯ Q (N-1)`, `v N = (W N)⁻ᵀ e₀`.
* `Bhat n = (-1)ⁿ Bhat₀ W n` and `w n` = cross product of its columns `1, 2`.
* `readout N A B = (3(A+B) X + 2(A-B) Y)·v N / (3 D·v N)`.
-/
import Zeta2L2Chi3.Data
import Zeta2L2Chi3.Defs

open Matrix

namespace Zeta2L2Chi3

/-! ### Products of linear factors as checker expressions -/

/-- The linear form `c₀ + a n + b s`. -/
def linPE (c0 a b : ℤ) : PE := PE.lit [[c0, a], [b]]

/-- Product of a list of expressions. -/
def prodPE : List PE → PE
  | [] => PE.lit [[1]]
  | e :: es => PE.mul e (prodPE es)

@[simp] lemma val_linPE {R : Type*} [CommRing R] (c0 a b : ℤ) (n s : R) :
    (linPE c0 a b).val n s = c0 + a * n + b * s := by
  simp [linPE, PE.val, litVal, hornerR]; ring

@[simp] lemma val_prodPE {R : Type*} [CommRing R] (l : List PE) (n s : R) :
    (prodPE l).val n s = (l.map fun e => e.val n s).prod := by
  induction l with
  | nil => simp [prodPE, PE.val, litVal, hornerR]
  | cons e es ih => simp [prodPE, PE.val, ih]

/-- `c ∏ (a n + b)` for a factor list. -/
def factoredPE (c : ℤ) (fs : List (ℤ × ℤ)) : PE :=
  PE.mul (PE.lit [[c]]) (prodPE (fs.map fun f => linPE f.2 f.1 0))

lemma val_factoredPE {R : Type*} [CommRing R] (c : ℤ) (fs : List (ℤ × ℤ)) (n s : R) :
    (factoredPE c fs).val n s = c * (fs.map fun f => (f.1 * n + f.2 : R)).prod := by
  simp only [factoredPE, PE.val, val_prodPE, List.map_map]
  simp [litVal, hornerR, Function.comp_def, add_comm, mul_comm]

lemma factored_pos {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (c : ℤ) (fs : List (ℤ × ℤ)) (hc : 0 < c) (hfs : ∀ f ∈ fs, 0 ≤ f.1 ∧ 0 < f.2) (x : R)
    (hx : 0 ≤ x) : 0 < (c : R) * (fs.map fun f => (f.1 * x + f.2 : R)).prod := by
  refine mul_pos (by exact_mod_cast hc) (List.prod_pos fun y hy => ?_)
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
  obtain ⟨h1, h2⟩ := hfs f hf
  have : (0 : R) ≤ f.1 := by exact_mod_cast h1
  have : (0 : R) < f.2 := by exact_mod_cast h2
  positivity

/-- A univariate polynomial identity `p = c ∏ (a n + b)`, as a checker expression. -/
def factorCheckPE (p : List ℤ) (c : ℤ) (fs : List (ℤ × ℤ)) : PE :=
  PE.sub (PE.lit [p]) (factoredPE c fs)

lemma hornerR_eq_factored {K : Type*} [Field K] [CharZero K] (p : List ℤ) (c : ℤ)
    (fs : List (ℤ × ℤ)) (B : ℤ) (h : (factorCheckPE p c fs).check B) (x : K) :
    hornerR p x = c * (fs.map fun f => (f.1 * x + f.2 : K)).prod := by
  have := PE.eq_zero_of_check _ B h x 0
  simp only [factorCheckPE, PE.val, val_factoredPE] at this
  simpa [litVal, sub_eq_zero] using this

/-! ### The matrix `Q` -/

theorem Qden_factored : (factorCheckPE Data.Qden Data.QdenConst Data.QdenLin).check (10 ^ 90) := by
  decide +kernel

lemma Qden_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) (hx : 0 ≤ x) :
    0 < hornerR Data.Qden x := by
  rw [hornerR_eq_factored _ _ _ _ Qden_factored]
  exact factored_pos _ _ (by decide) (by decide) x hx

/-- The restricted MG55 trajectory matrix `Q(n)`. -/
def Q (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => hornerR (Data.Qnum i j) (n : ℚ) / hornerR Data.Qden (n : ℚ)

/-- The entrywise numerator/denominator form of `data/exact_rational_data.json`. -/
def Qjson (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => hornerR (Data.QjsonNum i j) (n : ℚ) / hornerR (Data.QjsonDen i j) (n : ℚ)

/-- Cross-multiplied identities `Qnum · den_json = num_json · Qden`. -/
def QjsonPE (i j : Fin 3) : PE :=
  PE.sub (PE.mul (PE.lit [Data.Qnum i j]) (PE.lit [Data.QjsonDen i j]))
    (PE.mul (PE.lit [Data.QjsonNum i j]) (PE.lit [Data.Qden]))

theorem QjsonPE_check : ∀ i j : Fin 3, (QjsonPE i j).check (10 ^ 200) := by decide +kernel

theorem QjsonDen_factored : ∀ i j : Fin 3,
    (factorCheckPE (Data.QjsonDen i j) (Data.QjsonDenConst i j) (Data.QjsonDenLin i j)).check
      (10 ^ 90) := by decide +kernel

theorem QjsonDen_ne (i j : Fin 3) (n : ℕ) : hornerR (Data.QjsonDen i j) (n : ℚ) ≠ 0 := by
  rw [hornerR_eq_factored _ _ _ _ (QjsonDen_factored i j)]
  refine (factored_pos _ _ ?_ ?_ (n : ℚ) (by positivity)).ne'
  · revert i j; decide
  · revert i j; decide

theorem Q_eq_json (n : ℕ) : Q n = Qjson n := by
  ext i j
  have key := PE.eq_zero_of_check (K := ℚ) _ _ (QjsonPE_check i j) n 0
  simp only [QjsonPE, PE.val, litVal, mul_zero, add_zero] at key
  have h1 : hornerR Data.Qden (n : ℚ) ≠ 0 := (Qden_pos (n : ℚ) (by positivity)).ne'
  have h2 := QjsonDen_ne i j n
  simp only [Q, Qjson]
  rw [div_eq_div_iff h1 h2]
  linarith

/-! ### `det Q(n) > 0` -/

/-- `det` of a `3×3` matrix of literal polynomials, as a checker expression. -/
def det3PE (a : Fin 3 → Fin 3 → List ℤ) : PE :=
  let e := fun i j => PE.lit [a i j]
  PE.add (PE.sub (PE.mul (e 0 0) (PE.sub (PE.mul (e 1 1) (e 2 2)) (PE.mul (e 1 2) (e 2 1))))
    (PE.mul (e 0 1) (PE.sub (PE.mul (e 1 0) (e 2 2)) (PE.mul (e 1 2) (e 2 0)))))
    (PE.mul (e 0 2) (PE.sub (PE.mul (e 1 0) (e 2 1)) (PE.mul (e 1 1) (e 2 0))))

theorem Qdet_check :
    (PE.sub (det3PE Data.Qnum) (factoredPE Data.QdetConst Data.QdetLin)).check (10 ^ 400) := by
  decide +kernel

lemma det_Qnum_pos (n : ℕ) :
    0 < (Matrix.of fun i j => hornerR (Data.Qnum i j) (n : ℚ)).det := by
  have key := PE.eq_zero_of_check (K := ℚ) _ _ Qdet_check n 0
  simp only [det3PE, PE.val, litVal, mul_zero, add_zero, val_factoredPE] at key
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  have hpos := factored_pos (R := ℚ) Data.QdetConst Data.QdetLin (by decide) (by decide) n
    (by positivity)
  linarith

lemma det_Q_pos (n : ℕ) : 0 < (Q n).det := by
  have hQ : Q n = (hornerR Data.Qden (n : ℚ))⁻¹ • Matrix.of fun i j => hornerR (Data.Qnum i j) (n : ℚ) := by
    ext i j; simp [Q, div_eq_inv_mul]
  rw [hQ, Matrix.det_smul, Fintype.card_fin]
  exact mul_pos (pow_pos (inv_pos.2 (Qden_pos _ (by positivity))) 3) (det_Qnum_pos n)

lemma det_Q_ne (n : ℕ) : (Q n).det ≠ 0 := (det_Q_pos n).ne'

/-! ### Products, the dual vector and the endpoint matrices -/

/-- `W N = Q(0) Q(1) ⋯ Q(N-1)`. -/
def W : ℕ → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => 1
  | N + 1 => W N * Q N

lemma det_W_pos (N : ℕ) : 0 < (W N).det := by
  induction N with
  | zero => simp [W]
  | succ N ih => rw [W, Matrix.det_mul]; exact mul_pos ih (det_Q_pos N)

lemma det_W_ne (N : ℕ) : (W N).det ≠ 0 := (det_W_pos N).ne'

/-- `Δ N = det W N = ∏_{j<N} det Q(j)`. -/
def Δ (N : ℕ) : ℚ := (W N).det

/-- The initial endpoint matrix `B̂₀` (rows `B₀, B_T, B_H`, columns `0,1,2`). -/
def Bhat0 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-789349/1680, -108221/140, -35787/35;
     1647/35, 3636/35, 5328/35;
     768/35, -1116/35, -2808/35]

lemma det_Bhat0 : Bhat0.det = -1944 / 35 := by
  rw [Matrix.det_fin_three]; simp [Bhat0]; norm_num

/-- `B̂_{n+1} = -B̂_n Q(n)`. -/
def Bhat : ℕ → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => Bhat0
  | n + 1 => -(Bhat n * Q n)

lemma Bhat_eq (n : ℕ) : Bhat n = (-1 : ℚ) ^ n • (Bhat0 * W n) := by
  induction n with
  | zero => simp [Bhat, W]
  | succ n ih => rw [Bhat, ih, W, pow_succ]; simp [Matrix.mul_assoc]

lemma det_Bhat (n : ℕ) : (Bhat n).det = (-1 : ℚ) ^ n * (-1944 / 35) * Δ n := by
  rw [Bhat_eq, Matrix.det_smul, Matrix.det_mul, det_Bhat0, Fintype.card_fin, Δ, ← pow_mul]
  have : ((-1 : ℚ) ^ (n * 3)) = (-1) ^ n := by
    rw [pow_mul]; rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h] <;> norm_num
  rw [this]; ring

/-- The fixed readout rows. -/
def rowD : Fin 3 → ℚ := ![243648, -498096, 264600]
def rowX : Fin 3 → ℚ := ![190344, -389162, 206743]
def rowY : Fin 3 → ℚ := ![400824, -819330, 435234]

def e0 : Fin 3 → ℚ := ![1, 0, 0]

/-- The dual vector `v_N = W_N^{-T} e₀`. -/
noncomputable def v (N : ℕ) : Fin 3 → ℚ := (W N)ᵀ⁻¹ *ᵥ e0

/-- The cofactor vector `w_n` = cross product of columns `1` and `2` of `B̂_n`. -/
def w (n : ℕ) : Fin 3 → ℚ :=
  ![Bhat n 1 1 * Bhat n 2 2 - Bhat n 2 1 * Bhat n 1 2,
    Bhat n 2 1 * Bhat n 0 2 - Bhat n 0 1 * Bhat n 2 2,
    Bhat n 0 1 * Bhat n 1 2 - Bhat n 1 1 * Bhat n 0 2]

/-- `w` is the first row of the adjugate. -/
lemma w_eq_adjugate (n : ℕ) (j : Fin 3) : w n j = (Bhat n).adjugate 0 j := by
  rw [Matrix.adjugate_fin_three]; fin_cases j <;> simp [w] <;> ring

/-- `A₀ = B̂₀^{-T}`, explicitly. -/
def A0 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![188/3, -1153/9, 1225/18;
     6355/12, -155897/144, 55211/96;
     5567/27, -136555/324, 72539/324]

lemma A0_spec : Bhat0ᵀ * A0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Bhat0, A0, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma A0_eq : A0 = Bhat0ᵀ⁻¹ := by
  exact (Matrix.inv_eq_right_inv A0_spec).symm

/-- The nine rational readout identities. -/
lemma rowD_eq : rowD = fun j => 3888 * A0 0 j := by
  ext j; fin_cases j <;> simp [rowD, A0] <;> norm_num
lemma rowX_eq : rowX = fun j => 3888 * (4 * A0 1 j - 6 * A0 2 j) / 18 := by
  ext j; fin_cases j <;> simp [rowX, A0] <;> norm_num
lemma rowY_eq : rowY = fun j => 3888 * A0 2 j / 2 := by
  ext j; fin_cases j <;> simp [rowY, A0] <;> norm_num

/-! ### Cofactor form of the dual vector and the readout (ALG05, END04) -/

lemma adjugate_eq_det_smul_inv {M : Matrix (Fin 3) (Fin 3) ℚ} (h : M.det ≠ 0) :
    M.adjugate = M.det • M⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ h, one_smul]

lemma v_apply (N : ℕ) (j : Fin 3) : v N j = (W N)⁻¹ 0 j := by
  rw [v, ← Matrix.transpose_nonsing_inv]
  simp [Matrix.mulVec, dotProduct, e0, Fin.sum_univ_three]

/-- `w_n = (det B̂₀) Δ_n · A₀ v_n` with `A₀ = B̂₀^{-T}`. -/
theorem w_eq_A0_v (n : ℕ) : w n = ((-1944 / 35 : ℚ) * Δ n) • (A0 *ᵥ v n) := by
  have hB : (Bhat n).det ≠ 0 := by
    rw [det_Bhat]; have := det_W_ne n; unfold Δ; positivity
  have hBinv : (Bhat n)⁻¹ = (-1 : ℚ) ^ n • ((W n)⁻¹ * Bhat0⁻¹) := by
    apply Matrix.inv_eq_left_inv
    have h0 : IsUnit Bhat0.det := by rw [det_Bhat0]; norm_num
    have hW : IsUnit (W n).det := isUnit_iff_ne_zero.2 (det_W_ne n)
    rw [Bhat_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Bhat0⁻¹, Matrix.nonsing_inv_mul _ h0, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hW, ← pow_add, ← two_mul, pow_mul]
    simp
  ext j
  rw [w_eq_adjugate, adjugate_eq_det_smul_inv hB, hBinv, det_Bhat, A0_eq,
    ← Matrix.transpose_nonsing_inv]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Pi.smul_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, v_apply]
  have h2 : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have hs : ∑ x, (W n)⁻¹ 0 x * Bhat0⁻¹ x j = ∑ x, Bhat0⁻¹ x j * (W n)⁻¹ 0 x :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hs]
  linear_combination (-1944 / 35 * Δ n * ∑ x, Bhat0⁻¹ x j * (W n)⁻¹ 0 x) * h2

lemma rowD_v (N : ℕ) : rowD ⬝ᵥ v N = 3888 * (A0 *ᵥ v N) 0 := by
  rw [rowD_eq]; simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma rowX_v (N : ℕ) :
    rowX ⬝ᵥ v N = 3888 * (4 * (A0 *ᵥ v N) 1 - 6 * (A0 *ᵥ v N) 2) / 18 := by
  rw [rowX_eq]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

lemma rowY_v (N : ℕ) : rowY ⬝ᵥ v N = 3888 * (A0 *ᵥ v N) 2 / 2 := by
  rw [rowY_eq]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The CMF readout `[3(A+B) X + 2(A-B) Y] v_N / (3 D v_N)`. -/
noncomputable def readout (N : ℕ) (A B : ℤ) : ℚ :=
  (3 * (A + B) * (rowX ⬝ᵥ v N) + 2 * (A - B) * (rowY ⬝ᵥ v N)) / (3 * (rowD ⬝ᵥ v N))

/-- Equation (2.3): the readout in terms of the cofactor vector. -/
theorem readout_eq_w (N : ℕ) (A B : ℤ) :
    readout N A B = 2 * ((A + B) * w N 1 - 3 * B * w N 2) / (9 * w N 0) := by
  have hc : ((-1944 / 35 : ℚ) * Δ N) ≠ 0 := mul_ne_zero (by norm_num) (det_W_ne N)
  have hΔ : Δ N ≠ 0 := det_W_ne N
  rw [readout, rowX_v, rowY_v, rowD_v, w_eq_A0_v]
  simp only [Pi.smul_apply, smul_eq_mul]
  set a := A0 *ᵥ v N
  by_cases ha : a 0 = 0
  · simp [ha]
  · field_simp
    ring

/-- `D v_N = 3888 w_{N,0} / ((det B̂₀) Δ_N)`. -/
theorem rowD_v_eq_w (N : ℕ) : rowD ⬝ᵥ v N = 3888 * w N 0 / ((-1944 / 35 : ℚ) * Δ N) := by
  have hΔ : Δ N ≠ 0 := det_W_ne N
  rw [rowD_v, w_eq_A0_v]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp

end Zeta2L2Chi3
