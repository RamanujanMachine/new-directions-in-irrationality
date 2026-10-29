/-
# The forward/dual normalization (3.1): `f_n = (35/1944) Δ_n⁻¹ w_n` (FWD02)

`Y_n = Φ_n K(n)` (Φ_n = forward rows) satisfies `Y_{n+1} Q(n)ᵀ = Y_n` by the row transport
(`phi_transport`) and the pairing identity ALG03; hence `Y_n = Y_0 W_n^{-T}` and
`f_n = Y_n e₀ = Y_0 v_n`, with `Y_0 = -(1/3888) [D; (9/2)X + 3Y; 2Y]`.
-/
import Zeta2L2Chi3.FTransport
import Zeta2L2Chi3.FInit
import Zeta2L2Chi3.Alg03

open Matrix Finset

noncomputable section

namespace Zeta2L2Chi3

/-- the forward row matrix `Φ_n` (3 × 4) -/
def Phi (n : ℕ) : Matrix (Fin 3) (Fin 4) ℝ :=
  Matrix.of ![fun j => phi1 n j, fun j => phiT n j, fun j => phiH n j]

def Mmat (n : ℕ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => Mval n i j

def Qr (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := (Q n).map (Rat.cast : ℚ → ℝ)

lemma Phi_succ (n : ℕ) : Phi (n + 1) = (cval n)⁻¹ • (Phi n * Mmat n) := by
  ext i j
  obtain ⟨h1, h2, h3⟩ := phi_transport n j
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  fin_cases i <;> simp [Phi, Mmat, h1, h2, h3]

/-! ### ALG03 as a real matrix identity -/

lemma Kmat_eq (n : ℕ) (l : Fin 4) (m : Fin 3) :
    Kmat n l m = ((KL / Data.Kden l m : ℤ) : ℝ) * hornerR (Data.Knum l m) (n : ℝ) / 6 := by
  simp only [Kmat]
  fin_cases l <;> fin_cases m <;> simp [KL, Data.Kden] <;> ring

lemma Qr_apply (n : ℕ) (j m : Fin 3) :
    Qr n j m = hornerR (Data.Qnum j m) (n : ℝ) / hornerR Data.Qden (n : ℝ) := by
  simp only [Qr, Matrix.map_apply, Q, Rat.cast_div]
  have h := fun l => hornerR_map (Rat.castHom ℝ) l (n : ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at h
  rw [h, h]

lemma fin4_list : List.finRange 4 = [0, 1, 2, 3] := by decide
lemma fin3_list : List.finRange 3 = [0, 1, 2] := by decide

/-- **ALG03**: `M(n) K(n+1) Q(n)ᵀ = c(n) K(n)`, entrywise. -/
theorem alg03_real (n : ℕ) (i : Fin 4) (j : Fin 3) :
    ∑ l : Fin 4, ∑ m : Fin 3, Mval n i l * Kmat (n + 1) l m * Qr n j m = cval n * Kmat n i j := by
  have key := PE.eq_zero_of_check (K := ℝ) _ _ (alg03_check i j) 0 ((n : ℝ) + 1)
  simp only [alg03PE, KsPE, PE.val, litS_val, val_sumPE, fin4_list, fin3_list, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_nil, List.sum_cons, List.sum_nil, litVal, hornerR, add_sub_cancel_right,
    mul_zero, add_zero] at key
  have hcd : hornerR Data.cden (n : ℝ) ≠ 0 := (cden_pos n).ne'
  have hMd : hornerR Data.Mden (n : ℝ) ≠ 0 := (Mden_pos n).ne'
  have hQd : hornerR Data.Qden (n : ℝ) ≠ 0 := (Qden_pos (n : ℝ) (by positivity)).ne'
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, Kmat_eq, Qr_apply, Mval, cval, Nat.cast_succ]
  have h6 : (6 * hornerR Data.cden (n : ℝ) * hornerR Data.Mden (n : ℝ) * hornerR Data.Qden (n : ℝ)) ≠ 0 := by
    positivity
  rw [← sub_eq_zero]
  refine (mul_eq_zero_iff_right h6).mp ?_
  rw [← key]
  field_simp
  ring

/-- `M(n) K(n+1) Q(n)ᵀ = c(n) K(n)` as a matrix identity -/
lemma MKQ (n : ℕ) : Mmat n * (Kmat (n + 1) * (Qr n)ᵀ) = cval n • Kmat n := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, ← alg03_real n i j, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Mmat, Finset.sum_mul]
  exact Finset.sum_comm

/-! ### The matrices `Y_n = Φ_n K(n)` -/

/-- `Y_n = Φ_n K(n)` (3 × 3) -/
def Y (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Phi n * Kmat n

lemma cval_ne (n : ℕ) : cval n ≠ 0 := div_ne_zero (cnum_pos n).ne' (cden_pos n).ne'

lemma Y_succ (n : ℕ) : Y (n + 1) * (Qr n)ᵀ = Y n := by
  simp only [Y, Phi_succ, Matrix.smul_mul, Matrix.mul_assoc]
  rw [MKQ, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (cval_ne n), one_smul]

/-- `W_n` cast to `ℝ` -/
def Wr (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := (W n).map (Rat.cast : ℚ → ℝ)

lemma Wr_succ (n : ℕ) : Wr (n + 1) = Wr n * Qr n := by
  show (W n * Q n).map (Rat.castHom ℝ) = (W n).map (Rat.castHom ℝ) * (Q n).map (Rat.castHom ℝ)
  exact Matrix.map_mul

lemma Y_W (n : ℕ) : Y n * (Wr n)ᵀ = Y 0 := by
  induction n with
  | zero => simp [Wr, W]
  | succ n ih => rw [Wr_succ, Matrix.transpose_mul, ← Matrix.mul_assoc, Y_succ, ih]

lemma Wr_mulVec_v (n : ℕ) :
    (Wr n)ᵀ *ᵥ (fun k => (v n k : ℝ)) = fun k => (e0 k : ℝ) := by
  have h : (W n)ᵀ *ᵥ v n = e0 := by
    have hu : IsUnit (W n)ᵀ.det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (det_W_ne n)
    rw [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  funext k
  have := RingHom.map_mulVec (Rat.castHom ℝ) (W n)ᵀ (v n) k
  rw [h] at this
  rw [Wr, ← Matrix.transpose_map]
  exact this.symm

lemma Y_zero : Y 0 = -(A0.map (Rat.cast : ℚ → ℝ)) := by
  have hT := congrFun phiT_zero
  have hH := congrFun phiH_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y, Phi, Matrix.mul_apply, Fin.sum_univ_four, phi1_zero, hT, hH, a00, a01, Kmat,
      Data.Knum, Data.Kden, hornerR, A0] <;> norm_num

/-- **The normalization identity (3.1)**: `f_n = (35/1944) Δ_n⁻¹ w_n`. -/
theorem fvec_eq (n : ℕ) (i : Fin 3) :
    fvec n i = (((35 / 1944 : ℚ) * (Δ n)⁻¹ * w n i : ℚ) : ℝ) := by
  have hΔ : Δ n ≠ 0 := det_W_ne n
  have hw : (35 / 1944 : ℚ) * (Δ n)⁻¹ * w n i = -(A0 *ᵥ v n) i := by
    rw [w_eq_A0_v]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [hw]
  have h1 : fvec n i = (Y n *ᵥ (fun k => (e0 k : ℝ))) i := by
    fin_cases i <;>
      simp [fvec, Y, Phi, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three, e0]
  rw [h1, ← Wr_mulVec_v, Matrix.mulVec_mulVec, Y_W, Y_zero, Matrix.neg_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Zeta2L2Chi3
