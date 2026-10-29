/-
# The telescoping identity for the forward (5F4) transport

For `j ∈ {0,1,2,3}` put
`G_j(t) = R_n(t) N_j(n,t) / (4 c_num(n) D_M(n) rden(n,t))`, written with the denominator
`RDen (n+1) t · rdenA(n,t) = RDen n t · rden(n,t)` (`Gf`).  Then
`t^j R_{n+1}(t) - c(n)⁻¹ ∑_l M_{lj}(n) t^l R_n(t) = G_j(t) - G_j(t-1)` wherever the finitely many
denominators involved are nonzero (`fwd_tele`).

We also record the product forms of the denominators of `R_m` and of `G_j` as products over
finite sets of poles (`DF_eq`, `DG_eq`), and positivity of `c_num`, `c_den`, `D_M` at `n ≥ 0`.
-/
import Zeta2L2Chi3.FCert0
import Zeta2L2Chi3.FCert1
import Zeta2L2Chi3.FCert2
import Zeta2L2Chi3.FCert3
import Zeta2L2Chi3.FShift

open Finset Polynomial

noncomputable section

namespace Zeta2L2Chi3

/-! ### The certificates -/

/-- the forward certificate polynomials -/
def FNcert : Fin 4 → PE := ![FNcert0, FNcert1, FNcert2, FNcert3]

theorem FNcert_check (j : Fin 4) : ∃ B, (fcertPE j 4 (FNcert j)).check B := by
  fin_cases j
  · exact ⟨_, fcert0_check⟩
  · exact ⟨_, fcert1_check⟩
  · exact ⟨_, fcert2_check⟩
  · exact ⟨_, fcert3_check⟩

lemma val_frnumInt (n t : ℝ) : (prodPE frnumInt).val n t = (fK1 : ℝ) * frnumR n t := by
  simp only [val_prodPE, frnumInt, List.map_append, List.map_map, List.prod_append]
  simp [frnumR, fK1, List.range_succ, Finset.prod_range_succ, Function.comp_def]
  ring

lemma val_frdenInt (n t : ℝ) :
    (prodPE frdenInt).val n t = 4 * (frdenAR n t * frdenBR n t) := by
  simp only [val_prodPE, frdenInt, List.map_append, List.map_map, List.prod_append]
  simp [frdenAR, frdenBR, List.range_succ, Finset.prod_range_succ, Function.comp_def]
  ring

lemma val_fBsInt (n t : ℝ) : (prodPE fBsInt).val n t = 6 * (fBsNR n t * fBsDR n t) := by
  simp [fBsInt, fBsNR, fBsDR]; ring

lemma val_fAsInt (n t : ℝ) : (prodPE fAsInt).val n t = 6 * (fAsNR n t * fAsDR n t) := by
  simp [fAsInt, fAsNR, fAsDR]; ring

lemma val_sumMPE (j : Fin 4) (n t : ℝ) :
    (sumMPE j).val n t = ∑ l : Fin 4, hornerR (Data.Mnum l j) n * t ^ (l : ℕ) := by
  simp [sumMPE, PE.val, litVal, val_spowPE, Fin.sum_univ_four]

/-- **The forward certificate identity**, in rational form. -/
theorem fcert_identity (j : Fin 4) (Nc : PE) (B : ℤ) (h : (fcertPE j 4 Nc).check B) (n t : ℝ) :
    Nc.val n t * ((frdenAR n (t - 1) * frdenBR n (t - 1)) * (fAsNR n t * fAsDR n t)) -
      (fBsNR n t * fBsDR n t) * (frdenAR n t * frdenBR n t) * Nc.val n (t - 1) =
    4 * (hornerR (Data.cnum 0 0) n * hornerR Data.Mden n * t ^ (j : ℕ) * frnumR n t -
      hornerR Data.cden n * (frdenAR n t * frdenBR n t) *
        ∑ l : Fin 4, hornerR (Data.Mnum l j) n * t ^ (l : ℕ)) *
      ((frdenAR n (t - 1) * frdenBR n (t - 1)) * (fAsNR n t * fAsDR n t)) := by
  have key := PE.eq_zero_of_check _ B h n t
  simp only [fcertPE, PE.val, val_frnumInt, val_frdenInt, val_fBsInt, val_fAsInt, val_sumMPE,
    val_spowPE] at key
  simp only [litVal, hornerR] at key
  have hK : (fK1 : ℝ) ≠ 0 := by norm_num [fK1]
  apply mul_left_cancel₀ (show (96 : ℝ) * fK1 ≠ 0 from mul_ne_zero (by norm_num) hK)
  push_cast at key ⊢
  linear_combination key

/-! ### The telescoping identity -/

/-- `c(n)` -/
def cval (n : ℕ) : ℝ := hornerR (Data.cnum 0 0) (n : ℝ) / hornerR Data.cden (n : ℝ)

/-- `M(n)_{lj}` -/
def Mval (n : ℕ) (l j : Fin 4) : ℝ := hornerR (Data.Mnum l j) (n : ℝ) / hornerR Data.Mden (n : ℝ)

/-- the normalising constant `1 / (4 c_num D_M)` -/
def κF (n : ℕ) : ℝ := 1 / (4 * hornerR (Data.cnum 0 0) (n : ℝ) * hornerR Data.Mden (n : ℝ))

/-- the certificate quotient `G_j(t) = R_n(t) N_j(n,t) / (4 c_num D_M rden(n,t))` -/
def Gf (n : ℕ) (j : Fin 4) (t : ℝ) : ℝ :=
  κF n * RNum n t * (FNcert j).val (n : ℝ) t / (RDen (n + 1) t * frdenAR n t)

/-- **The telescoping identity.** -/
theorem fwd_tele (n : ℕ) (j : Fin 4) (t : ℝ) (hD : RDen n t ≠ 0) (_hD1 : RDen n (t - 1) ≠ 0)
    (hA : frdenAR n t ≠ 0) (hA1 : frdenAR n (t - 1) ≠ 0) (hB : frdenBR n t ≠ 0)
    (hB1 : frdenBR n (t - 1) ≠ 0) (hAsN : fAsNR n t ≠ 0) (hAsD : fAsDR n t ≠ 0) :
    t ^ (j : ℕ) * RNum (n + 1) t / RDen (n + 1) t -
      ∑ l : Fin 4, (cval n)⁻¹ * Mval n l j * (t ^ (l : ℕ) * RNum n t / RDen n t) =
    Gf n j t - Gf n j (t - 1) := by
  obtain ⟨B, hB'⟩ := FNcert_check j
  have hc := fcert_identity j (FNcert j) B hB' (n : ℝ) t
  have hcn : hornerR (Data.cnum 0 0) (n : ℝ) ≠ 0 := (cnum_pos n).ne'
  have hcd : hornerR Data.cden (n : ℝ) ≠ 0 := (cden_pos n).ne'
  have hMd : hornerR Data.Mden (n : ℝ) ≠ 0 := (Mden_pos n).ne'
  have hBsD : fBsDR n t ≠ 0 := by
    intro h0
    have := RDen_shift n t
    rw [h0, mul_zero] at this
    exact mul_ne_zero hD hAsD this.symm
  have e1 : RNum (n + 1) t = RNum n t * frnumR n t / frdenAR n t := by
    rw [eq_div_iff hA]; exact RNum_succ n t
  have e2 : RDen (n + 1) t = RDen n t * frdenBR n t := RDen_succ n t
  have e3 : RDen (n + 1) (t - 1) = RDen n (t - 1) * frdenBR n (t - 1) := RDen_succ n (t - 1)
  have e4 : RNum n (t - 1) = RNum n t * fBsNR n t / fAsNR n t := by
    rw [eq_div_iff hAsN]; exact RNum_shift n t
  have e5 : RDen n (t - 1) = RDen n t * fAsDR n t / fBsDR n t := by
    rw [eq_div_iff hBsD]; exact RDen_shift n t
  simp only [Gf, κF, cval, Mval]
  rw [e1, e2, e3, e4, e5]
  rw [Fin.sum_univ_four] at hc ⊢
  generalize (FNcert j).val (n : ℝ) t = N at hc ⊢
  generalize (FNcert j).val (n : ℝ) (t - 1) = N1 at hc ⊢
  generalize RNum n t = P
  generalize RDen n t = D at hD ⊢
  generalize frnumR n t = rn at hc ⊢
  generalize frdenAR n t = rA at hc hA ⊢
  generalize frdenBR n t = rB at hc hB ⊢
  generalize frdenAR n (t - 1) = rA1 at hc hA1 ⊢
  generalize frdenBR n (t - 1) = rB1 at hc hB1 ⊢
  generalize fAsNR n t = aN at hc hAsN ⊢
  generalize fAsDR n t = aD at hc hAsD ⊢
  generalize fBsNR n t = bN at hc ⊢
  generalize fBsDR n t = bD at hc hBsD ⊢
  generalize hornerR (Data.cnum 0 0) (n : ℝ) = cn at hc hcn ⊢
  generalize hornerR Data.cden (n : ℝ) = cd at hc hcd ⊢
  generalize hornerR Data.Mden (n : ℝ) = Md at hc hMd ⊢
  generalize hornerR (Data.Mnum 0 j) (n : ℝ) = m0 at hc ⊢
  generalize hornerR (Data.Mnum 1 j) (n : ℝ) = m1 at hc ⊢
  generalize hornerR (Data.Mnum 2 j) (n : ℝ) = m2 at hc ⊢
  generalize hornerR (Data.Mnum 3 j) (n : ℝ) = m3 at hc ⊢
  have E1 : 1 / (4 * cn * Md) * P * N / (D * rB * rA) -
      1 / (4 * cn * Md) * (P * bN / aN) * N1 / (D * aD / bD * rB1 * rA1) =
      P * (N * ((rA1 * rB1) * (aN * aD)) - (bN * bD) * (rA * rB) * N1) /
        (4 * cn * Md * D * (rA * rB) * ((rA1 * rB1) * (aN * aD))) := by
    field_simp
  rw [E1, hc]
  field_simp

end Zeta2L2Chi3
