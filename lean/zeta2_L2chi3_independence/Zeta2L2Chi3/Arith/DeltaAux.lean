/-
# Auxiliary lemmas for `DeltaVal`: the one-step identity for `det Q(n)`

Both sides of `det Q(n) = C₀ g(n+1)/g(n) ∏ (∏_{i<A} (β + A n + i))^m` are products of linear
factors `a n + b`; after normalizing each factor to a primitive pair the two multisets of factors
agree (checked by `decide +kernel`).
-/
import Zeta2L2Chi3.Arith.Defs
import Zeta2L2Chi3.Matrices
import Zeta2L2Chi3.Dual

open Finset

namespace Zeta2L2Chi3.Arith

open Zeta2L2Chi3

/-- `∏ (a x + b)` over a list of pairs `(a, b)` -/
def PL (L : List (ℤ × ℤ)) (x : ℚ) : ℚ := (L.map fun f => (f.1 : ℚ) * x + f.2).prod

@[simp] lemma PL_nil (x : ℚ) : PL [] x = 1 := rfl
@[simp] lemma PL_cons (f : ℤ × ℤ) (L : List (ℤ × ℤ)) (x : ℚ) :
    PL (f :: L) x = ((f.1 : ℚ) * x + f.2) * PL L x := rfl

lemma PL_append (L M : List (ℤ × ℤ)) (x : ℚ) : PL (L ++ M) x = PL L x * PL M x := by
  simp [PL]

lemma PL_perm {L M : List (ℤ × ℤ)} (h : L.Perm M) (x : ℚ) : PL L x = PL M x := by
  unfold PL; exact (h.map _).prod_eq

lemma PL_pos (L : List (ℤ × ℤ)) (hL : ∀ f ∈ L, 0 ≤ f.1 ∧ 0 < f.2) (x : ℚ) (hx : 0 ≤ x) :
    0 < PL L x := by
  induction L with
  | nil => simp
  | cons f L ih =>
    rw [PL_cons]
    obtain ⟨h1, h2⟩ := hL f (by simp)
    have : (0 : ℚ) ≤ f.1 := by exact_mod_cast h1
    have : (0 : ℚ) < f.2 := by exact_mod_cast h2
    exact mul_pos (by positivity) (ih fun g hg => hL g (by simp [hg]))

/-- shift `x ↦ x + 1` -/
def shL (L : List (ℤ × ℤ)) : List (ℤ × ℤ) := L.map fun f => (f.1, f.1 + f.2)

lemma PL_succ (L : List (ℤ × ℤ)) (x : ℚ) : PL L (x + 1) = PL (shL L) x := by
  induction L with
  | nil => simp [shL]
  | cons f L ih => simp only [shL, List.map_cons] at ih ⊢; rw [PL_cons, PL_cons, ih]; push_cast; ring

/-- primitive normalization of a pair -/
def nrm (f : ℤ × ℤ) : ℤ × ℤ := (f.1 / (Int.gcd f.1 f.2 : ℤ), f.2 / (Int.gcd f.1 f.2 : ℤ))

def gcds (L : List (ℤ × ℤ)) : ℕ := (L.map fun f => Int.gcd f.1 f.2).prod

lemma PL_nrm (L : List (ℤ × ℤ)) (x : ℚ) : PL L x = gcds L * PL (L.map nrm) x := by
  induction L with
  | nil => simp [gcds]
  | cons f L ih =>
    rw [List.map_cons, PL_cons, PL_cons, ih]
    simp only [gcds, List.map_cons, List.prod_cons, nrm]
    have ha : ((f.1 / (Int.gcd f.1 f.2 : ℤ) : ℤ) : ℚ) * (Int.gcd f.1 f.2 : ℚ) = f.1 := by
      exact_mod_cast Int.ediv_mul_cancel (Int.gcd_dvd_left ..)
    have hb : ((f.2 / (Int.gcd f.1 f.2 : ℤ) : ℤ) : ℚ) * (Int.gcd f.1 f.2 : ℚ) = f.2 := by
      exact_mod_cast Int.ediv_mul_cancel (Int.gcd_dvd_right ..)
    push_cast
    rw [← ha, ← hb]; ring

/-- comparison of two factored rational functions -/
lemma fr_eq {c1 c2 : ℚ} {N1 D1 N2 D2 : List (ℤ × ℤ)} (x : ℚ) (hD1 : PL D1 x ≠ 0)
    (hD2 : PL D2 x ≠ 0) (hperm : ((N1 ++ D2).map nrm).Perm ((N2 ++ D1).map nrm))
    (hc : c1 * gcds (N1 ++ D2) = c2 * gcds (N2 ++ D1)) :
    c1 * PL N1 x / PL D1 x = c2 * PL N2 x / PL D2 x := by
  rw [div_eq_div_iff hD1 hD2, mul_assoc, mul_assoc, ← PL_append, ← PL_append, PL_nrm (N1 ++ D2),
    PL_nrm (N2 ++ D1), PL_perm hperm, ← mul_assoc, ← mul_assoc, hc]

/-! ### Rising-factorial blocks -/

/-- the linear factors `den(β) (β + A n + i) = den(β) A n + num(β) + den(β) i`, `i < A` -/
def famLin (f : Fam) : List (ℤ × ℤ) :=
  (List.range f.la).map fun i : ℕ => (((f.be.den * f.la : ℕ) : ℤ), f.be.num + f.be.den * (i : ℤ))

lemma famProd_aux (f : Fam) (n k : ℕ) :
    ∏ i ∈ range k, (f.be + ((f.la * n : ℕ) : ℚ) + i) =
      ((f.be.den : ℚ)⁻¹) ^ k * PL ((List.range k).map fun i : ℕ =>
        (((f.be.den * f.la : ℕ) : ℤ), f.be.num + f.be.den * (i : ℤ))) n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, List.range_succ, List.map_append, PL_append, pow_succ]
    have hd : (f.be.den : ℚ) ≠ 0 := by exact_mod_cast f.be.den_ne_zero
    have hb : f.be = (f.be.num : ℚ) / f.be.den := (Rat.num_div_den _).symm
    have hfac : f.be + ((f.la * n : ℕ) : ℚ) + k = (f.be.den : ℚ)⁻¹ *
        ((((f.be.den * f.la : ℕ) : ℤ) : ℚ) * n + ((f.be.num + f.be.den * (k : ℤ) : ℤ) : ℚ)) := by
      nth_rewrite 1 [hb]
      field_simp
      push_cast
      ring
    simp only [List.map_cons, List.map_nil, PL_cons, PL_nil]
    rw [hfac]
    ring

lemma famProd (f : Fam) (n : ℕ) :
    ∏ i ∈ range f.la, (f.be + ((f.la * n : ℕ) : ℚ) + i) =
      ((f.be.den : ℚ)⁻¹) ^ f.la * PL (famLin f) n :=
  famProd_aux f n f.la

/-- numerator / denominator factor lists and constant of a gamma list with exponents `±1` -/
def gNum (G : List (Fam × ℤ)) : List (ℤ × ℤ) :=
  G.flatMap fun fm => if fm.2 = 1 then famLin fm.1 else []
def gDen (G : List (Fam × ℤ)) : List (ℤ × ℤ) :=
  G.flatMap fun fm => if fm.2 = 1 then [] else famLin fm.1
def gConst (G : List (Fam × ℤ)) : ℚ :=
  (G.map fun fm => if fm.2 = 1 then ((fm.1.be.den : ℚ)⁻¹) ^ fm.1.la
    else (fm.1.be.den : ℚ) ^ fm.1.la).prod

lemma gamma_fr (G : List (Fam × ℤ)) (hG : ∀ fm ∈ G, fm.2 = 1 ∨ fm.2 = -1) (n : ℕ) :
    (G.map fun fm => (∏ i ∈ range fm.1.la, (fm.1.be + ((fm.1.la * n : ℕ) : ℚ) + i)) ^ fm.2).prod =
      gConst G * PL (gNum G) n / PL (gDen G) n := by
  induction G with
  | nil => simp [gConst, gNum, gDen]
  | cons fm G ih =>
    rw [List.map_cons, List.prod_cons, ih (fun g hg => hG g (by simp [hg])), famProd]
    simp only [gConst, gNum, gDen, List.map_cons, List.prod_cons, List.flatMap_cons]
    rcases hG fm (by simp) with h | h
    · simp only [h, ite_true, zpow_one, List.nil_append, PL_append]
      ring
    · simp only [h, show (-1 : ℤ) ≠ 1 by decide, ite_false, zpow_neg_one, List.nil_append,
        PL_append, mul_inv, inv_pow, inv_inv]
      ring

/-! ### `g` and `det Q` in factored form -/

def gN : List (ℤ × ℤ) := [(8, 1), (9, 1), (15, 2), (20, 3), (24, 1), (24, 1)]
def gD : List (ℤ × ℤ) := [(2, 1), (3, 1), (3, 1), (6, 1), (8, 3), (9, 2), (10, 3), (12, 1), (15, 1),
  (15, 4), (18, 1), (18, 1), (24, 5), (30, 7)]

lemma det_Qnum_eq (n : ℕ) :
    (Matrix.of fun i j => hornerR (Data.Qnum i j) (n : ℚ)).det =
      Data.QdetConst * PL Data.QdetLin n := by
  have key := PE.eq_zero_of_check (K := ℚ) _ _ Qdet_check n 0
  simp only [det3PE, PE.val, litVal, mul_zero, add_zero, val_factoredPE] at key
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  unfold PL
  linarith

lemma det_Q_fr (n : ℕ) :
    (Q n).det = ((Data.QdetConst : ℚ) / (Data.QdenConst : ℚ) ^ 3) * PL Data.QdetLin n /
      PL (Data.QdenLin ++ Data.QdenLin ++ Data.QdenLin) n := by
  have hQ : Q n = (hornerR Data.Qden (n : ℚ))⁻¹ • Matrix.of fun i j => hornerR (Data.Qnum i j) (n : ℚ) := by
    ext i j; simp [Q, div_eq_inv_mul]
  rw [hQ, Matrix.det_smul, Fintype.card_fin, det_Qnum_eq,
    hornerR_eq_factored _ _ _ _ Qden_factored, PL_append, PL_append]
  unfold PL
  ring

end Zeta2L2Chi3.Arith
