/-
# Forward transport: shift identities and product forms of denominators

* `RNum_succ`, `RDen_succ`: the `n`-shift identities `R_{n+1} rden = R_n rnum` (in numerator /
  denominator form);
* `RNum_shift`, `RDen_shift`: the `t`-shift identities `R_n(t-1) As(t) = R_n(t) Bs(t)`;
* `DF_eq`: `∏_{k ∈ KF m} (t-k)^{eF m k} = RDen m t`;
* `DG_eq`: the pole set `KG n` and orders `eG n` of the certificate quotient `G_j`, with
  `∏_{k ∈ KG n} (t-k)^{eG n k} = RDen (n+1) t · rdenA(n,t)`;
* positivity of `c_num`, `c_den`, `D_M` at `n ≥ 0`.
-/
import Zeta2L2Chi3.Forward
import Zeta2L2Chi3.DualShift

open Finset Polynomial

noncomputable section

namespace Zeta2L2Chi3

/-! ### Semantic factor products -/

/-- `rnum` -/
def frnumR (n t : ℝ) : ℝ := (∏ i ∈ range 12, (t + 12 * n + 2 + i)) *
  (∏ i ∈ range 6, (t + 6 * n + 7 / 3 + i)) * ∏ i ∈ range 5, (t + 5 * n + 5 / 2 + i)

/-- first part of `rden` -/
def frdenAR (n t : ℝ) : ℝ :=
  (t + 2 * n + 1) * (t + 2 * n + 2) * (t + 2 * n + 3 / 2) * (t + 2 * n + 5 / 2)

/-- second part of `rden` -/
def frdenBR (n t : ℝ) : ℝ := (∏ i ∈ range 10, (t - 10 * n - 11 + i)) *
  (∏ i ∈ range 8, (t - 8 * n - 9 + i)) * (t + n + 1)

def fAsNR (n t : ℝ) : ℝ := (t + 12 * n + 1) * (t + 6 * n + 4 / 3) * (t + 5 * n + 3 / 2)
def fAsDR (n t : ℝ) : ℝ := (t - 10 * n - 2) * (t - 8 * n - 2)
def fBsNR (n t : ℝ) : ℝ := (t + 2 * n) * (t + 1 / 3) * (t + 2 * n + 1 / 2)
def fBsDR (n t : ℝ) : ℝ := t * (t + n)

/-! ### Shift identities -/

theorem RNum_succ (n : ℕ) (t : ℝ) : RNum (n + 1) t * frdenAR n t = RNum n t * frnumR n t := by
  unfold RNum frdenAR frnumR
  have hA : rf (t + 2 * ((n + 1 : ℕ) : ℝ) + 1) (10 * (n + 1) + 1) *
      ((t + 2 * n + 1) * (t + 2 * n + 2)) =
      rf (t + 2 * n + 1) (10 * n + 1) * ∏ i ∈ range 12, (t + 12 * n + 2 + i) := by
    have e1 := rf_two (t + 2 * (n : ℝ) + 1) (10 * (n + 1) + 1)
    have e2 : rf (t + 2 * (n : ℝ) + 1) (10 * (n + 1) + 1 + 2) =
        rf (t + 2 * n + 1) (10 * n + 1) * rf (t + 2 * n + 1 + ((10 * n + 1 : ℕ) : ℝ)) 12 := by
      rw [show 10 * (n + 1) + 1 + 2 = (10 * n + 1) + 12 by ring, rf_add]
    have e3 : t + 2 * ((n + 1 : ℕ) : ℝ) + 1 = t + 2 * n + 1 + 2 := by push_cast; ring
    have e4 : rf (t + 2 * (n : ℝ) + 1 + ((10 * n + 1 : ℕ) : ℝ)) 12 =
        ∏ i ∈ range 12, (t + 12 * n + 2 + i) := by
      unfold rf; refine prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e3, ← e4]
    linear_combination e2 - e1
  have hB : rf (t + 4 / 3) (6 * (n + 1) + 1) =
      rf (t + 4 / 3) (6 * n + 1) * ∏ i ∈ range 6, (t + 6 * n + 7 / 3 + i) := by
    rw [show 6 * (n + 1) + 1 = (6 * n + 1) + 6 by ring, rf_add]
    congr 1
    unfold rf; refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have hC : rf (t + 2 * ((n + 1 : ℕ) : ℝ) + 3 / 2) (3 * (n + 1) + 1) *
      ((t + 2 * n + 3 / 2) * (t + 2 * n + 5 / 2)) =
      rf (t + 2 * n + 3 / 2) (3 * n + 1) * ∏ i ∈ range 5, (t + 5 * n + 5 / 2 + i) := by
    have e1 := rf_two (t + 2 * (n : ℝ) + 3 / 2) (3 * (n + 1) + 1)
    have e2 : rf (t + 2 * (n : ℝ) + 3 / 2) (3 * (n + 1) + 1 + 2) =
        rf (t + 2 * n + 3 / 2) (3 * n + 1) * rf (t + 2 * n + 3 / 2 + ((3 * n + 1 : ℕ) : ℝ)) 5 := by
      rw [show 3 * (n + 1) + 1 + 2 = (3 * n + 1) + 5 by ring, rf_add]
    have e3 : t + 2 * ((n + 1 : ℕ) : ℝ) + 3 / 2 = t + 2 * n + 3 / 2 + 2 := by push_cast; ring
    have e4 : rf (t + 2 * (n : ℝ) + 3 / 2 + ((3 * n + 1 : ℕ) : ℝ)) 5 =
        ∏ i ∈ range 5, (t + 5 * n + 5 / 2 + i) := by
      unfold rf; refine prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e3, ← e4]
    linear_combination e2 - e1
  rw [hB]
  linear_combination
    (rf (t + 4 / 3) (6 * n + 1) * ∏ i ∈ range 6, (t + 6 * (n : ℝ) + 7 / 3 + i)) *
      (rf (t + 2 * ((n + 1 : ℕ) : ℝ) + 3 / 2) (3 * (n + 1) + 1) *
        ((t + 2 * n + 3 / 2) * (t + 2 * n + 5 / 2))) * hA +
    (rf (t + 2 * n + 1) (10 * n + 1) * ∏ i ∈ range 12, (t + 12 * (n : ℝ) + 2 + i)) *
      (rf (t + 4 / 3) (6 * n + 1) * ∏ i ∈ range 6, (t + 6 * (n : ℝ) + 7 / 3 + i)) * hC

theorem RDen_succ (n : ℕ) (t : ℝ) : RDen (n + 1) t = RDen n t * frdenBR n t := by
  unfold RDen frdenBR
  have hA : rf (t - 10 * ((n + 1 : ℕ) : ℝ) - 1) (10 * (n + 1) + 2) =
      rf (t - 10 * n - 1) (10 * n + 2) * ∏ i ∈ range 10, (t - 10 * n - 11 + i) := by
    rw [show 10 * (n + 1) + 2 = 10 + (10 * n + 2) by ring, rf_add, mul_comm]
    have e : t - 10 * ((n + 1 : ℕ) : ℝ) - 1 + ((10 : ℕ) : ℝ) = t - 10 * n - 1 := by
      push_cast; ring
    rw [e]
    congr 1
    unfold rf; refine prod_congr rfl fun i _ => ?_; push_cast; ring
  have hB : rf (t - 8 * ((n + 1 : ℕ) : ℝ) - 1) (9 * (n + 1) + 2) =
      rf (t - 8 * n - 1) (9 * n + 2) * ((∏ i ∈ range 8, (t - 8 * n - 9 + i)) * (t + n + 1)) := by
    rw [show 9 * (n + 1) + 2 = 8 + ((9 * n + 2) + 1) by ring, rf_add]
    have e : t - 8 * ((n + 1 : ℕ) : ℝ) - 1 + ((8 : ℕ) : ℝ) = t - 8 * n - 1 := by
      push_cast; ring
    rw [e, rf_succ (t - 8 * (n : ℝ) - 1) (9 * n + 2)]
    have e2 : rf (t - 8 * ((n + 1 : ℕ) : ℝ) - 1) 8 = ∏ i ∈ range 8, (t - 8 * n - 9 + i) := by
      unfold rf; refine prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e2]
    push_cast; ring
  rw [hA, hB]; ring

theorem RNum_shift (n : ℕ) (t : ℝ) : RNum n (t - 1) * fAsNR n t = RNum n t * fBsNR n t := by
  unfold RNum fAsNR fBsNR
  have a1 : t - 1 + 2 * (n : ℝ) + 1 = t + 2 * n := by ring
  have a2 : t - 1 + 4 / 3 = t + 1 / 3 := by ring
  have a3 : t - 1 + 2 * (n : ℝ) + 3 / 2 = t + 2 * n + 1 / 2 := by ring
  rw [a1, a2, a3]
  have e1 := rf_shift (t + 2 * (n : ℝ)) (10 * n + 1)
  have e2 := rf_shift (t + 1 / 3) (6 * n + 1)
  have e3 := rf_shift (t + 2 * (n : ℝ) + 1 / 2) (3 * n + 1)
  have b2 : t + 1 / 3 + 1 = t + 4 / 3 := by ring
  have b3 : t + 2 * (n : ℝ) + 1 / 2 + 1 = t + 2 * n + 3 / 2 := by ring
  rw [b2] at e2
  rw [b3] at e3
  push_cast at e1 e2 e3
  linear_combination
    (-(rf (t + 1 / 3) (6 * n + 1) * (t + 6 * n + 4 / 3) * rf (t + 2 * n + 1 / 2) (3 * n + 1) *
      (t + 5 * n + 3 / 2))) * e1 -
    (rf (t + 2 * n + 1) (10 * n + 1) * (t + 2 * n) * rf (t + 2 * n + 1 / 2) (3 * n + 1) *
      (t + 5 * n + 3 / 2)) * e2 -
    (rf (t + 2 * n + 1) (10 * n + 1) * (t + 2 * n) * rf (t + 4 / 3) (6 * n + 1) * (t + 1 / 3)) * e3

theorem RDen_shift (n : ℕ) (t : ℝ) : RDen n (t - 1) * fBsDR n t = RDen n t * fAsDR n t := by
  unfold RDen fBsDR fAsDR
  have a1 : t - 1 - 10 * (n : ℝ) - 1 = t - 10 * n - 2 := by ring
  have a2 : t - 1 - 8 * (n : ℝ) - 1 = t - 8 * n - 2 := by ring
  rw [a1, a2]
  have e1 := rf_shift (t - 10 * (n : ℝ) - 2) (10 * n + 2)
  have e2 := rf_shift (t - 8 * (n : ℝ) - 2) (9 * n + 2)
  have b1 : t - 10 * (n : ℝ) - 2 + 1 = t - 10 * n - 1 := by ring
  have b2 : t - 8 * (n : ℝ) - 2 + 1 = t - 8 * n - 1 := by ring
  rw [b1] at e1
  rw [b2] at e2
  push_cast at e1 e2
  linear_combination
    (-(rf (t - 8 * n - 2) (9 * n + 2) * (t + n))) * e1 -
    (rf (t - 10 * n - 1) (10 * n + 2) * (t - 10 * n - 2)) * e2

/-! ### Polynomial forms -/

lemma RNumPoly_eval (n : ℕ) (t : ℝ) : (RNumPoly n).eval t = RNum n t := by
  simp only [RNumPoly, RNum, rf, eval_mul, eval_prod, eval_add, eval_X, eval_C]
  congr 1; congr 1
  all_goals refine prod_congr rfl fun i _ => by ring

/-! ### Products over integer intervals -/

lemma Icc_eq_image_range (c : ℤ) (m : ℕ) :
    Icc (c - m + 1) c = (range m).image (fun i : ℕ => c - i) := by
  ext z
  simp only [mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(c - z).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

lemma prod_Icc_cast (c : ℤ) (m : ℕ) (t : ℝ) :
    ∏ k ∈ (Icc (c - m + 1) c).image (fun z : ℤ => (z : ℝ)), (t - k) = rf (t - c) m := by
  rw [prod_image (fun x _ y _ h => by exact_mod_cast h), Icc_eq_image_range,
    prod_image (fun x _ y _ h => by omega)]
  unfold rf
  refine prod_congr rfl fun i _ => ?_
  push_cast; ring

lemma prod_pow_union_ite (A B : Finset ℝ) (f : ℝ → ℝ) :
    ∏ k ∈ A ∪ B, f k ^ ((if k ∈ A then 1 else 0) + (if k ∈ B then 1 else 0)) =
      (∏ k ∈ A, f k) * ∏ k ∈ B, f k := by
  have h : ∀ C ⊆ A ∪ B, ∏ k ∈ A ∪ B, f k ^ (if k ∈ C then 1 else 0) = ∏ k ∈ C, f k := by
    intro C hC
    calc ∏ k ∈ A ∪ B, f k ^ (if k ∈ C then 1 else 0)
        = ∏ k ∈ C, f k ^ (if k ∈ C then 1 else 0) :=
          (prod_subset hC (fun k _ hk => by simp [hk])).symm
      _ = ∏ k ∈ C, f k := prod_congr rfl fun k hk => by simp [hk]
  simp only [pow_add, prod_mul_distrib]
  rw [h A subset_union_left, h B subset_union_right]

/-- the two integer blocks of poles of `R_m` -/
def IA (m : ℕ) : Finset ℝ := (Icc (0 : ℤ) (10 * m + 1)).image (fun z : ℤ => (z : ℝ))
def IB (m : ℕ) : Finset ℝ := (Icc (-(m : ℤ)) (8 * m + 1)).image (fun z : ℤ => (z : ℝ))

lemma KF_eq (m : ℕ) : KF m = IA m ∪ IB m := by
  rw [KF, IA, IB, ← image_union]
  congr 1
  ext z
  simp only [mem_Icc, mem_union]
  omega

lemma mem_intImage {a b : ℤ} {x : ℝ} :
    x ∈ (Icc a b).image (fun z : ℤ => (z : ℝ)) ↔ ∃ z : ℤ, a ≤ z ∧ z ≤ b ∧ (z : ℝ) = x := by
  simp only [mem_image, mem_Icc, and_assoc]

lemma eF_eq (m : ℕ) (k : ℝ) (hk : k ∈ KF m) :
    eF m k = (if k ∈ IA m then 1 else 0) + (if k ∈ IB m then 1 else 0) := by
  obtain ⟨z, hz1, hz2, rfl⟩ := mem_intImage.1 hk
  have hA : (z : ℝ) ∈ IA m ↔ 0 ≤ z ∧ z ≤ 10 * m + 1 := by
    rw [IA, mem_intImage]
    constructor
    · rintro ⟨w, h1, h2, h3⟩
      have : w = z := by exact_mod_cast h3
      subst this; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨z, h1, h2, rfl⟩
  have hB : (z : ℝ) ∈ IB m ↔ -(m : ℤ) ≤ z ∧ z ≤ 8 * m + 1 := by
    rw [IB, mem_intImage]
    constructor
    · rintro ⟨w, h1, h2, h3⟩
      have : w = z := by exact_mod_cast h3
      subst this; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨z, h1, h2, rfl⟩
  have hE : (0 ≤ (z : ℝ) ∧ (z : ℝ) ≤ 8 * (m : ℝ) + 1) ↔ (0 ≤ z ∧ z ≤ 8 * m + 1) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  simp only [eF, hE, hA, hB]
  split_ifs <;> omega

/-- the denominator of `R_m` as a product over its poles -/
theorem DF_eq (m : ℕ) (t : ℝ) : ∏ k ∈ KF m, (t - k) ^ eF m k = RDen m t := by
  rw [prod_congr rfl (fun k hk => congrArg _ (eF_eq m k hk)), KF_eq, prod_pow_union_ite, IA, IB]
  have h1 : Icc (0 : ℤ) (10 * m + 1) = Icc ((10 * m + 1 : ℤ) - ((10 * m + 2 : ℕ) : ℤ) + 1)
      (10 * m + 1) := by congr 1; push_cast; ring
  have h2 : Icc (-(m : ℤ)) (8 * m + 1) = Icc ((8 * m + 1 : ℤ) - ((9 * m + 2 : ℕ) : ℤ) + 1)
      (8 * m + 1) := by congr 1; push_cast; ring
  rw [h1, h2, prod_Icc_cast, prod_Icc_cast, RDen]
  push_cast
  congr 2 <;> ring

/-! ### The poles of the certificate quotient `G_j` -/

def KG1 (n : ℕ) : Finset ℝ := (Icc (0 : ℤ) (10 * n + 11)).image (fun z : ℤ => (z : ℝ)) ∪
  {-(2 * (n : ℝ) + 1), -(2 * (n : ℝ) + 2), -(2 * (n : ℝ) + 3 / 2), -(2 * (n : ℝ) + 5 / 2)}
def KG2 (n : ℕ) : Finset ℝ := (Icc (-(n : ℤ) - 1) (8 * n + 9)).image (fun z : ℤ => (z : ℝ))
def KG (n : ℕ) : Finset ℝ := KG1 n ∪ KG2 n
def eG (n : ℕ) (k : ℝ) : ℕ := (if k ∈ KG1 n then 1 else 0) + (if k ∈ KG2 n then 1 else 0)

lemma eG_le (n : ℕ) (k : ℝ) : eG n k ≤ 2 := by unfold eG; split_ifs <;> omega

theorem DG_eq (n : ℕ) (t : ℝ) :
    ∏ k ∈ KG n, (t - k) ^ eG n k = RDen (n + 1) t * frdenAR n t := by
  unfold KG eG
  rw [prod_pow_union_ite]
  have hdisj : Disjoint ((Icc (0 : ℤ) (10 * n + 11)).image (fun z : ℤ => (z : ℝ)))
      ({-(2 * (n : ℝ) + 1), -(2 * (n : ℝ) + 2), -(2 * (n : ℝ) + 3 / 2),
        -(2 * (n : ℝ) + 5 / 2)} : Finset ℝ) := by
    rw [Finset.disjoint_left]
    intro x hx hH
    obtain ⟨z, hz1, -, rfl⟩ := mem_intImage.1 hx
    have hz : (0 : ℝ) ≤ z := by exact_mod_cast hz1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [mem_insert, mem_singleton] at hH
    rcases hH with h | h | h | h <;> linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hH : ∏ k ∈ ({-(2 * (n : ℝ) + 1), -(2 * (n : ℝ) + 2), -(2 * (n : ℝ) + 3 / 2),
      -(2 * (n : ℝ) + 5 / 2)} : Finset ℝ), (t - k) = frdenAR n t := by
    rw [prod_insert (by simp only [mem_insert, mem_singleton]; intro h; rcases h with h | h | h <;> linarith),
      prod_insert (by simp only [mem_insert, mem_singleton]; intro h; rcases h with h | h <;> linarith),
      prod_insert (by simp only [mem_singleton]; intro h; linarith), prod_singleton, frdenAR]
    ring
  rw [KG1, prod_union hdisj, hH, KG2]
  have h1 : Icc (0 : ℤ) (10 * n + 11) = Icc ((10 * n + 11 : ℤ) - ((10 * (n + 1) + 2 : ℕ) : ℤ) + 1)
      (10 * n + 11) := by congr 1; push_cast; ring
  have h2 : Icc (-(n : ℤ) - 1) (8 * n + 9) = Icc ((8 * n + 9 : ℤ) - ((9 * (n + 1) + 2 : ℕ) : ℤ) + 1)
      (8 * n + 9) := by congr 1; push_cast; ring
  rw [h1, h2, prod_Icc_cast, prod_Icc_cast, RDen]
  have e1 : t - (((10 * n + 11 : ℤ)) : ℝ) = t - 10 * ((n + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have e2 : t - (((8 * n + 9 : ℤ)) : ℝ) = t - 8 * ((n + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  rw [e1, e2]
  ring

/-! ### Positivity of the scalar polynomials -/

lemma hornerR_nonneg_of (l : List ℤ) (hl : ∀ a ∈ l, 0 ≤ a) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ hornerR l x := by
  induction l with
  | nil => simp [hornerR]
  | cons c cs ih =>
    simp only [hornerR]
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast hl c (List.mem_cons_self ..)
    have := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    positivity

lemma hornerR_pos_of (l : List ℤ) (hl : ∀ a ∈ l, 0 ≤ a) (h0 : 0 < l.headD 0) (x : ℝ)
    (hx : 0 ≤ x) : 0 < hornerR l x := by
  cases l with
  | nil => simp at h0
  | cons c cs =>
    simp only [hornerR]
    have hc : (0 : ℝ) < c := by exact_mod_cast h0
    have := hornerR_nonneg_of cs (fun a ha => hl a (List.mem_cons_of_mem _ ha)) x hx
    positivity

lemma cnum_pos (n : ℕ) : 0 < hornerR (Data.cnum 0 0) (n : ℝ) :=
  hornerR_pos_of _ (by decide +kernel) (by decide +kernel) _ (Nat.cast_nonneg n)

lemma cden_pos (n : ℕ) : 0 < hornerR Data.cden (n : ℝ) :=
  hornerR_pos_of _ (by decide +kernel) (by decide +kernel) _ (Nat.cast_nonneg n)

lemma Mden_pos (n : ℕ) : 0 < hornerR Data.Mden (n : ℝ) :=
  hornerR_pos_of _ (by decide +kernel) (by decide +kernel) _ (Nat.cast_nonneg n)

end Zeta2L2Chi3
