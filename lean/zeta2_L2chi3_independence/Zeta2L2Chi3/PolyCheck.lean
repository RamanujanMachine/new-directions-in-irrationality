/-
# A verified checker for polynomial identities in two variables

Expressions `PE` describe polynomials in two variables `n` (inner) and `s` (outer) with integer
coefficients, built from literal coefficient tables, `+`, `-`, `*` and the shift `s ↦ s - 1`.

`PE.eq_zero_of_check` shows: if for every `s₀ ∈ {0, …, degS e}` the integer `e(B, s₀)` vanishes
for an integer `B > 2 · ‖e(·, s₀)‖₁` (Kronecker substitution), then `e(x, s) = 0` for all `x, s`
in any field of characteristic zero.  All side conditions are decidable integer computations,
checked by the kernel (`decide +kernel`); no `native_decide` is used.
-/
import Mathlib

open Polynomial

namespace Zeta2L2Chi3

/-- Horner evaluation of an ascending integer coefficient list. -/
def hornerR {R : Type*} [CommRing R] : List ℤ → R → R
  | [], _ => 0
  | c :: cs, x => (c : R) + x * hornerR cs x

/-- `∑_j s^j (∑_i c_{j i} n^i)`. -/
def litVal {R : Type*} [CommRing R] : List (List ℤ) → R → R → R
  | [], _, _ => 0
  | l :: ls, n, s => hornerR l n + s * litVal ls n s

/-- Bivariate polynomial expressions. -/
inductive PE where
  | lit : List (List ℤ) → PE
  | add : PE → PE → PE
  | sub : PE → PE → PE
  | mul : PE → PE → PE
  | shift : PE → PE

namespace PE

/-- Value of an expression at `(n, s)`. -/
def val {R : Type*} [CommRing R] : PE → R → R → R
  | lit L, n, s => litVal L n s
  | add a b, n, s => a.val n s + b.val n s
  | sub a b, n, s => a.val n s - b.val n s
  | mul a b, n, s => a.val n s * b.val n s
  | shift a, n, s => a.val n (s - 1)

/-- `ℓ¹` norm of a coefficient list. -/
def l1List (l : List ℤ) : ℕ := (l.map Int.natAbs).sum

def litNorm : List (List ℤ) → ℕ → ℕ
  | [], _ => 0
  | l :: ls, a => l1List l + a * litNorm ls a

/-- Upper bound for the `ℓ¹` norm of `e(·, s₀)` as a polynomial in `n`. -/
def norm : PE → ℤ → ℕ
  | lit L, s => litNorm L s.natAbs
  | add a b, s => a.norm s + b.norm s
  | sub a b, s => a.norm s + b.norm s
  | mul a b, s => a.norm s * b.norm s
  | shift a, s => a.norm (s - 1)

/-- Upper bound for the degree in `s`. -/
def degS : PE → ℕ
  | lit L => L.length - 1
  | add a b => max a.degS b.degS
  | sub a b => max a.degS b.degS
  | mul a b => a.degS + b.degS
  | shift a => a.degS

end PE

/-! ### Ring homomorphisms commute with evaluation -/

lemma hornerR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List ℤ) (x : R) :
    f (hornerR l x) = hornerR l (f x) := by
  induction l with
  | nil => simp [hornerR]
  | cons c cs ih => simp [hornerR, ih]

lemma litVal_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (L : List (List ℤ))
    (x s : R) : f (litVal L x s) = litVal L (f x) (f s) := by
  induction L with
  | nil => simp [litVal]
  | cons l ls ih => simp [litVal, ih, hornerR_map]

lemma PE.val_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (e : PE) (x s : R) :
    f (e.val x s) = e.val (f x) (f s) := by
  induction e generalizing s with
  | lit L => simp [PE.val, litVal_map]
  | add a b iha ihb => simp [PE.val, iha, ihb]
  | sub a b iha ihb => simp [PE.val, iha, ihb]
  | mul a b iha ihb => simp [PE.val, iha, ihb]
  | shift a ih => simp [PE.val, ih]

/-! ### Polynomial semantics -/

/-- The polynomial with ascending coefficient list `l`. -/
noncomputable def toPoly : List ℤ → ℤ[X]
  | [] => 0
  | c :: cs => C c + X * toPoly cs

lemma eval₂_toPoly {R : Type*} [CommRing R] (l : List ℤ) (x : R) :
    (toPoly l).eval₂ (Int.castRingHom R) x = hornerR l x := by
  induction l with
  | nil => simp [toPoly, hornerR]
  | cons c cs ih =>
    simp only [toPoly, hornerR, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, ih]
    rw [eq_intCast]

noncomputable def litPolyN : List (List ℤ) → ℤ → ℤ[X]
  | [], _ => 0
  | l :: ls, s => toPoly l + C s * litPolyN ls s

namespace PE

/-- `e(·, s₀)` as an integer polynomial in `n`. -/
noncomputable def polyN : PE → ℤ → ℤ[X]
  | lit L, s => litPolyN L s
  | add a b, s => a.polyN s + b.polyN s
  | sub a b, s => a.polyN s - b.polyN s
  | mul a b, s => a.polyN s * b.polyN s
  | shift a, s => a.polyN (s - 1)

lemma eval₂_polyN {R : Type*} [CommRing R] (e : PE) (s : ℤ) (x : R) :
    (e.polyN s).eval₂ (Int.castRingHom R) x = e.val x (s : R) := by
  induction e generalizing s with
  | lit L =>
    simp only [polyN, val]
    induction L with
    | nil => simp [litPolyN, litVal]
    | cons l ls ih =>
      simp only [litPolyN, litVal, eval₂_add, eval₂_mul, eval₂_C, ih, eval₂_toPoly]
      rw [eq_intCast]
  | add a b iha ihb => simp [polyN, val, iha, ihb]
  | sub a b iha ihb => simp [polyN, val, iha, ihb]
  | mul a b iha ihb => simp [polyN, val, iha, ihb]
  | shift a ih => simp [polyN, val, ih]

end PE

/-! ### The `ℓ¹` norm of integer polynomials -/

/-- `‖p‖₁ = ∑ |coeff|`. -/
def l1 (p : ℤ[X]) : ℕ := p.sum fun _ c => c.natAbs

lemma l1_eq_sum_range (p : ℤ[X]) {N : ℕ} (hN : p.natDegree < N) :
    l1 p = ∑ i ∈ Finset.range N, (p.coeff i).natAbs := by
  unfold l1
  rw [Polynomial.sum_over_range' _ (by simp) N hN]

lemma natAbs_coeff_le_l1 (p : ℤ[X]) (i : ℕ) : (p.coeff i).natAbs ≤ l1 p := by
  by_cases hi : i ≤ p.natDegree
  · rw [l1_eq_sum_range p (Nat.lt_succ_self _)]
    exact Finset.single_le_sum (f := fun j => (p.coeff j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]; simp

lemma l1_add_le (p q : ℤ[X]) : l1 (p + q) ≤ l1 p + l1 q := by
  set N := max (max p.natDegree q.natDegree) (p + q).natDegree + 1
  rw [l1_eq_sum_range p (N := N) (by omega), l1_eq_sum_range q (N := N) (by omega),
    l1_eq_sum_range (p + q) (N := N) (by omega), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by rw [coeff_add]; exact Int.natAbs_add_le _ _

lemma l1_neg (p : ℤ[X]) : l1 (-p) = l1 p := by
  set N := p.natDegree + 1
  rw [l1_eq_sum_range p (N := N) (by omega), l1_eq_sum_range (-p) (N := N)
    (by rw [natDegree_neg]; omega)]
  simp

lemma l1_sub_le (p q : ℤ[X]) : l1 (p - q) ≤ l1 p + l1 q := by
  rw [sub_eq_add_neg]; exact (l1_add_le _ _).trans (by rw [l1_neg])

lemma l1_C (c : ℤ) : l1 (C c) = c.natAbs := by
  rw [l1_eq_sum_range (C c) (N := 1) (by rw [natDegree_C]; omega)]; simp

lemma l1_C_mul (c : ℤ) (p : ℤ[X]) : l1 (C c * p) = c.natAbs * l1 p := by
  set N := p.natDegree + 1
  have h1 : (C c * p).natDegree < N := lt_of_le_of_lt (natDegree_C_mul_le c p) (by omega)
  rw [l1_eq_sum_range _ h1, l1_eq_sum_range p (N := N) (by omega), Finset.mul_sum]
  simp [Int.natAbs_mul]

lemma l1_X_mul (p : ℤ[X]) : l1 (X * p) = l1 p := by
  set N := p.natDegree + 1
  have h1 : (X * p).natDegree < N + 1 := by
    refine lt_of_le_of_lt natDegree_mul_le ?_
    have := natDegree_X_le (R := ℤ); omega
  rw [l1_eq_sum_range p (N := N) (by omega), l1_eq_sum_range (X * p) h1]
  rw [Finset.sum_range_succ']
  simp [coeff_X_mul]

lemma l1_X_pow_mul (k : ℕ) (p : ℤ[X]) : l1 (X ^ k * p) = l1 p := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (X ^ k) X, mul_assoc, l1_X_mul, ih]

lemma l1_sum_le {ι : Type*} (t : Finset ι) (f : ι → ℤ[X]) :
    l1 (∑ i ∈ t, f i) ≤ ∑ i ∈ t, l1 (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [l1]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma l1_mul_le (p q : ℤ[X]) : l1 (p * q) ≤ l1 p * l1 q := by
  set N := p.natDegree + 1
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, Finset.sum_mul]
  refine (l1_sum_le _ _).trans ?_
  rw [l1_eq_sum_range p (N := N) (by omega), Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => le_of_eq ?_
  rw [mul_assoc, l1_C_mul, l1_X_pow_mul]

lemma l1_C_mul_le (c : ℤ) (p : ℤ[X]) : l1 (C c * p) ≤ c.natAbs * l1 p := le_of_eq (l1_C_mul c p)

lemma l1_toPoly_le (l : List ℤ) : l1 (toPoly l) ≤ PE.l1List l := by
  induction l with
  | nil => simp [toPoly, l1, PE.l1List]
  | cons c cs ih =>
    simp only [toPoly, PE.l1List, List.map_cons, List.sum_cons]
    refine (l1_add_le _ _).trans (Nat.add_le_add (le_of_eq (l1_C c)) ?_)
    rw [l1_X_mul]; exact ih

lemma l1_polyN_le (e : PE) (s : ℤ) : l1 (e.polyN s) ≤ e.norm s := by
  induction e generalizing s with
  | lit L =>
    simp only [PE.polyN, PE.norm]
    induction L with
    | nil => simp [litPolyN, PE.litNorm, l1]
    | cons l ls ih =>
      simp only [litPolyN, PE.litNorm]
      exact (l1_add_le _ _).trans (Nat.add_le_add (l1_toPoly_le l)
        ((l1_C_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)))
  | add a b iha ihb => exact (l1_add_le _ _).trans (Nat.add_le_add (iha s) (ihb s))
  | sub a b iha ihb => exact (l1_sub_le _ _).trans (Nat.add_le_add (iha s) (ihb s))
  | mul a b iha ihb => exact (l1_mul_le _ _).trans (Nat.mul_le_mul (iha s) (ihb s))
  | shift a ih => exact ih (s - 1)

lemma l1_divX_le (p : ℤ[X]) : l1 p.divX ≤ l1 p := by
  set N := p.natDegree + 1
  have h1 : p.divX.natDegree < N := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  rw [l1_eq_sum_range p (N := N + 1) (by omega), l1_eq_sum_range _ h1]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [coeff_divX]
  exact Nat.le_add_right _ _

/-- **Kronecker substitution.** An integer polynomial with `2‖p‖₁ < B` vanishing at `B` is zero. -/
theorem eq_zero_of_eval_large (p : ℤ[X]) (B : ℤ) (hB : 2 * (l1 p : ℤ) < B) (h : p.eval B = 0) :
    p = 0 := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have hdecomp := X_mul_divX_add p
    have hev : B * p.divX.eval B + p.coeff 0 = 0 := by
      have := congrArg (eval B) hdecomp; simp at this; linarith
    have hc0 : (p.coeff 0).natAbs ≤ l1 p := natAbs_coeff_le_l1 p 0
    have hB0 : 0 < B := by have : (0 : ℤ) ≤ l1 p := by positivity
                           linarith
    have hdiv : p.divX.eval B = 0 := by
      by_contra hne
      have h1 : B ≤ |B * p.divX.eval B| := by
        rw [abs_mul, abs_of_pos hB0]
        have : 1 ≤ |p.divX.eval B| := Int.one_le_abs hne
        nlinarith
      have h2 : |B * p.divX.eval B| = |p.coeff 0| := by
        rw [show B * p.divX.eval B = -p.coeff 0 by linarith, abs_neg]
      have h3 : |p.coeff 0| ≤ (l1 p : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hc0
      linarith
    have hcoeff : p.coeff 0 = 0 := by rw [hdiv, mul_zero, zero_add] at hev; exact hev
    by_cases hp : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hp, hcoeff, map_zero]
    · have hlt : p.divX.natDegree < d := by
        rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      have hb2 : 2 * (l1 p.divX : ℤ) < B := by
        have := l1_divX_le p; omega
      have hz : p.divX = 0 := ih _ hlt p.divX hb2 hdiv rfl
      rw [← hdecomp, hz, hcoeff]; simp

/-! ### Polynomials in `s` with coefficients evaluated at a point -/

noncomputable def litPolyS {K : Type*} [Field K] : List (List ℤ) → K → K[X]
  | [], _ => 0
  | l :: ls, x => C (hornerR l x) + X * litPolyS ls x

namespace PE

noncomputable def polyS {K : Type*} [Field K] : PE → K → K[X]
  | lit L, x => litPolyS L x
  | add a b, x => a.polyS x + b.polyS x
  | sub a b, x => a.polyS x - b.polyS x
  | mul a b, x => a.polyS x * b.polyS x
  | shift a, x => (a.polyS x).comp (X - 1)

lemma eval_polyS {K : Type*} [Field K] (e : PE) (x s : K) : (e.polyS x).eval s = e.val x s := by
  induction e generalizing s with
  | lit L =>
    simp only [polyS, val]
    induction L generalizing s with
    | nil => simp [litPolyS, litVal]
    | cons l ls ih => simp [litPolyS, litVal, ih]
  | add a b iha ihb => simp [polyS, val, iha, ihb]
  | sub a b iha ihb => simp [polyS, val, iha, ihb]
  | mul a b iha ihb => simp [polyS, val, iha, ihb]
  | shift a ih => simp [polyS, val, ih]

lemma natDegree_polyS_le {K : Type*} [Field K] (e : PE) (x : K) :
    (e.polyS x).natDegree < e.degS + 1 := by
  induction e with
  | lit L =>
    simp only [polyS, degS]
    suffices h : (litPolyS L x).natDegree ≤ L.length - 1 by omega
    induction L with
    | nil => simp [litPolyS]
    | cons l ls ih =>
      simp only [litPolyS, List.length_cons]
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      cases ls with
      | nil => simp [litPolyS]
      | cons l' ls' =>
        refine natDegree_mul_le.trans ?_
        have := natDegree_X_le (R := K)
        simp only [List.length_cons] at ih ⊢
        omega
  | add a b iha ihb =>
    simp only [polyS, degS]
    exact lt_of_le_of_lt (natDegree_add_le _ _) (by omega)
  | sub a b iha ihb =>
    simp only [polyS, degS]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (by omega)
  | mul a b iha ihb =>
    simp only [polyS, degS]
    exact lt_of_le_of_lt natDegree_mul_le (by omega)
  | shift a ih =>
    simp only [polyS, degS]
    refine lt_of_le_of_lt (natDegree_comp_le) ?_
    have : (X - 1 : K[X]).natDegree ≤ 1 := natDegree_sub_le_iff_left (by simp) |>.2 natDegree_X_le
    calc (a.polyS x).natDegree * (X - 1 : K[X]).natDegree ≤ (a.polyS x).natDegree * 1 :=
          Nat.mul_le_mul_left _ this
      _ < a.degS + 1 := by simpa using ih

/-- The decidable side condition of the checker. -/
def check (e : PE) (B : ℤ) : Prop :=
  ∀ s ∈ List.range (e.degS + 1), 2 * (e.norm (s : ℤ) : ℤ) < B ∧ e.val B (s : ℤ) = 0

instance (e : PE) (B : ℤ) : Decidable (e.check B) := by unfold check; infer_instance

/-- **Soundness of the checker.** -/
theorem eq_zero_of_check {K : Type*} [Field K] [CharZero K] (e : PE) (B : ℤ) (h : e.check B) :
    ∀ x s : K, e.val x s = 0 := by
  intro x s
  -- first: `e(x, s₀) = 0` for the grid points
  have hgrid : ∀ i : Fin (e.degS + 1), (e.polyS x).eval ((i : ℕ) : K) = 0 := by
    intro i
    obtain ⟨hB, hv⟩ := h i (List.mem_range.2 i.2)
    have hp : e.polyN (i : ℤ) = 0 := by
      apply eq_zero_of_eval_large _ B
      · exact lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left 2 (l1_polyN_le e _)) hB
      · have := eval₂_polyN e (i : ℤ) B
        rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _] at this
        rw [Int.cast_id] at this
        exact this.trans hv
    rw [eval_polyS]
    have := eval₂_polyN (R := K) e (i : ℤ) x
    rw [hp] at this; simpa using this.symm
  have hz : e.polyS x = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun i : Fin (e.degS + 1) => ((i : ℕ) : K)) ?_ hgrid ?_
    · intro i j hij
      simp only [Nat.cast_inj] at hij
      exact Fin.ext hij
    · simpa using natDegree_polyS_le e x
  rw [← eval_polyS, hz, eval_zero]

end PE

end Zeta2L2Chi3
