/-
# Generic lemmas on partial-fraction data and the forward functionals

* extension by zero (`ind`) and linear combinations of partial-fraction data;
* `Hsig_succ`: `H^{(j)}_ρ(m+1) - H^{(j)}_ρ(m) = (ρ+m)^{-j}` for all `m ∈ ℤ`;
* `Ubern_succ`: `U(q, x) - U(q, x+1) = q(-x)` (Bernoulli), and `Ubern_dq`: for the difference
  `Δq(t) = q(t) - q(t-1)`, `U(Δq, x) = q(-x) + κU q` with `κU q` independent of `x`;
* `pfun_succ`: shifting the start `m ↦ m+1` of `p_ρ^{(m)}`;
* `pfEval_delta`, `sum_da`, `pfun_delta`: the data of a difference `X(t) - X(t-1)`, and the
  values of `DP` and `p_ρ^{(m)}` on it.
-/
import Zeta2L2Chi3.Forward

open Polynomial Finset

noncomputable section

namespace Zeta2L2Chi3

/-! ### Extension by zero -/

/-- extension by zero of partial-fraction coefficients -/
def ind (K : Finset ℝ) (a : ℝ → ℝ) (k : ℝ) : ℝ := if k ∈ K then a k else 0

lemma sum_ind_mul (K S : Finset ℝ) (h : K ⊆ S) (a F : ℝ → ℝ) :
    ∑ k ∈ S, ind K a k * F k = ∑ k ∈ K, a k * F k := by
  rw [← sum_subset h (fun k _ hk => by simp [ind, hk])]
  exact sum_congr rfl fun k hk => by simp [ind, hk]

lemma sum_ind (K S : Finset ℝ) (h : K ⊆ S) (a : ℝ → ℝ) :
    ∑ k ∈ S, ind K a k = ∑ k ∈ K, a k := by
  simpa using sum_ind_mul K S h a (fun _ => 1)

lemma sum_ind_shift_mul (K S : Finset ℝ) (h : K.image (· + 1) ⊆ S) (a F : ℝ → ℝ) :
    ∑ k ∈ S, ind K a (k - 1) * F k = ∑ k ∈ K, a k * F (k + 1) := by
  rw [← sum_subset h (fun k _ hk => ?_)]
  · rw [sum_image (fun x _ y _ hxy => by simpa using hxy)]
    exact sum_congr rfl fun k hk => by simp [ind, hk]
  · have : k - 1 ∉ K := fun h' => hk (mem_image.2 ⟨k - 1, h', by ring⟩)
    simp [ind, this]

lemma pfEval_ext (K K' : Finset ℝ) (h : K ⊆ K') (q : ℝ[X]) (a b : ℝ → ℝ) (t : ℝ) :
    pfEval K' q (ind K a) (ind K b) t = pfEval K q a b t := by
  unfold pfEval
  congr 1
  rw [← sum_subset h (fun k _ hk => by simp [ind, hk])]
  exact sum_congr rfl fun k hk => by simp [ind, hk]

lemma pfun_ext (K K' : Finset ℝ) (h : K ⊆ K') (q : ℝ[X]) (a b : ℝ → ℝ) (ρ : ℝ) (m : ℤ) :
    pfun K' q (ind K a) (ind K b) ρ m = pfun K q a b ρ m := by
  unfold pfun
  congr 1
  rw [← sum_subset h (fun k _ hk => by simp [ind, hk])]
  exact sum_congr rfl fun k hk => by simp [ind, hk]

lemma pfEval_congr (K : Finset ℝ) (q : ℝ[X]) (a b a' b' : ℝ → ℝ)
    (h : ∀ k ∈ K, a k = a' k ∧ b k = b' k) (t : ℝ) :
    pfEval K q a b t = pfEval K q a' b' t := by
  unfold pfEval
  congr 1
  exact sum_congr rfl fun k hk => by rw [(h k hk).1, (h k hk).2]

lemma pfun_congr (K : Finset ℝ) (q : ℝ[X]) (a b a' b' : ℝ → ℝ)
    (h : ∀ k ∈ K, a k = a' k ∧ b k = b' k) (ρ : ℝ) (m : ℤ) :
    pfun K q a b ρ m = pfun K q a' b' ρ m := by
  unfold pfun
  congr 1
  exact sum_congr rfl fun k hk => by rw [(h k hk).1, (h k hk).2]

/-! ### The Bernoulli term -/

lemma Ubern_eq_range (q : ℝ[X]) (N : ℕ) (hN : ∀ i, N ≤ i → q.coeff i = 0) (x : ℝ) :
    Ubern q x = ∑ i ∈ range N, q.coeff i * (-1) ^ i * zetaNeg i x := by
  have k1 : ∑ i ∈ range N, q.coeff i * (-1) ^ i * zetaNeg i x =
      ∑ i ∈ range (max N (q.natDegree + 1)), q.coeff i * (-1) ^ i * zetaNeg i x := by
    apply sum_subset (range_subset_range.2 (le_max_left _ _))
    intro i _ hi
    simp only [mem_range, not_lt] at hi
    rw [hN i hi]; ring
  have k2 : ∑ i ∈ range (q.natDegree + 1), q.coeff i * (-1) ^ i * zetaNeg i x =
      ∑ i ∈ range (max N (q.natDegree + 1)), q.coeff i * (-1) ^ i * zetaNeg i x := by
    apply sum_subset (range_subset_range.2 (le_max_right _ _))
    intro i _ hi
    simp only [mem_range, not_lt] at hi
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring
  unfold Ubern
  rw [k1, k2]

lemma Ubern_add (p q : ℝ[X]) (x : ℝ) : Ubern (p + q) x = Ubern p x + Ubern q x := by
  set N := p.natDegree + q.natDegree + 1
  have hp : ∀ i, N ≤ i → p.coeff i = 0 := fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)
  have hq : ∀ i, N ≤ i → q.coeff i = 0 := fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Ubern_eq_range _ N (fun i hi => by rw [coeff_add, hp i hi, hq i hi, add_zero]),
    Ubern_eq_range p N hp, Ubern_eq_range q N hq, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by rw [coeff_add]; ring

lemma Ubern_C_mul (c : ℝ) (p : ℝ[X]) (x : ℝ) : Ubern (Polynomial.C c * p) x = c * Ubern p x := by
  set N := p.natDegree + 1
  have hp : ∀ i, N ≤ i → p.coeff i = 0 := fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Ubern_eq_range _ N (fun i hi => by rw [coeff_C_mul, hp i hi, mul_zero]),
    Ubern_eq_range p N hp, mul_sum]
  exact sum_congr rfl fun i _ => by rw [coeff_C_mul]; ring

lemma Ubern_neg (p : ℝ[X]) (x : ℝ) : Ubern (-p) x = -Ubern p x := by
  rw [show -p = Polynomial.C (-1) * p by simp, Ubern_C_mul]; ring

lemma Ubern_sub (p q : ℝ[X]) (x : ℝ) : Ubern (p - q) x = Ubern p x - Ubern q x := by
  rw [sub_eq_add_neg, Ubern_add, Ubern_neg]; ring

lemma Ubern_zero (x : ℝ) : Ubern 0 x = 0 := by simp [Ubern]

lemma Ubern_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (x : ℝ) :
    Ubern (∑ i ∈ s, p i) x = ∑ i ∈ s, Ubern (p i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ubern_zero]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, Ubern_add, ih]

lemma bern_eval_add_one (n : ℕ) (x : ℝ) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval (x + 1) =
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval x + n * x ^ (n - 1) := by
  have h := congrArg (fun p : ℚ[X] => (p.map (algebraMap ℚ ℝ)).eval x)
    (Polynomial.bernoulli_comp_one_add_X n)
  simp only [Polynomial.map_comp, eval_comp, Polynomial.map_add, eval_add, Polynomial.map_one,
    Polynomial.map_X, eval_one, eval_X, Polynomial.map_pow, nsmul_eq_mul, Polynomial.map_mul,
    Polynomial.map_natCast, eval_mul, eval_natCast, eval_pow] at h
  rw [add_comm x 1, h]

lemma zetaNeg_sub (i : ℕ) (x : ℝ) : zetaNeg i x - zetaNeg i (x + 1) = x ^ i := by
  unfold zetaNeg
  rw [bern_eval_add_one, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma Ubern_succ (q : ℝ[X]) (x : ℝ) : Ubern q x - Ubern q (x + 1) = q.eval (-x) := by
  unfold Ubern
  rw [← sum_sub_distrib, eval_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sub, zetaNeg_sub, neg_pow]
  ring

/-- the Bernoulli term as a polynomial function -/
def UP (r : ℝ[X]) : ℝ[X] := ∑ i ∈ range (r.natDegree + 1),
  Polynomial.C (r.coeff i * (-1) ^ i * (-1 / (i + 1))) * (Polynomial.bernoulli (i + 1)).map (algebraMap ℚ ℝ)

lemma UP_eval (r : ℝ[X]) (x : ℝ) : (UP r).eval x = Ubern r x := by
  unfold UP Ubern zetaNeg
  rw [eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]
  ring

lemma poly_periodic_const (p : ℝ[X]) (hp : ∀ x, p.eval (x + 1) = p.eval x) (x y : ℝ) :
    p.eval x = p.eval y := by
  have h : p - Polynomial.C (p.eval y) = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hr : ∀ k : ℕ, (p - Polynomial.C (p.eval y)).IsRoot (y + k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [IsRoot, eval_sub, eval_C] at ih ⊢
        rw [show y + ((k + 1 : ℕ) : ℝ) = (y + k) + 1 by push_cast; ring, hp]
        exact ih
    exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => y + k)
      (fun a b hab => by simpa using hab) hr
  have := congrArg (eval x) h
  simpa [sub_eq_zero] using this

/-- the difference polynomial `q(t) - q(t-1)` -/
def dq (q : ℝ[X]) : ℝ[X] := q - q.comp (X - Polynomial.C 1)

/-- the constant in `U(Δq, x) = q(-x) + κU q` -/
def κU (q : ℝ[X]) : ℝ := Ubern (dq q) 0 - q.eval 0

lemma Ubern_dq (q : ℝ[X]) (x : ℝ) : Ubern (dq q) x = q.eval (-x) + κU q := by
  set p := UP (dq q) - q.comp (-X)
  have hp : ∀ x, p.eval x = Ubern (dq q) x - q.eval (-x) := by
    intro x; simp [p, UP_eval]
  have hper : ∀ x, p.eval (x + 1) = p.eval x := by
    intro x
    rw [hp, hp]
    have h1 := Ubern_succ (dq q) x
    have h2 : (dq q).eval (-x) = q.eval (-x) - q.eval (-x - 1) := by
      simp only [dq, eval_sub, eval_comp, eval_X, eval_C]
    rw [h2] at h1
    have : -(x + 1) = -x - 1 := by ring
    rw [this]
    linarith
  have := poly_periodic_const p hper x 0
  rw [hp, hp, neg_zero] at this
  unfold κU
  linarith

/-! ### The harmonic sums -/

lemma Hsig_succ (j : ℕ) (ρ : ℝ) (m : ℤ) :
    Hsig j ρ (m + 1) - Hsig j ρ m = 1 / (ρ + m) ^ j := by
  rcases le_or_gt 0 m with hm | hm
  · have h1 : 0 ≤ m + 1 := by omega
    simp only [Hsig, if_pos hm, if_pos h1]
    rw [show (m + 1).toNat = m.toNat + 1 by omega, sum_range_succ]
    have : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg hm
    rw [this]; ring
  · rcases eq_or_lt_of_le (show m + 1 ≤ 0 by omega) with h | h
    · have hm1 : m = -1 := by omega
      subst hm1
      simp [Hsig]
    · simp only [Hsig, if_neg (show ¬ 0 ≤ m by omega), if_neg (show ¬ 0 ≤ m + 1 by omega)]
      rw [show (-m).toNat = (-(m + 1)).toNat + 1 by omega, sum_range_succ']
      have : ∑ l ∈ range (-(m + 1)).toNat, 1 / (ρ + ((m + 1 : ℤ) : ℝ) + l) ^ j =
          ∑ l ∈ range (-(m + 1)).toNat, 1 / (ρ + m + ((l + 1 : ℕ) : ℝ)) ^ j :=
        sum_congr rfl fun l _ => by push_cast; ring_nf
      rw [this]
      simp only [Nat.cast_zero, add_zero]
      ring

/-! ### Integer-pole data and the start shift -/

/-- every pole with a nonzero coefficient is an integer -/
def IntData (K : Finset ℝ) (a b : ℝ → ℝ) : Prop :=
  ∀ k ∈ K, ((⌊k⌋ : ℤ) : ℝ) = k ∨ (a k = 0 ∧ b k = 0)

lemma term_eq (a b ρ k : ℝ) (m : ℤ) (hk : ((⌊k⌋ : ℤ) : ℝ) = k ∨ (a = 0 ∧ b = 0)) :
    a * (1 / (ρ + ((⌊k⌋ + m : ℤ) : ℝ)) ^ 2) - b * (1 / (ρ + ((⌊k⌋ + m : ℤ) : ℝ)) ^ 1) =
      a / (-(ρ + m) - k) ^ 2 + b / (-(ρ + m) - k) := by
  rcases hk with hk | ⟨ha, hb⟩
  · push_cast
    rw [hk]
    have e : -(ρ + m) - k = -(ρ + (k + m)) := by ring
    rw [e, neg_sq, div_neg]
    ring
  · simp [ha, hb]

lemma pfun_succ (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (hI : IntData K a b) (ρ : ℝ) (m : ℤ) :
    pfun K q a b ρ (m + 1) = pfun K q a b ρ m + pfEval K q a b (-(ρ + m)) := by
  have hU := Ubern_succ q (ρ + m)
  unfold pfun pfEval
  have hx : ρ + ((m + 1 : ℤ) : ℝ) = ρ + m + 1 := by push_cast; ring
  rw [hx]
  have hsum : ∑ k ∈ K, (a k * Hsig 2 ρ (⌊k⌋ + (m + 1)) - b k * Hsig 1 ρ (⌊k⌋ + (m + 1))) =
      ∑ k ∈ K, (a k * Hsig 2 ρ (⌊k⌋ + m) - b k * Hsig 1 ρ (⌊k⌋ + m)) +
        ∑ k ∈ K, (a k / (-(ρ + m) - k) ^ 2 + b k / (-(ρ + m) - k)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have h2 := Hsig_succ 2 ρ (⌊k⌋ + m)
    have h1 := Hsig_succ 1 ρ (⌊k⌋ + m)
    rw [show ⌊k⌋ + (m + 1) = ⌊k⌋ + m + 1 by ring, ← term_eq (a k) (b k) ρ k m (hI k hk)]
    linear_combination a k * h2 - b k * h1
  rw [hsum]
  linarith

/-! ### Differences `X(t) - X(t-1)` -/

/-- coefficients of the difference -/
def da (K : Finset ℝ) (a : ℝ → ℝ) (k : ℝ) : ℝ := ind K a k - ind K a (k - 1)

lemma pfEval_delta (K S : Finset ℝ) (h1 : K ⊆ S) (h2 : K.image (· + 1) ⊆ S) (q : ℝ[X])
    (a b : ℝ → ℝ) (t : ℝ) :
    pfEval S (dq q) (da K a) (da K b) t = pfEval K q a b t - pfEval K q a b (t - 1) := by
  unfold pfEval dq da
  simp only [eval_sub, eval_comp, eval_X, eval_C]
  have e1 : ∑ k ∈ S, ((ind K a k - ind K a (k - 1)) / (t - k) ^ 2 +
      (ind K b k - ind K b (k - 1)) / (t - k)) =
      (∑ k ∈ S, ind K a k * (1 / (t - k) ^ 2) + ∑ k ∈ S, ind K b k * (1 / (t - k))) -
      (∑ k ∈ S, ind K a (k - 1) * (1 / (t - k) ^ 2) +
        ∑ k ∈ S, ind K b (k - 1) * (1 / (t - k))) := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [e1, sum_ind_mul K S h1, sum_ind_mul K S h1, sum_ind_shift_mul K S h2,
    sum_ind_shift_mul K S h2]
  have e3 : ∀ s : ℝ, ∑ k ∈ K, (a k / (s - k) ^ 2 + b k / (s - k)) =
      ∑ k ∈ K, a k * (1 / (s - k) ^ 2) + ∑ k ∈ K, b k * (1 / (s - k)) := by
    intro s
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have e4 : ∀ k : ℝ, t - (k + 1) = t - 1 - k := fun k => by ring
  simp only [e4]
  rw [e3, e3]
  ring

lemma sum_da (K S : Finset ℝ) (h1 : K ⊆ S) (h2 : K.image (· + 1) ⊆ S) (a : ℝ → ℝ) :
    ∑ k ∈ S, da K a k = 0 := by
  unfold da
  rw [sum_sub_distrib]
  have e1 := sum_ind_mul K S h1 a (fun _ => 1)
  have e2 := sum_ind_shift_mul K S h2 a (fun _ => 1)
  simp only [mul_one] at e1 e2
  rw [e1, e2, sub_self]

lemma pfun_delta (K S : Finset ℝ) (h1 : K ⊆ S) (h2 : K.image (· + 1) ⊆ S) (q : ℝ[X])
    (a b : ℝ → ℝ) (hI : IntData K a b) (ρ : ℝ) (m : ℤ) :
    pfun S (dq q) (da K a) (da K b) ρ m = -pfEval K q a b (-(ρ + m)) - κU q := by
  unfold pfun
  rw [Ubern_dq]
  have e1 : ∑ k ∈ S, (da K a k * Hsig 2 ρ (⌊k⌋ + m) - da K b k * Hsig 1 ρ (⌊k⌋ + m)) =
      (∑ k ∈ S, ind K a k * Hsig 2 ρ (⌊k⌋ + m) - ∑ k ∈ S, ind K b k * Hsig 1 ρ (⌊k⌋ + m)) -
      (∑ k ∈ S, ind K a (k - 1) * Hsig 2 ρ (⌊k⌋ + m) -
        ∑ k ∈ S, ind K b (k - 1) * Hsig 1 ρ (⌊k⌋ + m)) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by unfold da; ring
  rw [e1, sum_ind_mul K S h1, sum_ind_mul K S h1,
    sum_ind_shift_mul K S h2 a (fun k => Hsig 2 ρ (⌊k⌋ + m)),
    sum_ind_shift_mul K S h2 b (fun k => Hsig 1 ρ (⌊k⌋ + m))]
  have e2 : (∑ k ∈ K, a k * Hsig 2 ρ (⌊k⌋ + m) - ∑ k ∈ K, b k * Hsig 1 ρ (⌊k⌋ + m)) -
      (∑ k ∈ K, a k * Hsig 2 ρ (⌊k + 1⌋ + m) - ∑ k ∈ K, b k * Hsig 1 ρ (⌊k + 1⌋ + m)) =
      -∑ k ∈ K, (a k / (-(ρ + m) - k) ^ 2 + b k / (-(ρ + m) - k)) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    have h2 := Hsig_succ 2 ρ (⌊k⌋ + m)
    have h1 := Hsig_succ 1 ρ (⌊k⌋ + m)
    rw [Int.floor_add_one, show ⌊k⌋ + 1 + m = ⌊k⌋ + m + 1 by ring,
      ← term_eq (a k) (b k) ρ k m (hI k hk)]
    linear_combination (-(a k)) * h2 + b k * h1
  rw [e2, pfEval]
  ring

/-! ### Linear combinations of four data -/

lemma pfEval_lin (K : Finset ℝ) (q0 : ℝ[X]) (a0 b0 : ℝ → ℝ) (w : Fin 4 → ℝ) (q : Fin 4 → ℝ[X])
    (a b : Fin 4 → ℝ → ℝ) (t : ℝ) :
    pfEval K (q0 - ∑ l, Polynomial.C (w l) * q l) (fun k => a0 k - ∑ l, w l * a l k)
      (fun k => b0 k - ∑ l, w l * b l k) t =
    pfEval K q0 a0 b0 t - ∑ l, w l * pfEval K (q l) (a l) (b l) t := by
  unfold pfEval
  simp only [Fin.sum_univ_four, eval_sub, eval_add, eval_mul, eval_C]
  simp only [sub_div, add_div, sum_add_distrib, sum_sub_distrib, mul_add, mul_sum, mul_div_assoc]
  ring

lemma pfun_lin (K : Finset ℝ) (q0 : ℝ[X]) (a0 b0 : ℝ → ℝ) (w : Fin 4 → ℝ) (q : Fin 4 → ℝ[X])
    (a b : Fin 4 → ℝ → ℝ) (ρ : ℝ) (m : ℤ) :
    pfun K (q0 - ∑ l, Polynomial.C (w l) * q l) (fun k => a0 k - ∑ l, w l * a l k)
      (fun k => b0 k - ∑ l, w l * b l k) ρ m =
    pfun K q0 a0 b0 ρ m - ∑ l, w l * pfun K (q l) (a l) (b l) ρ m := by
  unfold pfun
  rw [Ubern_sub, Ubern_sum]
  simp only [Ubern_C_mul]
  have e : ∀ k, (a0 k - ∑ l, w l * a l k) * Hsig 2 ρ (⌊k⌋ + m) -
      (b0 k - ∑ l, w l * b l k) * Hsig 1 ρ (⌊k⌋ + m) =
      (a0 k * Hsig 2 ρ (⌊k⌋ + m) - b0 k * Hsig 1 ρ (⌊k⌋ + m)) -
        ∑ l, w l * (a l k * Hsig 2 ρ (⌊k⌋ + m) - b l k * Hsig 1 ρ (⌊k⌋ + m)) := by
    intro k; simp only [Fin.sum_univ_four]; ring
  rw [sum_congr rfl (fun k _ => e k), sum_sub_distrib, sum_comm]
  simp only [← mul_sum]
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

end Zeta2L2Chi3
