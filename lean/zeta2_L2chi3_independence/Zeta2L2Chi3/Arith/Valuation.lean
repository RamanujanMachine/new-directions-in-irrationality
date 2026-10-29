/-
# p-adic valuation toolkit and the content/log bridge

`VGe p k x` (`x ∈ p^k ℤ_(p)`) is closed under the ring operations; the content of a rational vector
has `p`-adic valuation `min_i v_p(w_i)`; and `log cont(w) = Σ_p v_p(cont w) log p`.
-/
import Zeta2L2Chi3.Arith.Defs
import Zeta2L2Chi3.Content

namespace Zeta2L2Chi3.Arith

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem VGe.zero (k : ℤ) : VGe p k 0 := Or.inl rfl
theorem VGe.mono {k k' : ℤ} {x : ℚ} (h : VGe p k x) (hk : k' ≤ k) : VGe p k' x :=
  h.imp id (fun h => hk.trans h)
theorem VGe.add {k : ℤ} {x y : ℚ} (hx : VGe p k x) (hy : VGe p k y) : VGe p k (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  rcases hx with rfl | hx
  · simpa using (hy.resolve_left (by simpa using hxy))
  rcases hy with rfl | hy
  · simpa using hx
  exact (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy)
theorem VGe.neg {k : ℤ} {x : ℚ} (hx : VGe p k x) : VGe p k (-x) := by
  rcases hx with rfl | hx
  · exact Or.inl (by simp)
  · exact Or.inr (by simpa using hx)
theorem VGe.sub {k : ℤ} {x y : ℚ} (hx : VGe p k x) (hy : VGe p k y) : VGe p k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg
theorem VGe.mul {k l : ℤ} {x y : ℚ} (hx : VGe p k x) (hy : VGe p l y) : VGe p (k + l) (x * y) := by
  rcases hx with rfl | hx
  · exact Or.inl (by simp)
  rcases hy with rfl | hy
  · exact Or.inl (by simp)
  by_cases h0 : x = 0
  · exact Or.inl (by simp [h0])
  by_cases h1 : y = 0
  · exact Or.inl (by simp [h1])
  right; rw [padicValRat.mul h0 h1]; omega
theorem VGe.pow {k : ℤ} {x : ℚ} (m : ℕ) (hx : VGe p k x) : VGe p (m * k) (x ^ m) := by
  induction m with
  | zero => right; simp
  | succ m ih =>
    have := ih.mul hx
    rw [pow_succ]; convert this using 1; push_cast; ring
theorem VGe.list_sum {k : ℤ} {l : List ℚ} (h : ∀ x ∈ l, VGe p k x) : VGe p k l.sum := by
  induction l with
  | nil => exact VGe.zero k
  | cons a l ih =>
    rw [List.sum_cons]
    exact (h a (by simp)).add (ih (fun x hx => h x (by simp [hx])))
theorem VGe.finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℚ} {k : ℤ} (h : ∀ i ∈ s, VGe p k (f i)) :
    VGe p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using VGe.zero (p := p) k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih (fun x hx => h x (by simp [hx])))
theorem VGe.list_prod {l : List ℚ} (h : ∀ x ∈ l, VGe p 0 x) : VGe p 0 l.prod := by
  induction l with
  | nil => right; simp
  | cons a l ih =>
    rw [List.prod_cons]
    simpa using (h a (by simp)).mul (ih (fun x hx => h x (by simp [hx])))
theorem VGe.intCast (z : ℤ) : VGe p 0 (z : ℚ) := by
  right; rw [padicValRat.of_int]; simp [padicValInt]
theorem VGe.natCast (m : ℕ) : VGe p 0 (m : ℚ) := by
  right; rw [padicValRat.of_nat]; simp
theorem VGe.zpow (k : ℤ) : VGe p k ((p : ℚ) ^ k) := by
  right; rw [padicValRat.zpow, padicValRat.self hp.out.one_lt]; simp
theorem VGe.iff {k : ℤ} {x : ℚ} (hx : x ≠ 0) : VGe p k x ↔ k ≤ padicValRat p x :=
  ⟨fun h => h.resolve_left hx, Or.inr⟩
/-- inverse of an element of exact valuation -/
theorem VGe.inv {x : ℚ} (hx : x ≠ 0) : VGe p (-padicValRat p x) x⁻¹ := by
  right; rw [padicValRat.inv]
/-- a rational whose denominator is prime to `p` is `p`-integral -/
theorem VGe.of_den {x : ℚ} (hd : ¬ p ∣ x.den) : VGe p 0 x := by
  right; rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hd]; simp [padicValInt]
/-- `x ∈ p ℤ_(p)` for `x` with denominator prime to `p` -/
theorem VGe.one_iff {x : ℚ} (hd : ¬ p ∣ x.den) : VGe p 1 x ↔ (p : ℤ) ∣ x.num := by
  have h1 := padicValInt_dvd_iff (p := p) 1 x.num
  rw [pow_one] at h1
  rw [h1]
  unfold VGe
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hd, Rat.num_eq_zero]
  simp
/-- a nonzero rational with numerator and denominator of absolute value `< p` is a `p`-unit -/
theorem padicValRat_eq_zero_of_small {x : ℚ} (hx : x ≠ 0) (hn : x.num.natAbs < p) (hd : x.den < p) :
    padicValRat p x = 0 := by
  have hn0 : x.num.natAbs ≠ 0 := by simpa using hx
  have h1 : ¬ p ∣ x.num.natAbs := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h) (by omega)
  have h2 : ¬ p ∣ x.den := fun h => absurd (Nat.le_of_dvd x.den_pos h) (by omega)
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd h2, padicValInt,
    padicValNat.eq_zero_of_not_dvd h1]
  simp
/-- if `x` is a unit and `x ≡ y (mod p)` then `1/x² ≡ 1/y² (mod p)` (both units) -/
theorem VGe.inv_sq_congr {x y : ℚ} (hx : padicValRat p x = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxy : VGe p 1 (x - y)) : VGe p 1 (1 / x ^ 2 - 1 / y ^ 2) := by
  have hX : VGe p 0 x := Or.inr hx.ge
  have hY : VGe p 0 y := by
    have := hX.sub (hxy.mono (by norm_num)); simpa using this
  have hy : padicValRat p y = 0 := by
    have hy' : 0 ≤ padicValRat p y := hY.resolve_left hy0
    by_contra hne
    have h1 : VGe p 1 y := Or.inr (by omega)
    have := (hxy.add h1)
    simp only [sub_add_cancel] at this
    have := this.resolve_left hx0
    omega
  have hinv : VGe p 0 ((x ^ 2 * y ^ 2)⁻¹) := by
    have := VGe.inv (p := p) (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hy0))
    rwa [padicValRat.mul (pow_ne_zero 2 hx0) (pow_ne_zero 2 hy0), padicValRat.pow,
      padicValRat.pow, hx, hy, mul_zero, add_zero, neg_zero] at this
  have key : 1 / x ^ 2 - 1 / y ^ 2 = (-(x - y)) * (y + x) * (x ^ 2 * y ^ 2)⁻¹ := by
    field_simp; ring
  rw [key]
  have := (hxy.neg.mul (hY.add hX)).mul hinv
  simpa using this

/-- `prim w` is primitive at `p`: some entry is prime to `p` -/
theorem exists_not_dvd_prim (w : Fin 3 → ℚ) (hw : w ≠ 0) : ∃ i, ¬ (p : ℤ) ∣ prim w i := by
  by_contra hcon
  push Not at hcon
  have hG := contG_ne_zero w hw
  have hdvd : ∀ i, p * contG w ∣ (intVec w i).natAbs := by
    intro i
    obtain ⟨m, hm⟩ := hcon i
    have : intVec w i = prim w i * contG w := (Int.ediv_mul_cancel (contG_dvd w i)).symm
    rw [this, hm, Int.natAbs_mul, Int.natAbs_mul]
    exact ⟨m.natAbs, by simp; ring⟩
  have : p * contG w ∣ contG w := by
    unfold contG at hdvd ⊢
    exact Nat.dvd_gcd (hdvd 0) (Nat.dvd_gcd (hdvd 1) (hdvd 2))
  have h2 : p * contG w ∣ 1 * contG w := by simpa using this
  have := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hG) h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)

/-- the content has valuation at least the minimum valuation of the entries -/
theorem le_padicValRat_cont (w : Fin 3 → ℚ) (hw : w ≠ 0) (k : ℤ) (h : ∀ i, VGe p k (w i)) :
    k ≤ padicValRat p (cont w) := by
  obtain ⟨i, hi⟩ := exists_not_dvd_prim (p := p) w hw
  have hc := (cont_pos w hw).ne'
  have hpi : (prim w i : ℚ) ≠ 0 := by
    intro h0; apply hi; rw [Int.cast_eq_zero.mp h0]; exact dvd_zero _
  have hwi := w_eq_cont_prim w hw i
  have hw0 : w i ≠ 0 := by rw [hwi]; exact mul_ne_zero hc hpi
  have := (h i).resolve_left hw0
  rw [hwi, padicValRat.mul hc hpi, padicValRat.of_int, padicValInt,
    padicValNat.eq_zero_of_not_dvd (by rwa [Int.natCast_dvd] at hi)] at this
  simpa using this

end

/-- `log x = Σ_{q ∈ T} v_q(x) log q` for positive rational `x` and a finite set of primes `T`
containing the prime factors of numerator and denominator -/
theorem log_eq_sum_padicValRat (x : ℚ) (hx : 0 < x) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime)
    (hnum : x.num.natAbs.primeFactors ⊆ T) (hden : x.den.primeFactors ⊆ T) :
    Real.log x = ∑ q ∈ T, (padicValRat q x : ℝ) * Real.log q := by
  have hn : (0 : ℤ) < x.num := Rat.num_pos.mpr hx
  have hxR : ((x : ℚ) : ℝ) = (x.num.natAbs : ℝ) / (x.den : ℝ) := by
    have : ((x.num.natAbs : ℤ) : ℝ) = (x.num : ℝ) := by
      rw [Int.natAbs_of_nonneg hn.le]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hn)]
    conv_lhs => rw [← Rat.num_div_den x]
    push_cast; rfl
  have hn0 : (x.num.natAbs : ℝ) ≠ 0 := by
    have : x.num.natAbs ≠ 0 := by omega
    exact_mod_cast this
  have hd0 : (x.den : ℝ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  rw [hxR, Real.log_div hn0 hd0, Real.log_nat_eq_sum_factorization,
    Real.log_nat_eq_sum_factorization]
  rw [Finsupp.sum_of_support_subset _ (by simpa [Nat.support_factorization] using hnum) _
      (by intros; simp),
    Finsupp.sum_of_support_subset _ (by simpa [Nat.support_factorization] using hden) _
      (by intros; simp), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [padicValRat_def, padicValInt, Nat.factorization_def _ (hT q hq),
    Nat.factorization_def _ (hT q hq)]
  simp only [Int.cast_sub, Int.cast_natCast]; ring

/-- `log cont(w) ≥ Σ_{q ∈ S} b_q log q` whenever `b_q ≤ v_q(w_i)` for all `q, i` and `b_q = 0` off `S` -/
theorem log_cont_ge (w : Fin 3 → ℚ) (hw : w ≠ 0) (S : Finset ℕ) (b : ℕ → ℤ)
    (hS : ∀ q ∈ S, q.Prime) (hb : ∀ q, q.Prime → ∀ i, VGe q (b q) (w i))
    (hb0 : ∀ q, q.Prime → q ∉ S → b q = 0) :
    ∑ q ∈ S, (b q : ℝ) * Real.log q ≤ Real.log (cont w) := by
  set x := cont w
  set T := S ∪ x.num.natAbs.primeFactors ∪ x.den.primeFactors
  have hT : ∀ q ∈ T, q.Prime := by
    intro q hq
    simp only [T, Finset.mem_union, Nat.mem_primeFactors] at hq
    rcases hq with (hq | hq) | hq
    · exact hS q hq
    · exact hq.1
    · exact hq.1
  rw [log_eq_sum_padicValRat x (cont_pos w hw) T hT (by intro q hq; simp [T, hq])
    (by intro q hq; simp [T, hq])]
  have hST : S ⊆ T := by intro q hq; simp [T, hq]
  rw [Finset.sum_subset hST (f := fun q => (b q : ℝ) * Real.log q)
    (fun q hqT hqS => by simp [hb0 q (hT q hqT) hqS])]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have : Fact q.Prime := ⟨hT q hq⟩
  have h1 : b q ≤ padicValRat q x := le_padicValRat_cont w hw (b q) (hb q (hT q hq))
  have h2 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) h2

end Zeta2L2Chi3.Arith
