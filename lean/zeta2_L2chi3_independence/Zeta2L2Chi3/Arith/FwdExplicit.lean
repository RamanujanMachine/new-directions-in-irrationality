/-
# Explicit partial-fraction coefficients of the forward kernel

For a pole `k ∈ KZ n = [-n, 10n+1]` of `R_n` (order `eZ n k ∈ {1, 2}`), put
`N = NF n` (the numerator `∏_z (t - z)`), `D_k = DF n k = ∏_{l ≠ k} (t - l)^{e_l}`,
`S_N = SNF n = Σ_z 1/(t - z)`, `S_D = SDF n k = Σ_{l ≠ k} e_l/(t - l)` and `g(t) = t^j N(t)/D_k(t)`.
Then

* double pole: `a_k = g(k) = k^j N(k)/D_k(k)` and `b_k = g'(k) = (j k^{j-1} + k^j (S_N(k) - S_D(k))) N(k)/D_k(k)`;
* simple pole: `a_k = 0`, `b_k = g(k)`.

`fa_fb_eq` identifies the abstract data `fa, fb` (defined by choice) with these rational numbers.
-/
import Zeta2L2Chi3.Forward
import Zeta2L2Chi3.Arith.Defs

open Polynomial Finset Filter Topology

noncomputable section

namespace Zeta2L2Chi3.Arith

/-! ### Poles, orders and the explicit building blocks -/

/-- the poles of `R_n`, as integers -/
def KZ (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) (10 * n + 1)

/-- the pole orders, as a function on integers -/
def eZ (n : ℕ) (k : ℤ) : ℕ := if 0 ≤ k ∧ k ≤ 8 * n + 1 then 2 else 1

section generic
variable {K : Type*} [Field K]

/-- the numerator of `R_n` (`= RNum n` over `ℝ`) -/
def NF (n : ℕ) (t : K) : K :=
  rf (t + 2 * n + 1) (10 * n + 1) * rf (t + 4 / 3) (6 * n + 1) * rf (t + 2 * n + 3 / 2) (3 * n + 1)

/-- the denominator of `R_n` with the pole `k` removed -/
def DF (n : ℕ) (k : ℤ) (t : K) : K := ∏ l ∈ (KZ n).erase k, (t - l) ^ eZ n l

/-- logarithmic derivative of the numerator -/
def SNF (n : ℕ) (t : K) : K :=
  ∑ i ∈ range (10 * n + 1), 1 / (t + 2 * n + 1 + i) + ∑ i ∈ range (6 * n + 1), 1 / (t + 4 / 3 + i) +
    ∑ i ∈ range (3 * n + 1), 1 / (t + 2 * n + 3 / 2 + i)

/-- logarithmic derivative of `DF n k` -/
def SDF (n : ℕ) (k : ℤ) (t : K) : K := ∑ l ∈ (KZ n).erase k, (eZ n l : K) / (t - l)

end generic

/-- `g(k) = k^j N(k)/D_k(k)` -/
def gQ (n j : ℕ) (k : ℤ) : ℚ := (k : ℚ) ^ j * (NF n (k : ℚ) / DF n k (k : ℚ))

/-- double-pole coefficient -/
def aQ (n j : ℕ) (k : ℤ) : ℚ := if eZ n k = 2 then gQ n j k else 0

/-- simple-pole coefficient -/
def bQ (n j : ℕ) (k : ℤ) : ℚ :=
  if eZ n k = 2 then
    ((j : ℚ) * (k : ℚ) ^ (j - 1) + (k : ℚ) ^ j * (SNF n (k : ℚ) - SDF n k (k : ℚ))) *
      (NF n (k : ℚ) / DF n k (k : ℚ))
  else gQ n j k

/-! ### Casts -/

lemma NF_cast (n : ℕ) (t : ℚ) : ((NF n t : ℚ) : ℝ) = NF n (t : ℝ) := by
  simp [NF, rf]

lemma DF_cast (n : ℕ) (k : ℤ) (t : ℚ) : ((DF n k t : ℚ) : ℝ) = DF n k (t : ℝ) := by
  simp [DF]

lemma SNF_cast (n : ℕ) (t : ℚ) : ((SNF n t : ℚ) : ℝ) = SNF n (t : ℝ) := by
  simp [SNF]

lemma SDF_cast (n : ℕ) (k : ℤ) (t : ℚ) : ((SDF n k t : ℚ) : ℝ) = SDF n k (t : ℝ) := by
  simp [SDF]

lemma aQ_cast (n j : ℕ) (k : ℤ) : ((aQ n j k : ℚ) : ℝ) =
    if eZ n k = 2 then (k : ℝ) ^ j * (NF n (k : ℝ) / DF n k (k : ℝ)) else 0 := by
  unfold aQ gQ
  split_ifs <;> push_cast [NF_cast, DF_cast] <;> rfl

lemma bQ_cast (n j : ℕ) (k : ℤ) : ((bQ n j k : ℚ) : ℝ) =
    if eZ n k = 2 then
      ((j : ℝ) * (k : ℝ) ^ (j - 1) + (k : ℝ) ^ j * (SNF n (k : ℝ) - SDF n k (k : ℝ))) *
        (NF n (k : ℝ) / DF n k (k : ℝ))
    else (k : ℝ) ^ j * (NF n (k : ℝ) / DF n k (k : ℝ)) := by
  unfold bQ gQ
  split_ifs <;> push_cast [NF_cast, DF_cast, SNF_cast, SDF_cast] <;> rfl

/-! ### Nonvanishing -/

lemma mem_KZ {n : ℕ} {k : ℤ} : k ∈ KZ n ↔ -(n : ℤ) ≤ k ∧ k ≤ 10 * n + 1 := Finset.mem_Icc

lemma NF_ne_zero (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) : NF n (k : ℚ) ≠ 0 := by
  rw [mem_KZ] at hk
  unfold NF rf
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine prod_ne_zero_iff.2 fun i _ => ?_
  · have : (k : ℚ) + 2 * n + 1 + i = ((k + 2 * n + 1 + i : ℤ) : ℚ) := by push_cast; ring
    rw [this, Int.cast_ne_zero]; omega
  · have : ((k : ℚ) + 4 / 3 + i) * 3 = ((3 * k + 4 + 3 * i : ℤ) : ℚ) := by push_cast; ring
    intro h
    rw [h, zero_mul, eq_comm, Int.cast_eq_zero] at this; omega
  · have : ((k : ℚ) + 2 * n + 3 / 2 + i) * 2 = ((2 * k + 4 * n + 3 + 2 * i : ℤ) : ℚ) := by
      push_cast; ring
    intro h
    rw [h, zero_mul, eq_comm, Int.cast_eq_zero] at this; omega

lemma DF_ne_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (k : ℤ) (t : K)
    (ht : ∀ l ∈ (KZ n).erase k, t ≠ l) : DF n k t ≠ 0 :=
  prod_ne_zero_iff.2 fun l hl => pow_ne_zero _ (sub_ne_zero.2 (ht l hl))

lemma DF_self_ne_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (k : ℤ) : DF n k (k : K) ≠ 0 :=
  DF_ne_zero n k _ fun l hl h => (ne_of_mem_erase hl) (by exact_mod_cast h.symm)

/-! ### The real picture: products over `KF n` -/

lemma prod_KF (n : ℕ) (f : ℝ → ℝ) : ∏ x ∈ KF n, f x = ∏ l ∈ KZ n, f l :=
  prod_image (fun _ _ _ _ h => Int.cast_injective h)

lemma sum_KF (n : ℕ) (f : ℝ → ℝ) : ∑ x ∈ KF n, f x = ∑ l ∈ KZ n, f l :=
  sum_image (fun _ _ _ _ h => Int.cast_injective h)

lemma mem_KF (n : ℕ) (l : ℤ) : (l : ℝ) ∈ KF n ↔ l ∈ KZ n := by
  simp only [KF, KZ, mem_image, Int.cast_inj]
  exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun h => ⟨l, h, rfl⟩⟩

lemma eF_cast (n : ℕ) (l : ℤ) : eF n (l : ℝ) = eZ n l := by
  have : (0 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 8 * n + 1) ↔ (0 ≤ l ∧ l ≤ 8 * n + 1) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
    · exact_mod_cast h1
    · exact_mod_cast h2
  simp only [eF, eZ, this]

lemma Dprod_split (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (t : ℝ) :
    ∏ x ∈ KF n, (t - x) ^ eF n x = (t - k) ^ eZ n k * DF n k t := by
  rw [prod_KF]
  simp only [eF_cast]
  rw [← mul_prod_erase _ _ hk]
  rfl

lemma RNumPoly_eval_NF (n : ℕ) (t : ℝ) : (RNumPoly n).eval t = NF n t := by
  simp only [RNumPoly, NF, rf, eval_mul, eval_prod, eval_add, eval_X, eval_C]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;> exact prod_congr rfl fun i _ => by ring

lemma fdata_simple (n j : ℕ) : ∀ k ∈ KF n, eF n k ≤ 1 → fa n j k = 0 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (fdata_exists n j)))).1

/-! ### Derivatives -/

theorem hasDerivAt_prod_pow {ι : Type*} (s : Finset ι) (c : ι → ℝ) (e : ι → ℕ) (x : ℝ)
    (hx : ∀ i ∈ s, x - c i ≠ 0) :
    HasDerivAt (fun t => ∏ i ∈ s, (t - c i) ^ e i)
      ((∏ i ∈ s, (x - c i) ^ e i) * ∑ i ∈ s, (e i : ℝ) / (x - c i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (1 : ℝ)
  | insert a s ha ih =>
    have h1 : HasDerivAt (fun t => (t - c a) ^ e a) ((e a : ℝ) * (x - c a) ^ (e a - 1) * 1) x :=
      ((hasDerivAt_id' x).sub_const (c a)).pow (e a)
    have h2 := ih (fun i hi => hx i (mem_insert_of_mem hi))
    have h3 := h1.mul h2
    simp only [prod_insert ha, sum_insert ha]
    convert h3 using 1
    have hxa := hx a (mem_insert_self a s)
    have key : (e a : ℝ) * (x - c a) ^ (e a - 1) = (x - c a) ^ e a * ((e a : ℝ) / (x - c a)) := by
      rcases Nat.eq_zero_or_pos (e a) with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, e a = m + 1 := ⟨e a - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, pow_succ]
        field_simp
    rw [mul_one, key]
    ring

theorem hasDerivAt_rf (c : ℝ) (m : ℕ) (x : ℝ) (hx : ∀ i ∈ range m, x + c + i ≠ 0) :
    HasDerivAt (fun t => rf (t + c) m) (rf (x + c) m * ∑ i ∈ range m, 1 / (x + c + i)) x := by
  have h := hasDerivAt_prod_pow (range m) (fun i => -(c + i)) (fun _ => 1) x
    (fun i hi h => hx i hi (by linarith))
  have e1 : (fun t => rf (t + c) m) = fun t => ∏ i ∈ range m, (t - -(c + (i : ℝ))) ^ (fun _ => 1) i := by
    funext t
    simp only [rf, pow_one]
    exact prod_congr rfl fun i _ => by ring
  rw [e1]
  convert h using 1
  simp only [rf, pow_one, Nat.cast_one]
  congr 1
  · exact prod_congr rfl fun i _ => by ring
  · exact sum_congr rfl fun i _ => by ring_nf

theorem hasDerivAt_NF (n : ℕ) (x : ℝ) (hx : NF n x ≠ 0) :
    HasDerivAt (fun t => NF n t) (NF n x * SNF n x) x := by
  unfold NF at hx ⊢
  have h12 := left_ne_zero_of_mul hx
  have h3 := right_ne_zero_of_mul hx
  have h1 := left_ne_zero_of_mul h12
  have h2 := right_ne_zero_of_mul h12
  unfold rf at h1 h2 h3
  have d1 := hasDerivAt_rf (2 * n + 1) (10 * n + 1) x (fun i hi => by
    have := prod_ne_zero_iff.1 h1 i hi; rwa [← add_assoc])
  have d2 := hasDerivAt_rf (4 / 3) (6 * n + 1) x (fun i hi => prod_ne_zero_iff.1 h2 i hi)
  have d3 := hasDerivAt_rf (2 * n + 3 / 2) (3 * n + 1) x (fun i hi => by
    have := prod_ne_zero_iff.1 h3 i hi; rwa [← add_assoc])
  simp only [← add_assoc] at d1 d3
  convert (d1.mul d2).mul d3 using 1
  simp only [SNF, Pi.mul_apply]
  ring

theorem hasDerivAt_DF (n : ℕ) (k : ℤ) (x : ℝ) (hx : ∀ l ∈ (KZ n).erase k, x - l ≠ 0) :
    HasDerivAt (fun t => DF n k t) (DF n k x * SDF n k x) x :=
  hasDerivAt_prod_pow ((KZ n).erase k) (fun l => (l : ℝ)) (eZ n) x hx

theorem hasDerivAt_g (n j : ℕ) (k : ℤ) (x : ℝ) (hN : NF n x ≠ 0) (hD : DF n k x ≠ 0)
    (hx : ∀ l ∈ (KZ n).erase k, x - l ≠ 0) :
    HasDerivAt (fun t => t ^ j * NF n t / DF n k t)
      (((j : ℝ) * x ^ (j - 1) + x ^ j * (SNF n x - SDF n k x)) * (NF n x / DF n k x)) x := by
  have h := ((hasDerivAt_pow j x).mul (hasDerivAt_NF n x hN)).div (hasDerivAt_DF n k x hx) hD
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-! ### Identification of `fa`, `fb` -/

theorem fa_fb_eq (n j : ℕ) (k : ℤ) (hk : k ∈ KZ n) :
    fa n j (k : ℝ) = ((aQ n j k : ℚ) : ℝ) ∧ fb n j (k : ℝ) = ((bQ n j k : ℚ) : ℝ) := by
  set x : ℝ := (Int.cast k : ℝ) with hxdef
  have hxK : x ∈ KF n := (mem_KF n k).2 hk
  have hev := pf_eventually_notMem (KF n) x
  have hne : ∀ t ∉ KF n, ∀ l ∈ KZ n, t - l ≠ 0 := fun t ht l hl h =>
    ht (by rw [sub_eq_zero.1 h]; exact (mem_KF n l).2 hl)
  have hrep : ∀ t ∉ KF n, pfEval (KF n) (fq n j) (fa n j) (fb n j) t =
      t ^ j * NF n t / ((t - x) ^ eZ n k * DF n k t) := by
    intro t ht
    rw [← fdata_spec n j t ht, eval_mul, eval_pow, eval_X, RNumPoly_eval_NF, Dprod_split n k hk]
  have hD0 : ∀ t ∉ KF n, DF n k t ≠ 0 := fun t ht =>
    DF_ne_zero n k t fun l hl => sub_ne_zero.1 (hne t ht l (mem_of_mem_erase hl))
  have hDx : DF n k x ≠ 0 := DF_self_ne_zero n k
  have hNx : NF n x ≠ 0 := by
    rw [hxdef, ← Rat.cast_intCast, ← NF_cast]
    exact_mod_cast NF_ne_zero n k hk
  have hxl : ∀ l ∈ (KZ n).erase k, x - l ≠ 0 := fun l hl h =>
    (ne_of_mem_erase hl) (by have := (sub_eq_zero.1 h).symm; rw [hxdef] at this; exact_mod_cast this)
  have hg := hasDerivAt_g n j k x hNx hDx hxl
  set g : ℝ → ℝ := fun t => t ^ j * NF n t / DF n k t with hgdef
  have hgc : Tendsto g (𝓝[≠] x) (𝓝 (g x)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [aQ_cast, bQ_cast]
  by_cases he : eZ n k = 2
  · simp only [he, ite_true]
    have ha : fa n j x = g x := by
      refine tendsto_nhds_unique (tendsto_double (KF n) (fq n j) (fa n j) (fb n j) x hxK) ?_
      refine hgc.congr' ?_
      filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
      have htx : t - x ≠ 0 := sub_ne_zero.2 ht'
      rw [hrep t ht, he, hgdef]
      field_simp [hD0 t ht]
    refine ⟨by rw [ha, hgdef]; ring, ?_⟩
    refine tendsto_nhds_unique (tendsto_simple (KF n) (fq n j) (fa n j) (fb n j) x hxK) ?_
    refine (hasDerivAt_iff_tendsto_slope.1 hg).congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
    have htx : t - x ≠ 0 := sub_ne_zero.2 ht'
    rw [hrep t ht, he, ha, slope_def_field, hgdef]
    field_simp [hD0 t ht]
  · have he1 : eZ n k = 1 := by unfold eZ at he ⊢; split_ifs at he ⊢ <;> simp_all
    simp only [he, ite_false]
    have ha : fa n j x = 0 := fdata_simple n j x hxK (by rw [hxdef, eF_cast]; omega)
    refine ⟨ha, ?_⟩
    refine tendsto_nhds_unique (tendsto_simple (KF n) (fq n j) (fa n j) (fb n j) x hxK) ?_
    have : g x = x ^ j * (NF n x / DF n k x) := by rw [hgdef]; ring
    rw [← this]
    refine hgc.congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
    have htx : t - x ≠ 0 := sub_ne_zero.2 ht'
    rw [hrep t ht, he1, ha, hgdef]
    field_simp [hD0 t ht]
    ring

end Zeta2L2Chi3.Arith
