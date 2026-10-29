/-
# Auxiliary machinery for Lemma A, part 3: the dual zeros and poles

The concrete zero list `Zd n` and pole records `Pd n p` of `F_n`, the identification of the
packet types with `dualTypeAt`, of the residues with `vres`, and the verification of `Hyp`.
-/
import Zeta2L2Chi3.Arith.LemmaAAux2
import Zeta2L2Chi3.Arith.Lattice
import Zeta2L2Chi3.Dual

namespace Zeta2L2Chi3.Arith
namespace LA

open Finset

/-- the members `c + i` of a family -/
def famMem (f : Fam) (n : ℕ) : List ℚ := (List.range (f.len n)).map (fun i : ℕ => f.c n + (i : ℚ))

/-- pole records of a family with label `lab` and weights `w` -/
def recs (f : Fam) (n lab : ℕ) (w : ℕ → ℚ) : List Rec :=
  (List.range (f.len n)).map (fun j : ℕ => (f.c n + (j : ℚ), lab, w j))

/-- the zeros of `F_n` -/
def Zd (n : ℕ) : List ℚ := famMem (dualZ[0]!) n ++ famMem (dualZ[1]!) n

/-- the poles of `F_n` with labels and harmonic weights `h(ρ) + c_θ` -/
def Pd (n p : ℕ) : List Rec :=
  recs (dualP[0]!) n 0 (fun j => hwI n j) ++ recs (dualP[1]!) n 1 (fun j => hwT j + cT p) ++
    recs (dualP[2]!) n 2 (fun j => hwH n j + cH p)

theorem dz0 : dualZ[0]! = ⟨-10, -1, 10, 1⟩ := rfl
theorem dz1 : dualZ[1]! = ⟨-8, -1, 9, 1⟩ := rfl
theorem dp0 : dualP[0]! = ⟨2, 0, 10, 2⟩ := rfl
theorem dp1 : dualP[1]! = ⟨0, 1 / 3, 6, 2⟩ := rfl
theorem dp2 : dualP[2]! = ⟨2, 1 / 2, 3, 2⟩ := rfl

/-! ### List / Finset conversions -/

theorem lprod_range (N : ℕ) (f : ℕ → ℚ) : ((List.range N).map f).prod = ∏ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.prod_append, ih, prod_range_succ]; simp

theorem lsum_range (N : ℕ) (f : ℕ → ℚ) : ((List.range N).map f).sum = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem prod_map_filter {α : Type*} (l : List α) (P : α → Bool) (g : α → ℚ) :
    ((l.filter P).map g).prod = (l.map (fun x => if P x then g x else 1)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem sum_recs (f : Fam) (n lab : ℕ) (w : ℕ → ℚ) (g : Rec → ℚ) :
    ((recs f n lab w).map g).sum = ∑ j ∈ range (f.len n), g (f.c n + j, lab, w j) := by
  rw [recs, List.map_map, lsum_range]; rfl

/-! ### Residues -/

theorem num_eq (n : ℕ) (x : ℚ) : ((Zd n).map (fun z => x - z)).prod = FNum n x := by
  rw [Zd, List.map_append, List.prod_append, famMem, famMem, List.map_map, List.map_map,
    lprod_range, lprod_range, FNum, rf, rf, dz0, dz1]
  simp only [Fam.len, Fam.c, Function.comp]
  congr 1
  · rw [← prod_range_reflect]
    apply prod_congr rfl; intro i hi; rw [mem_range] at hi
    rw [show 10 * n + 1 - 1 - i = 10 * n - i by omega, Nat.cast_sub (by omega)]
    push_cast; ring
  · rw [← prod_range_reflect]
    apply prod_congr rfl; intro i hi; rw [mem_range] at hi
    rw [show 9 * n + 1 - 1 - i = 9 * n - i by omega, Nat.cast_sub (by omega)]
    push_cast; ring

theorem den_ne (f : Fam) (n lab : ℕ) (w : ℕ → ℚ) (x : ℚ) (hne : ∀ i : ℕ, f.c n + i ≠ x) :
    (((recs f n lab w).filter (fun q => q.1 ≠ x)).map (fun q => q.1 - x)).prod =
      ∏ i ∈ range (f.len n), (f.c n + i - x) := by
  rw [List.filter_eq_self.mpr, recs, List.map_map, lprod_range]
  · rfl
  · intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    simpa using hne i

theorem den_eq (f : Fam) (n lab : ℕ) (w : ℕ → ℚ) (j : ℕ) :
    (((recs f n lab w).filter (fun q => q.1 ≠ f.c n + j)).map (fun q => q.1 - (f.c n + j))).prod =
      ∏ i ∈ (range (f.len n)).erase j, (f.c n + i - (f.c n + j)) := by
  rw [prod_map_filter, recs, List.map_map, lprod_range, ← filter_ne', prod_filter]
  apply prod_congr rfl; intro i _
  simp [Function.comp]

/-- `6 x` for the three pole families has residues `0, 2, 3` mod 6 -/
theorem ne_of_six {x y : ℚ} {a b : ℤ} (hx : 6 * x = a) (hy : 6 * y = b) (hab : a % 6 ≠ b % 6) :
    x ≠ y := by
  rintro rfl
  have : (a : ℚ) = b := by rw [← hx, ← hy]
  exact hab (by rw [show a = b by exact_mod_cast this])

theorem six_I (n i : ℕ) : 6 * ((dualP[0]!).c n + i) = ((12 * n + 6 * i : ℕ) : ℤ) := by
  rw [dp0]; simp only [Fam.c]; push_cast; ring
theorem six_T (n i : ℕ) : 6 * ((dualP[1]!).c n + i) = ((2 + 6 * i : ℕ) : ℤ) := by
  rw [dp1]; simp only [Fam.c]; push_cast; ring
theorem six_H (n i : ℕ) : 6 * ((dualP[2]!).c n + i) = ((12 * n + 3 + 6 * i : ℕ) : ℤ) := by
  rw [dp2]; simp only [Fam.c]; push_cast; ring

theorem cI (n j : ℕ) : (dualP[0]!).c n + j = (iP n j : ℚ) := by
  rw [dp0]; simp [Fam.c, iP]
theorem cT' (n j : ℕ) : (dualP[1]!).c n + j = (tP j : ℚ) := by
  rw [dp1]; simp [Fam.c, tP]
theorem cH' (n j : ℕ) : (dualP[2]!).c n + j = (hP n j : ℚ) := by
  rw [dp2]; simp [Fam.c, hP]; try ring

theorem lenI (n : ℕ) : (dualP[0]!).len n = 10 * n + 2 := by rw [dp0]; rfl
theorem lenT (n : ℕ) : (dualP[1]!).len n = 6 * n + 2 := by rw [dp1]; rfl
theorem lenH (n : ℕ) : (dualP[2]!).len n = 3 * n + 2 := by rw [dp2]; rfl

theorem vres_eq (n p : ℕ) (x : ℚ) : vres (Zd n) (Pd n p) x = FNum n x /
    ((((recs (dualP[0]!) n 0 (fun j => hwI n j)).filter (fun q => q.1 ≠ x)).map (fun q => q.1 - x)).prod *
     (((recs (dualP[1]!) n 1 (fun j => hwT j + cT p)).filter (fun q => q.1 ≠ x)).map
        (fun q => q.1 - x)).prod *
     (((recs (dualP[2]!) n 2 (fun j => hwH n j + cH p)).filter (fun q => q.1 ≠ x)).map
        (fun q => q.1 - x)).prod) := by
  rw [vres, num_eq, Pd, List.filter_append, List.filter_append, List.map_append, List.map_append,
    List.prod_append, List.prod_append]

theorem vres_T (n p j : ℕ) : vres (Zd n) (Pd n p) (tP j) = -resT n j := by
  rw [vres_eq, den_ne _ _ _ _ _ (fun i h => ne_of_six (six_I n i) (by rw [← cT' n j]; exact six_T n j)
      (by omega) h),
    den_ne _ _ _ _ _ (fun i h => ne_of_six (six_H n i) (by rw [← cT' n j]; exact six_T n j)
      (by omega) h)]
  rw [← cT' n j, den_eq, resT, ← cT' n j, lenI, lenT, lenH]
  rw [neg_div, neg_neg]
  congr 1
  rw [rf, rf]
  congr 1
  congr 1
  all_goals (apply prod_congr rfl; intro i _; simp only [cI, cT', cH', iP, tP, hP]; try ring)

theorem vres_H (n p j : ℕ) : vres (Zd n) (Pd n p) (hP n j) = -resH n j := by
  rw [vres_eq, den_ne _ _ _ _ _ (fun i h => ne_of_six (six_I n i) (by rw [← cH' n j]; exact six_H n j)
      (by omega) h),
    den_ne _ _ _ _ _ (fun i h => ne_of_six (six_T n i) (by rw [← cH' n j]; exact six_H n j)
      (by omega) h)]
  rw [← cH' n j, den_eq, resH, ← cH' n j, lenI, lenT, lenH]
  rw [neg_div, neg_neg]
  congr 1
  rw [rf, rf]
  congr 1
  congr 1
  all_goals (apply prod_congr rfl; intro i _; simp only [cI, cT', cH', iP, tP, hP]; try ring)

theorem vres_I (n p j : ℕ) : vres (Zd n) (Pd n p) (iP n j) = -resI n j := by
  rw [vres_eq, den_ne _ _ _ _ _ (fun i h => ne_of_six (six_T n i) (by rw [← cI n j]; exact six_I n j)
      (by omega) h),
    den_ne _ _ _ _ _ (fun i h => ne_of_six (six_H n i) (by rw [← cI n j]; exact six_I n j)
      (by omega) h)]
  rw [← cI n j, den_eq, resI, ← cI n j, lenI, lenT, lenH]
  rw [neg_div, neg_neg]
  congr 1
  rw [rf, rf]
  congr 1
  congr 1
  all_goals (apply prod_congr rfl; intro i _; simp only [cI, cT', cH', iP, tP, hP]; try ring)

/-! ### Packet types, hypotheses, span membership -/

theorem disj_IT (n : ℕ) : List.Disjoint (famMem (dualP[0]!) n) (famMem (dualP[1]!) n) := by
  intro x h1 h2
  simp only [famMem, List.mem_map] at h1 h2
  obtain ⟨i, _, rfl⟩ := h1; obtain ⟨j, _, hj⟩ := h2
  exact ne_of_six (six_I n i) (six_T n j) (by omega) hj.symm

theorem disj_IH (n : ℕ) : List.Disjoint (famMem (dualP[0]!) n) (famMem (dualP[2]!) n) := by
  intro x h1 h2
  simp only [famMem, List.mem_map] at h1 h2
  obtain ⟨i, _, rfl⟩ := h1; obtain ⟨j, _, hj⟩ := h2
  exact ne_of_six (six_I n i) (six_H n j) (by omega) hj.symm

theorem disj_TH (n : ℕ) : List.Disjoint (famMem (dualP[1]!) n) (famMem (dualP[2]!) n) := by
  intro x h1 h2
  simp only [famMem, List.mem_map] at h1 h2
  obtain ⟨i, _, rfl⟩ := h1; obtain ⟨j, _, hj⟩ := h2
  exact ne_of_six (six_T n i) (six_H n j) (by omega) hj.symm

theorem famMem_nodup (f : Fam) (n : ℕ) : (famMem f n).Nodup :=
  List.nodup_range.map (fun a b h => by exact_mod_cast (add_left_cancel h))

theorem recs_fst (f : Fam) (n lab : ℕ) (w : ℕ → ℚ) : (recs f n lab w).map Prod.fst = famMem f n := by
  simp [recs, famMem, List.map_map, Function.comp_def]

theorem Pd_nodup (n p : ℕ) : ((Pd n p).map Prod.fst).Nodup := by
  rw [Pd, List.map_append, List.map_append, recs_fst, recs_fst, recs_fst, List.nodup_append',
    List.nodup_append', List.disjoint_append_left]
  exact ⟨⟨famMem_nodup _ n, famMem_nodup _ n, disj_IT n⟩, famMem_nodup _ n, disj_IH n, disj_TH n⟩

theorem Pd_six (n p : ℕ) : ∀ q ∈ Pd n p, ∃ a : ℤ, 6 * q.1 = a ∧ 0 ≤ a ∧ a ≤ 72 * n + 9 := by
  intro q hq
  simp only [Pd, List.mem_append, recs, List.mem_map, List.mem_range] at hq
  rcases hq with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
  · rw [lenI] at hj; exact ⟨_, six_I n j, by omega, by omega⟩
  · rw [lenT] at hj; exact ⟨_, six_T n j, by omega, by omega⟩
  · rw [lenH] at hj; exact ⟨_, six_H n j, by omega, by omega⟩

theorem den_dvd_six {x : ℚ} {a : ℤ} (hx : 6 * x = a) : x.den ∣ 6 := by
  have hx' : x = Rat.divInt a 6 := by rw [Rat.divInt_eq_div]; push_cast; linarith
  have h1 : ((x.den : ℤ)) ∣ 6 := by rw [hx']; exact Rat.den_dvd a 6
  exact_mod_cast h1

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem p_mod6 (hp5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h; omega
  omega

theorem not_dvd_six (hp5 : 5 ≤ p) : ¬ p ∣ 6 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 5 ∨ p = 6 by omega) with rfl | rfl
  · omega
  · exact absurd hp.out (by decide)

theorem famMem_class (f : Fam) (hf : f.be.den ∣ 6) (hp5 : 5 ≤ p) (n r : ℕ) (hr : r < p) :
    ((famMem f n).filter (cls p r)).map (Tv p r) =
      run ((f.lo (p % 6)).floorAt n p r) ((f.hi (p % 6)).floorAt n p r) (-(f.shift (p % 6))) := by
  rw [← family_class f hf (p % 6) (p_mod6 hp5) p hp5 rfl n r hr]
  simp only [famMem, List.filter_map, List.map_map, bind_pure_comp, List.map_eq_map]
  rfl

theorem recs_class (f : Fam) (hf : f.be.den ∣ 6) (hp5 : 5 ≤ p) (n r lab : ℕ) (w : ℕ → ℚ)
    (hr : r < p) :
    ((recs f n lab w).filter (fun q => cls p r q.1)).map (fun q => (Tv p r q.1, q.2.1)) =
      (run ((f.lo (p % 6)).floorAt n p r) ((f.hi (p % 6)).floorAt n p r)
        (-(f.shift (p % 6)))).map (·, lab) := by
  rw [← family_class f hf (p % 6) (p_mod6 hp5) p hp5 rfl n r hr]
  simp only [recs, List.filter_map, List.map_map, bind_pure_comp, List.map_eq_map]
  rfl

theorem typ_eq (n r : ℕ) (hp5 : 5 ≤ p) (hr : r < p) :
    typ p (Zd n) (Pd n p) r (if r = 0 then 1 else 0) = dualTypeAt n p r := by
  simp only [typ, Zd, Pd, List.filter_append, List.map_append]
  rw [famMem_class _ (den_dvd_six (a := -6) (by rw [dz0]; norm_num)) hp5 n r hr,
    famMem_class _ (den_dvd_six (a := -6) (by rw [dz1]; norm_num)) hp5 n r hr,
    recs_class _ (den_dvd_six (a := 0) (by rw [dp0]; norm_num)) hp5 n r 0 _ hr,
    recs_class _ (den_dvd_six (a := 2) (by rw [dp1]; norm_num)) hp5 n r 1 _ hr,
    recs_class _ (den_dvd_six (a := 3) (by rw [dp2]; norm_num)) hp5 n r 2 _ hr]
  rfl

theorem den_ndvd {x : ℚ} {a : ℤ} (hx : 6 * x = a) (hp5 : 5 ≤ p) : ¬ p ∣ x.den := by
  intro h
  exact not_dvd_six hp5 (h.trans (den_dvd_six hx))

theorem small_val {y : ℚ} {m : ℤ} (hy : 6 * y = m) (hm0 : m ≠ 0) (hm : m.natAbs < p ^ 2)
    (hp5 : 5 ≤ p) : padicValRat p y ≤ 1 := by
  have hy' : y = (m : ℚ) / 6 := by linarith
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  rw [hy', padicValRat.div hm0' (by norm_num), padicValRat.of_int]
  have h6 : padicValRat p 6 = 0 := by
    rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (not_dvd_six hp5)]
    simp
  rw [h6, sub_zero]
  by_contra hcon
  push Not at hcon
  have h2 : 2 ≤ padicValInt p m := by omega
  have h3 := (padicValInt_dvd_iff 2 m).mpr (Or.inr h2)
  have h4 : p ^ 2 ∣ m.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h3; simpa [Int.natAbs_pow] using this
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) h4
  omega

theorem hyp_dual (n : ℕ) (hp5 : 5 ≤ p) (hbig : 144 * n + 24 < p ^ 2) : Hyp p (Zd n) (Pd n p) where
  hZd := by
    intro z hz
    simp only [Zd, famMem, List.mem_append, List.mem_map, List.mem_range, dz0, dz1,
      Fam.c] at hz
    rcases hz with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
    · exact den_ndvd (a := 6 * (-10 * n - 1 + i)) (by push_cast; ring) hp5
    · exact den_ndvd (a := 6 * (-8 * n - 1 + i)) (by push_cast; ring) hp5
  hPd := fun q hq => by obtain ⟨a, ha, _⟩ := Pd_six n p q hq; exact den_ndvd ha hp5
  hnd := Pd_nodup n p
  hdiff := by
    intro q hq q' hq' hne
    obtain ⟨a, ha, ha1, ha2⟩ := Pd_six n p q hq
    obtain ⟨b, hb, hb1, hb2⟩ := Pd_six n p q' hq'
    refine small_val (m := a - b) (by push_cast; linarith) ?_ ?_ hp5
    · intro h; apply hne
      have : (a : ℚ) = b := by exact_mod_cast (sub_eq_zero.mp h)
      linarith
    · have h1 : (a - b).natAbs ≤ 72 * n + 9 := by omega
      omega
  hH := by
    intro q hq m hm
    obtain ⟨a, ha, ha1, ha2⟩ := Pd_six n p q hq
    have h6 : ((6 * (m : ℤ) : ℤ) : ℚ) < a := by push_cast; linarith
    have h6' : 6 * (m : ℤ) < a := by exact_mod_cast h6
    refine small_val (m := a - 6 * m) (by push_cast; linarith) (by omega) ?_ hp5
    have h1 : (a - 6 * m).natAbs ≤ 72 * n + 9 := by omega
    omega
  hw := by
    intro q hq r hr hc
    have hc' : (p : ℤ) ∣ (q.1 - r).num := by simpa [cls] using hc
    simp only [Pd, List.mem_append, recs, List.mem_map, List.mem_range] at hq
    rcases hq with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [lenI] at hj
      simp only [cI] at hc' ⊢
      exact harm_split_I hp5 n j r hbig hj hr hc'
    · rw [lenT] at hj
      simp only [cT'] at hc' ⊢
      exact harm_split_T hp5 n j r hbig hj hr hc'
    · rw [lenH] at hj
      simp only [cH'] at hc' ⊢
      exact harm_split_H_plus hp5 n j r hbig hj hr hc'

theorem huniq_dual (n : ℕ) (hp5 : 5 ≤ p) :
    ∀ q ∈ Pd n p, ∃! r, r < p ∧ cls p r q.1 = true := by
  intro q hq
  obtain ⟨a, ha, _⟩ := Pd_six n p q hq
  simpa [cls] using exists_unique_class p q.1 (den_ndvd ha hp5)

theorem class_inSpan (Z : List ℚ) (P : List Rec) (H : Hyp p Z P) (r k : ℕ) (hr : r < p)
    (hk : 1 ≤ k) :
    InSpan p (typ p Z P r (if r = 0 then 1 else 0)).gens
      (rowVec p Z P k (P.filter (fun q => cls p r q.1))) := by
  set jmin := if r = 0 then 1 else 0 with hjdef
  set t := typ p Z P r jmin with ht
  by_cases hps : t.ps = []
  · have hnil : P.filter (fun q => cls p r q.1) = [] := by
      have e : t.ps = (P.filter (fun q => cls p r q.1)).map (fun q => (Tv p r q.1, q.2.1)) := rfl
      rw [e] at hps; exact List.map_eq_nil_iff.mp hps
    rw [hnil]
    have h0 : rowVec p Z P k [] = 0 := by funext i; fin_cases i <;> simp [rowVec]
    rw [h0]; exact InSpan.zero _
  obtain ⟨φ, br, rem, hφ, hφ0, hbr, hrem, heq⟩ := class_decomp Z P H r k jmin hr hk hjdef
  rw [heq]
  have hp0 := p_ne_zero' (p := p)
  have hgens : t.gens = ((List.range (Jt + 1 - t.jmin)).map
      (fun i => (t.h + 1 + ((t.jmin + i : ℕ) : ℤ), t.V (t.jmin + i)))) ++ [(t.regW, unitVec 0)] ++
      (List.finRange 4).map (fun k => (t.h + Jt + 2, unitVec k)) := by
    rw [PType.gens, if_neg hps]
  have hjm : jmin ≤ 1 := by rw [hjdef]; split_ifs <;> simp
  refine InSpan.add (InSpan.add ?_ ?_) ?_
  · apply Finset.sum_induction _ (InSpan p t.gens) (fun a b ha hb => InSpan.add ha hb)
      (InSpan.zero _)
    intro j _
    by_cases hj : jmin ≤ (j : ℕ)
    · have hg : (t.h + 1 + ((j : ℕ) : ℤ), t.V j) ∈ t.gens := by
        rw [hgens]
        apply List.mem_append_left; apply List.mem_append_left
        refine List.mem_map.mpr ⟨(j : ℕ) - jmin, List.mem_range.mpr ?_, ?_⟩
        · have := j.isLt; show (j : ℕ) - jmin < Jt + 1 - jmin; simp only [Jt]; omega
        · show (t.h + 1 + ((jmin + ((j : ℕ) - jmin) : ℕ) : ℤ), t.V (jmin + ((j : ℕ) - jmin))) = _
          rw [Nat.add_sub_cancel' hj]
      have := InSpan.gen hg (φ j) (hφ j) 0 le_rfl
      simpa using this
    · have hj1 : jmin = 1 := by omega
      have : j = 0 := Fin.ext (by omega)
      subst this
      rw [hφ0 hj1, zero_mul, zero_smul]; exact InSpan.zero _
  · have hg : (t.regW, unitVec 0) ∈ t.gens := by rw [hgens]; simp
    have ha : VGe p 0 (br / (p : ℚ) ^ t.regW) := by
      have := hbr.mul (VGe.zpow (p := p) (-t.regW)); rw [add_neg_cancel] at this
      rwa [div_eq_mul_inv, ← zpow_neg]
    have := InSpan.gen hg _ ha 0 le_rfl
    simp only [add_zero] at this
    rwa [div_mul_cancel₀ _ (zpow_ne_zero _ hp0)] at this
  · apply Finset.sum_induction _ (InSpan p t.gens) (fun a b ha hb => InSpan.add ha hb)
      (InSpan.zero _)
    intro c _
    have hg : (t.h + Jt + 2, unitVec c) ∈ t.gens := by rw [hgens]; simp
    have ha : VGe p 0 (rem c / (p : ℚ) ^ (t.h + Jt + 2)) := by
      have := (hrem c).mul (VGe.zpow (p := p) (-(t.h + Jt + 2))); rw [add_neg_cancel] at this
      rwa [div_eq_mul_inv, ← zpow_neg]
    have := InSpan.gen hg _ ha 0 le_rfl
    simp only [add_zero] at this
    rwa [div_mul_cancel₀ _ (zpow_ne_zero _ hp0)] at this

theorem total_inSpan (Z : List ℚ) (P : List Rec) (H : Hyp p Z P)
    (huniq : ∀ q ∈ P, ∃! r, r < p ∧ cls p r q.1 = true) (k : ℕ) (hk : 1 ≤ k) (G : ℕ → PType)
    (hG : ∀ r < p, G r = typ p Z P r (if r = 0 then 1 else 0)) :
    InSpan p ((List.range p).flatMap (fun r => (G r).gens)) (rowVec p Z P k P) := by
  rw [← rowVec_sum Z P k huniq]
  apply Finset.sum_induction _ (InSpan p _) (fun a b ha hb => InSpan.add ha hb) (InSpan.zero _)
  intro r hr
  rw [Finset.mem_range] at hr
  refine InSpan.mono (fun g hg => List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, hg⟩) ?_
  rw [hG r hr]
  exact class_inSpan Z P H r k hr hk

end

end LA
end Zeta2L2Chi3.Arith
