/-
# Per-chamber valuation bounds for `w_n`

* dual: Lemma A + candidate types + lattice soundness give `v_p(w_n) ≥ dualCellBound`;
* forward: (3.1), the forward packet bound, the `Δ_n` valuation and the candidate minimum give
  `v_p(w_n) ≥ fwdCellBound - |v_p(g(n)/g(0))|`, and `fwdCellBound` is periodic in the lift.
-/
import Zeta2L2Chi3.Arith.LemmaA
import Zeta2L2Chi3.Arith.Cell
import Zeta2L2Chi3.Arith.FwdVal
import Zeta2L2Chi3.Arith.DeltaVal
import Zeta2L2Chi3.DualTransport
import Zeta2L2Chi3.CastRows

namespace Zeta2L2Chi3.Arith

namespace CB

theorem fracQ_add_int (y : ℚ) (z : ℤ) : fracQ (y + z) = fracQ y := by
  unfold fracQ; rw [Int.floor_add_intCast]; push_cast; ring

theorem lin_shift (E : Endpt) (x : ℚ) (L : ℕ) :
    E.a * ((L : ℚ) + x) + E.b = (E.a * x + E.b) + ((E.a * L : ℤ) : ℚ) := by push_cast; ring

theorem qstar_shift (E : Endpt) (x : ℚ) (L : ℕ) : qstar E (L + x) = qstar E x + E.a * L := by
  unfold qstar; rw [lin_shift, fracQ_add_int, Int.floor_add_intCast]; split_ifs <;> ring

theorem keyOf_shift (E : Endpt) (x : ℚ) (L : ℕ) : keyOf E (L + x) = keyOf E x := by
  unfold keyOf; rw [lin_shift, fracQ_add_int]

theorem isTop1_shift (E : Endpt) (x : ℚ) (L : ℕ) : isTop1 E (L + x) = isTop1 E x := by
  unfold isTop1; rw [lin_shift, fracQ_add_int]

theorem candSets_shift (Es : List Endpt) (x : ℚ) (L : ℕ) : candSets Es (L + x) = candSets Es x := by
  unfold candSets; simp only [keyOf_shift, isTop1_shift]

theorem floorsOf_shift (Es : List Endpt) (x : ℚ) (L : ℕ) (S : List Bool) (i : ℕ) :
    floorsOf Es (L + x) S i = floorsOf Es x S i + (Es[i]!).a * L := by
  unfold floorsOf; rw [qstar_shift]; ring

theorem detProfile_shift (e : ℕ) (x : ℚ) (L : ℕ) : detProfile e (L + x) = detProfile e x := by
  simp only [detProfile, gammaF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qstar_shift,
    Fam.hi, Fam.lo]
  push_cast; ring

end CB

namespace CB

theorem mem_run {Flo Fhi : ℤ} {sh x : ℚ} (h : x ∈ run Flo Fhi sh) : ∃ m : ℤ, x = m + sh := by
  unfold run at h
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
  exact ⟨_, rfl⟩

theorem run_nodup (Flo Fhi : ℤ) (sh : ℚ) : (run Flo Fhi sh).Nodup := by
  unfold run
  refine List.Nodup.map (fun a b hab => ?_) ?_
  · simp only [add_left_inj, Int.cast_inj] at hab
    omega
  · simp; rw [← List.map_eq_flatMap]; exact List.nodup_range.map (Nat.cast_injective (R := ℤ))

theorem mem_dualCandTypes {e : ℕ} {x : ℚ} {t : PType} (ht : t ∈ dualCandTypes e x) :
    ∃ F j, t = mkDualType e F j := by
  unfold dualCandTypes at ht
  obtain ⟨S, -, hS⟩ := List.mem_flatMap.1 ht
  split_ifs at hS
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl <;> exact ⟨_, _, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    exact ⟨_, _, hS⟩

/-- the shifts of the dual families -/
theorem dual_shifts (e : ℕ) (he : e = 1 ∨ e = 5) :
    (dualZ[0]!).shift e = 0 ∧ (dualZ[1]!).shift e = 0 ∧ (dualP[0]!).shift e = 0 ∧
    ((dualP[1]!).shift e = 2 / 3 ∨ (dualP[1]!).shift e = 1 / 3) ∧ (dualP[2]!).shift e = 1 / 2 := by
  rcases he with rfl | rfl
  · refine ⟨?_, ?_, ?_, Or.inl ?_, ?_⟩ <;> decide +kernel
  · refine ⟨?_, ?_, ?_, Or.inr ?_, ?_⟩ <;> decide +kernel

theorem den_of_int_add {x : ℚ} (m : ℤ) (c : ℤ) (sh : ℚ) (hsh : 6 * sh = c) (hx : x = m + sh) :
    x.den ∣ 6 :=
  LA.den_dvd_six (a := 6 * m + c) (by rw [hx]; push_cast; rw [← hsh]; ring)

theorem mkDualType_den (e : ℕ) (he : e = 1 ∨ e = 5) (F : ℕ → ℤ) (j : ℕ) :
    ∀ x ∈ (mkDualType e F j).zs ++ (mkDualType e F j).ps.map Prod.fst, x.den ∣ 6 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dual_shifts e he
  have hint : ∀ (Flo Fhi : ℤ) (s : ℚ) (c : ℤ), 6 * s = c → ∀ x ∈ run Flo Fhi (-s), x.den ∣ 6 := by
    intro Flo Fhi s c hs x hx
    obtain ⟨m, hm⟩ := mem_run hx
    exact den_of_int_add m (-c) (-s) (by push_cast; linarith) hm
  intro x hx
  simp only [mkDualType, List.mem_append, List.map_append, List.map_map, List.mem_map,
    Function.comp_def] at hx
  rcases hx with (hx | hx) | ((⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
  · exact hint _ _ _ 0 (by rw [h0]; norm_num) x hx
  · exact hint _ _ _ 0 (by rw [h1]; norm_num) x hx
  · exact hint _ _ _ 0 (by rw [h2]; norm_num) y hy
  · rcases h3 with h3 | h3
    · exact hint _ _ _ 4 (by rw [h3]; norm_num) y hy
    · exact hint _ _ _ 2 (by rw [h3]; norm_num) y hy
  · exact hint _ _ _ 3 (by rw [h4]; norm_num) y hy

theorem run_six {a b c : ℤ} {s x : ℚ} (hs : 6 * s = c) (hx : x ∈ run a b (-s)) :
    ∃ m : ℤ, 6 * x = ((6 * m - c : ℤ) : ℚ) := by
  obtain ⟨m, rfl⟩ := mem_run hx
  exact ⟨m, by push_cast; linarith⟩

theorem run_disj {a b c d c1 c2 : ℤ} {s t : ℚ} (hs : 6 * s = c1) (ht : 6 * t = c2)
    (hc : (c1 - c2) % 6 ≠ 0) : ∀ x ∈ run a b (-s), ∀ y ∈ run c d (-t), x ≠ y := by
  intro x hx y hy hxy
  subst hxy
  obtain ⟨m, hm⟩ := run_six hs hx
  obtain ⟨m', hm'⟩ := run_six ht hy
  have : (6 * m - c1 : ℤ) = 6 * m' - c2 := by exact_mod_cast hm.symm.trans hm'
  omega

theorem mkDualType_nodup (e : ℕ) (he : e = 1 ∨ e = 5) (F : ℕ → ℤ) (j : ℕ) :
    ((mkDualType e F j).ps.map Prod.fst).Nodup := by
  obtain ⟨-, -, h2, h3, h4⟩ := dual_shifts e he
  simp only [mkDualType, List.map_append, List.map_map, Function.comp_def, List.map_id']
  rw [h2, h4]
  rcases h3 with h3 | h3 <;> rw [h3]
  · refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨run_nodup _ _ _, run_nodup _ _ _,
      run_disj (c1 := 0) (c2 := 4) (by norm_num) (by norm_num) (by decide)⟩, run_nodup _ _ _, ?_⟩
    intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact run_disj (c1 := 0) (c2 := 3) (by norm_num) (by norm_num) (by decide) x hx y hy
    · exact run_disj (c1 := 4) (c2 := 3) (by norm_num) (by norm_num) (by decide) x hx y hy
  · refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨run_nodup _ _ _, run_nodup _ _ _,
      run_disj (c1 := 0) (c2 := 2) (by norm_num) (by norm_num) (by decide)⟩, run_nodup _ _ _, ?_⟩
    intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact run_disj (c1 := 0) (c2 := 3) (by norm_num) (by norm_num) (by decide) x hx y hy
    · exact run_disj (c1 := 2) (c2 := 3) (by norm_num) (by norm_num) (by decide) x hx y hy

theorem mkDualType_lab (e : ℕ) (F : ℕ → ℤ) (j : ℕ) : ∀ q ∈ (mkDualType e F j).ps, q.2 ≤ 2 := by
  intro q hq
  simp only [mkDualType, List.mem_append, List.mem_map] at hq
  rcases hq with (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩) | ⟨y, -, rfl⟩ <;> norm_num

theorem Gsq_pint {p : ℕ} [Fact p.Prime] (m : ℕ) (hm : m < p) : VGe p 0 (Gsq m) := by
  unfold Gsq
  refine VGe.finset_sum (fun a ha => ?_)
  have ha : a + 1 < p := by rw [Finset.mem_range] at ha; omega
  have h0 : ((a + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hv : padicValRat p ((a + 1 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd
      (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have := (VGe.inv (p := p) h0).pow 2
  rw [hv] at this
  have e : (1 : ℚ) / ((a : ℚ) + 1) ^ 2 = (((a + 1 : ℕ) : ℚ))⁻¹ ^ 2 := by
    rw [inv_pow, one_div]; push_cast; ring
  rw [e]; simpa using this

theorem cT_pint {p : ℕ} [Fact p.Prime] : VGe p 0 (cT p) := by
  have hp := (Fact.out : p.Prime).two_le
  unfold cT inv3; apply Gsq_pint; split_ifs <;> omega

theorem cH_pint {p : ℕ} [Fact p.Prime] : VGe p 0 (cH p) := by
  have hp := (Fact.out : p.Prime).two_le
  unfold cH inv2; apply Gsq_pint; omega

theorem colVec_three (n p k : ℕ) (hk : k ≤ 2) : colVec n p k 3 = 0 := by
  have h : (((BI n k + BT n k + BH n k : ℚ)) : ℝ) = 0 := by
    push_cast [cast_BI, cast_BT, cast_BH]; rw [BI_eq n k hk]; ring
  have h' : (BI n k + BT n k + BH n k : ℚ) = 0 := by exact_mod_cast h
  simpa [colVec] using h'

theorem w_B (n : ℕ) : w n 0 = BT n 1 * BH n 2 - BH n 1 * BT n 2 ∧
    w n 1 = BH n 1 * B0 n 2 - B0 n 1 * BH n 2 ∧ w n 2 = B0 n 1 * BT n 2 - BT n 1 * B0 n 2 := by
  have hB : ∀ i j, Bhat n i j = (Bres n : Matrix (Fin 3) (Fin 3) ℚ) i j := fun i j => by
    rw [Bres_eq_Bhat]
  simp only [w, hB]
  simp [Bres]

end CB


namespace CB

theorem le_foldr_min {l : List ℤ} {c : ℤ} (hc : c ≤ 0) (h : ∀ x ∈ l, c ≤ x) : c ≤ l.foldr min 0 := by
  induction l with
  | nil => simpa using hc
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact le_min (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem foldr_min_nonpos (l : List ℤ) : l.foldr min 0 ≤ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons]; exact (min_le_right _ _).trans ih

/-- `w = (1944/35) Δ f` transfers valuations -/
theorem w_val {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (wv dv fv : ℚ) (hd : dv ≠ 0)
    (hf : fv = 35 / 1944 * dv⁻¹ * wv) (a : ℤ) (hfv : VGe p a fv) : VGe p (padicValRat p dv + a) wv := by
  have hw : wv = 1944 / 35 * dv * fv := by rw [hf]; field_simp
  have hu : VGe p 0 (1944 / 35 : ℚ) := by
    apply VGe.of_den
    have : (1944 / 35 : ℚ).den = 35 := by decide +kernel
    rw [this]
    intro h
    have hpp := (Fact.out : p.Prime)
    have h57 : p ∣ 5 * 7 := h
    rcases (Nat.Prime.dvd_mul hpp).1 h57 with h5 | h7
    · have := Nat.le_of_dvd (by norm_num) h5; omega
    · have := Nat.le_of_dvd (by norm_num) h7; omega
  have hdv : VGe p (padicValRat p dv) dv := Or.inr le_rfl
  rw [hw]
  simpa using (hu.mul hdv).mul hfv

/-- floor differences of a family are within one of `len / p` -/
theorem floor_diff_bounds (f : Fam) (e n p r : ℕ) (hp : 0 < p) (t s A B : ℚ)
    (ht : t = n / p) (hs : s = 1 / p) (hA : (f.la : ℚ) = A) (hB : (f.mu : ℚ) = B) :
    A * t + B * s - 1 < (((f.hi e).floorAt n p r - (f.lo e).floorAt n p r : ℤ) : ℚ) ∧
    (((f.hi e).floorAt n p r - (f.lo e).floorAt n p r : ℤ) : ℚ) < A * t + B * s + 1 := by
  unfold Endpt.floorAt
  set u := ((f.hi e).val n p - r) / p
  set v := ((f.lo e).val n p - r) / p
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have huv : u - v = A * t + B * s := by
    simp only [u, v, Endpt.val, Fam.hi, Fam.lo, ht, hs, ← hA, ← hB]
    field_simp
    push_cast
    ring
  have h1 := Int.floor_le u
  have h2 := Int.lt_floor_add_one u
  have h3 := Int.floor_le v
  have h4 := Int.lt_floor_add_one v
  push_cast
  constructor <;> linarith

theorem hminF_crude (n p : ℕ) (hp : 2 ≤ p) : -5 ≤ hminF n p := by
  unfold hminF
  refine le_foldr_min (by norm_num) (fun x hx => ?_)
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  set e := p % 6
  have hp0 : 0 < p := by omega
  set t : ℚ := n / p
  set s : ℚ := 1 / p
  have hs : s < 1 := by
    simp only [s]; rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : 1 < p)
  have b0 := floor_diff_bounds ⟨-12, -1, 10, 1⟩ e n p r hp0 t s 10 1 rfl rfl (by norm_num) (by norm_num)
  have b1 := floor_diff_bounds ⟨-6, -4 / 3, 6, 1⟩ e n p r hp0 t s 6 1 rfl rfl (by norm_num) (by norm_num)
  have b2 := floor_diff_bounds ⟨-5, -3 / 2, 3, 1⟩ e n p r hp0 t s 3 1 rfl rfl (by norm_num) (by norm_num)
  have b3 := floor_diff_bounds ⟨0, 0, 10, 2⟩ e n p r hp0 t s 10 2 rfl rfl (by norm_num) (by norm_num)
  have b4 := floor_diff_bounds ⟨-1, 0, 9, 2⟩ e n p r hp0 t s 9 2 rfl rfl (by norm_num) (by norm_num)
  have hF : fwdH (fun E => ((endpts (fwdZ ++ fwdP) e)[E]!).floorAt n p r) =
      ((Fam.hi ⟨-12, -1, 10, 1⟩ e).floorAt n p r - (Fam.lo ⟨-12, -1, 10, 1⟩ e).floorAt n p r) +
      ((Fam.hi ⟨-6, -4 / 3, 6, 1⟩ e).floorAt n p r - (Fam.lo ⟨-6, -4 / 3, 6, 1⟩ e).floorAt n p r) +
      ((Fam.hi ⟨-5, -3 / 2, 3, 1⟩ e).floorAt n p r - (Fam.lo ⟨-5, -3 / 2, 3, 1⟩ e).floorAt n p r) -
      ((Fam.hi ⟨0, 0, 10, 2⟩ e).floorAt n p r - (Fam.lo ⟨0, 0, 10, 2⟩ e).floorAt n p r) -
      ((Fam.hi ⟨-1, 0, 9, 2⟩ e).floorAt n p r - (Fam.lo ⟨-1, 0, 9, 2⟩ e).floorAt n p r) := rfl
  have key : (-6 : ℚ) < ((fwdH (fun E => ((endpts (fwdZ ++ fwdP) e)[E]!).floorAt n p r) : ℤ) : ℚ) := by
    rw [hF]
    push_cast at b0 b1 b2 b3 b4 ⊢
    linarith [b0.1, b1.1, b2.1, b3.2, b4.2]
  have : (-6 : ℤ) < fwdH (fun E => ((endpts (fwdZ ++ fwdP) e)[E]!).floorAt n p r) := by
    exact_mod_cast key
  omega

theorem gamma_crude (n p : ℕ) (hp : 0 < p) (e : ℕ) :
    -10 ≤ (gammaF.map (fun fm => fm.2 * ((fm.1.hi e).floorAt n p 0 - (fm.1.lo e).floorAt n p 0))).sum := by
  set t : ℚ := n / p
  set s : ℚ := 1 / p
  have b0 := floor_diff_bounds ⟨0, 2 / 3, 12, 0⟩ e n p 0 hp t s 12 0 rfl rfl (by norm_num) (by norm_num)
  have b1 := floor_diff_bounds ⟨0, 1, 8, 0⟩ e n p 0 hp t s 8 0 rfl rfl (by norm_num) (by norm_num)
  have b2 := floor_diff_bounds ⟨0, 1 / 3, 5, 0⟩ e n p 0 hp t s 5 0 rfl rfl (by norm_num) (by norm_num)
  have b3 := floor_diff_bounds ⟨0, 1 / 3, 8, 0⟩ e n p 0 hp t s 8 0 rfl rfl (by norm_num) (by norm_num)
  have b4 := floor_diff_bounds ⟨0, 1, 6, 0⟩ e n p 0 hp t s 6 0 rfl rfl (by norm_num) (by norm_num)
  have b5 := floor_diff_bounds ⟨0, 1, 5, 0⟩ e n p 0 hp t s 5 0 rfl rfl (by norm_num) (by norm_num)
  have b6 := floor_diff_bounds ⟨0, 1 / 6, 4, 0⟩ e n p 0 hp t s 4 0 rfl rfl (by norm_num) (by norm_num)
  have b7 := floor_diff_bounds ⟨0, 1 / 2, 9, 0⟩ e n p 0 hp t s 9 0 rfl rfl (by norm_num) (by norm_num)
  have b8 := floor_diff_bounds ⟨0, 2 / 3, 6, 0⟩ e n p 0 hp t s 6 0 rfl rfl (by norm_num) (by norm_num)
  have b9 := floor_diff_bounds ⟨0, 2 / 3, 5, 0⟩ e n p 0 hp t s 5 0 rfl rfl (by norm_num) (by norm_num)
  have b10 := floor_diff_bounds ⟨0, 1 / 3, 4, 0⟩ e n p 0 hp t s 4 0 rfl rfl (by norm_num) (by norm_num)
  have key : (-11 : ℚ) < (((gammaF.map (fun fm => fm.2 * ((fm.1.hi e).floorAt n p 0 -
      (fm.1.lo e).floorAt n p 0))).sum : ℤ) : ℚ) := by
    simp only [gammaF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 ⊢
    linarith [b0.2, b1.1, b2.2, b3.1, b4.2, b5.1, b6.1, b7.2, b8.1, b9.1, b10.2]
  have : (-11 : ℤ) < (gammaF.map (fun fm => fm.2 * ((fm.1.hi e).floorAt n p 0 -
      (fm.1.lo e).floorAt n p 0))).sum := by exact_mod_cast key
  omega

end CB

section generic
variable (fq : ℕ → Fin 3 → ℚ) (G : ℕ → ℚ)
  (hfeq : ∀ n i, fq n i = (35 / 1944 : ℚ) * (Δ n)⁻¹ * w n i)
  (hfval : ∀ (n p : ℕ) [Fact p.Prime], 7 ≤ p → 144 * n + 24 < p ^ 2 → ∀ i,
    VGe p (min 0 (hminF n p)) (fq n i))
  (hΔ : ∀ (n p : ℕ) [Fact p.Prime], 5 ≤ p → 144 * n + 24 < p ^ 2 →
    padicValRat p (Δ n) = padicValRat p (G n) +
      (gammaF.map (fun fm => fm.2 * ((fm.1.hi (p % 6)).floorAt n p 0 - (fm.1.lo (p % 6)).floorAt n p 0))).sum)
  (hΔne : ∀ n, Δ n ≠ 0)
include hfeq hfval hΔ hΔne

theorem fwd_crude_gen : ∃ P0 : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → 144 * n + 24 < p ^ 2 →
    ∀ i, VGe p (-16 - (padicValRat p (G n)).natAbs) (w n i) := by
  refine ⟨11, fun n p hp hP hbig i => ?_⟩
  have := Fact.mk hp
  have h := CB.w_val hP (w n i) (Δ n) (fq n i) (hΔne n) (hfeq n i) _ (hfval n p (by omega) hbig i)
  refine h.mono ?_
  rw [hΔ n p (by omega) hbig]
  have h1 := CB.gamma_crude n p (by omega) (p % 6)
  have h2 := CB.hminF_crude n p (by omega)
  have h3 : -((padicValRat p (G n)).natAbs : ℤ) ≤ padicValRat p (G n) := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  have h4 : -5 ≤ min 0 (hminF n p) := le_min (by norm_num) h2
  linarith

theorem fwd_cell_gen (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hwF : wallFree (endpts (fwdZ ++ fwdP) e) lo hi x0 = true)
    (hwG : wallFree1 (endpts (gammaF.map (·.1)) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (fwdCellBound e (L + x0) - (padicValRat p (G n)).natAbs) (w n i) := by
  obtain ⟨P1, K1, hF⟩ := fwdH_ge_cand e he lo hi x0 hwF L
  obtain ⟨P2, K2, hG⟩ := gamma_counts1 e he lo hi x0 hwG L
  refine ⟨max (max P1 P2) 11, max K1 K2, fun n p hp hP hpe h1 h2 hbig i => ?_⟩
  have := Fact.mk hp
  have hP1 : P1 ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP
  have hP2 : P2 ≤ p := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP
  have hp11 : 11 ≤ p := le_trans (le_max_right _ _) hP
  have hK1 : (K1 : ℚ) ≤ (max K1 K2 : ℕ) := by exact_mod_cast le_max_left _ _
  have hK2 : (K2 : ℚ) ≤ (max K1 K2 : ℕ) := by exact_mod_cast le_max_right _ _
  have h1a : ((L : ℚ) + lo) * p + K1 ≤ n := by linarith
  have h2a : (n : ℚ) + K1 ≤ ((L : ℚ) + hi) * p := by linarith
  have h1b : ((L : ℚ) + lo) * p + K2 ≤ n := by linarith
  have h2b : (n : ℚ) + K2 ≤ ((L : ℚ) + hi) * p := by linarith
  have h := CB.w_val hp11 (w n i) (Δ n) (fq n i) (hΔne n) (hfeq n i) _ (hfval n p (by omega) hbig i)
  refine h.mono ?_
  rw [hΔ n p (by omega) hbig, hpe]
  have hgam : (gammaF.map (fun fm => fm.2 * ((fm.1.hi e).floorAt n p 0 - (fm.1.lo e).floorAt n p 0))).sum =
      detProfile e (L + x0) := by
    unfold detProfile
    congr 1
    refine List.map_congr_left (fun fm hfm => ?_)
    rw [hG n p hp hP2 hpe h1b h2b fm hfm]
  rw [hgam]
  set M := ((candSets (endpts (fwdZ ++ fwdP) e) (L + x0)).map
          (fun S => fwdH (floorsOf (endpts (fwdZ ++ fwdP) e) (L + x0) S))).foldr min 0 with hM
  have hM0 : M ≤ 0 := CB.foldr_min_nonpos _
  have hmin : M ≤ hminF n p := by
    unfold hminF
    rw [hpe]
    refine CB.le_foldr_min hM0 (fun x hx => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact hF n p r hp hP1 hpe h1a h2a (List.mem_range.1 hr)
  have hcb : fwdCellBound e (L + x0) = min 0 M + detProfile e (L + x0) := rfl
  rw [hcb, min_eq_right hM0]
  have h3 : -((padicValRat p (G n)).natAbs : ℤ) ≤ padicValRat p (G n) := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  have h4 : M ≤ min 0 (hminF n p) := le_min hM0 hmin
  linarith

end generic

theorem dual_cell_bound (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hw : wallFree (endpts (dualZ ++ dualP) e) lo hi x0 = true) (L : ℕ) (ex : ℕ → PType → Bool) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (dualCellBound e (L + x0) ex) (w n i) := by
  obtain ⟨P1, K1, hmem⟩ := dualType_mem_cand e he lo hi x0 hw L
  set Ts := dualCandTypes e (L + x0) with hTs
  set B : ℚ := ((Ts.flatMap (fun t => t.zs ++ t.ps.map Prod.fst)).map (fun x => |x|)).sum with hB
  refine ⟨max (max P1 5) (⌈12 * B⌉.toNat + 1), K1, ?_⟩
  intro n p hp hP hpe h1 h2 hbig i
  have := Fact.mk hp
  have hP1 : P1 ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP
  have hp5 : 5 ≤ p := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP
  have hPB : ⌈12 * B⌉.toNat + 1 ≤ p := le_trans (le_max_right _ _) hP
  have hcand : ∀ r < p, dualTypeAt n p r ∈ Ts := fun r hr => hmem n p r hp hP1 hpe h1 h2 hr
  have hspan : ∀ k, k = 1 ∨ k = 2 → InSpan p (Ts.flatMap PType.gens) (colVec n p k) := by
    intro k hk
    refine (lemmaA n p hp5 hbig k hk).mono (fun g hg => ?_)
    obtain ⟨r, hr, hg⟩ := List.mem_flatMap.1 hg
    exact List.mem_flatMap.2 ⟨_, hcand r (List.mem_range.1 hr), hg⟩
  have hint : ∀ t ∈ Ts, ∀ g ∈ t.gens, ∀ k, VGe p 0 (g.2 k) := by
    intro t ht
    obtain ⟨F, j, rfl⟩ := CB.mem_dualCandTypes ht
    refine PType.gens_pint _ hp5 (fun x hx => ⟨CB.mkDualType_den e he F j x hx, ?_⟩)
    have hxB : |x| ≤ B := by
      rw [hB]
      apply List.single_le_sum (fun y hy => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact abs_nonneg z)
      exact List.mem_map.2 ⟨x, List.mem_flatMap.2 ⟨_, ht, hx⟩, rfl⟩
    have hc : (12 * B : ℚ) ≤ ((⌈12 * B⌉.toNat : ℕ) : ℚ) := by
      have := Int.le_ceil (12 * B)
      have h2 : (⌈12 * B⌉ : ℚ) ≤ ((⌈12 * B⌉.toNat : ℤ) : ℚ) := by
        exact_mod_cast Int.self_le_toNat _
      push_cast at h2 ⊢; linarith
    have hc2 : ((⌈12 * B⌉.toNat : ℕ) : ℚ) + 1 ≤ p := by exact_mod_cast hPB
    linarith
  have hnd : ∀ t ∈ Ts, (t.ps.map Prod.fst).Nodup := by
    intro t ht; obtain ⟨F, j, rfl⟩ := CB.mem_dualCandTypes ht; exact CB.mkDualType_nodup e he F j
  have hlab : ∀ t ∈ Ts, ∀ q ∈ t.ps, q.2 ≤ 2 := by
    intro t ht; obtain ⟨F, j, rfl⟩ := CB.mem_dualCandTypes ht; exact CB.mkDualType_lab e F j
  obtain ⟨hA, hB2, hC⟩ := dualBound_sound Ts ex hint hnd hlab (colVec n p 1) (colVec n p 2)
    (hspan 1 (Or.inl rfl)) (hspan 2 (Or.inr rfl)) (CB.colVec_three n p 1 (by norm_num))
    (CB.colVec_three n p 2 (by norm_num))
  have hD : dualCellBound e (L + x0) ex = dualBoundOf Ts ex := rfl
  rw [hD]
  set D := dualBoundOf Ts ex
  obtain ⟨w0, w1, w2⟩ := CB.w_B n
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm12 : minor 1 2 (colVec n p 1) (colVec n p 2) = w n 0 := by
    rw [w0]; simp [minor, colVec]
  have hW0 : VGe p D (w n 0) := hm12 ▸ hA
  have hpinv : ∀ x : ℚ, VGe p (D + 2) x → VGe p D (((p : ℚ) ^ 2)⁻¹ * x) := by
    intro x hx
    have := (VGe.zpow (p := p) (-2)).mul hx
    rw [show (-2 : ℤ) + (D + 2) = D by ring, zpow_neg, zpow_ofNat] at this
    exact this
  fin_cases i
  · exact hW0
  · have e1 : w n 1 =
        -(((p : ℚ) ^ 2)⁻¹ * minor 0 2 (colVec n p 1) (colVec n p 2)) - cT p * w n 0 := by
      rw [w1, w0]; simp only [minor, colVec, B0']; simp; field_simp; ring
    show VGe p D (w n 1)
    rw [e1]
    exact (hpinv _ hC).neg.sub (by simpa using CB.cT_pint.mul hW0)
  · have e2 : w n 2 =
        ((p : ℚ) ^ 2)⁻¹ * minor 0 1 (colVec n p 1) (colVec n p 2) - cH p * w n 0 := by
      rw [w2, w0]; simp only [minor, colVec, B0']; simp; field_simp; ring
    show VGe p D (w n 2)
    rw [e2]
    exact (hpinv _ hB2).sub (by simpa using CB.cH_pint.mul hW0)

theorem fwd_cell_bound (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hwF : wallFree (endpts (fwdZ ++ fwdP) e) lo hi x0 = true)
    (hwG : wallFree1 (endpts (gammaF.map (·.1)) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (fwdCellBound e (L + x0) - (padicValRat p (gfun n / gfun 0)).natAbs) (w n i) :=
  fwd_cell_gen fvecQ (fun n => gfun n / gfun 0) fvecQ_eq
    (fun n p _ hp hbig i => fwd_val n p hp hbig i)
    (fun n p _ hp hbig => padicValRat_Delta n p hp hbig) Delta_ne_zero e he lo hi x0 hwF hwG L

/-- the forward chamber bound does not depend on the lift -/
theorem fwdCellBound_shift (e : ℕ) (x : ℚ) (L : ℕ) : fwdCellBound e (L + x) = fwdCellBound e x := by
  unfold fwdCellBound; dsimp only
  rw [CB.candSets_shift, CB.detProfile_shift]
  congr 3
  refine List.map_congr_left (fun S _ => ?_)
  have h : floorsOf (endpts (fwdZ ++ fwdP) e) (L + x) S =
      fun i => floorsOf (endpts (fwdZ ++ fwdP) e) x S i + ((endpts (fwdZ ++ fwdP) e)[i]!).a * L :=
    funext (CB.floorsOf_shift _ x L S)
  rw [h]
  simp only [fwdH]
  have e0 : ((endpts (fwdZ ++ fwdP) e)[0]!).a = -12 := rfl
  have e1 : ((endpts (fwdZ ++ fwdP) e)[1]!).a = -2 := rfl
  have e2 : ((endpts (fwdZ ++ fwdP) e)[2]!).a = -6 := rfl
  have e3 : ((endpts (fwdZ ++ fwdP) e)[3]!).a = 0 := rfl
  have e4 : ((endpts (fwdZ ++ fwdP) e)[4]!).a = -5 := rfl
  have e5 : ((endpts (fwdZ ++ fwdP) e)[5]!).a = -2 := rfl
  have e6 : ((endpts (fwdZ ++ fwdP) e)[6]!).a = 0 := rfl
  have e7 : ((endpts (fwdZ ++ fwdP) e)[7]!).a = 10 := rfl
  have e8 : ((endpts (fwdZ ++ fwdP) e)[8]!).a = -1 := rfl
  have e9 : ((endpts (fwdZ ++ fwdP) e)[9]!).a = 8 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  ring

/-- crude bound for all large primes (any `n/p`) -/
theorem fwd_crude : ∃ P0 : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → 144 * n + 24 < p ^ 2 →
    ∀ i, VGe p (-16 - (padicValRat p (gfun n / gfun 0)).natAbs) (w n i) :=
  fwd_crude_gen fvecQ (fun n => gfun n / gfun 0) fvecQ_eq
    (fun n p _ hp hbig i => fwd_val n p hp hbig i)
    (fun n p _ hp hbig => padicValRat_Delta n p hp hbig) Delta_ne_zero

end Zeta2L2Chi3.Arith
