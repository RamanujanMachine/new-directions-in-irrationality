/-
# Assembly of the content bound from the chamber certificates

`contentBound_of` derives `ContentBound` from the summation theorem `content_rate`, applied to the
chambers `cellsF L` (forward chambers `fcells`, with the dual bounds of `dualTab` for `L < 20`),
assuming the certificate facts `fcells.all FCell.ok`, `dc.all DCell.ok` and the matching check
`dualOk dc` (discharged by the kernel in `Final.lean` with `dc = dcells0 ++ ⋯ ++ dcells11`).
-/
import Zeta2L2Chi3.Arith.CellBounds
import Zeta2L2Chi3.Arith.Sum
import Zeta2L2Chi3.Arith.Density
import Zeta2L2Chi3.Arith.FwdVal
import Zeta2L2Chi3.Arith.DeltaVal
import Zeta2L2Chi3.Reduction

open Filter

namespace Zeta2L2Chi3.Arith

/-- the chambers of lift `L` -/
def cellsF (L : ℕ) : List Chamber :=
  (fcells.zip (dualRow L)).map (fun p => ⟨p.1.e, p.1.lo, p.1.hi, cellM p.1 p.2⟩)

/-- every dual override of `dualTab` is certified by the `DCell` `dc[j]` -/
def dualOk (dc : List DCell) : Bool :=
  (List.range 20).all (fun L => (fcells.zip (dualTab.getD L [])).all (fun p =>
    p.2.all (fun x => (dc[x.2]?).any (fun d =>
      decide (d.L = L ∧ d.e = p.1.e ∧ d.lo = p.1.lo ∧ d.hi = p.1.hi ∧ d.m = x.1)))))

/-- the loss from the gamma factor `g(n)/g(0)` -/
noncomputable def γF (n p : ℕ) : ℕ := (padicValRat p (gfun n / gfun 0)).natAbs

theorem dualRow_len (L : ℕ) : (dualRow L).length = fcells.length := by
  unfold dualRow
  split_ifs with h
  · have := List.all_eq_true.1 dualTab_len L (List.mem_range.2 h)
    simpa using this
  · simp

theorem cellsF_fst (L : ℕ) : (fcells.zip (dualRow L)).map Prod.fst = fcells :=
  List.map_fst_zip (dualRow_len L).ge

theorem mem_cellsF {L : ℕ} {c : Chamber} (hc : c ∈ cellsF L) :
    ∃ p ∈ fcells.zip (dualRow L), c = ⟨p.1.e, p.1.lo, p.1.hi, cellM p.1 p.2⟩ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact ⟨p, hp, rfl⟩

theorem fcell_e {f : FCell} (hf : f ∈ fcells) : f.e = 1 ∨ f.e = 5 := by
  have := List.all_eq_true.1 fcells_e f hf
  simpa using this

theorem filter_cells {X : Type*} (l : List (FCell × X)) (g : FCell × X → ℤ) (e : ℕ) :
    ((l.map (fun p => (⟨p.1.e, p.1.lo, p.1.hi, g p⟩ : Chamber))).filter (fun c => decide (c.e = e))).map
        (fun c => (c.lo, c.hi)) =
      ((l.map Prod.fst).filter (fun f => decide (f.e = e))).map (fun f => (f.lo, f.hi)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons]
    split_ifs <;> simp_all

theorem cover (L : ℕ) (e : ℕ) (W : List ℚ)
    (hW : (fcells.filter (fun f => decide (f.e = e))).map (fun f => (f.lo, f.hi)) = W.zip W.tail) :
    ((cellsF L).filter (fun c => decide (c.e = e))).map (fun c => (c.lo, c.hi)) = W.zip W.tail := by
  unfold cellsF
  rw [filter_cells, cellsF_fst, hW]

theorem walls1_head : walls1.head? = some 0 ∧ walls1.getLast? = some 1 := by
  constructor <;> decide +kernel

theorem walls5_head : walls5.head? = some 0 ∧ walls5.getLast? = some 1 := by
  constructor <;> decide +kernel

/-! ### Per-chamber bounds -/

theorem fwd_chamber {f : FCell} (hf : f ∈ fcells) (hok : f.ok = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = f.e →
      ((L : ℚ) + f.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + f.hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (f.m - γF n p) (w n i) := by
  simp only [FCell.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hwF⟩, hwG⟩, hm⟩ := hok
  obtain ⟨P0, K, h⟩ := fwd_cell_bound f.e (fcell_e hf) f.lo f.hi (midpt f.lo f.hi) hwF hwG L
  refine ⟨P0, K, fun n p hp hP he h1 h2 hbig i => ?_⟩
  have := h n p hp hP he h1 h2 hbig i
  rwa [fwdCellBound_shift, hm] at this

theorem dual_chamber {f : FCell} (hf : f ∈ fcells) (hok : f.ok = true) {d : DCell} (hd : d.ok = true)
    (L : ℕ) (hL : d.L = L) (he : d.e = f.e) (hlo : d.lo = f.lo) (hhi : d.hi = f.hi) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = f.e →
      ((L : ℚ) + f.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + f.hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (d.m - γF n p) (w n i) := by
  simp only [FCell.ok, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hwD, -⟩, -⟩, -⟩ := hok
  simp only [DCell.ok, decide_eq_true_eq] at hd
  rw [hL, he, hlo, hhi] at hd
  obtain ⟨P0, K, h⟩ := dual_cell_bound f.e (fcell_e hf) f.lo f.hi (midpt f.lo f.hi) hwD L
    (fun i _ => d.hints.contains i)
  refine ⟨P0, K, fun n p hp hP hpe h1 h2 hbig i => ?_⟩
  have := h n p hp hP hpe h1 h2 hbig i
  rw [hd] at this
  have hpf := Fact.mk hp
  exact this.mono (by omega)

theorem cell_bound (dc : List DCell) (hfc : fcells.all FCell.ok = true) (hdc : dc.all DCell.ok = true)
    (hdual : dualOk dc = true) (L : ℕ) (c : Chamber) (hc : c ∈ cellsF L) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = c.e →
      ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (c.m - γF n p) (w n i) := by
  obtain ⟨⟨f, o⟩, hp, rfl⟩ := mem_cellsF hc
  have hf := (List.of_mem_zip hp).1
  have hok := List.all_eq_true.1 hfc f hf
  rcases o with _ | ⟨m, j⟩
  · exact fwd_chamber hf hok L
  · have ho := (List.of_mem_zip hp).2
    by_cases hL : L < 20
    · have hrow : dualRow L = dualTab.getD L [] := by unfold dualRow; simp [hL]
      rw [hrow] at hp
      have h1 := List.all_eq_true.1 hdual L (List.mem_range.2 hL)
      have h2 := List.all_eq_true.1 h1 _ hp
      simp only [Option.all_some] at h2
      cases hj : dc[j]? with
      | none => rw [hj] at h2; simp at h2
      | some d =>
        rw [hj] at h2
        simp only [Option.any_some, decide_eq_true_eq] at h2
        obtain ⟨hdL, hde, hdlo, hdhi, hdm⟩ := h2
        have hdok := List.all_eq_true.1 hdc d (List.mem_of_getElem? hj)
        have := dual_chamber hf hok hdok L hdL hde hdlo hdhi
        simpa [cellM, hdm] using this
    · unfold dualRow at ho
      simp [hL] at ho

/-! ### Small primes and `p = 2, 3` -/

theorem w_split (n : ℕ) (i : Fin 3) (hw : w n i ≠ 0) :
    fvecQ n i ≠ 0 ∧ w n i = 1944 / 35 * Δ n * fvecQ n i := by
  have hΔ := Delta_ne_zero n
  have he := fvecQ_eq n i
  refine ⟨?_, ?_⟩
  · rw [he]; exact mul_ne_zero (mul_ne_zero (by norm_num) (inv_ne_zero hΔ)) hw
  · rw [he]
    calc w n i = (1944 / 35 * (35 / 1944)) * (Δ n * (Δ n)⁻¹) * w n i := by
          rw [mul_inv_cancel₀ hΔ]; norm_num
      _ = 1944 / 35 * Δ n * (35 / 1944 * (Δ n)⁻¹ * w n i) := by ring

theorem w_padic (n : ℕ) (i : Fin 3) (hw : w n i ≠ 0) (p : ℕ) [Fact p.Prime] :
    fvecQ n i ≠ 0 ∧ padicValRat p (w n i) =
      padicValRat p (1944 / 35) + padicValRat p (Δ n) + padicValRat p (fvecQ n i) := by
  obtain ⟨hf, he⟩ := w_split n i hw
  refine ⟨hf, ?_⟩
  rw [he, padicValRat.mul (mul_ne_zero (by norm_num) (Delta_ne_zero n)) hf,
    padicValRat.mul (by norm_num) (Delta_ne_zero n)]

theorem const_val (p : ℕ) [Fact p.Prime] : -(padicValNat p 35 : ℤ) ≤ padicValRat p (1944 / 35) := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  have h1 : padicValRat p (1944 : ℚ) = padicValNat p 1944 := by
    rw [show (1944 : ℚ) = ((1944 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  have h2 : padicValRat p (35 : ℚ) = padicValNat p 35 := by
    rw [show (35 : ℚ) = ((35 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  rw [h1, h2]
  omega

theorem val35_le (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) : padicValNat p 35 ≤ 1 := by
  by_contra h
  have h2 : p ^ 2 ∣ 35 := (padicValNat_dvd_iff_le (by norm_num)).2 (by omega)
  have h3 : p ^ 2 ≤ 35 := Nat.le_of_dvd (by norm_num) h2
  have h4 : p ≤ 5 := by nlinarith
  have : p = 5 := by omega
  subst this
  norm_num at h2

theorem small_bound : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, w n i ≠ 0 →
    -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (w n i) := by
  obtain ⟨C1, h1⟩ := delta_val_small
  obtain ⟨C2, h2⟩ := fwd_val_small
  refine ⟨C1 + C2 + 1, fun n p hn hp h5 i hw => ?_⟩
  have := Fact.mk hp
  obtain ⟨hf, he⟩ := w_padic n i hw p
  have a1 := h1 n p hn hp h5
  have a2 := h2 n p hn hp h5 i hf
  have a3 := const_val p
  have a4 := val35_le p h5
  have a3' : (-1 : ℝ) ≤ (padicValRat p (1944 / 35) : ℝ) := by
    have : (-1 : ℤ) ≤ padicValRat p (1944 / 35) := by omega
    exact_mod_cast this
  have hX : 0 ≤ Real.log n / Real.log p := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [he]
  push_cast
  nlinarith

theorem two_bound : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, w n i ≠ 0 →
    12 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (w n i) := by
  obtain ⟨C1, h1⟩ := delta_val_two
  obtain ⟨C2, h2⟩ := fwd_val_two
  refine ⟨C1 + C2, fun n hn i hw => ?_⟩
  have := Fact.mk Nat.prime_two
  obtain ⟨hf, he⟩ := w_padic n i hw 2
  have a1 := h1 n hn
  have a2 := h2 n hn i hf
  have a3 := const_val 2
  have a4 : padicValNat 2 35 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [a4] at a3
  have a5 : (0 : ℤ) ≤ padicValRat 2 (1944 / 35) := by simpa using a3
  have a3' : (0 : ℝ) ≤ (padicValRat 2 (1944 / 35) : ℝ) := by exact_mod_cast a5
  rw [he]
  push_cast
  linarith

theorem three_bound : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, w n i ≠ 0 →
    18 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (w n i) := by
  obtain ⟨C1, h1⟩ := delta_val_three
  obtain ⟨C2, h2⟩ := fwd_val_three
  refine ⟨C1 + C2, fun n hn i hw => ?_⟩
  have := Fact.mk Nat.prime_three
  obtain ⟨hf, he⟩ := w_padic n i hw 3
  have a1 := h1 n hn
  have a2 := h2 n hn i hf
  have a3 := const_val 3
  have a4 : padicValNat 3 35 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [a4] at a3
  have a5 : (0 : ℤ) ≤ padicValRat 3 (1944 / 35) := by simpa using a3
  have a3' : (0 : ℝ) ≤ (padicValRat 3 (1944 / 35) : ℝ) := by exact_mod_cast a5
  rw [he]
  push_cast
  linarith

theorem gamma_mass : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∑ q ∈ S, (γF n q : ℝ) * Real.log q ≤ C * Real.log (n + 1) := by
  obtain ⟨C, h⟩ := gfun_mass
  refine ⟨C, fun n hn S hS => ?_⟩
  have := h n hn S hS
  simpa [γF, Nat.cast_natAbs, Int.cast_abs] using this

theorem density_eq : chamberDensity cellsF 10000000 = densR 10000000 := by
  unfold chamberDensity densR cellsF cellData
  refine Finset.sum_congr rfl (fun L _ => ?_)
  simp only [List.map_map]
  rfl

/-- the content bound, from the certificate facts -/
theorem contentBound_of (dc : List DCell) (hfc : fcells.all FCell.ok = true)
    (hdc : dc.all DCell.ok = true) (hdual : dualOk dc = true) : ContentBound := by
  have hrate := content_rate cellsF 10000000 (by norm_num)
    (fun L _ => ⟨⟨walls1, walls1_head.1, walls1_head.2, cover L 1 walls1 walls1_eq, walls1_pw⟩,
      ⟨walls5, walls5_head.1, walls5_head.2, cover L 5 walls5 walls5_eq, walls5_pw⟩⟩)
    (fun L _ c hc => by
      obtain ⟨p, hp, rfl⟩ := mem_cellsF hc
      exact fcell_e (List.of_mem_zip hp).1)
    (fun c hc hlo => by
      obtain ⟨p, hp, rfl⟩ := mem_cellsF hc
      have hq : (p.1, cellM p.1 p.2) ∈ cellData 0 := List.mem_map_of_mem hp
      have := List.all_eq_true.1 cellData_zero _ hq
      simp only [decide_eq_true_eq] at this
      exact this hlo)
    γF gamma_mass
    (fun L _ c hc => cell_bound dc hfc hdc hdual L c hc)
    16 (by
      obtain ⟨P0, h⟩ := fwd_crude
      exact ⟨P0, fun n p hp hP hbig i => by simpa [γF] using h n p hp hP hbig i⟩)
    small_bound two_bound three_bound w_ne_zero
  intro ε hε
  have hd := density_bound
  rw [← density_eq] at hd
  filter_upwards [hrate ε hε] with n hn
  have hc : (0 : ℝ) < ((cont (w n) : ℚ) : ℝ) := by exact_mod_cast cont_pos (w n) (w_ne_zero n)
  rw [← Real.exp_log hc]
  apply Real.exp_le_exp.2
  refine le_trans ?_ hn
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  push_cast
  unfold β0
  linarith

end Zeta2L2Chi3.Arith
