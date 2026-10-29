import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem fcells_c0 : ((fcells.drop (6 * 0)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c1 : ((fcells.drop (6 * 1)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c2 : ((fcells.drop (6 * 2)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c3 : ((fcells.drop (6 * 3)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c4 : ((fcells.drop (6 * 4)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c5 : ((fcells.drop (6 * 5)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c6 : ((fcells.drop (6 * 6)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c7 : ((fcells.drop (6 * 7)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c8 : ((fcells.drop (6 * 8)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c9 : ((fcells.drop (6 * 9)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c10 : ((fcells.drop (6 * 10)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c11 : ((fcells.drop (6 * 11)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c12 : ((fcells.drop (6 * 12)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c13 : ((fcells.drop (6 * 13)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c14 : ((fcells.drop (6 * 14)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c15 : ((fcells.drop (6 * 15)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c16 : ((fcells.drop (6 * 16)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c17 : ((fcells.drop (6 * 17)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c18 : ((fcells.drop (6 * 18)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c19 : ((fcells.drop (6 * 19)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c20 : ((fcells.drop (6 * 20)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c21 : ((fcells.drop (6 * 21)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c22 : ((fcells.drop (6 * 22)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c23 : ((fcells.drop (6 * 23)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c24 : ((fcells.drop (6 * 24)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c25 : ((fcells.drop (6 * 25)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c26 : ((fcells.drop (6 * 26)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c27 : ((fcells.drop (6 * 27)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c28 : ((fcells.drop (6 * 28)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c29 : ((fcells.drop (6 * 29)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c30 : ((fcells.drop (6 * 30)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c31 : ((fcells.drop (6 * 31)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c32 : ((fcells.drop (6 * 32)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c33 : ((fcells.drop (6 * 33)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c34 : ((fcells.drop (6 * 34)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c35 : ((fcells.drop (6 * 35)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c36 : ((fcells.drop (6 * 36)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c37 : ((fcells.drop (6 * 37)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c38 : ((fcells.drop (6 * 38)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c39 : ((fcells.drop (6 * 39)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c40 : ((fcells.drop (6 * 40)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c41 : ((fcells.drop (6 * 41)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c42 : ((fcells.drop (6 * 42)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_c43 : ((fcells.drop (6 * 43)).take 6).all FCell.ok = true := by decide +kernel

theorem fcells_ok : fcells.all FCell.ok = true :=
  all_chunks _ 6 44 fcells (by decide) (fun j hj => by
    interval_cases j
    exacts [fcells_c0, fcells_c1, fcells_c2, fcells_c3, fcells_c4, fcells_c5, fcells_c6, fcells_c7, fcells_c8, fcells_c9, fcells_c10, fcells_c11, fcells_c12, fcells_c13, fcells_c14, fcells_c15, fcells_c16, fcells_c17, fcells_c18, fcells_c19, fcells_c20, fcells_c21, fcells_c22, fcells_c23, fcells_c24, fcells_c25, fcells_c26, fcells_c27, fcells_c28, fcells_c29, fcells_c30, fcells_c31, fcells_c32, fcells_c33, fcells_c34, fcells_c35, fcells_c36, fcells_c37, fcells_c38, fcells_c39, fcells_c40, fcells_c41, fcells_c42, fcells_c43])

end Zeta2L2Chi3.Arith
