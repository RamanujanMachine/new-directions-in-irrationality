import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells0 : List DCell := [
  ⟨1, 0, (0 : ℚ), (1/48 : ℚ), 0, []⟩,
  ⟨1, 1, (0 : ℚ), (1/48 : ℚ), -2, []⟩,
  ⟨1, 0, (1/48 : ℚ), (1/42 : ℚ), 0, []⟩,
  ⟨1, 1, (1/48 : ℚ), (1/42 : ℚ), -2, []⟩,
  ⟨1, 0, (1/42 : ℚ), (1/30 : ℚ), 0, []⟩,
  ⟨1, 1, (1/42 : ℚ), (1/30 : ℚ), -2, []⟩,
  ⟨1, 0, (1/30 : ℚ), (1/26 : ℚ), 0, []⟩,
  ⟨1, 1, (1/30 : ℚ), (1/26 : ℚ), -2, []⟩,
  ⟨1, 0, (1/26 : ℚ), (1/24 : ℚ), 0, []⟩,
  ⟨1, 1, (1/26 : ℚ), (1/24 : ℚ), -2, []⟩,
  ⟨1, 0, (1/24 : ℚ), (1/22 : ℚ), 1, []⟩,
  ⟨1, 1, (1/24 : ℚ), (1/22 : ℚ), 0, []⟩,
  ⟨1, 0, (1/22 : ℚ), (1/20 : ℚ), 1, []⟩,
  ⟨1, 1, (1/22 : ℚ), (1/20 : ℚ), 0, []⟩,
  ⟨1, 0, (1/20 : ℚ), (1/18 : ℚ), 1, []⟩,
  ⟨1, 1, (1/20 : ℚ), (1/18 : ℚ), 0, []⟩,
  ⟨1, 0, (1/18 : ℚ), (1/15 : ℚ), -1, []⟩,
  ⟨1, 1, (1/18 : ℚ), (1/15 : ℚ), -1, []⟩,
  ⟨1, 0, (1/15 : ℚ), (1/14 : ℚ), -2, []⟩,
  ⟨1, 1, (1/15 : ℚ), (1/14 : ℚ), -2, []⟩,
  ⟨1, 0, (1/14 : ℚ), (1/12 : ℚ), -2, []⟩,
  ⟨1, 1, (1/14 : ℚ), (1/12 : ℚ), -2, []⟩,
  ⟨1, 0, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 1, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 0, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 1, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 0, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 1, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 0, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 1, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 0, (1/9 : ℚ), (3/26 : ℚ), -2, []⟩,
  ⟨1, 1, (1/9 : ℚ), (3/26 : ℚ), -2, []⟩,
  ⟨1, 0, (3/26 : ℚ), (1/8 : ℚ), -2, []⟩,
  ⟨1, 1, (3/26 : ℚ), (1/8 : ℚ), -2, []⟩,
  ⟨1, 0, (1/8 : ℚ), (2/15 : ℚ), -1, []⟩,
  ⟨1, 1, (1/8 : ℚ), (2/15 : ℚ), -1, []⟩,
  ⟨1, 0, (2/15 : ℚ), (3/22 : ℚ), -1, []⟩,
  ⟨1, 1, (2/15 : ℚ), (3/22 : ℚ), -1, []⟩,
  ⟨1, 0, (3/22 : ℚ), (5/36 : ℚ), -1, []⟩,
  ⟨1, 1, (3/22 : ℚ), (5/36 : ℚ), -1, []⟩,
  ⟨1, 0, (5/36 : ℚ), (7/48 : ℚ), -1, []⟩,
  ⟨1, 1, (5/36 : ℚ), (7/48 : ℚ), -1, []⟩,
  ⟨1, 0, (7/48 : ℚ), (3/20 : ℚ), -1, []⟩,
  ⟨1, 1, (7/48 : ℚ), (3/20 : ℚ), -1, []⟩,
  ⟨1, 0, (3/20 : ℚ), (1/6 : ℚ), -1, []⟩,
  ⟨1, 1, (3/20 : ℚ), (1/6 : ℚ), -1, []⟩,
  ⟨1, 0, (1/6 : ℚ), (2/11 : ℚ), -2, []⟩,
  ⟨1, 1, (1/6 : ℚ), (2/11 : ℚ), -2, []⟩,
  ⟨1, 0, (2/11 : ℚ), (5/26 : ℚ), -2, []⟩,
  ⟨1, 1, (2/11 : ℚ), (5/26 : ℚ), -2, []⟩,
  ⟨1, 0, (5/26 : ℚ), (1/5 : ℚ), -2, []⟩,
  ⟨1, 1, (5/26 : ℚ), (1/5 : ℚ), -2, []⟩,
  ⟨1, 0, (1/5 : ℚ), (5/24 : ℚ), -1, []⟩,
  ⟨1, 1, (1/5 : ℚ), (5/24 : ℚ), -1, []⟩,
  ⟨1, 0, (5/24 : ℚ), (3/14 : ℚ), -1, []⟩,
  ⟨1, 1, (5/24 : ℚ), (3/14 : ℚ), -1, []⟩,
  ⟨1, 0, (3/14 : ℚ), (2/9 : ℚ), -1, []⟩,
  ⟨1, 1, (3/14 : ℚ), (2/9 : ℚ), -1, []⟩,
  ⟨1, 0, (2/9 : ℚ), (5/22 : ℚ), -2, []⟩,
  ⟨1, 1, (2/9 : ℚ), (5/22 : ℚ), -2, []⟩,
  ⟨1, 0, (5/22 : ℚ), (7/30 : ℚ), -2, []⟩,
  ⟨1, 1, (5/22 : ℚ), (7/30 : ℚ), -2, []⟩,
  ⟨1, 0, (7/30 : ℚ), (5/21 : ℚ), -2, []⟩,
  ⟨1, 1, (7/30 : ℚ), (5/21 : ℚ), -2, []⟩,
  ⟨1, 0, (5/21 : ℚ), (1/4 : ℚ), -2, []⟩,
  ⟨1, 1, (5/21 : ℚ), (1/4 : ℚ), -2, []⟩,
  ⟨1, 0, (1/4 : ℚ), (4/15 : ℚ), -1, []⟩,
  ⟨1, 1, (1/4 : ℚ), (4/15 : ℚ), -1, []⟩,
  ⟨1, 0, (4/15 : ℚ), (7/26 : ℚ), -2, []⟩,
  ⟨1, 1, (4/15 : ℚ), (7/26 : ℚ), -2, []⟩,
  ⟨1, 0, (7/26 : ℚ), (13/48 : ℚ), -2, []⟩,
  ⟨1, 1, (7/26 : ℚ), (13/48 : ℚ), -2, []⟩,
  ⟨1, 0, (13/48 : ℚ), (3/11 : ℚ), -2, []⟩,
  ⟨1, 1, (13/48 : ℚ), (3/11 : ℚ), -2, []⟩,
  ⟨1, 0, (3/11 : ℚ), (5/18 : ℚ), -2, []⟩,
  ⟨1, 1, (3/11 : ℚ), (5/18 : ℚ), -2, []⟩,
  ⟨1, 0, (5/18 : ℚ), (7/24 : ℚ), -2, []⟩,
  ⟨1, 1, (5/18 : ℚ), (7/24 : ℚ), -2, []⟩,
  ⟨1, 0, (7/24 : ℚ), (3/10 : ℚ), 0, []⟩,
  ⟨1, 1, (7/24 : ℚ), (3/10 : ℚ), 0, []⟩,
  ⟨1, 0, (3/10 : ℚ), (11/36 : ℚ), 0, []⟩,
  ⟨1, 1, (3/10 : ℚ), (11/36 : ℚ), 0, []⟩,
  ⟨1, 0, (11/36 : ℚ), (13/42 : ℚ), -1, []⟩,
  ⟨1, 1, (11/36 : ℚ), (13/42 : ℚ), -1, []⟩,
  ⟨1, 0, (13/42 : ℚ), (7/22 : ℚ), -1, []⟩,
  ⟨1, 1, (13/42 : ℚ), (7/22 : ℚ), -1, []⟩,
  ⟨1, 0, (7/22 : ℚ), (1/3 : ℚ), -1, []⟩,
  ⟨1, 1, (7/22 : ℚ), (1/3 : ℚ), -1, []⟩,
  ⟨1, 0, (1/3 : ℚ), (9/26 : ℚ), -2, []⟩,
  ⟨1, 1, (1/3 : ℚ), (9/26 : ℚ), -2, []⟩,
  ⟨1, 0, (9/26 : ℚ), (7/20 : ℚ), -2, []⟩,
  ⟨1, 1, (9/26 : ℚ), (7/20 : ℚ), -2, []⟩,
  ⟨1, 0, (7/20 : ℚ), (5/14 : ℚ), -2, []⟩,
  ⟨1, 1, (7/20 : ℚ), (5/14 : ℚ), -2, []⟩,
  ⟨1, 0, (5/14 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨1, 1, (5/14 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨1, 0, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨1, 1, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨1, 0, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨1, 1, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩]

theorem dcells0_c0 : ((dcells0.drop (4 * 0)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c1 : ((dcells0.drop (4 * 1)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c2 : ((dcells0.drop (4 * 2)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c3 : ((dcells0.drop (4 * 3)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c4 : ((dcells0.drop (4 * 4)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c5 : ((dcells0.drop (4 * 5)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c6 : ((dcells0.drop (4 * 6)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c7 : ((dcells0.drop (4 * 7)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c8 : ((dcells0.drop (4 * 8)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c9 : ((dcells0.drop (4 * 9)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c10 : ((dcells0.drop (4 * 10)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c11 : ((dcells0.drop (4 * 11)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c12 : ((dcells0.drop (4 * 12)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c13 : ((dcells0.drop (4 * 13)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c14 : ((dcells0.drop (4 * 14)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c15 : ((dcells0.drop (4 * 15)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c16 : ((dcells0.drop (4 * 16)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c17 : ((dcells0.drop (4 * 17)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c18 : ((dcells0.drop (4 * 18)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c19 : ((dcells0.drop (4 * 19)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c20 : ((dcells0.drop (4 * 20)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c21 : ((dcells0.drop (4 * 21)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c22 : ((dcells0.drop (4 * 22)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c23 : ((dcells0.drop (4 * 23)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_c24 : ((dcells0.drop (4 * 24)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells0_ok : dcells0.all DCell.ok = true :=
  all_chunks _ 4 25 dcells0 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells0_c0, dcells0_c1, dcells0_c2, dcells0_c3, dcells0_c4, dcells0_c5, dcells0_c6, dcells0_c7, dcells0_c8, dcells0_c9, dcells0_c10, dcells0_c11, dcells0_c12, dcells0_c13, dcells0_c14, dcells0_c15, dcells0_c16, dcells0_c17, dcells0_c18, dcells0_c19, dcells0_c20, dcells0_c21, dcells0_c22, dcells0_c23, dcells0_c24])

end Zeta2L2Chi3.Arith
