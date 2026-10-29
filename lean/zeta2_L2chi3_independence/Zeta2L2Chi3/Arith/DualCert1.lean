import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells1 : List DCell := [
  ⟨1, 0, (3/8 : ℚ), (8/21 : ℚ), -1, []⟩,
  ⟨1, 1, (3/8 : ℚ), (8/21 : ℚ), -1, []⟩,
  ⟨1, 0, (8/21 : ℚ), (7/18 : ℚ), -1, []⟩,
  ⟨1, 1, (8/21 : ℚ), (7/18 : ℚ), -1, []⟩,
  ⟨1, 0, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 1, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 0, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 1, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 0, (2/5 : ℚ), (9/22 : ℚ), -2, []⟩,
  ⟨1, 1, (2/5 : ℚ), (9/22 : ℚ), -2, []⟩,
  ⟨1, 0, (9/22 : ℚ), (5/12 : ℚ), -2, []⟩,
  ⟨1, 1, (9/22 : ℚ), (5/12 : ℚ), -2, []⟩,
  ⟨1, 0, (5/12 : ℚ), (11/26 : ℚ), -1, []⟩,
  ⟨1, 1, (5/12 : ℚ), (11/26 : ℚ), -1, []⟩,
  ⟨1, 0, (11/26 : ℚ), (13/30 : ℚ), -1, []⟩,
  ⟨1, 1, (11/26 : ℚ), (13/30 : ℚ), -1, []⟩,
  ⟨1, 0, (13/30 : ℚ), (4/9 : ℚ), -1, []⟩,
  ⟨1, 1, (13/30 : ℚ), (4/9 : ℚ), -1, []⟩,
  ⟨1, 0, (4/9 : ℚ), (9/20 : ℚ), 0, []⟩,
  ⟨1, 1, (4/9 : ℚ), (9/20 : ℚ), 0, []⟩,
  ⟨1, 0, (9/20 : ℚ), (19/42 : ℚ), 0, []⟩,
  ⟨1, 1, (9/20 : ℚ), (19/42 : ℚ), 0, []⟩,
  ⟨1, 0, (19/42 : ℚ), (5/11 : ℚ), 0, []⟩,
  ⟨1, 1, (19/42 : ℚ), (5/11 : ℚ), 0, []⟩,
  ⟨1, 0, (5/11 : ℚ), (11/24 : ℚ), 0, []⟩,
  ⟨1, 1, (5/11 : ℚ), (11/24 : ℚ), 0, []⟩,
  ⟨1, 0, (11/24 : ℚ), (7/15 : ℚ), 0, []⟩,
  ⟨1, 1, (11/24 : ℚ), (7/15 : ℚ), 0, []⟩,
  ⟨1, 0, (7/15 : ℚ), (17/36 : ℚ), -1, []⟩,
  ⟨1, 1, (7/15 : ℚ), (17/36 : ℚ), -1, []⟩,
  ⟨1, 0, (17/36 : ℚ), (1/2 : ℚ), -2, []⟩,
  ⟨1, 1, (17/36 : ℚ), (1/2 : ℚ), -2, []⟩,
  ⟨1, 0, (1/2 : ℚ), (25/48 : ℚ), -3, []⟩,
  ⟨1, 1, (1/2 : ℚ), (25/48 : ℚ), -3, []⟩,
  ⟨1, 0, (25/48 : ℚ), (11/21 : ℚ), -3, []⟩,
  ⟨1, 1, (25/48 : ℚ), (11/21 : ℚ), -3, []⟩,
  ⟨1, 0, (11/21 : ℚ), (8/15 : ℚ), -3, []⟩,
  ⟨1, 1, (11/21 : ℚ), (8/15 : ℚ), -3, []⟩,
  ⟨1, 0, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨1, 1, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨1, 0, (13/24 : ℚ), (6/11 : ℚ), 0, []⟩,
  ⟨1, 1, (13/24 : ℚ), (6/11 : ℚ), 0, []⟩,
  ⟨1, 0, (6/11 : ℚ), (11/20 : ℚ), 0, []⟩,
  ⟨1, 1, (6/11 : ℚ), (11/20 : ℚ), 0, []⟩,
  ⟨1, 0, (11/20 : ℚ), (5/9 : ℚ), 0, []⟩,
  ⟨1, 1, (11/20 : ℚ), (5/9 : ℚ), 0, []⟩,
  ⟨1, 0, (5/9 : ℚ), (17/30 : ℚ), -2, []⟩,
  ⟨1, 1, (5/9 : ℚ), (17/30 : ℚ), -2, []⟩,
  ⟨1, 0, (17/30 : ℚ), (15/26 : ℚ), -2, []⟩,
  ⟨1, 1, (17/30 : ℚ), (15/26 : ℚ), -2, []⟩,
  ⟨1, 0, (15/26 : ℚ), (7/12 : ℚ), -2, []⟩,
  ⟨1, 1, (15/26 : ℚ), (7/12 : ℚ), -2, []⟩,
  ⟨1, 0, (7/12 : ℚ), (13/22 : ℚ), -3, []⟩,
  ⟨1, 1, (7/12 : ℚ), (13/22 : ℚ), -3, []⟩,
  ⟨1, 0, (13/22 : ℚ), (25/42 : ℚ), -3, []⟩,
  ⟨1, 1, (13/22 : ℚ), (25/42 : ℚ), -3, []⟩,
  ⟨1, 0, (25/42 : ℚ), (3/5 : ℚ), -3, []⟩,
  ⟨1, 1, (25/42 : ℚ), (3/5 : ℚ), -3, []⟩,
  ⟨1, 0, (3/5 : ℚ), (11/18 : ℚ), -2, []⟩,
  ⟨1, 1, (3/5 : ℚ), (11/18 : ℚ), -2, []⟩,
  ⟨1, 0, (11/18 : ℚ), (5/8 : ℚ), -2, []⟩,
  ⟨1, 1, (11/18 : ℚ), (5/8 : ℚ), -2, []⟩,
  ⟨1, 0, (5/8 : ℚ), (19/30 : ℚ), 0, []⟩,
  ⟨1, 1, (5/8 : ℚ), (19/30 : ℚ), 0, []⟩,
  ⟨1, 0, (19/30 : ℚ), (7/11 : ℚ), 0, []⟩,
  ⟨1, 1, (19/30 : ℚ), (7/11 : ℚ), 0, []⟩,
  ⟨1, 0, (7/11 : ℚ), (23/36 : ℚ), 0, []⟩,
  ⟨1, 1, (7/11 : ℚ), (23/36 : ℚ), 0, []⟩,
  ⟨1, 0, (23/36 : ℚ), (9/14 : ℚ), -1, []⟩,
  ⟨1, 1, (23/36 : ℚ), (9/14 : ℚ), -1, []⟩,
  ⟨1, 0, (9/14 : ℚ), (31/48 : ℚ), -1, []⟩,
  ⟨1, 1, (9/14 : ℚ), (31/48 : ℚ), -1, []⟩,
  ⟨1, 0, (31/48 : ℚ), (13/20 : ℚ), -1, []⟩,
  ⟨1, 1, (31/48 : ℚ), (13/20 : ℚ), -1, []⟩,
  ⟨1, 0, (13/20 : ℚ), (17/26 : ℚ), -1, []⟩,
  ⟨1, 1, (13/20 : ℚ), (17/26 : ℚ), -1, []⟩,
  ⟨1, 0, (17/26 : ℚ), (2/3 : ℚ), -1, []⟩,
  ⟨1, 1, (17/26 : ℚ), (2/3 : ℚ), -1, []⟩,
  ⟨1, 0, (2/3 : ℚ), (15/22 : ℚ), -2, []⟩,
  ⟨1, 1, (2/3 : ℚ), (15/22 : ℚ), -2, []⟩,
  ⟨1, 0, (15/22 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨1, 1, (15/22 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨1, 0, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨1, 1, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨1, 0, (17/24 : ℚ), (13/18 : ℚ), -2, []⟩,
  ⟨1, 1, (17/24 : ℚ), (13/18 : ℚ), -2, []⟩,
  ⟨1, 0, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 1, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 0, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 1, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 0, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 1, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 0, (11/15 : ℚ), (31/42 : ℚ), -3, []⟩,
  ⟨1, 1, (11/15 : ℚ), (31/42 : ℚ), -3, []⟩,
  ⟨1, 0, (31/42 : ℚ), (3/4 : ℚ), -3, []⟩,
  ⟨1, 1, (31/42 : ℚ), (3/4 : ℚ), -3, []⟩,
  ⟨1, 0, (3/4 : ℚ), (23/30 : ℚ), -3, []⟩,
  ⟨1, 1, (3/4 : ℚ), (23/30 : ℚ), -3, []⟩,
  ⟨1, 0, (23/30 : ℚ), (37/48 : ℚ), -3, []⟩,
  ⟨1, 1, (23/30 : ℚ), (37/48 : ℚ), -3, []⟩]

theorem dcells1_c0 : ((dcells1.drop (4 * 0)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c1 : ((dcells1.drop (4 * 1)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c2 : ((dcells1.drop (4 * 2)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c3 : ((dcells1.drop (4 * 3)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c4 : ((dcells1.drop (4 * 4)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c5 : ((dcells1.drop (4 * 5)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c6 : ((dcells1.drop (4 * 6)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c7 : ((dcells1.drop (4 * 7)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c8 : ((dcells1.drop (4 * 8)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c9 : ((dcells1.drop (4 * 9)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c10 : ((dcells1.drop (4 * 10)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c11 : ((dcells1.drop (4 * 11)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c12 : ((dcells1.drop (4 * 12)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c13 : ((dcells1.drop (4 * 13)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c14 : ((dcells1.drop (4 * 14)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c15 : ((dcells1.drop (4 * 15)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c16 : ((dcells1.drop (4 * 16)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c17 : ((dcells1.drop (4 * 17)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c18 : ((dcells1.drop (4 * 18)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c19 : ((dcells1.drop (4 * 19)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c20 : ((dcells1.drop (4 * 20)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c21 : ((dcells1.drop (4 * 21)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c22 : ((dcells1.drop (4 * 22)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c23 : ((dcells1.drop (4 * 23)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_c24 : ((dcells1.drop (4 * 24)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells1_ok : dcells1.all DCell.ok = true :=
  all_chunks _ 4 25 dcells1 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells1_c0, dcells1_c1, dcells1_c2, dcells1_c3, dcells1_c4, dcells1_c5, dcells1_c6, dcells1_c7, dcells1_c8, dcells1_c9, dcells1_c10, dcells1_c11, dcells1_c12, dcells1_c13, dcells1_c14, dcells1_c15, dcells1_c16, dcells1_c17, dcells1_c18, dcells1_c19, dcells1_c20, dcells1_c21, dcells1_c22, dcells1_c23, dcells1_c24])

end Zeta2L2Chi3.Arith
