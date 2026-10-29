import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells4 : List DCell := [
  ⟨5, 0, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 1, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 0, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 1, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 0, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 1, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 0, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 1, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 0, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 1, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 0, (5/9 : ℚ), (17/30 : ℚ), -2, []⟩,
  ⟨5, 1, (5/9 : ℚ), (17/30 : ℚ), -2, []⟩,
  ⟨5, 0, (17/30 : ℚ), (15/26 : ℚ), -2, []⟩,
  ⟨5, 1, (17/30 : ℚ), (15/26 : ℚ), -2, []⟩,
  ⟨5, 0, (15/26 : ℚ), (7/12 : ℚ), -2, []⟩,
  ⟨5, 1, (15/26 : ℚ), (7/12 : ℚ), -2, []⟩,
  ⟨5, 0, (7/12 : ℚ), (13/22 : ℚ), -1, []⟩,
  ⟨5, 1, (7/12 : ℚ), (13/22 : ℚ), -1, []⟩,
  ⟨5, 0, (13/22 : ℚ), (3/5 : ℚ), -1, []⟩,
  ⟨5, 1, (13/22 : ℚ), (3/5 : ℚ), -1, []⟩,
  ⟨5, 0, (3/5 : ℚ), (29/48 : ℚ), 0, []⟩,
  ⟨5, 1, (3/5 : ℚ), (29/48 : ℚ), 0, []⟩,
  ⟨5, 0, (29/48 : ℚ), (11/18 : ℚ), 0, []⟩,
  ⟨5, 1, (29/48 : ℚ), (11/18 : ℚ), 0, []⟩,
  ⟨5, 0, (11/18 : ℚ), (13/21 : ℚ), -2, []⟩,
  ⟨5, 1, (11/18 : ℚ), (13/21 : ℚ), -2, []⟩,
  ⟨5, 0, (13/21 : ℚ), (5/8 : ℚ), -2, []⟩,
  ⟨5, 1, (13/21 : ℚ), (5/8 : ℚ), -2, []⟩,
  ⟨5, 0, (5/8 : ℚ), (19/30 : ℚ), -1, []⟩,
  ⟨5, 1, (5/8 : ℚ), (19/30 : ℚ), -1, []⟩,
  ⟨5, 0, (19/30 : ℚ), (7/11 : ℚ), -1, []⟩,
  ⟨5, 1, (19/30 : ℚ), (7/11 : ℚ), -1, []⟩,
  ⟨5, 0, (7/11 : ℚ), (9/14 : ℚ), -1, []⟩,
  ⟨5, 1, (7/11 : ℚ), (9/14 : ℚ), -1, []⟩,
  ⟨5, 0, (9/14 : ℚ), (13/20 : ℚ), -1, []⟩,
  ⟨5, 1, (9/14 : ℚ), (13/20 : ℚ), -1, []⟩,
  ⟨5, 0, (13/20 : ℚ), (17/26 : ℚ), -1, []⟩,
  ⟨5, 1, (13/20 : ℚ), (17/26 : ℚ), -1, []⟩,
  ⟨5, 0, (17/26 : ℚ), (2/3 : ℚ), -1, []⟩,
  ⟨5, 1, (17/26 : ℚ), (2/3 : ℚ), -1, []⟩,
  ⟨5, 0, (2/3 : ℚ), (15/22 : ℚ), -2, []⟩,
  ⟨5, 1, (2/3 : ℚ), (15/22 : ℚ), -2, []⟩,
  ⟨5, 0, (15/22 : ℚ), (29/42 : ℚ), -2, []⟩,
  ⟨5, 1, (15/22 : ℚ), (29/42 : ℚ), -2, []⟩,
  ⟨5, 0, (29/42 : ℚ), (25/36 : ℚ), -2, []⟩,
  ⟨5, 1, (29/42 : ℚ), (25/36 : ℚ), -2, []⟩,
  ⟨5, 0, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 1, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 0, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 1, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 0, (17/24 : ℚ), (13/18 : ℚ), -1, []⟩,
  ⟨5, 1, (17/24 : ℚ), (13/18 : ℚ), -1, []⟩,
  ⟨5, 0, (13/18 : ℚ), (8/11 : ℚ), -1, []⟩,
  ⟨5, 1, (13/18 : ℚ), (8/11 : ℚ), -1, []⟩,
  ⟨5, 0, (8/11 : ℚ), (35/48 : ℚ), -1, []⟩,
  ⟨5, 1, (8/11 : ℚ), (35/48 : ℚ), -1, []⟩,
  ⟨5, 0, (35/48 : ℚ), (19/26 : ℚ), -1, []⟩,
  ⟨5, 1, (35/48 : ℚ), (19/26 : ℚ), -1, []⟩,
  ⟨5, 0, (19/26 : ℚ), (11/15 : ℚ), -1, []⟩,
  ⟨5, 1, (19/26 : ℚ), (11/15 : ℚ), -1, []⟩,
  ⟨5, 0, (11/15 : ℚ), (3/4 : ℚ), -2, []⟩,
  ⟨5, 1, (11/15 : ℚ), (3/4 : ℚ), -2, []⟩,
  ⟨5, 0, (3/4 : ℚ), (16/21 : ℚ), -1, []⟩,
  ⟨5, 1, (3/4 : ℚ), (16/21 : ℚ), -1, []⟩,
  ⟨5, 0, (16/21 : ℚ), (23/30 : ℚ), -1, []⟩,
  ⟨5, 1, (16/21 : ℚ), (23/30 : ℚ), -1, []⟩,
  ⟨5, 0, (23/30 : ℚ), (17/22 : ℚ), -1, []⟩,
  ⟨5, 1, (23/30 : ℚ), (17/22 : ℚ), -1, []⟩,
  ⟨5, 0, (17/22 : ℚ), (7/9 : ℚ), -1, []⟩,
  ⟨5, 1, (17/22 : ℚ), (7/9 : ℚ), -1, []⟩,
  ⟨5, 0, (7/9 : ℚ), (11/14 : ℚ), -2, []⟩,
  ⟨5, 1, (7/9 : ℚ), (11/14 : ℚ), -2, []⟩,
  ⟨5, 0, (11/14 : ℚ), (19/24 : ℚ), -2, []⟩,
  ⟨5, 1, (11/14 : ℚ), (19/24 : ℚ), -2, []⟩,
  ⟨5, 0, (19/24 : ℚ), (4/5 : ℚ), -2, []⟩,
  ⟨5, 1, (19/24 : ℚ), (4/5 : ℚ), -2, []⟩,
  ⟨5, 0, (4/5 : ℚ), (21/26 : ℚ), -1, []⟩,
  ⟨5, 1, (4/5 : ℚ), (21/26 : ℚ), -1, []⟩,
  ⟨5, 0, (21/26 : ℚ), (9/11 : ℚ), -1, []⟩,
  ⟨5, 1, (21/26 : ℚ), (9/11 : ℚ), -1, []⟩,
  ⟨5, 0, (9/11 : ℚ), (5/6 : ℚ), -1, []⟩,
  ⟨5, 1, (9/11 : ℚ), (5/6 : ℚ), -1, []⟩,
  ⟨5, 0, (5/6 : ℚ), (17/20 : ℚ), -2, []⟩,
  ⟨5, 1, (5/6 : ℚ), (17/20 : ℚ), -2, []⟩,
  ⟨5, 0, (17/20 : ℚ), (41/48 : ℚ), -2, []⟩,
  ⟨5, 1, (17/20 : ℚ), (41/48 : ℚ), -2, []⟩,
  ⟨5, 0, (41/48 : ℚ), (31/36 : ℚ), -2, []⟩,
  ⟨5, 1, (41/48 : ℚ), (31/36 : ℚ), -2, []⟩,
  ⟨5, 0, (31/36 : ℚ), (19/22 : ℚ), -3, []⟩,
  ⟨5, 1, (31/36 : ℚ), (19/22 : ℚ), -3, []⟩,
  ⟨5, 0, (19/22 : ℚ), (13/15 : ℚ), -3, []⟩,
  ⟨5, 1, (19/22 : ℚ), (13/15 : ℚ), -3, []⟩,
  ⟨5, 0, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨5, 1, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨5, 0, (7/8 : ℚ), (23/26 : ℚ), -1, []⟩,
  ⟨5, 1, (7/8 : ℚ), (23/26 : ℚ), -1, []⟩,
  ⟨5, 0, (23/26 : ℚ), (8/9 : ℚ), -1, []⟩,
  ⟨5, 1, (23/26 : ℚ), (8/9 : ℚ), -1, []⟩,
  ⟨5, 0, (8/9 : ℚ), (9/10 : ℚ), 0, []⟩,
  ⟨5, 1, (8/9 : ℚ), (9/10 : ℚ), 0, []⟩]

theorem dcells4_c0 : ((dcells4.drop (4 * 0)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c1 : ((dcells4.drop (4 * 1)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c2 : ((dcells4.drop (4 * 2)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c3 : ((dcells4.drop (4 * 3)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c4 : ((dcells4.drop (4 * 4)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c5 : ((dcells4.drop (4 * 5)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c6 : ((dcells4.drop (4 * 6)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c7 : ((dcells4.drop (4 * 7)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c8 : ((dcells4.drop (4 * 8)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c9 : ((dcells4.drop (4 * 9)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c10 : ((dcells4.drop (4 * 10)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c11 : ((dcells4.drop (4 * 11)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c12 : ((dcells4.drop (4 * 12)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c13 : ((dcells4.drop (4 * 13)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c14 : ((dcells4.drop (4 * 14)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c15 : ((dcells4.drop (4 * 15)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c16 : ((dcells4.drop (4 * 16)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c17 : ((dcells4.drop (4 * 17)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c18 : ((dcells4.drop (4 * 18)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c19 : ((dcells4.drop (4 * 19)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c20 : ((dcells4.drop (4 * 20)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c21 : ((dcells4.drop (4 * 21)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c22 : ((dcells4.drop (4 * 22)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c23 : ((dcells4.drop (4 * 23)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_c24 : ((dcells4.drop (4 * 24)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells4_ok : dcells4.all DCell.ok = true :=
  all_chunks _ 4 25 dcells4 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells4_c0, dcells4_c1, dcells4_c2, dcells4_c3, dcells4_c4, dcells4_c5, dcells4_c6, dcells4_c7, dcells4_c8, dcells4_c9, dcells4_c10, dcells4_c11, dcells4_c12, dcells4_c13, dcells4_c14, dcells4_c15, dcells4_c16, dcells4_c17, dcells4_c18, dcells4_c19, dcells4_c20, dcells4_c21, dcells4_c22, dcells4_c23, dcells4_c24])

end Zeta2L2Chi3.Arith
