import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells3 : List DCell := [
  ⟨5, 0, (1/8 : ℚ), (2/15 : ℚ), 0, []⟩,
  ⟨5, 1, (1/8 : ℚ), (2/15 : ℚ), 0, []⟩,
  ⟨5, 0, (2/15 : ℚ), (3/22 : ℚ), -1, []⟩,
  ⟨5, 1, (2/15 : ℚ), (3/22 : ℚ), -1, []⟩,
  ⟨5, 0, (3/22 : ℚ), (3/20 : ℚ), -1, []⟩,
  ⟨5, 1, (3/22 : ℚ), (3/20 : ℚ), -1, []⟩,
  ⟨5, 0, (3/20 : ℚ), (1/6 : ℚ), -1, []⟩,
  ⟨5, 1, (3/20 : ℚ), (1/6 : ℚ), -1, []⟩,
  ⟨5, 0, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 1, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 0, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 1, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 0, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 1, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 0, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 1, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 0, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 1, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 0, (1/5 : ℚ), (5/24 : ℚ), -4, []⟩,
  ⟨5, 1, (1/5 : ℚ), (5/24 : ℚ), -4, []⟩,
  ⟨5, 0, (5/24 : ℚ), (3/14 : ℚ), -3, []⟩,
  ⟨5, 1, (5/24 : ℚ), (3/14 : ℚ), -3, []⟩,
  ⟨5, 0, (3/14 : ℚ), (2/9 : ℚ), -3, []⟩,
  ⟨5, 1, (3/14 : ℚ), (2/9 : ℚ), -3, []⟩,
  ⟨5, 0, (2/9 : ℚ), (5/22 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 1, (2/9 : ℚ), (5/22 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 0, (5/22 : ℚ), (11/48 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 1, (5/22 : ℚ), (11/48 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 0, (11/48 : ℚ), (7/30 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 1, (11/48 : ℚ), (7/30 : ℚ), -2, [5, 7, 10]⟩,
  ⟨5, 0, (7/30 : ℚ), (1/4 : ℚ), -2, [2, 5, 7]⟩,
  ⟨5, 1, (7/30 : ℚ), (1/4 : ℚ), -2, [2, 5, 7]⟩,
  ⟨5, 0, (1/4 : ℚ), (11/42 : ℚ), -1, []⟩,
  ⟨5, 1, (1/4 : ℚ), (11/42 : ℚ), -1, []⟩,
  ⟨5, 0, (11/42 : ℚ), (4/15 : ℚ), -1, []⟩,
  ⟨5, 1, (11/42 : ℚ), (4/15 : ℚ), -1, []⟩,
  ⟨5, 0, (4/15 : ℚ), (7/26 : ℚ), 0, []⟩,
  ⟨5, 1, (4/15 : ℚ), (7/26 : ℚ), 0, []⟩,
  ⟨5, 0, (7/26 : ℚ), (3/11 : ℚ), 0, []⟩,
  ⟨5, 1, (7/26 : ℚ), (3/11 : ℚ), 0, []⟩,
  ⟨5, 0, (3/11 : ℚ), (5/18 : ℚ), 0, []⟩,
  ⟨5, 1, (3/11 : ℚ), (5/18 : ℚ), 0, []⟩,
  ⟨5, 0, (5/18 : ℚ), (7/24 : ℚ), -1, []⟩,
  ⟨5, 1, (5/18 : ℚ), (7/24 : ℚ), -1, []⟩,
  ⟨5, 0, (7/24 : ℚ), (3/10 : ℚ), -1, []⟩,
  ⟨5, 1, (7/24 : ℚ), (3/10 : ℚ), -1, []⟩,
  ⟨5, 0, (3/10 : ℚ), (7/22 : ℚ), -1, []⟩,
  ⟨5, 1, (3/10 : ℚ), (7/22 : ℚ), -1, []⟩,
  ⟨5, 0, (7/22 : ℚ), (1/3 : ℚ), -1, []⟩,
  ⟨5, 1, (7/22 : ℚ), (1/3 : ℚ), -1, []⟩,
  ⟨5, 0, (1/3 : ℚ), (9/26 : ℚ), -2, []⟩,
  ⟨5, 1, (1/3 : ℚ), (9/26 : ℚ), -2, []⟩,
  ⟨5, 0, (9/26 : ℚ), (7/20 : ℚ), -2, []⟩,
  ⟨5, 1, (9/26 : ℚ), (7/20 : ℚ), -2, []⟩,
  ⟨5, 0, (7/20 : ℚ), (17/48 : ℚ), -2, []⟩,
  ⟨5, 1, (7/20 : ℚ), (17/48 : ℚ), -2, []⟩,
  ⟨5, 0, (17/48 : ℚ), (5/14 : ℚ), -2, []⟩,
  ⟨5, 1, (17/48 : ℚ), (5/14 : ℚ), -2, []⟩,
  ⟨5, 0, (5/14 : ℚ), (13/36 : ℚ), -2, []⟩,
  ⟨5, 1, (5/14 : ℚ), (13/36 : ℚ), -2, []⟩,
  ⟨5, 0, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 1, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 0, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 1, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 0, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 1, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 0, (3/8 : ℚ), (7/18 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 1, (3/8 : ℚ), (7/18 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 0, (7/18 : ℚ), (2/5 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 1, (7/18 : ℚ), (2/5 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 0, (2/5 : ℚ), (17/42 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 1, (2/5 : ℚ), (17/42 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 0, (17/42 : ℚ), (9/22 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 1, (17/42 : ℚ), (9/22 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 0, (9/22 : ℚ), (5/12 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 1, (9/22 : ℚ), (5/12 : ℚ), -2, [4, 7, 10]⟩,
  ⟨5, 0, (5/12 : ℚ), (11/26 : ℚ), -2, [4, 9, 10]⟩,
  ⟨5, 1, (5/12 : ℚ), (11/26 : ℚ), -2, [4, 9, 10]⟩,
  ⟨5, 0, (11/26 : ℚ), (13/30 : ℚ), -2, [3, 4, 9]⟩,
  ⟨5, 1, (11/26 : ℚ), (13/30 : ℚ), -2, [3, 4, 9]⟩,
  ⟨5, 0, (13/30 : ℚ), (4/9 : ℚ), -2, [3, 4, 9]⟩,
  ⟨5, 1, (13/30 : ℚ), (4/9 : ℚ), -2, [3, 4, 9]⟩,
  ⟨5, 0, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 1, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 0, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 1, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 0, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 1, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 0, (11/24 : ℚ), (7/15 : ℚ), -1, []⟩,
  ⟨5, 1, (11/24 : ℚ), (7/15 : ℚ), -1, []⟩,
  ⟨5, 0, (7/15 : ℚ), (10/21 : ℚ), -1, []⟩,
  ⟨5, 1, (7/15 : ℚ), (10/21 : ℚ), -1, []⟩,
  ⟨5, 0, (10/21 : ℚ), (23/48 : ℚ), -1, []⟩,
  ⟨5, 1, (10/21 : ℚ), (23/48 : ℚ), -1, []⟩,
  ⟨5, 0, (23/48 : ℚ), (1/2 : ℚ), -1, []⟩,
  ⟨5, 1, (23/48 : ℚ), (1/2 : ℚ), -1, []⟩,
  ⟨5, 0, (1/2 : ℚ), (19/36 : ℚ), -1, []⟩,
  ⟨5, 1, (1/2 : ℚ), (19/36 : ℚ), -1, []⟩,
  ⟨5, 0, (19/36 : ℚ), (8/15 : ℚ), -2, []⟩,
  ⟨5, 1, (19/36 : ℚ), (8/15 : ℚ), -2, []⟩]

theorem dcells3_c0 : ((dcells3.drop (4 * 0)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c1 : ((dcells3.drop (4 * 1)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c2 : ((dcells3.drop (4 * 2)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c3 : ((dcells3.drop (4 * 3)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c4 : ((dcells3.drop (4 * 4)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c5 : ((dcells3.drop (4 * 5)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c6 : ((dcells3.drop (4 * 6)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c7 : ((dcells3.drop (4 * 7)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c8 : ((dcells3.drop (4 * 8)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c9 : ((dcells3.drop (4 * 9)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c10 : ((dcells3.drop (4 * 10)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c11 : ((dcells3.drop (4 * 11)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c12 : ((dcells3.drop (4 * 12)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c13 : ((dcells3.drop (4 * 13)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c14 : ((dcells3.drop (4 * 14)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c15 : ((dcells3.drop (4 * 15)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c16 : ((dcells3.drop (4 * 16)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c17 : ((dcells3.drop (4 * 17)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c18 : ((dcells3.drop (4 * 18)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c19 : ((dcells3.drop (4 * 19)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c20 : ((dcells3.drop (4 * 20)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c21 : ((dcells3.drop (4 * 21)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c22 : ((dcells3.drop (4 * 22)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c23 : ((dcells3.drop (4 * 23)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_c24 : ((dcells3.drop (4 * 24)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells3_ok : dcells3.all DCell.ok = true :=
  all_chunks _ 4 25 dcells3 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells3_c0, dcells3_c1, dcells3_c2, dcells3_c3, dcells3_c4, dcells3_c5, dcells3_c6, dcells3_c7, dcells3_c8, dcells3_c9, dcells3_c10, dcells3_c11, dcells3_c12, dcells3_c13, dcells3_c14, dcells3_c15, dcells3_c16, dcells3_c17, dcells3_c18, dcells3_c19, dcells3_c20, dcells3_c21, dcells3_c22, dcells3_c23, dcells3_c24])

end Zeta2L2Chi3.Arith
