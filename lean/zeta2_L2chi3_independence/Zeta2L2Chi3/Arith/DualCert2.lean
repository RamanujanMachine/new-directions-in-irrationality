import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells2 : List DCell := [
  ⟨1, 0, (37/48 : ℚ), (17/22 : ℚ), -3, []⟩,
  ⟨1, 1, (37/48 : ℚ), (17/22 : ℚ), -3, []⟩,
  ⟨1, 0, (17/22 : ℚ), (7/9 : ℚ), -3, []⟩,
  ⟨1, 1, (17/22 : ℚ), (7/9 : ℚ), -3, []⟩,
  ⟨1, 0, (7/9 : ℚ), (11/14 : ℚ), -2, [1, 2, 9]⟩,
  ⟨1, 1, (7/9 : ℚ), (11/14 : ℚ), -2, [1, 2, 9]⟩,
  ⟨1, 0, (11/14 : ℚ), (19/24 : ℚ), -2, [1, 2, 9]⟩,
  ⟨1, 1, (11/14 : ℚ), (19/24 : ℚ), -2, [1, 2, 9]⟩,
  ⟨1, 0, (19/24 : ℚ), (4/5 : ℚ), -1, []⟩,
  ⟨1, 1, (19/24 : ℚ), (4/5 : ℚ), -1, []⟩,
  ⟨1, 0, (4/5 : ℚ), (29/36 : ℚ), 0, []⟩,
  ⟨1, 1, (4/5 : ℚ), (29/36 : ℚ), 0, []⟩,
  ⟨1, 0, (29/36 : ℚ), (21/26 : ℚ), 0, []⟩,
  ⟨1, 1, (29/36 : ℚ), (21/26 : ℚ), 0, []⟩,
  ⟨1, 0, (21/26 : ℚ), (17/21 : ℚ), 0, []⟩,
  ⟨1, 1, (21/26 : ℚ), (17/21 : ℚ), 0, []⟩,
  ⟨1, 0, (17/21 : ℚ), (9/11 : ℚ), 0, []⟩,
  ⟨1, 1, (17/21 : ℚ), (9/11 : ℚ), 0, []⟩,
  ⟨1, 0, (9/11 : ℚ), (5/6 : ℚ), 0, []⟩,
  ⟨1, 1, (9/11 : ℚ), (5/6 : ℚ), 0, []⟩,
  ⟨1, 0, (5/6 : ℚ), (17/20 : ℚ), -2, []⟩,
  ⟨1, 1, (5/6 : ℚ), (17/20 : ℚ), -2, []⟩,
  ⟨1, 0, (17/20 : ℚ), (19/22 : ℚ), -2, []⟩,
  ⟨1, 1, (17/20 : ℚ), (19/22 : ℚ), -2, []⟩,
  ⟨1, 0, (19/22 : ℚ), (13/15 : ℚ), -2, []⟩,
  ⟨1, 1, (19/22 : ℚ), (13/15 : ℚ), -2, []⟩,
  ⟨1, 0, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 1, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 0, (7/8 : ℚ), (37/42 : ℚ), -2, [4, 5, 10]⟩,
  ⟨1, 1, (7/8 : ℚ), (37/42 : ℚ), -2, [4, 5, 10]⟩,
  ⟨1, 0, (37/42 : ℚ), (23/26 : ℚ), -2, [4, 5, 10]⟩,
  ⟨1, 1, (37/42 : ℚ), (23/26 : ℚ), -2, [4, 5, 10]⟩,
  ⟨1, 0, (23/26 : ℚ), (8/9 : ℚ), -2, [3, 4, 5]⟩,
  ⟨1, 1, (23/26 : ℚ), (8/9 : ℚ), -2, [3, 4, 5]⟩,
  ⟨1, 0, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 1, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 0, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 1, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 0, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 1, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 0, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨1, 1, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨1, 0, (11/12 : ℚ), (13/14 : ℚ), -2, [0, 1, 4, 6]⟩,
  ⟨1, 1, (11/12 : ℚ), (13/14 : ℚ), -2, [0, 1, 4, 6]⟩,
  ⟨1, 0, (13/14 : ℚ), (14/15 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (13/14 : ℚ), (14/15 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (14/15 : ℚ), (17/18 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (14/15 : ℚ), (17/18 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (17/18 : ℚ), (19/20 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (17/18 : ℚ), (19/20 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (19/20 : ℚ), (20/21 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (19/20 : ℚ), (20/21 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (20/21 : ℚ), (21/22 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (20/21 : ℚ), (21/22 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (21/22 : ℚ), (23/24 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (21/22 : ℚ), (23/24 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (23/24 : ℚ), (25/26 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 1, (23/24 : ℚ), (25/26 : ℚ), -2, [0, 1, 4, 10]⟩,
  ⟨1, 0, (25/26 : ℚ), (29/30 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 1, (25/26 : ℚ), (29/30 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 0, (29/30 : ℚ), (35/36 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 1, (29/30 : ℚ), (35/36 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 0, (35/36 : ℚ), (1 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 1, (35/36 : ℚ), (1 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨5, 0, (0 : ℚ), (1/36 : ℚ), 0, []⟩,
  ⟨5, 1, (0 : ℚ), (1/36 : ℚ), -2, []⟩,
  ⟨5, 0, (1/36 : ℚ), (1/30 : ℚ), -1, []⟩,
  ⟨5, 1, (1/36 : ℚ), (1/30 : ℚ), -3, []⟩,
  ⟨5, 0, (1/30 : ℚ), (1/26 : ℚ), -1, []⟩,
  ⟨5, 1, (1/30 : ℚ), (1/26 : ℚ), -3, []⟩,
  ⟨5, 0, (1/26 : ℚ), (1/24 : ℚ), -1, []⟩,
  ⟨5, 1, (1/26 : ℚ), (1/24 : ℚ), -3, []⟩,
  ⟨5, 0, (1/24 : ℚ), (1/22 : ℚ), -1, []⟩,
  ⟨5, 1, (1/24 : ℚ), (1/22 : ℚ), -3, []⟩,
  ⟨5, 0, (1/22 : ℚ), (1/21 : ℚ), -1, []⟩,
  ⟨5, 1, (1/22 : ℚ), (1/21 : ℚ), -3, []⟩,
  ⟨5, 0, (1/21 : ℚ), (1/20 : ℚ), -1, []⟩,
  ⟨5, 1, (1/21 : ℚ), (1/20 : ℚ), -3, []⟩,
  ⟨5, 0, (1/20 : ℚ), (1/18 : ℚ), -1, []⟩,
  ⟨5, 1, (1/20 : ℚ), (1/18 : ℚ), -3, []⟩,
  ⟨5, 0, (1/18 : ℚ), (1/15 : ℚ), -1, []⟩,
  ⟨5, 1, (1/18 : ℚ), (1/15 : ℚ), -3, []⟩,
  ⟨5, 0, (1/15 : ℚ), (1/14 : ℚ), 0, []⟩,
  ⟨5, 1, (1/15 : ℚ), (1/14 : ℚ), -2, []⟩,
  ⟨5, 0, (1/14 : ℚ), (1/12 : ℚ), 0, []⟩,
  ⟨5, 1, (1/14 : ℚ), (1/12 : ℚ), -2, []⟩,
  ⟨5, 0, (1/12 : ℚ), (1/11 : ℚ), 0, []⟩,
  ⟨5, 1, (1/12 : ℚ), (1/11 : ℚ), 0, []⟩,
  ⟨5, 0, (1/11 : ℚ), (1/10 : ℚ), 0, []⟩,
  ⟨5, 1, (1/11 : ℚ), (1/10 : ℚ), 0, []⟩,
  ⟨5, 0, (1/10 : ℚ), (5/48 : ℚ), 0, []⟩,
  ⟨5, 1, (1/10 : ℚ), (5/48 : ℚ), 0, []⟩,
  ⟨5, 0, (5/48 : ℚ), (1/9 : ℚ), 0, []⟩,
  ⟨5, 1, (5/48 : ℚ), (1/9 : ℚ), 0, []⟩,
  ⟨5, 0, (1/9 : ℚ), (3/26 : ℚ), -2, []⟩,
  ⟨5, 1, (1/9 : ℚ), (3/26 : ℚ), -2, []⟩,
  ⟨5, 0, (3/26 : ℚ), (5/42 : ℚ), -2, []⟩,
  ⟨5, 1, (3/26 : ℚ), (5/42 : ℚ), -2, []⟩,
  ⟨5, 0, (5/42 : ℚ), (1/8 : ℚ), -2, []⟩,
  ⟨5, 1, (5/42 : ℚ), (1/8 : ℚ), -2, []⟩]

theorem dcells2_c0 : ((dcells2.drop (4 * 0)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c1 : ((dcells2.drop (4 * 1)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c2 : ((dcells2.drop (4 * 2)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c3 : ((dcells2.drop (4 * 3)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c4 : ((dcells2.drop (4 * 4)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c5 : ((dcells2.drop (4 * 5)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c6 : ((dcells2.drop (4 * 6)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c7 : ((dcells2.drop (4 * 7)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c8 : ((dcells2.drop (4 * 8)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c9 : ((dcells2.drop (4 * 9)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c10 : ((dcells2.drop (4 * 10)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c11 : ((dcells2.drop (4 * 11)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c12 : ((dcells2.drop (4 * 12)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c13 : ((dcells2.drop (4 * 13)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c14 : ((dcells2.drop (4 * 14)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c15 : ((dcells2.drop (4 * 15)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c16 : ((dcells2.drop (4 * 16)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c17 : ((dcells2.drop (4 * 17)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c18 : ((dcells2.drop (4 * 18)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c19 : ((dcells2.drop (4 * 19)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c20 : ((dcells2.drop (4 * 20)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c21 : ((dcells2.drop (4 * 21)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c22 : ((dcells2.drop (4 * 22)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c23 : ((dcells2.drop (4 * 23)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_c24 : ((dcells2.drop (4 * 24)).take 4).all DCell.ok = true := by decide +kernel

theorem dcells2_ok : dcells2.all DCell.ok = true :=
  all_chunks _ 4 25 dcells2 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells2_c0, dcells2_c1, dcells2_c2, dcells2_c3, dcells2_c4, dcells2_c5, dcells2_c6, dcells2_c7, dcells2_c8, dcells2_c9, dcells2_c10, dcells2_c11, dcells2_c12, dcells2_c13, dcells2_c14, dcells2_c15, dcells2_c16, dcells2_c17, dcells2_c18, dcells2_c19, dcells2_c20, dcells2_c21, dcells2_c22, dcells2_c23, dcells2_c24])

end Zeta2L2Chi3.Arith
