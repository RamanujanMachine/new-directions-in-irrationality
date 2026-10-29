import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells5 : List DCell := [
  ⟨5, 0, (9/10 : ℚ), (19/21 : ℚ), 0, []⟩,
  ⟨5, 1, (9/10 : ℚ), (19/21 : ℚ), 0, []⟩,
  ⟨5, 0, (19/21 : ℚ), (10/11 : ℚ), 0, []⟩,
  ⟨5, 1, (19/21 : ℚ), (10/11 : ℚ), 0, []⟩,
  ⟨5, 0, (10/11 : ℚ), (11/12 : ℚ), 0, []⟩,
  ⟨5, 1, (10/11 : ℚ), (11/12 : ℚ), 0, []⟩,
  ⟨5, 0, (11/12 : ℚ), (13/14 : ℚ), -1, []⟩,
  ⟨5, 1, (11/12 : ℚ), (13/14 : ℚ), -1, []⟩,
  ⟨5, 0, (13/14 : ℚ), (14/15 : ℚ), -1, []⟩,
  ⟨5, 1, (13/14 : ℚ), (14/15 : ℚ), -1, []⟩,
  ⟨5, 0, (14/15 : ℚ), (17/18 : ℚ), -2, []⟩,
  ⟨5, 1, (14/15 : ℚ), (17/18 : ℚ), -2, []⟩,
  ⟨5, 0, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 1, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 0, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 1, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 0, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨5, 1, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨5, 0, (23/24 : ℚ), (25/26 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 1, (23/24 : ℚ), (25/26 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 0, (25/26 : ℚ), (29/30 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 1, (25/26 : ℚ), (29/30 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 0, (29/30 : ℚ), (41/42 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 1, (29/30 : ℚ), (41/42 : ℚ), -2, [0, 1, 4, 8]⟩,
  ⟨5, 0, (41/42 : ℚ), (47/48 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨5, 1, (41/42 : ℚ), (47/48 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨5, 0, (47/48 : ℚ), (1 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨5, 1, (47/48 : ℚ), (1 : ℚ), -2, [0, 1, 3, 4]⟩,
  ⟨1, 2, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 2, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 2, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 2, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 2, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 2, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 2, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 2, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 2, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 2, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 2, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 2, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 2, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 2, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨5, 2, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 2, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 2, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 2, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 2, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 2, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 2, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 2, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 2, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 2, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 2, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 2, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 2, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 2, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 2, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 2, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 2, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 2, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 2, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 2, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 2, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨1, 3, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 3, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 3, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 3, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 3, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 3, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 3, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 3, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 3, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 3, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 3, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 3, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 3, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 3, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨5, 3, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 3, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 3, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 3, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 3, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 3, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 3, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 3, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 3, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 3, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 3, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 3, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 3, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 3, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 3, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 3, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 3, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 3, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 3, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 3, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 3, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨1, 4, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 4, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩]

theorem dcells5_c0 : ((dcells5.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c1 : ((dcells5.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c2 : ((dcells5.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c3 : ((dcells5.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c4 : ((dcells5.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c5 : ((dcells5.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c6 : ((dcells5.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c7 : ((dcells5.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c8 : ((dcells5.drop (1 * 8)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c9 : ((dcells5.drop (1 * 9)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c10 : ((dcells5.drop (1 * 10)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c11 : ((dcells5.drop (1 * 11)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c12 : ((dcells5.drop (1 * 12)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c13 : ((dcells5.drop (1 * 13)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c14 : ((dcells5.drop (1 * 14)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c15 : ((dcells5.drop (1 * 15)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c16 : ((dcells5.drop (1 * 16)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c17 : ((dcells5.drop (1 * 17)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c18 : ((dcells5.drop (1 * 18)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c19 : ((dcells5.drop (1 * 19)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c20 : ((dcells5.drop (1 * 20)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c21 : ((dcells5.drop (1 * 21)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c22 : ((dcells5.drop (1 * 22)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c23 : ((dcells5.drop (1 * 23)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c24 : ((dcells5.drop (1 * 24)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c25 : ((dcells5.drop (1 * 25)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c26 : ((dcells5.drop (1 * 26)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c27 : ((dcells5.drop (1 * 27)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c28 : ((dcells5.drop (1 * 28)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c29 : ((dcells5.drop (1 * 29)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c30 : ((dcells5.drop (1 * 30)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c31 : ((dcells5.drop (1 * 31)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c32 : ((dcells5.drop (1 * 32)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c33 : ((dcells5.drop (1 * 33)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c34 : ((dcells5.drop (1 * 34)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c35 : ((dcells5.drop (1 * 35)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c36 : ((dcells5.drop (1 * 36)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c37 : ((dcells5.drop (1 * 37)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c38 : ((dcells5.drop (1 * 38)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c39 : ((dcells5.drop (1 * 39)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c40 : ((dcells5.drop (1 * 40)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c41 : ((dcells5.drop (1 * 41)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c42 : ((dcells5.drop (1 * 42)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c43 : ((dcells5.drop (1 * 43)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c44 : ((dcells5.drop (1 * 44)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c45 : ((dcells5.drop (1 * 45)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c46 : ((dcells5.drop (1 * 46)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c47 : ((dcells5.drop (1 * 47)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c48 : ((dcells5.drop (1 * 48)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c49 : ((dcells5.drop (1 * 49)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c50 : ((dcells5.drop (1 * 50)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c51 : ((dcells5.drop (1 * 51)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c52 : ((dcells5.drop (1 * 52)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c53 : ((dcells5.drop (1 * 53)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c54 : ((dcells5.drop (1 * 54)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c55 : ((dcells5.drop (1 * 55)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c56 : ((dcells5.drop (1 * 56)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c57 : ((dcells5.drop (1 * 57)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c58 : ((dcells5.drop (1 * 58)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c59 : ((dcells5.drop (1 * 59)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c60 : ((dcells5.drop (1 * 60)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c61 : ((dcells5.drop (1 * 61)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c62 : ((dcells5.drop (1 * 62)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c63 : ((dcells5.drop (1 * 63)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c64 : ((dcells5.drop (1 * 64)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c65 : ((dcells5.drop (1 * 65)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c66 : ((dcells5.drop (1 * 66)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c67 : ((dcells5.drop (1 * 67)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c68 : ((dcells5.drop (1 * 68)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c69 : ((dcells5.drop (1 * 69)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c70 : ((dcells5.drop (1 * 70)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c71 : ((dcells5.drop (1 * 71)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c72 : ((dcells5.drop (1 * 72)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c73 : ((dcells5.drop (1 * 73)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c74 : ((dcells5.drop (1 * 74)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c75 : ((dcells5.drop (1 * 75)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c76 : ((dcells5.drop (1 * 76)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c77 : ((dcells5.drop (1 * 77)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c78 : ((dcells5.drop (1 * 78)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c79 : ((dcells5.drop (1 * 79)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c80 : ((dcells5.drop (1 * 80)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c81 : ((dcells5.drop (1 * 81)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c82 : ((dcells5.drop (1 * 82)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c83 : ((dcells5.drop (1 * 83)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c84 : ((dcells5.drop (1 * 84)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c85 : ((dcells5.drop (1 * 85)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c86 : ((dcells5.drop (1 * 86)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c87 : ((dcells5.drop (1 * 87)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c88 : ((dcells5.drop (1 * 88)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c89 : ((dcells5.drop (1 * 89)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c90 : ((dcells5.drop (1 * 90)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c91 : ((dcells5.drop (1 * 91)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c92 : ((dcells5.drop (1 * 92)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c93 : ((dcells5.drop (1 * 93)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c94 : ((dcells5.drop (1 * 94)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c95 : ((dcells5.drop (1 * 95)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c96 : ((dcells5.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c97 : ((dcells5.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c98 : ((dcells5.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_c99 : ((dcells5.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells5_ok : dcells5.all DCell.ok = true :=
  all_chunks _ 1 100 dcells5 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells5_c0, dcells5_c1, dcells5_c2, dcells5_c3, dcells5_c4, dcells5_c5, dcells5_c6, dcells5_c7, dcells5_c8, dcells5_c9, dcells5_c10, dcells5_c11, dcells5_c12, dcells5_c13, dcells5_c14, dcells5_c15, dcells5_c16, dcells5_c17, dcells5_c18, dcells5_c19, dcells5_c20, dcells5_c21, dcells5_c22, dcells5_c23, dcells5_c24, dcells5_c25, dcells5_c26, dcells5_c27, dcells5_c28, dcells5_c29, dcells5_c30, dcells5_c31, dcells5_c32, dcells5_c33, dcells5_c34, dcells5_c35, dcells5_c36, dcells5_c37, dcells5_c38, dcells5_c39, dcells5_c40, dcells5_c41, dcells5_c42, dcells5_c43, dcells5_c44, dcells5_c45, dcells5_c46, dcells5_c47, dcells5_c48, dcells5_c49, dcells5_c50, dcells5_c51, dcells5_c52, dcells5_c53, dcells5_c54, dcells5_c55, dcells5_c56, dcells5_c57, dcells5_c58, dcells5_c59, dcells5_c60, dcells5_c61, dcells5_c62, dcells5_c63, dcells5_c64, dcells5_c65, dcells5_c66, dcells5_c67, dcells5_c68, dcells5_c69, dcells5_c70, dcells5_c71, dcells5_c72, dcells5_c73, dcells5_c74, dcells5_c75, dcells5_c76, dcells5_c77, dcells5_c78, dcells5_c79, dcells5_c80, dcells5_c81, dcells5_c82, dcells5_c83, dcells5_c84, dcells5_c85, dcells5_c86, dcells5_c87, dcells5_c88, dcells5_c89, dcells5_c90, dcells5_c91, dcells5_c92, dcells5_c93, dcells5_c94, dcells5_c95, dcells5_c96, dcells5_c97, dcells5_c98, dcells5_c99])

end Zeta2L2Chi3.Arith
