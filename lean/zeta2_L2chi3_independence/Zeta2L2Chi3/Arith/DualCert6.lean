import Zeta2L2Chi3.Arith.ChamberData

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

def dcells6 : List DCell := [
  ⟨1, 4, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 4, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 4, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 4, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 4, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 4, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 4, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 4, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 4, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 4, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 4, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 4, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨5, 4, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 4, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 4, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 4, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 4, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 4, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 4, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 4, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 4, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 4, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 4, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 4, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 4, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 4, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 4, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 4, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 4, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 4, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 4, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 4, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 4, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨1, 5, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 5, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 5, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 5, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 5, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 5, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 5, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 5, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 5, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 5, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 5, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 5, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 5, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 5, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨5, 5, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 5, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 5, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 5, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 5, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 5, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 5, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 5, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 5, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 5, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 5, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 5, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 5, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 5, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 5, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 5, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 5, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 5, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩,
  ⟨5, 5, (17/18 : ℚ), (19/20 : ℚ), -3, []⟩,
  ⟨5, 5, (19/20 : ℚ), (21/22 : ℚ), -3, []⟩,
  ⟨5, 5, (21/22 : ℚ), (23/24 : ℚ), -3, []⟩,
  ⟨1, 6, (1/12 : ℚ), (1/11 : ℚ), -2, []⟩,
  ⟨1, 6, (1/11 : ℚ), (2/21 : ℚ), -2, []⟩,
  ⟨1, 6, (2/21 : ℚ), (1/10 : ℚ), -2, []⟩,
  ⟨1, 6, (1/10 : ℚ), (1/9 : ℚ), -2, []⟩,
  ⟨1, 6, (7/18 : ℚ), (19/48 : ℚ), -2, []⟩,
  ⟨1, 6, (19/48 : ℚ), (2/5 : ℚ), -2, []⟩,
  ⟨1, 6, (13/18 : ℚ), (8/11 : ℚ), -3, []⟩,
  ⟨1, 6, (8/11 : ℚ), (19/26 : ℚ), -3, []⟩,
  ⟨1, 6, (19/26 : ℚ), (11/15 : ℚ), -3, []⟩,
  ⟨1, 6, (13/15 : ℚ), (7/8 : ℚ), -2, []⟩,
  ⟨1, 6, (8/9 : ℚ), (43/48 : ℚ), -2, []⟩,
  ⟨1, 6, (43/48 : ℚ), (9/10 : ℚ), -2, []⟩,
  ⟨1, 6, (9/10 : ℚ), (10/11 : ℚ), -2, []⟩,
  ⟨1, 6, (10/11 : ℚ), (11/12 : ℚ), -2, []⟩,
  ⟨5, 6, (1/6 : ℚ), (2/11 : ℚ), -3, []⟩,
  ⟨5, 6, (2/11 : ℚ), (4/21 : ℚ), -3, []⟩,
  ⟨5, 6, (4/21 : ℚ), (5/26 : ℚ), -3, []⟩,
  ⟨5, 6, (5/26 : ℚ), (7/36 : ℚ), -3, []⟩,
  ⟨5, 6, (7/36 : ℚ), (1/5 : ℚ), -4, []⟩,
  ⟨5, 6, (13/36 : ℚ), (4/11 : ℚ), -2, []⟩,
  ⟨5, 6, (4/11 : ℚ), (11/30 : ℚ), -2, []⟩,
  ⟨5, 6, (11/30 : ℚ), (3/8 : ℚ), -2, []⟩,
  ⟨5, 6, (4/9 : ℚ), (9/20 : ℚ), -2, []⟩,
  ⟨5, 6, (9/20 : ℚ), (5/11 : ℚ), -2, []⟩,
  ⟨5, 6, (5/11 : ℚ), (11/24 : ℚ), -2, []⟩,
  ⟨5, 6, (8/15 : ℚ), (13/24 : ℚ), -2, []⟩,
  ⟨5, 6, (13/24 : ℚ), (6/11 : ℚ), -2, []⟩,
  ⟨5, 6, (6/11 : ℚ), (23/42 : ℚ), -2, []⟩,
  ⟨5, 6, (23/42 : ℚ), (11/20 : ℚ), -2, []⟩,
  ⟨5, 6, (11/20 : ℚ), (5/9 : ℚ), -2, []⟩,
  ⟨5, 6, (25/36 : ℚ), (7/10 : ℚ), -2, []⟩,
  ⟨5, 6, (7/10 : ℚ), (17/24 : ℚ), -2, []⟩]

theorem dcells6_c0 : ((dcells6.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c1 : ((dcells6.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c2 : ((dcells6.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c3 : ((dcells6.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c4 : ((dcells6.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c5 : ((dcells6.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c6 : ((dcells6.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c7 : ((dcells6.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c8 : ((dcells6.drop (1 * 8)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c9 : ((dcells6.drop (1 * 9)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c10 : ((dcells6.drop (1 * 10)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c11 : ((dcells6.drop (1 * 11)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c12 : ((dcells6.drop (1 * 12)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c13 : ((dcells6.drop (1 * 13)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c14 : ((dcells6.drop (1 * 14)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c15 : ((dcells6.drop (1 * 15)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c16 : ((dcells6.drop (1 * 16)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c17 : ((dcells6.drop (1 * 17)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c18 : ((dcells6.drop (1 * 18)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c19 : ((dcells6.drop (1 * 19)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c20 : ((dcells6.drop (1 * 20)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c21 : ((dcells6.drop (1 * 21)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c22 : ((dcells6.drop (1 * 22)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c23 : ((dcells6.drop (1 * 23)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c24 : ((dcells6.drop (1 * 24)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c25 : ((dcells6.drop (1 * 25)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c26 : ((dcells6.drop (1 * 26)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c27 : ((dcells6.drop (1 * 27)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c28 : ((dcells6.drop (1 * 28)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c29 : ((dcells6.drop (1 * 29)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c30 : ((dcells6.drop (1 * 30)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c31 : ((dcells6.drop (1 * 31)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c32 : ((dcells6.drop (1 * 32)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c33 : ((dcells6.drop (1 * 33)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c34 : ((dcells6.drop (1 * 34)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c35 : ((dcells6.drop (1 * 35)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c36 : ((dcells6.drop (1 * 36)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c37 : ((dcells6.drop (1 * 37)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c38 : ((dcells6.drop (1 * 38)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c39 : ((dcells6.drop (1 * 39)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c40 : ((dcells6.drop (1 * 40)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c41 : ((dcells6.drop (1 * 41)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c42 : ((dcells6.drop (1 * 42)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c43 : ((dcells6.drop (1 * 43)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c44 : ((dcells6.drop (1 * 44)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c45 : ((dcells6.drop (1 * 45)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c46 : ((dcells6.drop (1 * 46)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c47 : ((dcells6.drop (1 * 47)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c48 : ((dcells6.drop (1 * 48)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c49 : ((dcells6.drop (1 * 49)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c50 : ((dcells6.drop (1 * 50)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c51 : ((dcells6.drop (1 * 51)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c52 : ((dcells6.drop (1 * 52)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c53 : ((dcells6.drop (1 * 53)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c54 : ((dcells6.drop (1 * 54)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c55 : ((dcells6.drop (1 * 55)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c56 : ((dcells6.drop (1 * 56)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c57 : ((dcells6.drop (1 * 57)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c58 : ((dcells6.drop (1 * 58)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c59 : ((dcells6.drop (1 * 59)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c60 : ((dcells6.drop (1 * 60)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c61 : ((dcells6.drop (1 * 61)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c62 : ((dcells6.drop (1 * 62)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c63 : ((dcells6.drop (1 * 63)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c64 : ((dcells6.drop (1 * 64)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c65 : ((dcells6.drop (1 * 65)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c66 : ((dcells6.drop (1 * 66)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c67 : ((dcells6.drop (1 * 67)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c68 : ((dcells6.drop (1 * 68)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c69 : ((dcells6.drop (1 * 69)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c70 : ((dcells6.drop (1 * 70)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c71 : ((dcells6.drop (1 * 71)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c72 : ((dcells6.drop (1 * 72)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c73 : ((dcells6.drop (1 * 73)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c74 : ((dcells6.drop (1 * 74)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c75 : ((dcells6.drop (1 * 75)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c76 : ((dcells6.drop (1 * 76)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c77 : ((dcells6.drop (1 * 77)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c78 : ((dcells6.drop (1 * 78)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c79 : ((dcells6.drop (1 * 79)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c80 : ((dcells6.drop (1 * 80)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c81 : ((dcells6.drop (1 * 81)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c82 : ((dcells6.drop (1 * 82)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c83 : ((dcells6.drop (1 * 83)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c84 : ((dcells6.drop (1 * 84)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c85 : ((dcells6.drop (1 * 85)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c86 : ((dcells6.drop (1 * 86)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c87 : ((dcells6.drop (1 * 87)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c88 : ((dcells6.drop (1 * 88)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c89 : ((dcells6.drop (1 * 89)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c90 : ((dcells6.drop (1 * 90)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c91 : ((dcells6.drop (1 * 91)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c92 : ((dcells6.drop (1 * 92)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c93 : ((dcells6.drop (1 * 93)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c94 : ((dcells6.drop (1 * 94)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c95 : ((dcells6.drop (1 * 95)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c96 : ((dcells6.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c97 : ((dcells6.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c98 : ((dcells6.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_c99 : ((dcells6.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells6_ok : dcells6.all DCell.ok = true :=
  all_chunks _ 1 100 dcells6 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells6_c0, dcells6_c1, dcells6_c2, dcells6_c3, dcells6_c4, dcells6_c5, dcells6_c6, dcells6_c7, dcells6_c8, dcells6_c9, dcells6_c10, dcells6_c11, dcells6_c12, dcells6_c13, dcells6_c14, dcells6_c15, dcells6_c16, dcells6_c17, dcells6_c18, dcells6_c19, dcells6_c20, dcells6_c21, dcells6_c22, dcells6_c23, dcells6_c24, dcells6_c25, dcells6_c26, dcells6_c27, dcells6_c28, dcells6_c29, dcells6_c30, dcells6_c31, dcells6_c32, dcells6_c33, dcells6_c34, dcells6_c35, dcells6_c36, dcells6_c37, dcells6_c38, dcells6_c39, dcells6_c40, dcells6_c41, dcells6_c42, dcells6_c43, dcells6_c44, dcells6_c45, dcells6_c46, dcells6_c47, dcells6_c48, dcells6_c49, dcells6_c50, dcells6_c51, dcells6_c52, dcells6_c53, dcells6_c54, dcells6_c55, dcells6_c56, dcells6_c57, dcells6_c58, dcells6_c59, dcells6_c60, dcells6_c61, dcells6_c62, dcells6_c63, dcells6_c64, dcells6_c65, dcells6_c66, dcells6_c67, dcells6_c68, dcells6_c69, dcells6_c70, dcells6_c71, dcells6_c72, dcells6_c73, dcells6_c74, dcells6_c75, dcells6_c76, dcells6_c77, dcells6_c78, dcells6_c79, dcells6_c80, dcells6_c81, dcells6_c82, dcells6_c83, dcells6_c84, dcells6_c85, dcells6_c86, dcells6_c87, dcells6_c88, dcells6_c89, dcells6_c90, dcells6_c91, dcells6_c92, dcells6_c93, dcells6_c94, dcells6_c95, dcells6_c96, dcells6_c97, dcells6_c98, dcells6_c99])

end Zeta2L2Chi3.Arith
