import Zeta2L2Chi3.Arith.DualData9

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells9_c0 : ((dcells9.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c1 : ((dcells9.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c2 : ((dcells9.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c3 : ((dcells9.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c4 : ((dcells9.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c5 : ((dcells9.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c6 : ((dcells9.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c7 : ((dcells9.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
