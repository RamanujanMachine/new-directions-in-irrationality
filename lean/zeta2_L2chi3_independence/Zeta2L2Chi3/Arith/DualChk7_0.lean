import Zeta2L2Chi3.Arith.DualData7

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells7_c0 : ((dcells7.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c1 : ((dcells7.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c2 : ((dcells7.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c3 : ((dcells7.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c4 : ((dcells7.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c5 : ((dcells7.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c6 : ((dcells7.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c7 : ((dcells7.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
