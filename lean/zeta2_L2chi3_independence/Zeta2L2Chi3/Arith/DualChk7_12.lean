import Zeta2L2Chi3.Arith.DualData7

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells7_c96 : ((dcells7.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c97 : ((dcells7.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c98 : ((dcells7.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells7_c99 : ((dcells7.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
