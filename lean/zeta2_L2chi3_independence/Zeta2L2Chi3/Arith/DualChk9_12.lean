import Zeta2L2Chi3.Arith.DualData9

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells9_c96 : ((dcells9.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c97 : ((dcells9.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c98 : ((dcells9.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells9_c99 : ((dcells9.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
