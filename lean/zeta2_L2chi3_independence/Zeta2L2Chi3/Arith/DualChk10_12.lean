import Zeta2L2Chi3.Arith.DualData10

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells10_c96 : ((dcells10.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c97 : ((dcells10.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c98 : ((dcells10.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c99 : ((dcells10.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
