import Zeta2L2Chi3.Arith.DualData10

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells10_c0 : ((dcells10.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c1 : ((dcells10.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c2 : ((dcells10.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c3 : ((dcells10.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c4 : ((dcells10.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c5 : ((dcells10.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c6 : ((dcells10.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells10_c7 : ((dcells10.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
