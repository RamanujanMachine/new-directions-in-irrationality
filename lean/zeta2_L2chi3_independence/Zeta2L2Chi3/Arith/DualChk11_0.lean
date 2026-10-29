import Zeta2L2Chi3.Arith.DualData11

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells11_c0 : ((dcells11.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c1 : ((dcells11.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c2 : ((dcells11.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c3 : ((dcells11.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c4 : ((dcells11.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c5 : ((dcells11.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c6 : ((dcells11.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c7 : ((dcells11.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
