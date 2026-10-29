import Zeta2L2Chi3.Arith.DualData8

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells8_c0 : ((dcells8.drop (1 * 0)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c1 : ((dcells8.drop (1 * 1)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c2 : ((dcells8.drop (1 * 2)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c3 : ((dcells8.drop (1 * 3)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c4 : ((dcells8.drop (1 * 4)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c5 : ((dcells8.drop (1 * 5)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c6 : ((dcells8.drop (1 * 6)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c7 : ((dcells8.drop (1 * 7)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
