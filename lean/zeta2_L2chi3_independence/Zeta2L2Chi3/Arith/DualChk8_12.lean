import Zeta2L2Chi3.Arith.DualData8

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells8_c96 : ((dcells8.drop (1 * 96)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c97 : ((dcells8.drop (1 * 97)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c98 : ((dcells8.drop (1 * 98)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells8_c99 : ((dcells8.drop (1 * 99)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
