import Zeta2L2Chi3.Arith.DualData11

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

theorem dcells11_c56 : ((dcells11.drop (1 * 56)).take 1).all DCell.ok = true := by decide +kernel

theorem dcells11_c57 : ((dcells11.drop (1 * 57)).take 1).all DCell.ok = true := by decide +kernel

end Zeta2L2Chi3.Arith
