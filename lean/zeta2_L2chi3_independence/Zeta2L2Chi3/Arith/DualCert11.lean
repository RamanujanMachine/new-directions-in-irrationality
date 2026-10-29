import Zeta2L2Chi3.Arith.DualChk11_0
import Zeta2L2Chi3.Arith.DualChk11_1
import Zeta2L2Chi3.Arith.DualChk11_2
import Zeta2L2Chi3.Arith.DualChk11_3
import Zeta2L2Chi3.Arith.DualChk11_4
import Zeta2L2Chi3.Arith.DualChk11_5
import Zeta2L2Chi3.Arith.DualChk11_6
import Zeta2L2Chi3.Arith.DualChk11_7

namespace Zeta2L2Chi3.Arith

theorem dcells11_ok : dcells11.all DCell.ok = true :=
  all_chunks _ 1 58 dcells11 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells11_c0, dcells11_c1, dcells11_c2, dcells11_c3, dcells11_c4, dcells11_c5, dcells11_c6, dcells11_c7, dcells11_c8, dcells11_c9, dcells11_c10, dcells11_c11, dcells11_c12, dcells11_c13, dcells11_c14, dcells11_c15, dcells11_c16, dcells11_c17, dcells11_c18, dcells11_c19, dcells11_c20, dcells11_c21, dcells11_c22, dcells11_c23, dcells11_c24, dcells11_c25, dcells11_c26, dcells11_c27, dcells11_c28, dcells11_c29, dcells11_c30, dcells11_c31, dcells11_c32, dcells11_c33, dcells11_c34, dcells11_c35, dcells11_c36, dcells11_c37, dcells11_c38, dcells11_c39, dcells11_c40, dcells11_c41, dcells11_c42, dcells11_c43, dcells11_c44, dcells11_c45, dcells11_c46, dcells11_c47, dcells11_c48, dcells11_c49, dcells11_c50, dcells11_c51, dcells11_c52, dcells11_c53, dcells11_c54, dcells11_c55, dcells11_c56, dcells11_c57])

end Zeta2L2Chi3.Arith
