import Zeta2L2Chi3.Arith.DualChk7_0
import Zeta2L2Chi3.Arith.DualChk7_1
import Zeta2L2Chi3.Arith.DualChk7_2
import Zeta2L2Chi3.Arith.DualChk7_3
import Zeta2L2Chi3.Arith.DualChk7_4
import Zeta2L2Chi3.Arith.DualChk7_5
import Zeta2L2Chi3.Arith.DualChk7_6
import Zeta2L2Chi3.Arith.DualChk7_7
import Zeta2L2Chi3.Arith.DualChk7_8
import Zeta2L2Chi3.Arith.DualChk7_9
import Zeta2L2Chi3.Arith.DualChk7_10
import Zeta2L2Chi3.Arith.DualChk7_11
import Zeta2L2Chi3.Arith.DualChk7_12

namespace Zeta2L2Chi3.Arith

theorem dcells7_ok : dcells7.all DCell.ok = true :=
  all_chunks _ 1 100 dcells7 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells7_c0, dcells7_c1, dcells7_c2, dcells7_c3, dcells7_c4, dcells7_c5, dcells7_c6, dcells7_c7, dcells7_c8, dcells7_c9, dcells7_c10, dcells7_c11, dcells7_c12, dcells7_c13, dcells7_c14, dcells7_c15, dcells7_c16, dcells7_c17, dcells7_c18, dcells7_c19, dcells7_c20, dcells7_c21, dcells7_c22, dcells7_c23, dcells7_c24, dcells7_c25, dcells7_c26, dcells7_c27, dcells7_c28, dcells7_c29, dcells7_c30, dcells7_c31, dcells7_c32, dcells7_c33, dcells7_c34, dcells7_c35, dcells7_c36, dcells7_c37, dcells7_c38, dcells7_c39, dcells7_c40, dcells7_c41, dcells7_c42, dcells7_c43, dcells7_c44, dcells7_c45, dcells7_c46, dcells7_c47, dcells7_c48, dcells7_c49, dcells7_c50, dcells7_c51, dcells7_c52, dcells7_c53, dcells7_c54, dcells7_c55, dcells7_c56, dcells7_c57, dcells7_c58, dcells7_c59, dcells7_c60, dcells7_c61, dcells7_c62, dcells7_c63, dcells7_c64, dcells7_c65, dcells7_c66, dcells7_c67, dcells7_c68, dcells7_c69, dcells7_c70, dcells7_c71, dcells7_c72, dcells7_c73, dcells7_c74, dcells7_c75, dcells7_c76, dcells7_c77, dcells7_c78, dcells7_c79, dcells7_c80, dcells7_c81, dcells7_c82, dcells7_c83, dcells7_c84, dcells7_c85, dcells7_c86, dcells7_c87, dcells7_c88, dcells7_c89, dcells7_c90, dcells7_c91, dcells7_c92, dcells7_c93, dcells7_c94, dcells7_c95, dcells7_c96, dcells7_c97, dcells7_c98, dcells7_c99])

end Zeta2L2Chi3.Arith
