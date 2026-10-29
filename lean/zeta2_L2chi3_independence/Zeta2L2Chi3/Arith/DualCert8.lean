import Zeta2L2Chi3.Arith.DualChk8_0
import Zeta2L2Chi3.Arith.DualChk8_1
import Zeta2L2Chi3.Arith.DualChk8_2
import Zeta2L2Chi3.Arith.DualChk8_3
import Zeta2L2Chi3.Arith.DualChk8_4
import Zeta2L2Chi3.Arith.DualChk8_5
import Zeta2L2Chi3.Arith.DualChk8_6
import Zeta2L2Chi3.Arith.DualChk8_7
import Zeta2L2Chi3.Arith.DualChk8_8
import Zeta2L2Chi3.Arith.DualChk8_9
import Zeta2L2Chi3.Arith.DualChk8_10
import Zeta2L2Chi3.Arith.DualChk8_11
import Zeta2L2Chi3.Arith.DualChk8_12

namespace Zeta2L2Chi3.Arith

theorem dcells8_ok : dcells8.all DCell.ok = true :=
  all_chunks _ 1 100 dcells8 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells8_c0, dcells8_c1, dcells8_c2, dcells8_c3, dcells8_c4, dcells8_c5, dcells8_c6, dcells8_c7, dcells8_c8, dcells8_c9, dcells8_c10, dcells8_c11, dcells8_c12, dcells8_c13, dcells8_c14, dcells8_c15, dcells8_c16, dcells8_c17, dcells8_c18, dcells8_c19, dcells8_c20, dcells8_c21, dcells8_c22, dcells8_c23, dcells8_c24, dcells8_c25, dcells8_c26, dcells8_c27, dcells8_c28, dcells8_c29, dcells8_c30, dcells8_c31, dcells8_c32, dcells8_c33, dcells8_c34, dcells8_c35, dcells8_c36, dcells8_c37, dcells8_c38, dcells8_c39, dcells8_c40, dcells8_c41, dcells8_c42, dcells8_c43, dcells8_c44, dcells8_c45, dcells8_c46, dcells8_c47, dcells8_c48, dcells8_c49, dcells8_c50, dcells8_c51, dcells8_c52, dcells8_c53, dcells8_c54, dcells8_c55, dcells8_c56, dcells8_c57, dcells8_c58, dcells8_c59, dcells8_c60, dcells8_c61, dcells8_c62, dcells8_c63, dcells8_c64, dcells8_c65, dcells8_c66, dcells8_c67, dcells8_c68, dcells8_c69, dcells8_c70, dcells8_c71, dcells8_c72, dcells8_c73, dcells8_c74, dcells8_c75, dcells8_c76, dcells8_c77, dcells8_c78, dcells8_c79, dcells8_c80, dcells8_c81, dcells8_c82, dcells8_c83, dcells8_c84, dcells8_c85, dcells8_c86, dcells8_c87, dcells8_c88, dcells8_c89, dcells8_c90, dcells8_c91, dcells8_c92, dcells8_c93, dcells8_c94, dcells8_c95, dcells8_c96, dcells8_c97, dcells8_c98, dcells8_c99])

end Zeta2L2Chi3.Arith
