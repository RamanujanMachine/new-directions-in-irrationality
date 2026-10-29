import Zeta2L2Chi3.Arith.DualChk9_0
import Zeta2L2Chi3.Arith.DualChk9_1
import Zeta2L2Chi3.Arith.DualChk9_2
import Zeta2L2Chi3.Arith.DualChk9_3
import Zeta2L2Chi3.Arith.DualChk9_4
import Zeta2L2Chi3.Arith.DualChk9_5
import Zeta2L2Chi3.Arith.DualChk9_6
import Zeta2L2Chi3.Arith.DualChk9_7
import Zeta2L2Chi3.Arith.DualChk9_8
import Zeta2L2Chi3.Arith.DualChk9_9
import Zeta2L2Chi3.Arith.DualChk9_10
import Zeta2L2Chi3.Arith.DualChk9_11
import Zeta2L2Chi3.Arith.DualChk9_12

namespace Zeta2L2Chi3.Arith

theorem dcells9_ok : dcells9.all DCell.ok = true :=
  all_chunks _ 1 100 dcells9 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells9_c0, dcells9_c1, dcells9_c2, dcells9_c3, dcells9_c4, dcells9_c5, dcells9_c6, dcells9_c7, dcells9_c8, dcells9_c9, dcells9_c10, dcells9_c11, dcells9_c12, dcells9_c13, dcells9_c14, dcells9_c15, dcells9_c16, dcells9_c17, dcells9_c18, dcells9_c19, dcells9_c20, dcells9_c21, dcells9_c22, dcells9_c23, dcells9_c24, dcells9_c25, dcells9_c26, dcells9_c27, dcells9_c28, dcells9_c29, dcells9_c30, dcells9_c31, dcells9_c32, dcells9_c33, dcells9_c34, dcells9_c35, dcells9_c36, dcells9_c37, dcells9_c38, dcells9_c39, dcells9_c40, dcells9_c41, dcells9_c42, dcells9_c43, dcells9_c44, dcells9_c45, dcells9_c46, dcells9_c47, dcells9_c48, dcells9_c49, dcells9_c50, dcells9_c51, dcells9_c52, dcells9_c53, dcells9_c54, dcells9_c55, dcells9_c56, dcells9_c57, dcells9_c58, dcells9_c59, dcells9_c60, dcells9_c61, dcells9_c62, dcells9_c63, dcells9_c64, dcells9_c65, dcells9_c66, dcells9_c67, dcells9_c68, dcells9_c69, dcells9_c70, dcells9_c71, dcells9_c72, dcells9_c73, dcells9_c74, dcells9_c75, dcells9_c76, dcells9_c77, dcells9_c78, dcells9_c79, dcells9_c80, dcells9_c81, dcells9_c82, dcells9_c83, dcells9_c84, dcells9_c85, dcells9_c86, dcells9_c87, dcells9_c88, dcells9_c89, dcells9_c90, dcells9_c91, dcells9_c92, dcells9_c93, dcells9_c94, dcells9_c95, dcells9_c96, dcells9_c97, dcells9_c98, dcells9_c99])

end Zeta2L2Chi3.Arith
