import Zeta2L2Chi3.Arith.DualChk10_0
import Zeta2L2Chi3.Arith.DualChk10_1
import Zeta2L2Chi3.Arith.DualChk10_2
import Zeta2L2Chi3.Arith.DualChk10_3
import Zeta2L2Chi3.Arith.DualChk10_4
import Zeta2L2Chi3.Arith.DualChk10_5
import Zeta2L2Chi3.Arith.DualChk10_6
import Zeta2L2Chi3.Arith.DualChk10_7
import Zeta2L2Chi3.Arith.DualChk10_8
import Zeta2L2Chi3.Arith.DualChk10_9
import Zeta2L2Chi3.Arith.DualChk10_10
import Zeta2L2Chi3.Arith.DualChk10_11
import Zeta2L2Chi3.Arith.DualChk10_12

namespace Zeta2L2Chi3.Arith

theorem dcells10_ok : dcells10.all DCell.ok = true :=
  all_chunks _ 1 100 dcells10 (by decide) (fun j hj => by
    interval_cases j
    exacts [dcells10_c0, dcells10_c1, dcells10_c2, dcells10_c3, dcells10_c4, dcells10_c5, dcells10_c6, dcells10_c7, dcells10_c8, dcells10_c9, dcells10_c10, dcells10_c11, dcells10_c12, dcells10_c13, dcells10_c14, dcells10_c15, dcells10_c16, dcells10_c17, dcells10_c18, dcells10_c19, dcells10_c20, dcells10_c21, dcells10_c22, dcells10_c23, dcells10_c24, dcells10_c25, dcells10_c26, dcells10_c27, dcells10_c28, dcells10_c29, dcells10_c30, dcells10_c31, dcells10_c32, dcells10_c33, dcells10_c34, dcells10_c35, dcells10_c36, dcells10_c37, dcells10_c38, dcells10_c39, dcells10_c40, dcells10_c41, dcells10_c42, dcells10_c43, dcells10_c44, dcells10_c45, dcells10_c46, dcells10_c47, dcells10_c48, dcells10_c49, dcells10_c50, dcells10_c51, dcells10_c52, dcells10_c53, dcells10_c54, dcells10_c55, dcells10_c56, dcells10_c57, dcells10_c58, dcells10_c59, dcells10_c60, dcells10_c61, dcells10_c62, dcells10_c63, dcells10_c64, dcells10_c65, dcells10_c66, dcells10_c67, dcells10_c68, dcells10_c69, dcells10_c70, dcells10_c71, dcells10_c72, dcells10_c73, dcells10_c74, dcells10_c75, dcells10_c76, dcells10_c77, dcells10_c78, dcells10_c79, dcells10_c80, dcells10_c81, dcells10_c82, dcells10_c83, dcells10_c84, dcells10_c85, dcells10_c86, dcells10_c87, dcells10_c88, dcells10_c89, dcells10_c90, dcells10_c91, dcells10_c92, dcells10_c93, dcells10_c94, dcells10_c95, dcells10_c96, dcells10_c97, dcells10_c98, dcells10_c99])

end Zeta2L2Chi3.Arith
