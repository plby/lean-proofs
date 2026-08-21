import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap6Certificate

lemma tail_0_61 : cubicCRTSearchAux 6 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 61 = false := by
  rfl

lemma tail_0_103 : cubicCRTSearchAux 6 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 103 = false := by
  rfl

lemma tail_0_229 : cubicCRTSearchAux 6 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 229 = false := by
  rfl

end CubicCRTSearchGap6Certificate

end

end Erdos1058
