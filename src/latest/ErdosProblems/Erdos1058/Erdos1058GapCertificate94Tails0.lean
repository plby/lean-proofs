import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap94Certificate

lemma tail_1_121 : cubicCRTSearchAux 94 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 121 = false := by
  rfl

lemma tail_1_331 : cubicCRTSearchAux 94 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 331 = false := by
  rfl

lemma tail_1_499 : cubicCRTSearchAux 94 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 499 = false := by
  rfl

end CubicCRTSearchGap94Certificate

end

end Erdos1058
