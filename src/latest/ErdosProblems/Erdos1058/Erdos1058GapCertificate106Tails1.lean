import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058GapCertificate106Tails0

-- Serialize concrete search reductions to bound elaborator memory.
set_option Elab.async false

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap106Certificate

lemma tail_1_493 : cubicCRTSearchAux 106 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 493 = false := by
  rfl

end CubicCRTSearchGap106Certificate

end

end Erdos1058
