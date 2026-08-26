import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336
open scoped Pointwise

/-- Counterexample to the printed bound in Lemma 6.2 of Lev's 2020 preprint. -/
theorem lev_lemma_six_two_printed_bound_counterexample :
    let A : Finset (ZMod 6) := {0, 1, 3}
    let D : Finset (ZMod 6) := Finset.univ.filter (fun x =>
      ((A ×ˢ A).filter (fun p => p.1 - p.2 = x)).card = 1)
    A.card = 3 ∧ (A + A).card = 5 ∧
      (A + A).card ≤ 3 * A.card - 4 ∧ D.card = 4 ∧
      A.card ^ 2 < 4 * D.card := by
  decide

end Erdos336
