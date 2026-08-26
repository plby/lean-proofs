import Mathlib
import ErdosProblems.Erdos336.HighPowerSmallQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# General small-support obstruction for a primitive high power
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- If a primitive zero-containing `t`-th power occupies at most `K` points
and `K≤t`, then those points are already the whole group. -/
theorem card_le_of_highPower_ncard_le
    {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {t K : ℕ} (hKt : K ≤ t)
    (hsmall : (ExactPower D t).ncard ≤ K) :
    Fintype.card G ≤ K := by
  by_cases hfull : ExactPower D t = Set.univ
  · simpa [hfull] using hsmall
  · have hlow := add_one_le_ncard_exactPower_of_not_full
      hzero hexact t hfull
    omega

end Erdos336
