import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- The arithmetic core of Lev's quotient-minimality step: if saturating the
double costs no more than saturating the set, strict `9/4` doubling survives
saturation, and the saturated doubling defect does not increase. -/
theorem nine_four_survives_balanced_saturation
    {a aSat d dSat : ℕ}
    (ha : a ≤ aSat) (hd : d ≤ dSat)
    (hbalance : dSat - d ≤ aSat - a)
    (hdoub : 4 * d < 9 * a) :
    4 * dSat < 9 * aSat ∧ dSat - aSat ≤ d - a := by
  constructor <;> omega

/-- Finset specialization for subgroup/coset saturations. -/
theorem nine_four_card_survives_balanced_saturation
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A D H : Finset G) (hA : A ⊆ A + H) (hD : D ⊆ D + H)
    (hbalance : (D + H).card - D.card ≤ (A + H).card - A.card)
    (hdoub : 4 * D.card < 9 * A.card) :
    4 * (D + H).card < 9 * (A + H).card ∧
      (D + H).card - (A + H).card ≤ D.card - A.card := by
  exact nine_four_survives_balanced_saturation
    (Finset.card_le_card hA) (Finset.card_le_card hD) hbalance hdoub

end Erdos336
