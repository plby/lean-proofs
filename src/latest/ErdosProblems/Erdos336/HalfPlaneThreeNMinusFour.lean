import ErdosProblems.Erdos336.FourierNineteenTwentyfive

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma three_n_minus_four_of_nineteen_twentyfive_density
    (a b d e : ℕ) (ha : 133 ≤ a)
    (hd : 4 * d < 9 * a) (hb : 19 * a < 25 * b)
    (he : e ≤ d) : e + 4 ≤ 3 * b := by
  omega

variable {N : ℕ} [NeZero N]

/-- The robust `19/25` half-plane slice lies in the integer `3n-4` range once
the parent has at least 133 points. -/
theorem positiveHalf_three_n_minus_four
    (A : Finset (ZMod N)) (k : ZMod N)
    (hcard : 133 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card)
    (hdense : 19 * A.card < 25 * (fourierPositiveHalf A k).card) :
    (fourierPositiveHalf A k + fourierPositiveHalf A k).card + 4 ≤
      3 * (fourierPositiveHalf A k).card := by
  have hsub : fourierPositiveHalf A k ⊆ A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hsumSub : fourierPositiveHalf A k + fourierPositiveHalf A k ⊆
      A + A := Finset.add_subset_add hsub hsub
  exact three_n_minus_four_of_nineteen_twentyfive_density
    A.card (fourierPositiveHalf A k).card (A + A).card
      (fourierPositiveHalf A k + fourierPositiveHalf A k).card
    hcard hdoub hdense (Finset.card_le_card hsumSub)

end Erdos336
