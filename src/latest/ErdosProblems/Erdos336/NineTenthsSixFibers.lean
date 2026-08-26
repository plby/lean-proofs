import ErdosProblems.Erdos336.MinimalV3StrongNineTenthsPartialRectification
import ErdosProblems.Erdos336.QuotientFiberProduct
import ErdosProblems.Erdos336.HighPowerSmallSupport

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- A nine-tenths slice of a sparse high power in a quotient of order at least
37 must meet at least six quotient fibres. This removes all of the exceptional
three-, four-, and five-fibre cases from the rectified inverse step. -/
theorem six_le_card_image_of_nine_tenths_highPower
    (C : Set (ZMod N)) (t : ℕ) (ht : 12 ≤ t)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ u : ℕ, ExactPower C u = Set.univ)
    (π : ZMod N →+ ZMod m) (hπ : Function.Surjective π)
    (hm37 : 37 ≤ m)
    (B : Finset (ZMod N))
    (hBA : B ⊆ exactPowerFinset C t)
    (hdense : 9 * (exactPowerFinset C t).card < 10 * B.card)
    (hdoub : 4 * (exactPowerFinset C (2 * t)).card <
      9 * (exactPowerFinset C t).card) :
    6 ≤ (B.image π).card := by
  let A : Finset (ZMod N) := exactPowerFinset C t
  let r : ℕ := (B.image π).card
  let q : ℕ := (A.image π).card
  let d : ℕ := (A + A).card
  have hB : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hB0
    rw [hB0] at hdense
    simp at hdense
  have hrpos : 0 < r := by
    have := hB.image π
    simpa [r] using this.card_pos
  have himageProduct : q * B.card ≤ r * d := by
    have hp := card_image_mul_card_le_card_image_mul_card_add π A B hB
    have hABsub : A + B ⊆ A + A :=
      Finset.add_subset_add (Finset.Subset.rfl) hBA
    have hABcard : (A + B).card ≤ d := by
      simpa [d] using Finset.card_le_card hABsub
    calc
      q * B.card ≤ r * (A + B).card := by simpa [q, r] using hp
      _ ≤ r * d := Nat.mul_le_mul_left r hABcard
  have hdoub' : 4 * d < 9 * A.card := by
    simpa [A, d, exactPowerFinset_add_self] using hdoub
  have hdense' : 9 * A.card < 10 * B.card := by
    simpa [A] using hdense
  have hq_lt : 2 * q < 5 * r := by
    by_contra hnot
    have h5r : 5 * r ≤ 2 * q := by omega
    have hmul : (5 * r) * B.card ≤ (2 * q) * B.card :=
      Nat.mul_le_mul_right B.card h5r
    have hprod2 : (2 * q) * B.card ≤ 2 * (r * d) := by
      nlinarith
    have h5b2d : 5 * B.card ≤ 2 * d := by
      have hraw : r * (5 * B.card) ≤ r * (2 * d) := by
        nlinarith
      exact Nat.le_of_mul_le_mul_left hraw hrpos
    omega
  by_contra hrnot
  have hr5 : r ≤ 5 := by omega
  have hq12 : q ≤ 12 := by omega
  have hqt : q ≤ t := le_trans hq12 ht
  let D : Set (ZMod m) := π '' C
  have hzD : 0 ∈ D := ⟨0, hzero, π.map_zero⟩
  have hpD : ∃ u : ℕ, ExactPower D u = Set.univ :=
    exactPower_univ_image_of_surjective π hπ hprimitive
  have himageA : A.image π = exactPowerFinset D t := by
    simpa [A, D] using image_exactPowerFinset π C t
  have hsmallD : (ExactPower D t).ncard ≤ q := by
    rw [← card_exactPowerFinset, ← himageA]
  have hmleq : m ≤ q := by
    have hc := card_le_of_highPower_ncard_le hzD hpD hqt hsmallD
    simpa [ZMod.card] using hc
  omega

end Erdos336
