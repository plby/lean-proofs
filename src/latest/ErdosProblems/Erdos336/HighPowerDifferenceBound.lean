import Mathlib
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import ErdosProblems.Erdos336.DensePowerSaturation
import ErdosProblems.Erdos336.HighPowerSmallQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A corrected replacement for the false printed unique-difference bound:
strict `9/4` doubling and cardinality at least 21 force the entire difference
set, hence every set of uniquely represented differences, to have cardinality
at most one quarter of the square. -/
theorem four_mul_card_sub_le_sq_of_nine_four
    (A : Finset G) (hcard : 21 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card) :
    4 * (A - A).card ≤ A.card ^ 2 := by
  have hruz := Finset.ruzsa_triangle_inequality_sub_add_add A A A
  have hsquare := Nat.mul_self_lt_mul_self hdoub
  have hscaled : 16 * ((A - A).card * A.card) ≤
      16 * ((A + A).card * (A + A).card) :=
    Nat.mul_le_mul_left 16 hruz
  have hstrict : 16 * (A - A).card * A.card <
      81 * A.card * A.card := by
    calc
      16 * (A - A).card * A.card =
          16 * ((A - A).card * A.card) := by ring
      _ ≤ 16 * ((A + A).card * (A + A).card) := hscaled
      _ = (4 * (A + A).card) * (4 * (A + A).card) := by ring
      _ < (9 * A.card) * (9 * A.card) := hsquare
      _ = 81 * A.card * A.card := by ring
  have hcancel : 16 * (A - A).card < 81 * A.card := by
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hstrict)
  have hcompare : 81 * A.card ≤ 4 * (A.card ^ 2) := by
    nlinarith [Nat.zero_le A.card]
  have hfour : (4 * (A - A).card) * 4 < (A.card ^ 2) * 4 := by
    nlinarith
  exact (Nat.lt_of_mul_lt_mul_right hfour).le

/-- Any finset of differences inherits the same quarter-square bound. -/
theorem four_mul_card_le_sq_of_subset_sub_nine_four
    (A D : Finset G) (hD : D ⊆ A - A) (hcard : 21 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card) :
    4 * D.card ≤ A.card ^ 2 := by
  calc
    4 * D.card ≤ 4 * (A - A).card :=
      Nat.mul_le_mul_left 4 (Finset.card_le_card hD)
    _ ≤ A.card ^ 2 := four_mul_card_sub_le_sq_of_nine_four A hcard hdoub

section HighPower

variable [Fintype G]

/-- For a primitive zero-containing power, `t≥20` supplies the cardinality
hypothesis automatically unless the power has already saturated. -/
theorem highPower_four_mul_card_sub_le_sq
    {C : Set G} (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    {t : ℕ} (ht : 20 ≤ t) (hnotfull : ExactPower C t ≠ Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard) :
    let S := exactPowerFinset C t
    4 * (S - S).card ≤ S.card ^ 2 := by
  let S := exactPowerFinset C t
  have hcard : 21 ≤ S.card := by
    rw [card_exactPowerFinset]
    exact le_trans (by omega) <|
      add_one_le_ncard_exactPower_of_not_full hzero hprimitive t hnotfull
  have hsum : S + S = exactPowerFinset C (2 * t) := by
    apply Finset.coe_injective
    rw [Finset.coe_add]
    simp only [S, coe_exactPowerFinset]
    rw [exactPower_add]
    congr 2
    omega
  have hdoub' : 4 * (S + S).card < 9 * S.card := by
    rw [hsum]
    simpa [S] using hdoub
  exact four_mul_card_sub_le_sq_of_nine_four S hcard hdoub'

end HighPower

end Erdos336
