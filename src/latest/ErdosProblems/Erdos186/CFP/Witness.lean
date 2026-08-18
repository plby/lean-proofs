/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.StructureTheorem
import ErdosProblems.Erdos186.CFP.SymmetricGAP

/-!
# A nondegenerate CFP structure witness

`StructureTheorem.CFPWitness` is a deliberately weak, purely finite interface.
In particular, it admits the scale `k = 0`, which is useful for testing the
bookkeeping but is not the conclusion used in the Conlon--Fox--Pham argument.

This file packages the strengthened conclusion needed by that argument.  An
`EnhancedCFPWitness` contains the old witness and additionally records that

* the dilation scale is positive and is comparable with the reserve parameter;
* the undilated progression is proper, symmetric about zero, and nondegenerate;
* the offset of the *covered translate* belongs to the integer span of the
  progression steps.

The scale comparison is represented without division by positive numerator
and denominator parameters.  Thus
`scaleNum * s ≤ scaleDen * k` is the exact integer version of
`scaleNum / scaleDen ≤ k / s`.  No existence theorem is asserted here.
-/

namespace Erdos186

open scoped BigOperators

namespace CFP

/-- The nonvacuous finite conclusion of the CFP structure theorem.

Symmetry uses the presentation-level `GAP.Symmetric` predicate: the underlying
one-sided presentation has odd width `2 * radius + 1` and an offset which
moves its coordinate centre to zero.
-/
structure EnhancedCFPWitness {d : ℕ} (A : Finset (LatticePoint d))
    (s D k loss : ℕ) extends CFPWitness A s D k loss where
  /-- The scale is genuinely nonzero; this excludes the trivial zero-dilation
  witness. -/
  k_pos : 0 < k
  /-- Numerator of the fixed positive rational scale. -/
  scaleNum : ℕ
  /-- Denominator of the fixed positive rational scale. -/
  scaleDen : ℕ
  scaleNum_pos : 0 < scaleNum
  scaleDen_pos : 0 < scaleDen
  /-- Division-free form of `scaleNum / scaleDen ≤ k / s`. -/
  scale_lower : scaleNum * s ≤ scaleDen * k
  /-- The dilation uses no more elements than the reserve budget. -/
  scale_upper : k ≤ s
  /-- Properness of the original progression, in addition to the inherited
  properness of its `k`-dilation. -/
  progression_proper : progression.Proper
  /-- A coordinate centre witnessing that the original progression is
  symmetric about zero. -/
  progression_symmetric : progression.Symmetric
  /-- Every displayed direction is nondegenerate. -/
  progression_nondegenerate : progression.Nondegenerate
  /-- The offset of the translated, covered dilate is in the integer span of
  the steps.  This is homogeneity of the translate that actually occurs in
  the subset-sum coverage statement, rather than merely of the original GAP.
  -/
  covered_translate_homogeneous :
    ∃ z : Fin rank → ℤ,
      translatePoint + (progression.dilate k).offset =
        (fun j ↦ ∑ i, z i * progression.steps i j)

/-- An enhanced witness at a pair of scale constants fixed independently of
the input set.  The equalities in this subtype matter: merely storing a
positive numerator and denominator inside each witness would allow the
purported constant to vary with the input, which is not the uniform
Conlon--Fox--Pham conclusion. -/
def FixedScaleWitness {d : ℕ} (A : Finset (LatticePoint d))
    (s D k loss scaleNum scaleDen : ℕ) :=
  {W : EnhancedCFPWitness A s D k loss //
    W.scaleNum = scaleNum ∧ W.scaleDen = scaleDen}

namespace FixedScaleWitness

variable {d s D k loss scaleNum scaleDen : ℕ}
    {A : Finset (LatticePoint d)}

/-- Forget the proof that the two scale constants have their externally
fixed values. -/
abbrev enhanced
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    EnhancedCFPWitness A s D k loss :=
  W.1

theorem scaleNum_eq
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    W.enhanced.scaleNum = scaleNum :=
  W.2.1

theorem scaleDen_eq
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    W.enhanced.scaleDen = scaleDen :=
  W.2.2

theorem scaleNum_pos
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    0 < scaleNum := by
  rw [← W.scaleNum_eq]
  exact W.enhanced.scaleNum_pos

theorem scaleDen_pos
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    0 < scaleDen := by
  rw [← W.scaleDen_eq]
  exact W.enhanced.scaleDen_pos

/-- The scale lower bound with the externally fixed constants exposed. -/
theorem scale_lower
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen) :
    scaleNum * s ≤ scaleDen * k := by
  have h := W.enhanced.scale_lower
  simpa only [W.scaleNum_eq, W.scaleDen_eq] using h

end FixedScaleWitness

namespace EnhancedCFPWitness

variable {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness A s D k loss)

/-! ## Parameter consequences -/

/-- A positive dilation bounded by `s` forces a positive reserve budget. -/
theorem s_pos (W : EnhancedCFPWitness A s D k loss) : 0 < s :=
  lt_of_lt_of_le W.k_pos W.scale_upper

/-- The rational scale recorded by the witness is at most one. -/
theorem scaleNum_le_scaleDen : W.scaleNum ≤ W.scaleDen := by
  exact Nat.le_of_mul_le_mul_right
    (W.scale_lower.trans (Nat.mul_le_mul_left W.scaleDen W.scale_upper))
    W.s_pos

/-- A convenient bundled form of the two scale comparisons. -/
theorem scale_bounds :
    W.scaleNum * s ≤ W.scaleDen * k ∧ k ≤ s :=
  ⟨W.scale_lower, W.scale_upper⟩

/-! ## Projections to the basic witness -/

/-- Every enhanced witness has the original finite CFP interface. -/
abbrev basic : CFPWitness A s D k loss :=
  W.toCFPWitness

/-- Every reserved element is an element of the original set. -/
theorem reserved_subset : W.reserved ⊆ A :=
  W.basic.reserved_subset

/-- The covered translate is contained in the subset sums of the original
set, not only those of the reserve. -/
theorem covered_by_original_subsetSums :
    translate W.translatePoint (W.progression.dilate k).carrier ⊆
      GAP.subsetSums A :=
  W.basic.covered_by_original_subsetSums

/-- At most `loss` input elements lie outside the structured core. -/
theorem card_sdiff_core_le : (A \ W.core).card ≤ loss :=
  W.basic.card_sdiff_core_le

/-- Subtraction form of the loss estimate. -/
theorem card_sub_loss_le_core : A.card - loss ≤ W.core.card :=
  W.basic.card_sub_loss_le_core

/-! ## Cardinal consequences -/

/-- The surviving core injects into the actual carrier of the proper
progression. -/
theorem core_card_le_card_progression :
    W.core.card ≤ W.progression.carrier.card := by
  apply Finset.card_le_card
  exact (Finset.subset_insert 0 W.core).trans W.core_zero_subset

/-- The proper progression has as many actual points as displayed
coordinates. -/
theorem card_progression_eq_volume :
    W.progression.carrier.card = W.progression.volume :=
  W.progression.card_carrier_eq_volume W.progression_proper

/-- The original set, after the allowed loss, fits in the actual progression
carrier. -/
theorem card_sub_loss_le_card_progression :
    A.card - loss ≤ W.progression.carrier.card :=
  W.card_sub_loss_le_core.trans W.core_card_le_card_progression

/-- Volume version of `card_sub_loss_le_card_progression`. -/
theorem card_sub_loss_le_volume :
    A.card - loss ≤ W.progression.volume := by
  rw [← W.card_progression_eq_volume]
  exact W.card_sub_loss_le_card_progression

/-- Coverage and properness bound the dilated volume by the number of subset
sums of the reserve. -/
theorem dilated_volume_le_card_subsetSums :
    (W.progression.dilate k).volume ≤
      (GAP.subsetSums W.reserved).card :=
  W.basic.dilated_volume_le_card_subsetSums

/-- The covered proper dilate has at most one point for each subset of the
reserve. -/
theorem dilated_volume_le_pow_card_reserved :
    (W.progression.dilate k).volume ≤ 2 ^ W.reserved.card :=
  W.basic.dilated_volume_le_pow_card_reserved

/-- Parameter-budget version of the subset-sum counting bound. -/
theorem dilated_volume_le_pow_s :
    (W.progression.dilate k).volume ≤ 2 ^ s :=
  W.basic.dilated_volume_le_pow_s

/-! ## Symmetry and nondegeneracy consequences -/

/-- Choose radii for the symmetric presentation. -/
noncomputable def symmetryRadii : Fin W.rank → ℕ :=
  Classical.choose W.progression_symmetric

/-- The chosen radii really centre the progression at zero. -/
theorem symmetryCentered :
    W.progression.Centered W.symmetryRadii :=
  Classical.choose_spec W.progression_symmetric

theorem widths_eq_two_mul_symmetryRadii_add_one :
    W.progression.widths =
      (fun i ↦ 2 * W.symmetryRadii i + 1) :=
  W.symmetryCentered.widths_eq

theorem offset_eq_neg_sum_symmetryRadii :
    W.progression.offset =
      (fun j ↦ -∑ i, (W.symmetryRadii i : ℤ) * W.progression.steps i j) :=
  W.symmetryCentered.offset_eq

/-- The original progression contains zero. -/
theorem zero_mem_progression : 0 ∈ W.progression.carrier :=
  W.progression_symmetric.zero_mem_carrier

/-- The original progression carrier is invariant under negation. -/
theorem neg_mem_progression_iff (x : LatticePoint d) :
    -x ∈ W.progression.carrier ↔ x ∈ W.progression.carrier :=
  W.progression_symmetric.neg_mem_carrier_iff x

/-- The covered positive dilate remains symmetric. -/
theorem dilated_symmetric : (W.progression.dilate k).Symmetric :=
  W.progression_symmetric.dilate k

/-- The covered positive dilate remains nondegenerate. -/
theorem dilated_nondegenerate : (W.progression.dilate k).Nondegenerate :=
  W.progression_nondegenerate.dilate W.k_pos

/-- Symmetry and nondegeneracy improve the lower width bound from two to
three (all symmetric widths are odd). -/
theorem three_le_width (i : Fin W.rank) :
    3 ≤ W.progression.widths i := by
  have hwidth := congrFun W.widths_eq_two_mul_symmetryRadii_add_one i
  have hnondeg := W.progression_nondegenerate i
  omega

/-- The symmetric centre radius is positive in every displayed direction. -/
theorem symmetryRadii_pos (i : Fin W.rank) :
    0 < W.symmetryRadii i := by
  have hwidth := congrFun W.widths_eq_two_mul_symmetryRadii_add_one i
  have hnondeg := W.progression_nondegenerate i
  omega

/-! ## Nonemptiness consequences -/

/-- If less than the whole input is lost, the enhanced core is nonempty. -/
theorem core_nonempty (h : loss < A.card) : W.core.Nonempty :=
  W.basic.core_nonempty h

/-- If less than the whole input is lost, the proper progression carrier is
nonempty. -/
theorem progression_carrier_nonempty (h : loss < A.card) :
    W.progression.carrier.Nonempty :=
  W.basic.progression_carrier_nonempty h

end EnhancedCFPWitness

end CFP
end Erdos186
