/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section43FreimanDimension
import ErdosProblems.Erdos186.CFP.Bilu.Section8PresentationNormalization

/-!
# Bilu Section 9.3: the source affine-rank bound

Freiman's dimension lemma is applied to the selected normalized lift set.
Enlarged injectivity identifies its double sumset with the source double
sumset, so the homogenized affine rank is bounded only by the doubling
coefficient, independently of the current presentation rank.
-/

namespace Erdos186.CFP.Bilu.Section93AffineRankBound

open Set Module Submodule
open CFP.BiluFreiman
open Mahler MinkowskiSecond
open Section7FreimanMap
open Section7AffineSlice
open Section9KernelAffineReduction
open Section4PresentationLiftSet Section8PresentationNormalization
open Section92PresentationDescent Section92OuterInjectivityBridge
open Section43FreimanDimension
open SubspaceLattice

noncomputable section

set_option autoImplicit false

/-- General intrinsic-rank consequence of the dimension lemma. -/
theorem finrank_affineDirection_add_one_le_two_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [DecidableEq V]
    (S : Finset V) (hS : S.Nonempty) (sigma : ℕ)
    (hdouble : (pairSumset S).card ≤ sigma * S.card) :
    finrank ℝ (affineDirection S) + 1 ≤ 2 * sigma := by
  change affineRank S + 1 ≤ 2 * sigma
  exact affineRank_add_one_le_two_mul S hS sigma hdouble

/-- The same bound after translating into the intrinsic affine direction. -/
theorem affineRestriction_rank_add_one_le_two_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [DecidableEq V]
    (S : Finset V) (a : V) (ha : a ∈ S) (sigma : ℕ)
    (hdouble : (pairSumset S).card ≤ sigma * S.card) :
    finrank ℝ (affineDirection S) + 1 ≤ 2 * sigma :=
  finrank_affineDirection_add_one_le_two_mul S ⟨a, ha⟩ sigma hdouble

/-- The selected normalized lattice lifts in their canonical real ambient
space.  Affine dimension is a real-linear notion, so Section 9.3 applies
the dimension lemma to this faithful additive image. -/
def embeddedNormalizedLiftSet {A : Finset ℤ}
    (X : RankedBodyPresentation A) :
    Finset (EuclideanSpace ℝ (Fin X.1)) :=
  (normalizedLiftSet X).image integralReal

theorem integralReal_injective_local {n : ℕ} :
    Function.Injective (@integralReal n) := by
  intro x y hxy
  ext i
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) hxy
  change ((x i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) at hi
  exact_mod_cast hi

theorem integralReal_add_local {n : ℕ}
    (x y : IntegralPoint n) :
    integralReal (x + y) = integralReal x + integralReal y := by
  ext i
  simp [integralReal]

@[simp] theorem card_embeddedNormalizedLiftSet {A : Finset ℤ}
    (X : RankedBodyPresentation A) :
    (embeddedNormalizedLiftSet X).card = A.card := by
  rw [embeddedNormalizedLiftSet,
    Finset.card_image_of_injective _ integralReal_injective_local,
    card_normalizedLiftSet]

theorem card_pairSumset_embeddedNormalizedLiftSet_eq_twoA
    {A : Finset ℤ} (s : ℕ) (hs : 0 < s)
    (X : RankedBodyPresentation A) (hX : EnlargedInjective s X) :
    (pairSumset (embeddedNormalizedLiftSet X)).card = (twoA A).card := by
  rw [embeddedNormalizedLiftSet,
    card_pairSumset_image_eq integralReal
      integralReal_injective_local integralReal_add_local]
  exact card_pairSumset_normalizedLiftSet_eq_twoA s hs X hX

/-- Source-specific Section 9.3 bound for the normalized lift set. -/
theorem normalizedLiftSet_affineRank_add_one_le_two_mul
    {A : Finset ℤ} (s : ℕ) (hs : 0 < s)
    (X : RankedBodyPresentation A) (hX : EnlargedInjective s X)
    (hA : A.Nonempty) (sigma : ℕ)
    (hdouble : (twoA A).card ≤ sigma * A.card) :
    finrank ℝ (affineDirection (embeddedNormalizedLiftSet X)) + 1 ≤
      2 * sigma := by
  refine finrank_affineDirection_add_one_le_two_mul
      (embeddedNormalizedLiftSet X) ?_ sigma ?_
  · rw [← Finset.card_pos, card_embeddedNormalizedLiftSet]
    exact hA.card_pos
  · rw [card_pairSumset_embeddedNormalizedLiftSet_eq_twoA s hs X hX,
      card_embeddedNormalizedLiftSet]
    exact hdouble

/-- Real source coefficients are rounded upward exactly once. -/
theorem normalizedLiftSet_affineRank_add_one_le_two_mul_ceil
    {A : Finset ℤ} (s : ℕ) (hs : 0 < s)
    (X : RankedBodyPresentation A) (hX : EnlargedInjective s X)
    (hA : A.Nonempty) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hdouble : ((twoA A).card : ℝ) ≤ sigma * A.card) :
    finrank ℝ (affineDirection (embeddedNormalizedLiftSet X)) + 1 ≤
      2 * Nat.ceil sigma := by
  apply normalizedLiftSet_affineRank_add_one_le_two_mul s hs X hX hA
  have hsigmaCeil : sigma ≤ (Nat.ceil sigma : ℝ) := Nat.le_ceil sigma
  have hdoubleReal : ((twoA A).card : ℝ) ≤
      (Nat.ceil sigma : ℝ) * A.card :=
    hdouble.trans (mul_le_mul_of_nonneg_right hsigmaCeil (by positivity))
  exact_mod_cast hdoubleReal

end

end Erdos186.CFP.Bilu.Section93AffineRankBound

#print axioms
  Erdos186.CFP.Bilu.Section93AffineRankBound.normalizedLiftSet_affineRank_add_one_le_two_mul
#print axioms
  Erdos186.CFP.Bilu.Section93AffineRankBound.normalizedLiftSet_affineRank_add_one_le_two_mul_ceil
