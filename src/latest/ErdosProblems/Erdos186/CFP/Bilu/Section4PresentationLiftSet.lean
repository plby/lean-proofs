/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92MahlerVolumeConversion

/-!
# A Freiman lift set inside an enlarged-injective presentation

After the Section 9.2 rank repair, the presentation map is injective on a
uniform seminorm ball containing the sum of two unit-ball lifts.  Choosing one
lift of each source element therefore gives a finite set with exactly the same
cardinality and exactly the same doubling cardinality as the source set.  This
is the discrete input needed to apply the corrected Sections 6--9 construction
to an arbitrary current Section 4 candidate.
-/

namespace Erdos186.CFP.Bilu.Section4PresentationLiftSet

open scoped Pointwise
open CFP.BiluFreiman
open Mahler
open MahlerOuterContainer
open Section92OuterInjectivityBridge
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- A fixed unit-ball lift of each source element. -/
def presentationLift (X : RankedBodyPresentation A) (a : A) :
    IntegralPoint X.1 :=
  (X.2.lifts a a.property).choose

theorem presentationLift_mem_unitBall
    (X : RankedBodyPresentation A) (a : A) :
    X.2.seminorm (integralEmbed (presentationLift X a)) ≤ 1 :=
  (X.2.lifts a a.property).choose_spec.1

@[simp] theorem map_presentationLift
    (X : RankedBodyPresentation A) (a : A) :
    X.2.map (presentationLift X a) = a :=
  (X.2.lifts a a.property).choose_spec.2

/-- The finite set consisting of the selected unit-ball lifts. -/
def presentationLiftSet (X : RankedBodyPresentation A) :
    Finset (IntegralPoint X.1) :=
  A.attach.image (presentationLift X)

theorem presentationLift_injective (X : RankedBodyPresentation A) :
    Function.Injective (presentationLift X) := by
  intro a b hab
  apply Subtype.ext
  simpa only [map_presentationLift] using congrArg X.2.map hab

@[simp] theorem card_presentationLiftSet
    (X : RankedBodyPresentation A) :
    (presentationLiftSet X).card = A.card := by
  rw [presentationLiftSet, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · exact presentationLift_injective X

theorem mem_presentationLiftSet_iff
    (X : RankedBodyPresentation A) (z : IntegralPoint X.1) :
    z ∈ presentationLiftSet X ↔
      ∃ a : A, presentationLift X a = z := by
  simp only [presentationLiftSet, Finset.mem_image, Finset.mem_attach,
    true_and]

theorem presentationLiftSet_subset_unitBall
    (X : RankedBodyPresentation A) :
    ↑(presentationLiftSet X) ⊆
      {z : IntegralPoint X.1 |
        X.2.seminorm (integralEmbed z) ≤ 1} := by
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_presentationLiftSet_iff X z).mp hz
  exact presentationLift_mem_unitBall X a

/-- The uniform outer radius contains the sum of two unit-ball lifts. -/
theorem two_le_outerDilationBound
    (s n : ℕ) (hs : 0 < s) (hn : 0 < n) :
    (2 : ℝ) ≤ outerDilationBound n (2 * s) := by
  unfold outerDilationBound
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hout : (1 : ℝ) ≤ outerConstant n + 1 := by
    linarith [outerConstant_nonneg n]
  have htwo : (2 : ℝ) ≤ 2 * s := by nlinarith
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  rw [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (2 : ℝ) ≤ 2 * (s : ℝ) := htwo
    _ ≤ (2 * (s : ℝ)) * (n : ℝ) ^ 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * s)
    _ ≤ (2 * (s : ℝ)) * (n : ℝ) ^ 2 * (outerConstant n + 1) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hout
          (mul_nonneg (by positivity) (sq_nonneg (n : ℝ)))

theorem pairSum_mem_enlargedBall
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    {x y : IntegralPoint X.1}
    (hx : x ∈ presentationLiftSet X)
    (hy : y ∈ presentationLiftSet X) :
    X.2.seminorm (integralEmbed (x + y)) ≤
      outerDilationBound X.1 (2 * s) := by
  have hx' := presentationLiftSet_subset_unitBall X hx
  have hy' := presentationLiftSet_subset_unitBall X hy
  calc
    X.2.seminorm (integralEmbed (x + y)) =
        X.2.seminorm (integralEmbed x + integralEmbed y) := by rw [integralEmbed_add]
    _ ≤ X.2.seminorm (integralEmbed x) +
        X.2.seminorm (integralEmbed y) := map_add_le_add _ _ _
    _ ≤ 2 := by
      change X.2.seminorm (integralEmbed x) ≤ 1 at hx'
      change X.2.seminorm (integralEmbed y) ≤ 1 at hy'
      linarith
    _ ≤ outerDilationBound X.1 (2 * s) :=
      two_le_outerDilationBound s X.1 hs X.2.rank_pos

/-- On the two-fold lift sumset, enlarged injectivity makes the presentation
map injective. -/
theorem map_injOn_pairSumset
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) :
    Set.InjOn X.2.map ↑(presentationLiftSet X + presentationLiftSet X) := by
  intro x hx y hy hxy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Finset.mem_add.mp hy
  exact hX (pairSum_mem_enlargedBall s hs X hx₁ hx₂)
    (pairSum_mem_enlargedBall s hs X hy₁ hy₂) hxy

/-- Mapping the selected lift sumset gives exactly the source sumset. -/
theorem image_pairSumset_eq_twoA
    (X : RankedBodyPresentation A) :
    (presentationLiftSet X + presentationLiftSet X).image X.2.map =
      twoA A := by
  ext z
  rw [Finset.mem_image, mem_twoA_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hw
    obtain ⟨a, rfl⟩ := (mem_presentationLiftSet_iff X x).mp hx
    obtain ⟨b, rfl⟩ := (mem_presentationLiftSet_iff X y).mp hy
    exact ⟨a, a.property, b, b.property, by simp⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    let a' : A := ⟨a, ha⟩
    let b' : A := ⟨b, hb⟩
    refine ⟨presentationLift X a' + presentationLift X b', ?_, ?_⟩
    · exact Finset.mem_add.mpr ⟨presentationLift X a', by
        exact (mem_presentationLiftSet_iff X _).mpr ⟨a', rfl⟩,
        presentationLift X b', by
          exact (mem_presentationLiftSet_iff X _).mpr ⟨b', rfl⟩,
        rfl⟩
    · simp [a', b']

/-- The selected lift set has exactly the source doubling cardinality. -/
theorem card_pairSumset_presentationLiftSet_eq_twoA
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) :
    (presentationLiftSet X + presentationLiftSet X).card =
      (twoA A).card := by
  rw [← image_pairSumset_eq_twoA X,
    Finset.card_image_of_injOn (map_injOn_pairSumset s hs X hX)]

end

end Erdos186.CFP.Bilu.Section4PresentationLiftSet

#print axioms
  Erdos186.CFP.Bilu.Section4PresentationLiftSet.card_pairSumset_presentationLiftSet_eq_twoA
