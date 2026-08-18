/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4SmallCardinality
import ErdosProblems.Erdos186.CFP.Bilu.Section92ReducedOuterConstructor
import ErdosProblems.Erdos186.CFP.Bilu.Section94RankThresholdBoundary

/-!
# Rank-indexed presentations and Section 9.2 termination

This is the common discrete interface between the Section 9.1 initial
presentations and the primitive-kernel quotient.  It contains exactly the
fields preserved by quotient descent.  Minimal-rank selection makes the
enlarged injectivity test succeed, after which the existing Section 3
constructor produces a `ReducedOuterRealization`.
-/

namespace Erdos186.CFP.Bilu.Section92PresentationDescent

open MeasureTheory
open Mahler
open Section4SmallCardinality
open Section9ContainerIntegration
open Section92OuterInjectivityBridge
open Section92ReducedOuterConstructor
open Section94RankThresholdBoundary
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

/-- An appropriate standard-lattice presentation in a fixed positive rank.
The real unit-ball volume is included because it is the scalar minimized in
Section 4. -/
structure BodyPresentation (A : Finset ℤ) (rank : ℕ) where
  rank_pos : 0 < rank
  seminorm : Seminorm ℝ (Fin rank → ℝ)
  definite : IsDefinite seminorm
  full : AdmitsIndependent seminorm rank 1
  map : IntegralPoint rank →+ ℤ
  lifts : ∀ a ∈ A, ∃ z : IntegralPoint rank,
    seminorm (integralEmbed z) ≤ 1 ∧ map z = a
  bodyVolume_pos :
    0 < volume.real {x : Fin rank → ℝ | seminorm x ≤ 1}

/-- A presentation of unspecified rank. -/
abbrev RankedBodyPresentation (A : Finset ℤ) :=
  Σ rank, BodyPresentation A rank

/-- The real volume minimized in the Section 4 iteration. -/
def bodyVolume {A : Finset ℤ} (X : RankedBodyPresentation A) : ℝ :=
  volume.real {x : Fin X.1 → ℝ | X.2.seminorm x ≤ 1}

theorem bodyVolume_pos {A : Finset ℤ} (X : RankedBodyPresentation A) :
    0 < bodyVolume X :=
  X.2.bodyVolume_pos

/-- The stopping condition in Section 9.2. -/
def EnlargedInjective {A : Finset ℤ} (s : ℕ)
    (X : RankedBodyPresentation A) : Prop :=
  Set.InjOn X.2.map
    {z : IntegralPoint X.1 |
      X.2.seminorm (integralEmbed z) ≤
        outerDilationBound X.1 (2 * s)}

/-- Minimal-rank termination, preserving the rank bound of the supplied
initial presentation.  Every failed injectivity test is repaired in a
strictly smaller positive rank. -/
theorem exists_enlargedInjective_of_rankReduction
    {A : Finset ℤ} (s rankBound : ℕ)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (reduce : ∀ X : RankedBodyPresentation A,
      ¬ EnlargedInjective s X →
        ∃ Y : RankedBodyPresentation A, Y.1 < X.1) :
    ∃ X : RankedBodyPresentation A,
      EnlargedInjective s X ∧ X.1 ≤ rankBound := by
  obtain ⟨X, -, hgood, hrank⟩ :=
    exists_good_of_rank_reduction_with_rank_bound
      (fun _ : RankedBodyPresentation A ↦ True)
      (EnlargedInjective s) initial trivial rankBound hinitialRank
      (by
        intro X _ hbad
        obtain ⟨Y, hYX⟩ := reduce X hbad
        exact ⟨Y, trivial, hYX⟩)
  exact ⟨X, hgood, hrank⟩

/-- The terminal Section 3 constructor consumes a stopped presentation.
All analytic volume comparison has been isolated in `hvolume`. -/
theorem exists_reducedOuterRealization_of_presentation
    {A : Finset ℤ} {s volumeConstant rankBound : ℕ}
    (X : RankedBodyPresentation A)
    (hinjective : EnlargedInjective s X)
    (hvolume : ∀ D : MappedOuterContainer X.2.seminorm X.2.map,
      D.source.volume ≤ volumeConstant * A.card)
    (hrank : X.1 ≤ rankBound) :
    Nonempty (ReducedOuterRealization
      s volumeConstant rankBound A) :=
  exists_reducedOuterRealization_of_body X.2.rank_pos X.2.seminorm
    X.2.definite X.2.full X.2.map hinjective X.2.lifts hvolume hrank

/-- Complete nonanalytic Section 9.2 assembly: rank descent followed by the
reduced outer constructor. -/
theorem exists_reducedOuterRealization_of_rankReduction
    {A : Finset ℤ} (s volumeConstant rankBound : ℕ)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (reduce : ∀ X : RankedBodyPresentation A,
      ¬ EnlargedInjective s X →
        ∃ Y : RankedBodyPresentation A, Y.1 < X.1)
    (hvolume : ∀ X : RankedBodyPresentation A,
      EnlargedInjective s X →
      ∀ D : MappedOuterContainer X.2.seminorm X.2.map,
        D.source.volume ≤ volumeConstant * A.card) :
    Nonempty (ReducedOuterRealization
      s volumeConstant rankBound A) := by
  obtain ⟨X, hgood, hrank⟩ :=
    exists_enlargedInjective_of_rankReduction s rankBound initial
      hinitialRank reduce
  exact exists_reducedOuterRealization_of_presentation X hgood
    (hvolume X hgood) hrank

/-! ## The bounded-cardinality initializer in the common interface -/

/-- The formal-coordinate cube is a common body presentation. -/
def bodyPresentationOfSmallCard
    (A : Finset ℤ) (hA : A.Nonempty) :
    BodyPresentation A A.card where
  rank_pos := hA.card_pos
  seminorm := cubeSeminorm A
  definite := cubeSeminorm_definite A
  full := cubeSeminorm_admitsIndependent A
  map := coordinateMap A
  lifts := by
    intro a ha
    let a' : A := ⟨a, ha⟩
    exact ⟨coordinateLift A a', coordinateLift_mem_unitBall A a',
      coordinateMap_coordinateLift A a'⟩
  bodyVolume_pos := by
    change 0 < (volume
      {x : Fin A.card → ℝ | cubeSeminorm A x ≤ 1}).toReal
    rw [volume_cubeSeminorm_unitBall A hA]
    simp

/-- Rank-unspecified form of the bounded-cardinality initializer. -/
def rankedBodyPresentationOfSmallCard
    (A : Finset ℤ) (hA : A.Nonempty) :
    RankedBodyPresentation A :=
  ⟨A.card, bodyPresentationOfSmallCard A hA⟩

@[simp] theorem rank_rankedBodyPresentationOfSmallCard
    (A : Finset ℤ) (hA : A.Nonempty) :
    (rankedBodyPresentationOfSmallCard A hA).1 = A.card :=
  rfl

end


end Erdos186.CFP.Bilu.Section92PresentationDescent

#print axioms
  Erdos186.CFP.Bilu.Section92PresentationDescent.exists_enlargedInjective_of_rankReduction
#print axioms
  Erdos186.CFP.Bilu.Section92PresentationDescent.exists_reducedOuterRealization_of_rankReduction
#print axioms
  Erdos186.CFP.Bilu.Section92PresentationDescent.bodyPresentationOfSmallCard
