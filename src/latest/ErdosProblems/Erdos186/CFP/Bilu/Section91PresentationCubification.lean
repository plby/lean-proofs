/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91IntegerPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section92PresentationDescent
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Cubifying a bounded-rank Section 9.1 presentation

The covering construction already supplies a bounded-rank integral map and
one lift of every source element.  For nonemptiness of the admissible class,
no sharp volume estimate is needed: a sufficiently large sup-norm cube
contains the finitely many chosen lifts.  This module performs that finite
rescaling and packages the result in the common descent interface.
-/

namespace Erdos186.CFP.Bilu.Section91PresentationCubification

open scoped BigOperators NNReal
open MeasureTheory
open Mahler MinkowskiSecond
open Section92PresentationDescent
open Proposition75Data Section9NormalizedReplacement

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {rank : ℕ}

/-- A fixed lift of each source element through an integral presentation. -/
def chosenLift (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (a : A) : IntegralPoint rank :=
  (hlifts a a.property).choose

@[simp] theorem map_chosenLift (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (a : A) :
    phi (chosenLift phi hlifts a) = a :=
  (hlifts a a.property).choose_spec

/-- A positive radius containing all chosen lifts. -/
def liftRadius (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) : ℝ :=
  1 + ∑ a ∈ A.attach, ‖integralEmbed (chosenLift phi hlifts a)‖

theorem one_le_liftRadius (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    1 ≤ liftRadius phi hlifts := by
  unfold liftRadius
  have hsum : 0 ≤ ∑ a ∈ A.attach,
      ‖integralEmbed (chosenLift phi hlifts a)‖ := by
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  linarith

theorem liftRadius_pos (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    0 < liftRadius phi hlifts :=
  zero_lt_one.trans_le (one_le_liftRadius phi hlifts)

theorem norm_chosenLift_le_liftRadius
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (a : A) :
    ‖integralEmbed (chosenLift phi hlifts a)‖ ≤
      liftRadius phi hlifts := by
  have hsum : ‖integralEmbed (chosenLift phi hlifts a)‖ ≤
      ∑ b ∈ A.attach, ‖integralEmbed (chosenLift phi hlifts b)‖ := by
    apply Finset.single_le_sum (fun b _ ↦ norm_nonneg
      (integralEmbed (chosenLift phi hlifts b)))
    exact Finset.mem_attach A a
  unfold liftRadius
  linarith

/-- The reciprocal radius as a nonnegative seminorm scalar. -/
def inverseLiftRadius (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) : ℝ≥0 :=
  ⟨(liftRadius phi hlifts)⁻¹,
    inv_nonneg.mpr (liftRadius_pos phi hlifts).le⟩

/-- Sup norm rescaled so all selected lifts lie in its unit ball. -/
def cubifiedSeminorm (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    Seminorm ℝ (Fin rank → ℝ) :=
  inverseLiftRadius phi hlifts • normSeminorm ℝ (Fin rank → ℝ)

@[simp] theorem cubifiedSeminorm_apply
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (x : Fin rank → ℝ) :
    cubifiedSeminorm phi hlifts x =
      (liftRadius phi hlifts)⁻¹ * ‖x‖ :=
  rfl

theorem cubifiedSeminorm_definite
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    IsDefinite (cubifiedSeminorm phi hlifts) := by
  intro x hx
  rw [cubifiedSeminorm_apply] at hx
  have hinv : (liftRadius phi hlifts)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (liftRadius_pos phi hlifts))
  exact norm_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hinv)

theorem chosenLift_mem_cubifiedUnitBall
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (a : A) :
    cubifiedSeminorm phi hlifts
        (integralEmbed (chosenLift phi hlifts a)) ≤ 1 := by
  rw [cubifiedSeminorm_apply,
    inv_mul_le_one₀ (liftRadius_pos phi hlifts)]
  exact norm_chosenLift_le_liftRadius phi hlifts a

theorem cubifiedSeminorm_admitsIndependent
    (hrank : 0 < rank) (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    AdmitsIndependent (cubifiedSeminorm phi hlifts) rank 1 := by
  refine ⟨standardIntegralPoint,
    linearIndependent_integralEmbed_standard, ?_⟩
  intro i
  rw [cubifiedSeminorm_apply, integralEmbed_standardIntegralPoint,
    Pi.basisFun_apply, Pi.norm_single, norm_one,
    mul_one]
  exact (inv_le_one₀ (liftRadius_pos phi hlifts)).mpr
    (one_le_liftRadius phi hlifts)

theorem cubifiedUnitBall_eq_closedBall
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    {x : Fin rank → ℝ | cubifiedSeminorm phi hlifts x ≤ 1} =
      Metric.closedBall 0 (liftRadius phi hlifts) := by
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  rw [cubifiedSeminorm_apply,
    inv_mul_le_one₀ (liftRadius_pos phi hlifts)]

theorem cubifiedUnitBall_volume_pos
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    0 < volume.real
      {x : Fin rank → ℝ | cubifiedSeminorm phi hlifts x ≤ 1} := by
  rw [cubifiedUnitBall_eq_closedBall]
  exact ENNReal.toReal_pos
    (Metric.measure_closedBall_pos volume 0
      (liftRadius_pos phi hlifts)).ne'
    measure_closedBall_lt_top.ne

/-- Any positive-rank finite-lift presentation becomes a common body
presentation, without changing its map or rank. -/
def cubifiedBodyPresentation
    (hrank : 0 < rank) (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a) :
    BodyPresentation A rank where
  rank_pos := hrank
  seminorm := cubifiedSeminorm phi hlifts
  definite := cubifiedSeminorm_definite phi hlifts
  full := cubifiedSeminorm_admitsIndependent hrank phi hlifts
  map := phi
  lifts := by
    intro a ha
    let a' : A := ⟨a, ha⟩
    exact ⟨chosenLift phi hlifts a',
      chosenLift_mem_cubifiedUnitBall phi hlifts a',
      map_chosenLift phi hlifts a'⟩
  bodyVolume_pos := cubifiedUnitBall_volume_pos phi hlifts

/-- A finite integral presentation whose image contains a set of at least
two integers necessarily has positive source rank.  This removes the last
rank side condition from the large-cardinality Section 9.1 initializer. -/
theorem rank_pos_of_one_lt_card_of_lifts
    (phi : IntegralPoint rank →+ ℤ)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint rank, phi z = a)
    (hcard : 1 < A.card) :
    0 < rank := by
  apply Nat.pos_of_ne_zero
  intro hrank
  subst rank
  have hall : ∀ a ∈ A, a = 0 := by
    intro a ha
    obtain ⟨z, hz⟩ := hlifts a ha
    have hz0 : z = 0 := Subsingleton.elim z 0
    rw [hz0, map_zero] at hz
    exact hz.symm
  have hsubset : A ⊆ {0} := by
    intro a ha
    simp [hall a ha]
  have hle : A.card ≤ ({0} : Finset ℤ).card :=
    Finset.card_le_card hsubset
  simp only [Finset.card_singleton] at hle
  omega

variable {r : ℕ} {B : Set (EuclideanSpace ℝ (Fin 1))}
  {a : Fin r → EuclideanSpace ℝ (Fin 1)}
  {D : GeometricData B a} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

/-- The normalized covering output of Section 9.1, equipped with a
definite full-dimensional body containing chosen lifts of the source set.
The body is only an admissible starting point; sharp volume control is
provided later by the Section 7/9 source seed. -/
def bodyPresentationOfCoveredNormalizedReplacement
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (hcard : 1 < A.card) :
    BodyPresentation A
      (Section91InitialPresentation.InitialPresentation.initialRank N) :=
  cubifiedBodyPresentation
    (rank_pos_of_one_lt_card_of_lifts
      (Section91IntegerPresentation.InitialPresentation.integerPresentationMap N)
      (Section91IntegerPresentation.InitialPresentation.exists_integerLift N)
      hcard)
    (Section91IntegerPresentation.InitialPresentation.integerPresentationMap N)
    (Section91IntegerPresentation.InitialPresentation.exists_integerLift N)

/-- The same initializer with its rank bundled for Section 4/9 minimal-rank
selection. -/
def rankedBodyPresentationOfCoveredNormalizedReplacement
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (hcard : 1 < A.card) :
    RankedBodyPresentation A :=
  ⟨Section91InitialPresentation.InitialPresentation.initialRank N,
    bodyPresentationOfCoveredNormalizedReplacement N hcard⟩

/-- The concrete Section 9.1 initializer obeys the advertised uniform rank
bound. -/
theorem rankedBodyPresentationOfCoveredNormalizedReplacement_rank_le
    (N : CoveredNormalizedReplacement (D := D)
      (K := Section90IntegerInitialization.integerSet A)
      (coverConstant := coverConstant) constant scale sigma)
    (hcard : 1 < A.card) :
    (rankedBodyPresentationOfCoveredNormalizedReplacement N hcard).1 ≤
      (1 + r - 1) + sigma * coverConstant :=
  Section91IntegerPresentation.InitialPresentation.integerPresentationRank_le N

end


end Erdos186.CFP.Bilu.Section91PresentationCubification

#print axioms
  Erdos186.CFP.Bilu.Section91PresentationCubification.cubifiedBodyPresentation
#print axioms
  Erdos186.CFP.Bilu.Section91PresentationCubification.bodyPresentationOfCoveredNormalizedReplacement
