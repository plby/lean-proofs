/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond
import ErdosProblems.Erdos186.CFP.Bilu.Section4UniformVolumeDecay

/-!
# Bilu Section 4: the bounded-cardinality initial presentation

For a nonempty finite integer set `A`, give every element its own formal
integral coordinate.  The coordinate homomorphism sends the corresponding
standard basis vector to that element of `A`.  The sup-norm unit cube
contains all these literal lifts, is definite and lattice-thick, and has
volume exactly `2 ^ |A|`.

When `|A|` is below the fixed source cutoff this is a uniform initial body.
Any additive collisions are subsequently removed by the same primitive
kernel descent used in the large-cardinality branch.
-/

namespace Erdos186.CFP.Bilu.Section4SmallCardinality

open scoped BigOperators ENNReal
open Set MeasureTheory
open Mahler MinkowskiSecond

noncomputable section

set_option autoImplicit false

/-- A cardinality-normalized enumeration of `A`. -/
def coordinateEquiv (A : Finset ℤ) : A ≃ Fin A.card :=
  (Fintype.equivFin A).trans (finCongr (Fintype.card_coe A))

/-- The element of `A` indexed by a standard coordinate. -/
def coordinateValue (A : Finset ℤ) (i : Fin A.card) : ℤ :=
  (coordinateEquiv A).symm i

/-- Formal-coordinate presentation map. -/
def coordinateMap (A : Finset ℤ) :
    IntegralPoint A.card →+ ℤ where
  toFun z := ∑ i, z i * coordinateValue A i
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The coordinate assigned to an element of `A`. -/
def coordinateIndex (A : Finset ℤ) (a : A) : Fin A.card :=
  coordinateEquiv A a

/-- Literal standard-basis lift of a source element. -/
def coordinateLift (A : Finset ℤ) (a : A) : IntegralPoint A.card :=
  Pi.single (coordinateIndex A a) 1

@[simp] theorem coordinateValue_coordinateIndex
    (A : Finset ℤ) (a : A) :
    coordinateValue A (coordinateIndex A a) = a := by
  simp [coordinateValue, coordinateIndex]

@[simp] theorem coordinateMap_coordinateLift
    (A : Finset ℤ) (a : A) :
  coordinateMap A (coordinateLift A a) = a := by
  classical
  simp [coordinateMap, coordinateLift, Pi.single_apply]

/-- The sup-norm gauge of the standard cube. -/
def cubeSeminorm (A : Finset ℤ) :
    Seminorm ℝ (Fin A.card → ℝ) :=
  normSeminorm ℝ (Fin A.card → ℝ)

@[simp] theorem cubeSeminorm_apply
    (A : Finset ℤ) (x : Fin A.card → ℝ) :
    cubeSeminorm A x = ‖x‖ := rfl

theorem cubeSeminorm_definite (A : Finset ℤ) :
    IsDefinite (cubeSeminorm A) := by
  intro x hx
  exact norm_eq_zero.mp hx

/-- Every source element has a lift in the unit cube. -/
theorem coordinateLift_mem_unitBall
    (A : Finset ℤ) (a : A) :
    cubeSeminorm A (integralEmbed (coordinateLift A a)) ≤ 1 := by
  have hembed : integralEmbed (coordinateLift A a) =
      Pi.single (coordinateIndex A a) (1 : ℝ) := by
    classical
    ext i
    by_cases hi : coordinateIndex A a = i
    · subst i
      simp [coordinateLift, integralEmbed]
    · simp [coordinateLift, integralEmbed, hi]
  rw [cubeSeminorm_apply, hembed, Pi.norm_single]
  norm_num

/-- The standard integral basis witnesses full-rank thickness of the cube.
-/
theorem cubeSeminorm_admitsIndependent (A : Finset ℤ) :
    AdmitsIndependent (cubeSeminorm A) A.card 1 := by
  refine ⟨standardIntegralPoint,
    linearIndependent_integralEmbed_standard, ?_⟩
  intro i
  rw [cubeSeminorm_apply, integralEmbed_standardIntegralPoint,
    Pi.basisFun_apply, Pi.norm_single]
  norm_num

/-- The sup-norm unit ball is the literal product cube. -/
theorem cubeSeminorm_unitBall
    (A : Finset ℤ) (hA : A.Nonempty) :
    {x : Fin A.card → ℝ | cubeSeminorm A x ≤ 1} =
      Set.Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
  let : Nonempty (Fin A.card) := Fin.pos_iff_nonempty.mp hA.card_pos
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  rw [cubeSeminorm_apply, pi_norm_le_iff_of_nonempty,
    Pi.le_def, Pi.le_def]
  simp only [Real.norm_eq_abs, abs_le, forall_and]

/-- Exact volume of the formal-coordinate unit cube. -/
theorem volume_cubeSeminorm_unitBall
    (A : Finset ℤ) (hA : A.Nonempty) :
    volume {x : Fin A.card → ℝ | cubeSeminorm A x ≤ 1} =
      (2 : ENNReal) ^ A.card := by
  rw [cubeSeminorm_unitBall A hA, Real.volume_Icc_pi]
  norm_num [ENNReal.ofReal_ofNat]

/-- Complete initial presentation used on the bounded-cardinality branch.
It deliberately does not assert enlarged injectivity: primitive-kernel
descent removes precisely the additive relations that obstruct it. -/
structure SmallCardInitialPresentation (A : Finset ℤ) where
  rank : ℕ
  rank_eq_card : rank = A.card
  rank_pos : 0 < rank
  seminorm : Seminorm ℝ (Fin rank → ℝ)
  definite : IsDefinite seminorm
  full : AdmitsIndependent seminorm rank 1
  map : IntegralPoint rank →+ ℤ
  lifts : ∀ a ∈ A, ∃ z : IntegralPoint rank,
    seminorm (integralEmbed z) ≤ 1 ∧ map z = a
  unitBall_volume :
    volume {x : Fin rank → ℝ | seminorm x ≤ 1} =
      (2 : ENNReal) ^ A.card

/-- Canonical formal-coordinate initializer. -/
def smallCardInitialPresentation
    (A : Finset ℤ) (hA : A.Nonempty) :
    SmallCardInitialPresentation A where
  rank := A.card
  rank_eq_card := rfl
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
  unitBall_volume := volume_cubeSeminorm_unitBall A hA

/-- Below a fixed cutoff, the initial cube volume has a uniform power-of-two
bound. -/
theorem unitBall_volume_le_threshold
    {A : Finset ℤ} (hA : A.Nonempty) {threshold : ℕ}
    (hcard : A.card ≤ threshold) :
    volume {x : Fin A.card → ℝ | cubeSeminorm A x ≤ 1} ≤
      (2 : ENNReal) ^ threshold := by
  rw [volume_cubeSeminorm_unitBall A hA]
  exact pow_le_pow_right₀ (by norm_num) hcard

end

end Erdos186.CFP.Bilu.Section4SmallCardinality

#print axioms
  Erdos186.CFP.Bilu.Section4SmallCardinality.coordinateMap_coordinateLift
#print axioms
  Erdos186.CFP.Bilu.Section4SmallCardinality.volume_cubeSeminorm_unitBall
#print axioms
  Erdos186.CFP.Bilu.Section4SmallCardinality.smallCardInitialPresentation
