/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohn
import ErdosProblems.Erdos186.CFP.Bilu.SaturatedFlag
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Rank reduction for the discrete John theorem

This file constructs the intrinsic saturated lattice carried by a finite set
of integral points.  Unlike `DiscreteJohn.SymmetricConvexBody`, this
construction does not assume that the surrounding convex set has nonempty
ambient interior.  Its rank is at most the ambient dimension, and a chosen
integral basis gives exact, injective integer coordinates for every point of
the finite set.

The construction is the algebraic part of the rank dichotomy in the
discrete John theorem.  The remaining geometric part is to show that the
pullback of a compact symmetric convex set to these coordinates is a
full-dimensional convex body and to prove the dimension-uniform box
sandwich there.
-/

namespace Erdos186

open scoped BigOperators

namespace DiscreteJohn
namespace RankReduction

open CFP.Bilu.SaturatedFlag
open Module

variable {d : ℕ}

/-- The full lattice in the rational span of the displayed integral points.
Taking the saturation, rather than their bare integer span, is what makes
the output the lattice of the relevant rational subspace. -/
def sectionLattice (points : Finset (LatticePoint d)) :
    Submodule ℤ (LatticePoint d) :=
  rationalSpanLattice (points : Set (LatticePoint d))

/-- The intrinsic lattice rank of a finite set of integral points. -/
noncomputable def sectionRank (points : Finset (LatticePoint d)) : ℕ :=
  Module.finrank ℤ (sectionLattice points)

/-- The intrinsic saturated lattice has rank at most the ambient rank. -/
theorem sectionRank_le (points : Finset (LatticePoint d)) :
    sectionRank points ≤ d := by
  simpa [sectionRank] using (sectionLattice points).finrank_le

/-- Every displayed point belongs to its saturated rational-span lattice. -/
theorem mem_sectionLattice {points : Finset (LatticePoint d)}
    {z : LatticePoint d} (hz : z ∈ points) :
    z ∈ sectionLattice points := by
  rw [sectionLattice, mem_rationalSpanLattice]
  apply Submodule.subset_span
  exact ⟨z, hz, rfl⟩

/-- A finite free basis of the intrinsic saturated lattice. -/
noncomputable def sectionBasis (points : Finset (LatticePoint d)) :
    Basis (Fin (sectionRank points)) ℤ (sectionLattice points) :=
  Module.finBasis ℤ (sectionLattice points)

/-- The intrinsic basis, regarded as integral vectors in the ambient
coordinate lattice. -/
noncomputable def sectionSteps (points : Finset (LatticePoint d)) :
    Fin (sectionRank points) → LatticePoint d :=
  fun i ↦ (sectionBasis points i : LatticePoint d)

/-- Coordinates of a point known to lie in the intrinsic lattice. -/
noncomputable def sectionCoordinates (points : Finset (LatticePoint d))
    (z : LatticePoint d) (hz : z ∈ sectionLattice points) :
    LatticePoint (sectionRank points) :=
  (sectionBasis points).equivFun ⟨z, hz⟩

/-- Synthesis in the intrinsic basis agrees with the ambient
`integerCombination`. -/
theorem sectionBasis_synthesis (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    ((sectionBasis points).equivFun.symm a : sectionLattice points) =
      integerCombination (sectionSteps points) a := by
  funext j
  rw [Basis.equivFun_symm_apply]
  simp [integerCombination, sectionSteps]

/-- Intrinsic coordinates synthesize back to the original ambient point. -/
theorem section_synthesis_coordinates (points : Finset (LatticePoint d))
    (z : LatticePoint d) (hz : z ∈ sectionLattice points) :
    integerCombination (sectionSteps points)
        (sectionCoordinates points z hz) = z := by
  rw [← sectionBasis_synthesis]
  exact congrArg Subtype.val
    ((sectionBasis points).equivFun.symm_apply_apply ⟨z, hz⟩)

/-- The intrinsic saturated-lattice basis is integer independent in the
ambient lattice. -/
theorem sectionSteps_integerIndependent
    (points : Finset (LatticePoint d)) :
    IntegerIndependent (sectionSteps points) := by
  intro a b hab
  apply (sectionBasis points).equivFun.symm.injective
  apply Subtype.ext
  rw [sectionBasis_synthesis, sectionBasis_synthesis]
  exact hab

/-- The intrinsic integral basis remains independent after embedding in
real coordinate space.  This is the determinant/nondegeneracy input for
the active full-rank volume branch. -/
theorem sectionSteps_realLinearIndependent
    (points : Finset (LatticePoint d)) :
    LinearIndependent ℝ
      (fun i ↦ CFP.Bilu.Mahler.integralEmbed (sectionSteps points i)) := by
  have hInt : LinearIndependent ℤ (sectionSteps points) := by
    exact (sectionBasis points).linearIndependent.map'
      (sectionLattice points).subtype (Submodule.ker_subtype _)
  have hReal : LinearIndependent ℝ
      (fun i ↦ algebraMap ℤ ℝ ∘ sectionSteps points i) :=
    linearIndependent_algebraMap_comp_iff.mpr hInt
  have heq : (fun i ↦ algebraMap ℤ ℝ ∘ sectionSteps points i) =
      (fun i ↦ CFP.Bilu.Mahler.integralEmbed (sectionSteps points i)) := by
    funext i j
    rfl
  rw [heq] at hReal
  exact hReal

/-- Synthesis from intrinsic coordinates, bundled in the saturated
submodule. -/
noncomputable def sectionSynthesisSubmodule
    (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) : sectionLattice points :=
  (sectionBasis points).equivFun.symm a

/-- Synthesis from intrinsic coordinates, as an ambient integral point. -/
noncomputable def sectionSynthesis (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) : LatticePoint d :=
  sectionSynthesisSubmodule points a

theorem sectionSynthesis_eq_integerCombination
    (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    sectionSynthesis points a =
      integerCombination (sectionSteps points) a :=
  sectionBasis_synthesis points a

theorem sectionSynthesis_mem (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    sectionSynthesis points a ∈ sectionLattice points :=
  (sectionSynthesisSubmodule points a).property

@[simp]
theorem sectionCoordinates_sectionSynthesis
    (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    sectionCoordinates points (sectionSynthesis points a)
      (sectionSynthesis_mem points a) = a := by
  exact (sectionBasis points).equivFun.apply_symm_apply a

/-- The finite set of intrinsic coordinates of the displayed points. -/
noncomputable def sectionCoordinatePoints
    (points : Finset (LatticePoint d)) :
    Finset (LatticePoint (sectionRank points)) :=
  points.attach.image fun z ↦
    sectionCoordinates points z.1 (mem_sectionLattice z.2)

@[simp]
theorem mem_sectionCoordinatePoints_iff
    (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    a ∈ sectionCoordinatePoints points ↔ sectionSynthesis points a ∈ points := by
  constructor
  · intro ha
    rw [sectionCoordinatePoints] at ha
    obtain ⟨z, _hz, hza⟩ := Finset.mem_image.mp ha
    have hs : sectionSynthesis points
        (sectionCoordinates points z.1 (mem_sectionLattice z.2)) = z.1 := by
      rw [sectionSynthesis_eq_integerCombination]
      exact section_synthesis_coordinates points z.1
        (mem_sectionLattice z.2)
    rw [← hza, hs]
    exact z.2
  · intro ha
    rw [sectionCoordinatePoints]
    apply Finset.mem_image.mpr
    let z : points := ⟨sectionSynthesis points a, ha⟩
    refine ⟨z, Finset.mem_attach points z, ?_⟩
    exact sectionCoordinates_sectionSynthesis points a

/-- Intrinsic synthesis is injective. -/
theorem sectionSynthesis_injective (points : Finset (LatticePoint d)) :
    Function.Injective (sectionSynthesis points) := by
  intro a b hab
  apply sectionSteps_integerIndependent points
  rw [← sectionSynthesis_eq_integerCombination,
    ← sectionSynthesis_eq_integerCombination]
  exact hab

/-- Passing to intrinsic saturated-lattice coordinates preserves the exact
number of displayed lattice points. -/
@[simp]
theorem card_sectionCoordinatePoints
    (points : Finset (LatticePoint d)) :
    (sectionCoordinatePoints points).card = points.card := by
  rw [sectionCoordinatePoints]
  calc
    (points.attach.image fun z ↦
        sectionCoordinates points z.1 (mem_sectionLattice z.2)).card =
        points.attach.card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      apply Subtype.ext
      have hx := congrArg (sectionSynthesis points) hxy
      simpa only [sectionSynthesis_eq_integerCombination,
        section_synthesis_coordinates] using hx
    _ = points.card := Finset.card_attach

variable {r factor : ℕ}

/-- Transport lattice steps in intrinsic coordinates back to the ambient
lattice section. -/
noncomputable def liftSteps (points : Finset (LatticePoint d))
    (steps : Fin r → LatticePoint (sectionRank points)) :
    Fin r → LatticePoint d :=
  fun i ↦ sectionSynthesis points (steps i)

/-- Integral linear combinations commute with intrinsic synthesis. -/
theorem integerCombination_liftSteps
    (points : Finset (LatticePoint d))
    (steps : Fin r → LatticePoint (sectionRank points))
    (a : LatticePoint r) :
    integerCombination (liftSteps points steps) a =
      sectionSynthesis points (integerCombination steps a) := by
  rw [sectionSynthesis_eq_integerCombination]
  funext j
  simp only [integerCombination, liftSteps,
    sectionSynthesis_eq_integerCombination, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The coefficient types of two symmetric GAPs with the same radii are
canonically identified, independently of their ambient dimensions. -/
def transportSymmetricCoord {d₁ d₂ : ℕ}
    (steps₁ : Fin r → LatticePoint d₁)
    (steps₂ : Fin r → LatticePoint d₂) (radii : Fin r → ℕ)
    (n : (symmetricGAP steps₁ radii).Coord) :
    (symmetricGAP steps₂ radii).Coord :=
  fun i ↦ ⟨n i, by simpa using (n i).isLt⟩

@[simp]
theorem transportSymmetricCoord_coe {d₁ d₂ : ℕ}
    (steps₁ : Fin r → LatticePoint d₁)
    (steps₂ : Fin r → LatticePoint d₂) (radii : Fin r → ℕ)
    (n : (symmetricGAP steps₁ radii).Coord) (i : Fin r) :
    (transportSymmetricCoord steps₁ steps₂ radii n i : ℕ) = n i := rfl

/-- The coordinate point of a symmetric GAP is preserved by intrinsic
synthesis. -/
theorem sectionSynthesis_symmetricGAP_coordPoint
    (points : Finset (LatticePoint d))
    (steps : Fin r → LatticePoint (sectionRank points))
    (radii : Fin r → ℕ) (n : (symmetricGAP steps radii).Coord) :
    sectionSynthesis points ((symmetricGAP steps radii).coordPoint n) =
      (symmetricGAP (liftSteps points steps) radii).coordPoint
        (transportSymmetricCoord steps (liftSteps points steps) radii n) := by
  rw [symmetricGAP_coordPoint, symmetricGAP_coordPoint]
  simpa using (integerCombination_liftSteps points steps
    (fun i ↦ (n i : ℤ) - (radii i : ℤ))).symm

/-- Membership in a symmetric GAP is preserved and reflected by the
intrinsic lattice embedding. -/
theorem sectionSynthesis_mem_symmetricGAP_iff
    (points : Finset (LatticePoint d))
    (steps : Fin r → LatticePoint (sectionRank points))
    (radii : Fin r → ℕ) (a : LatticePoint (sectionRank points)) :
    sectionSynthesis points a ∈
        (symmetricGAP (liftSteps points steps) radii).carrier ↔
      a ∈ (symmetricGAP steps radii).carrier := by
  constructor
  · intro ha
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp ha
    let n' := transportSymmetricCoord
      (liftSteps points steps) steps radii n
    apply GAP.mem_carrier_iff.mpr
    refine ⟨n', ?_⟩
    apply sectionSynthesis_injective points
    have hcoord := sectionSynthesis_symmetricGAP_coordPoint
      points steps radii n'
    rw [show transportSymmetricCoord steps (liftSteps points steps)
        radii n' = n by
      funext i
      apply Fin.ext
      rfl] at hcoord
    rw [hcoord, hn]
  · intro ha
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp ha
    let n' := transportSymmetricCoord
      steps (liftSteps points steps) radii n
    apply GAP.mem_carrier_iff.mpr
    refine ⟨n', ?_⟩
    rw [← sectionSynthesis_symmetricGAP_coordPoint, hn]

/-- A discrete-John certificate in the intrinsic coordinate lattice lifts
to a certificate of the same rank, factor, and radii in the ambient
lattice.  This is the checked algebraic rank-reduction bridge. -/
noncomputable def liftCertificate
    (points : Finset (LatticePoint d))
    (C : Certificate (sectionCoordinatePoints points) r factor) :
    Certificate points r factor where
  steps := liftSteps points C.steps
  radii := C.radii
  factor_pos := C.factor_pos
  independent := by
    intro a b hab
    apply C.independent
    apply sectionSynthesis_injective points
    rw [← integerCombination_liftSteps,
      ← integerCombination_liftSteps]
    exact hab
  inner_subset := by
    intro z hz
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp hz
    let n' := transportSymmetricCoord (liftSteps points C.steps) C.steps
      (shrinkRadii factor C.radii) n
    let a : LatticePoint (sectionRank points) := C.inner.coordPoint n'
    have haInner : a ∈ C.inner.carrier :=
      GAP.mem_carrier_iff.mpr ⟨n', rfl⟩
    have haPoints : a ∈ sectionCoordinatePoints points :=
      C.inner_carrier_subset haInner
    rw [mem_sectionCoordinatePoints_iff] at haPoints
    have hmap : sectionSynthesis points a = z := by
      change sectionSynthesis points
          ((symmetricGAP C.steps (shrinkRadii factor C.radii)).coordPoint n') = z
      have hcoord := sectionSynthesis_symmetricGAP_coordPoint points C.steps
        (shrinkRadii factor C.radii) n'
      rw [show transportSymmetricCoord C.steps (liftSteps points C.steps)
          (shrinkRadii factor C.radii) n' = n by
        funext i
        apply Fin.ext
        rfl] at hcoord
      rw [hcoord]
      exact hn
    rwa [hmap] at haPoints
  subset_outer := by
    intro z hz
    let a : LatticePoint (sectionRank points) :=
      sectionCoordinates points z (mem_sectionLattice hz)
    have hsa : sectionSynthesis points a = z := by
      rw [sectionSynthesis_eq_integerCombination]
      exact section_synthesis_coordinates points z
        (mem_sectionLattice hz)
    have haPoints : a ∈ sectionCoordinatePoints points := by
      rw [mem_sectionCoordinatePoints_iff, hsa]
      exact hz
    have haOuter : a ∈ C.outer.carrier :=
      C.subset_outer_carrier haPoints
    change a ∈ (symmetricGAP C.steps C.radii).carrier at haOuter
    have hs := (sectionSynthesis_mem_symmetricGAP_iff
      points C.steps C.radii a).2 haOuter
    rwa [hsa] at hs

end RankReduction
end DiscreteJohn
end Erdos186
