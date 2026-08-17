/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.CrowdSchedule
import ErdosProblems.Erdos636.OuterSwitchingPath

/-!
# Graph-facing bridge for the canonical crowd schedule

This file specializes the natural-valued schedule to matching-cell degrees
along an `OuterSwitchingPath.RawPath`.  Its output is stronger than the
older abstract `CrowdSchedule` interface: besides a `CrowdedPath`, it
retains the exact boundary set, fixed-anchor fact on regular transitions,
and separate regular/boundary degree-motion bounds.
-/

open SimpleGraph

namespace Erdos636.OuterSwitchingPath

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma intAbs_natCast_sub_eq_natDist (x y : ℕ) :
    |(x : ℤ) - (y : ℤ)| = Nat.dist x y := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy, abs_of_nonpos]
    · omega
    · omega
  · rw [Nat.dist_eq_sub_of_le_right hyx, abs_of_nonneg]
    · omega
    · omega

/-- Degree of a matching particle along the raw switching path. -/
def matchingDegreeTrajectory
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) (x : Particle S) : ℕ :=
  degreeInto G (P.W i) x.1

/-- Forget the schedule metadata and retain the graph-facing crowded path. -/
noncomputable def crowdedPathOfCanonicalSchedule
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S)
    (A : Crowd.CanonicalNatCrowdSchedule nW blockLength threshold window step spread
      (matchingDegreeTrajectory P)) :
    CrowdedPath S threshold window where
  raw := P
  anchor := fun i ↦ (A.anchorAt i).1
  crowd := fun i ↦ (A.crowdAt i).image Subtype.val
  anchor_mem := fun i hi ↦ (A.anchorAt i).2
  crowd_subset := by
    intro i hi x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  crowd_large := by
    intro i hi
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact A.crowd_large i hi
  degree_window := by
    intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have h := A.crowd_near i hi y hy
    rw [intAbs_natCast_sub_eq_natDist]
    exact_mod_cast h

/-- A crowded path together with the motion information needed by the
outer separated-switching estimate. -/
structure ScheduledCrowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (blockLength threshold window step spread : ℕ) where
  crowded : CrowdedPath S threshold window
  boundary_subset : Crowd.canonicalBoundary nW blockLength ⊆ Finset.range nW
  boundary_card : (Crowd.canonicalBoundary nW blockLength).card ≤ nW / blockLength
  anchor_fixed : ∀ i < nW, i ∉ Crowd.canonicalBoundary nW blockLength →
    crowded.anchor (i + 1) = crowded.anchor i
  regular_degree_motion : ∀ i < nW,
    i ∉ Crowd.canonicalBoundary nW blockLength →
      |(degreeInto G (crowded.W (i + 1)) (crowded.anchor (i + 1)) : ℤ) -
        degreeInto G (crowded.W i) (crowded.anchor i)| ≤ step
  boundary_degree_motion : ∀ i ∈ Crowd.canonicalBoundary nW blockLength,
    |(degreeInto G (crowded.W (i + 1)) (crowded.anchor (i + 1)) : ℤ) -
      degreeInto G (crowded.W i) (crowded.anchor i)| ≤ spread + step

/-- Promote a canonical degree schedule to the graph-facing scheduled
crowded path. -/
noncomputable def scheduledCrowdedPathOfCanonicalSchedule
    {G : SimpleGraph V} {scale nW ell K blockLength threshold window step spread : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S)
    (A : Crowd.CanonicalNatCrowdSchedule nW blockLength threshold window step spread
      (matchingDegreeTrajectory P)) :
    ScheduledCrowdedPath S blockLength threshold window step spread where
  crowded := crowdedPathOfCanonicalSchedule P A
  boundary_subset := A.boundary_subset
  boundary_card := A.boundary_card
  anchor_fixed := by
    intro i hi hiBoundary
    change (A.anchorAt (i + 1)).1 = (A.anchorAt i).1
    apply congrArg Subtype.val
    have hidx := Crowd.canonicalBlockIndex_succ_eq_of_not_mem_boundary
      (tau := nW) (blockLength := blockLength) (i := i)
      A.blockLength_pos hi hiBoundary
    rw [congrFun A.anchorAt_eq (i + 1), congrFun A.anchorAt_eq i, hidx]
  regular_degree_motion := by
    intro i hi hiBoundary
    change |(matchingDegreeTrajectory P (i + 1) (A.anchorAt (i + 1)) : ℤ) -
      matchingDegreeTrajectory P i (A.anchorAt i)| ≤ step
    rw [intAbs_natCast_sub_eq_natDist]
    exact_mod_cast A.regular_motion i hi hiBoundary
  boundary_degree_motion := by
    intro i hiBoundary
    change |(matchingDegreeTrajectory P (i + 1) (A.anchorAt (i + 1)) : ℤ) -
      matchingDegreeTrajectory P i (A.anchorAt i)| ≤ spread + step
    rw [intAbs_natCast_sub_eq_natDist]
    exact_mod_cast A.boundary_motion i hiBoundary

/-- Graph-facing no-placeholder endpoint: the finite bounded-trajectory
premises directly produce a crowded outer path with its exceptional-motion
certificate. -/
theorem exists_scheduledCrowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (P : RawPath S) (blockLength : ℕ)
    (base : Fin (Crowd.canonicalBlockCount nW blockLength) → ℕ → ℕ)
    (span width threshold window stride travel step spread : ℕ)
    (hblock : 0 < blockLength) (hwidth : 0 < width) (hstride : 0 < stride)
    (controlled : ∀ q j,
      j * stride ≤ Crowd.canonicalBlockLast nW blockLength q →
        ∀ x : Particle S,
          base q j ≤ matchingDegreeTrajectory P
              (Crowd.canonicalGlobalTime blockLength q (j * stride)) x ∧
            matchingDegreeTrajectory P
              (Crowd.canonicalGlobalTime blockLength q (j * stride)) x <
                base q j + span)
    (travelBound : ∀ q t,
      t ≤ Crowd.canonicalBlockLast nW blockLength q →
        ∀ x : Particle S,
          Nat.dist
            (matchingDegreeTrajectory P (Crowd.canonicalGlobalTime blockLength q t) x)
            (matchingDegreeTrajectory P
              (Crowd.canonicalGlobalTime blockLength q ((t / stride) * stride)) x) ≤
              travel)
    (hradius : width + 2 * travel ≤ window)
    (hcount : ∀ q,
      (Crowd.canonicalBlockLast nW blockLength q / stride + 1) *
          Crowd.natBucketCount span width * threshold < Fintype.card (Particle S))
    (oneStep : ∀ i < nW, ∀ x : Particle S,
      Nat.dist (matchingDegreeTrajectory P (i + 1) x)
        (matchingDegreeTrajectory P i x) ≤ step)
    (sameTimeSpread : ∀ i ≤ nW, ∀ x y : Particle S,
      Nat.dist (matchingDegreeTrajectory P i x)
        (matchingDegreeTrajectory P i y) ≤ spread) :
    Nonempty (ScheduledCrowdedPath S blockLength threshold window step spread) := by
  obtain ⟨A⟩ := Crowd.exists_canonicalNatCrowdSchedule nW blockLength
    (matchingDegreeTrajectory P) base span width threshold window stride travel step spread
      hblock hwidth hstride controlled travelBound hradius hcount oneStep sameTimeSpread
  exact ⟨scheduledCrowdedPathOfCanonicalSchedule P A⟩

end

end Erdos636.OuterSwitchingPath
