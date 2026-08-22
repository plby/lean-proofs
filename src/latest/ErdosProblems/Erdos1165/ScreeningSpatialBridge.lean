/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ScreeningInstantiation
import ErdosProblems.Erdos1165.SpatialInsertionFiber

/-!
# Spatial insertion-fibre bridge for HLOZ screening

This small module keeps the stable numerical screening instantiation separate
from the actively developed spatial insertion fibre.  It records the three
deterministic identifications needed before the remaining canonical-walk
conditional estimates can be proved by disintegration.
-/

open scoped BigOperators

namespace Erdos1165.ScreeningSpatialBridge

open NegativeBinomial PathInsertion ScreeningInstantiation

/-- The actual spatial-domino failure total has exactly the HLOZ
negative-binomial mass after fixing the external word. -/
theorem spatialDominoTotal_conditionalMass_eq_hlozMass
    {o : LazyDecomposition.Orientation} {i : ℕ} (x : Point)
    (r : Fin i → PathInsertion.RetainedBlock o)
    (b : SpatialInsertionFiber.ExternalDomino x r) (ℓ : ℕ) :
    fixedExternalJointMass
          (SpatialInsertionFiber.dominoExternalMultiplicity x r b) ℓ /
        fixedExternalMarginalMass
          (SpatialInsertionFiber.dominoExternalMultiplicity x r b) =
      hlozMass (SpatialInsertionFiber.dominoExternalMultiplicity x r b) ℓ := by
  simpa only [hlozMass, hlozSuccess] using
    SpatialInsertionFiber.dominoTotal_conditionalMass x r b ℓ

/-- HLOZ (6.8) on a finite external fibre: imposing the level/favorite
cutoff factors the unnormalized insertion density over actual dominoes. -/
theorem spatialConditionedMass_factorization
    {o : LazyDecomposition.Orientation} {i : ℕ} (x : Point)
    (r : Fin i → PathInsertion.RetainedBlock o) (m : ℕ)
    (distinguished : Finset Point) (q : Fin (i + 1) → ℕ) :
    SpatialInsertionFiber.conditionedGapVectorMass x r m distinguished q =
      ∏ b : SpatialInsertionFiber.ExternalDomino x r,
        SpatialInsertionFiber.conditionedDominoCoordinateMass
          x r m distinguished q b :=
  SpatialInsertionFiber.conditionedGapVectorMass_factorization
    x r m distinguished q

/-- The actual endpoint local-time inequalities away from old favorite
dominoes are precisely the coordinatewise spatial truncations. -/
theorem spatialActualLevelCondition_iff_dominoTruncation
    {o : LazyDecomposition.Orientation} {i : ℕ} (x : Point)
    (r : Fin i → PathInsertion.RetainedBlock o)
    (hx : SpatialInsertionFiber.OrientationCompatible o x)
    (m : ℕ) (distinguished : Finset Point) (q : Fin (i + 1) → ℕ) :
    SpatialInsertionFiber.ActualEndpointsBelowLevelAway
        x r m distinguished q ↔
      SpatialInsertionFiber.DominoTruncation x r m distinguished q :=
  SpatialInsertionFiber.actualEndpointsBelowLevelAway_iff_dominoTruncation
    x r m distinguished q
      (SpatialInsertionFiber.baseMiddleDisjoint_of_compatible x r hx)

end Erdos1165.ScreeningSpatialBridge
