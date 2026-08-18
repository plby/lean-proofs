/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91InitialPresentation

/-!
# Standard integral coordinates for the Section 9.1 presentation

The lattice produced by the covering step is initially written as the
product of the coordinate section lattice and one copy of `ℤ` for every
covering centre.  This file chooses a basis of that product with exactly
the rank recorded in `InitialPresentation.initialRank`.  Consequently the
initial presentation becomes an additive map from a literal standard
integral lattice `ℤ^initialRank`, without changing its image or its rank
bound.

This is the algebraic interface needed by the primitive-kernel descent of
Section 9.2.
-/

namespace Erdos186.CFP.Bilu.Section91InitialCoordinates

open Proposition75Data Proposition75Case2 Proposition75Case2Construction
open Section9Replacement Section9ContainerIntegration
open Section91CoveringEnlargement Section9NormalizedReplacement
open Section91InitialPresentation Section91InitialPresentation.InitialPresentation
open SubspaceLattice
open Module

noncomputable section

variable {m r : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {a : Fin r → EuclideanSpace ℝ (Fin m)}
  {D : GeometricData B a}
  {K : Finset (Mahler.IntegralPoint m)} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

namespace InitialPresentation

variable (N : CoveredNormalizedReplacement (D := D) (K := K)
  (coverConstant := coverConstant) constant scale sigma)

/-- The literal coordinate section lattice has a basis indexed by its real
dimension.  Saturation supplies discreteness, and the full-span theorem
identifies its integral rank with that dimension. -/
theorem nonempty_coordinateIntegralBasis : Nonempty
    (Basis (Fin (finrank ℝ D.C0)) ℤ
      (integralPoints (coordinateC0 D))) := by
  classical
  obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation_coordinateC0 D
  letI hdiscRow : DiscreteTopology P.rowLattice := by
    change DiscreteTopology
      (Submodule.span ℤ (Set.range P.rowBasis))
    infer_instance
  letI : DiscreteTopology (integralPoints (coordinateC0 D)) :=
    hSat ▸ hdiscRow
  letI : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
    ⟨span_coordinateIntegralPoints_eq_top D⟩
  letI : Module.Free ℤ (integralPoints (coordinateC0 D)) :=
    ZLattice.module_free ℝ _
  letI : Module.Finite ℤ (integralPoints (coordinateC0 D)) :=
    ZLattice.module_finite ℝ _
  exact ⟨(Module.Free.chooseBasis ℤ
      (integralPoints (coordinateC0 D))).reindex
    (Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ,
        finrank_coordinateC0 D, Fintype.card_fin]))⟩

/-- A chosen basis of the literal coordinate section lattice. -/
noncomputable def coordinateIntegralBasis :
    Basis (Fin (finrank ℝ D.C0)) ℤ
      (integralPoints (coordinateC0 D)) :=
  Classical.choice (nonempty_coordinateIntegralBasis (D := D))

/-- A basis of the full direct-product lattice produced by Section 9.1,
indexed by its recorded initial rank. -/
noncomputable def initialBasis :
    Basis (Fin (initialRank N)) ℤ (InitialLattice N) :=
  ((coordinateIntegralBasis (D := D)).prod
      (Pi.basisFun ℤ N.cover.centers)).reindex
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
        Fintype.card_fin]
      rfl))

/-- Standard integral coordinates on the initial Section 9.1 lattice. -/
noncomputable def initialCoordinateEquiv :
    InitialLattice N ≃ₗ[ℤ] Mahler.IntegralPoint (initialRank N) :=
  (initialBasis N).equivFun

/-- The initial appropriate map, now with literal source `ℤ^initialRank`. -/
noncomputable def coordinatePresentationMap :
    Mahler.IntegralPoint (initialRank N) →+
      Mahler.IntegralPoint m :=
  (presentationMap (D := D) N).comp
    (initialCoordinateEquiv N).symm.toLinearMap.toAddHom

@[simp] theorem coordinatePresentationMap_initialCoordinateEquiv
    (q : InitialLattice N) :
    coordinatePresentationMap N (initialCoordinateEquiv N q) =
      presentationMap (D := D) N q := by
  simp [coordinatePresentationMap]

/-- Every point of `K` has a lift in the standard integral coordinates. -/
theorem exists_coordinateLift
    (x : Mahler.IntegralPoint m) (hx : x ∈ K) :
    ∃ q : Mahler.IntegralPoint (initialRank N),
      coordinatePresentationMap N q = x := by
  obtain ⟨q, hq⟩ := exists_initialLift N x hx
  exact ⟨initialCoordinateEquiv N q, by simpa using hq⟩

/-- The image of the standard-coordinate presentation contains `K`. -/
theorem subset_range_coordinatePresentationMap :
    (K : Set (Mahler.IntegralPoint m)) ⊆
      Set.range (coordinatePresentationMap N) := by
  intro x hx
  exact exists_coordinateLift N x hx

/-- The source-rank estimate survives passage to standard coordinates. -/
theorem coordinateRank_le :
    initialRank N ≤ (m + r - 1) + sigma * coverConstant :=
  initialRank_le N

end InitialPresentation

end

end Erdos186.CFP.Bilu.Section91InitialCoordinates

#print axioms Erdos186.CFP.Bilu.Section91InitialCoordinates.InitialPresentation.exists_coordinateLift
#print axioms Erdos186.CFP.Bilu.Section91InitialCoordinates.InitialPresentation.subset_range_coordinatePresentationMap
#print axioms Erdos186.CFP.Bilu.Section91InitialCoordinates.InitialPresentation.coordinateRank_le
