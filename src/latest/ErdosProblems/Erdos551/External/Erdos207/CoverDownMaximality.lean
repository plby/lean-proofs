/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.OutsideAvailability
import ErdosProblems.Erdos551.External.Erdos207.AbsorberPadding

/-!
# Maximality criterion for the outside cover-down

The constrained process need not be mentioned once it has reached a maximal
legal packing.  If every uncovered edge outside the flexible set occurs in
one still-legal ambient triangle, maximality forces the whole residual graph
outside the absorber to be supported on the flexible set.
-/

namespace Erdos207

open Finset

/-- Every edge of the leave outside `H` that is not wholly supported on `X`
has an ambient legal triangle extension. -/
def OutsideLeaveEdgesLegallyExtendable
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (H : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, (graphDifference (leaveGraph P) H).Adj u v →
    (u ∉ X ∨ v ∉ X) →
      ∃ T : TripleOn V, T ∈ A ∧ u ∈ T.1 ∧ v ∈ T.1 ∧
        IsLegalExtension F P T

theorem graphSupportedOn_of_maximal_legal
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V}
    (hmax : legalAvailable F P A = ∅)
    (hext : OutsideLeaveEdgesLegallyExtendable F A P H X) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  intro u v huv
  constructor
  · by_contra huX
    obtain ⟨T, hTA, _huT, _hvT, hTlegal⟩ :=
      hext huv (Or.inl huX)
    have hTavailable : T ∈ legalAvailable F P A :=
      mem_legalAvailable_iff.mpr ⟨hTA, hTlegal⟩
    simpa [hmax] using hTavailable
  · by_contra hvX
    obtain ⟨T, hTA, _huT, _hvT, hTlegal⟩ :=
      hext huv (Or.inr hvX)
    have hTavailable : T ∈ legalAvailable F P A :=
      mem_legalAvailable_iff.mpr ⟨hTA, hTlegal⟩
    simpa [hmax] using hTavailable

/-- The exact extension condition needed to upgrade the canonical maximal
constrained packing to a KSSS outside packing. -/
theorem exists_ksssOutsidePacking_of_maximal_extensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V)
    (hext : ∀ P : TripleSystemOn V,
      IsPackingOn P →
      AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q B) →
      P ⊆ outsideAvailableTriangles H B →
      legalAvailable (absorberErdosForbiddenConfigurationsOn q B) P
        (outsideAvailableTriangles H B) = ∅ →
      OutsideLeaveEdgesLegallyExtendable
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) P H X) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  obtain ⟨P, hpacking, havoid, hPsub, hmax⟩ :=
    exists_maximal_absorberGreedyPacking q B
      (outsideAvailableTriangles H B)
  refine ⟨P, hasKSSSOutsidePacking_of_maximal hpacking hPsub havoid ?_⟩
  exact graphSupportedOn_of_maximal_legal hmax
    (hext P hpacking havoid hPsub hmax)

end Erdos207
