/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.CoverDownPacking

/-!
# Ambient triangles outside an absorber

The initial availability family contains exactly triangles outside the bank
that use no absorber edge.  In particular, such triangles may use vertices of
the absorber: these triangles are indispensable for covering the non-absorber
edges incident with those vertices.  Containment in this family supplies all
structural parts of an outside packing except the substantive cover-down
assertion that its leave is supported on the flexible set.
-/

namespace Erdos207

open Finset

/-- No edge of `T` belongs to `H`. -/
def TriangleAvoidsGraph {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) (T : TripleOn V) : Prop :=
  ∀ u ∈ T.1, ∀ v ∈ T.1, u ≠ v → ¬ H.Adj u v

/-- Canonical ambient family for the absorber-relative constrained process. -/
noncomputable def outsideAvailableTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (B : TripleSystemOn V) :
    TripleSystemOn V := by
  classical
  exact (univ : Finset (TripleOn V)).filter fun T ↦
    T ∉ B ∧ TriangleAvoidsGraph H T

@[simp]
lemma mem_outsideAvailableTriangles_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {B : TripleSystemOn V}
    {T : TripleOn V} :
    T ∈ outsideAvailableTriangles H B ↔
      T ∉ B ∧ TriangleAvoidsGraph H T := by
  classical
  simp [outsideAvailableTriangles]

lemma disjoint_bank_of_subset_outsideAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {B P : TripleSystemOn V}
    (hP : P ⊆ outsideAvailableTriangles H B) : Disjoint P B := by
  rw [Finset.disjoint_left]
  intro T hTP hTB
  exact (mem_outsideAvailableTriangles_iff.mp (hP hTP)).1 hTB

lemma absorber_le_leave_of_subset_outsideAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {B P : TripleSystemOn V}
    (hP : P ⊆ outsideAvailableTriangles H B) : H ≤ leaveGraph P := by
  intro u v huv
  rw [leaveGraph_adj]
  refine ⟨huv.ne, ?_⟩
  rintro ⟨T, hTP, huT, hvT, _huv⟩
  exact (mem_outsideAvailableTriangles_iff.mp (hP hTP)).2
    u huT v hvT huv.ne huv

/-- A maximal legal packing in the canonical outside availability family
always exists and automatically has every structural property except
flexible support of the final leave. -/
theorem exists_maximal_outsidePacking
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (B : TripleSystemOn V) :
    ∃ P : TripleSystemOn V,
      IsPackingOn P ∧ Disjoint P B ∧
      AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q B) ∧
      H ≤ leaveGraph P ∧
      legalAvailable (absorberErdosForbiddenConfigurationsOn q B) P
        (outsideAvailableTriangles H B) = ∅ := by
  obtain ⟨P, hpacking, havoid, hPsub, hmax⟩ :=
    exists_maximal_absorberGreedyPacking q B
      (outsideAvailableTriangles H B)
  exact ⟨P, hpacking, disjoint_bank_of_subset_outsideAvailable hPsub,
    havoid, absorber_le_leave_of_subset_outsideAvailable hPsub, hmax⟩

/-- Adding the flexible-support conclusion to the canonical maximal packing
is exactly enough for `HasKSSSOutsidePacking`. -/
theorem hasKSSSOutsidePacking_of_maximal
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (hPsub : P ⊆ outsideAvailableTriangles H B)
    (havoid : AvoidsForbidden P
      (absorberErdosForbiddenConfigurationsOn q B))
    (hsupport : GraphSupportedOn
      (graphDifference (leaveGraph P) H) (X : Set V)) :
    HasKSSSOutsidePacking q H X B P := by
  exact ⟨hpacking, disjoint_bank_of_subset_outsideAvailable hPsub,
    havoid, absorber_le_leave_of_subset_outsideAvailable hPsub, hsupport⟩

end Erdos207
