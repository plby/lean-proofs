/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsideCandidateCount

/-!
# Counting forbidden-completion obstructions

A prospective triangle is forbidden precisely when it is contained in an
active forbidden configuration, meaning that every other triangle of that
configuration has already been selected.  This file turns that statement
into exact finite cardinal inequalities.  The probabilistic part of KSSS is
therefore reduced to bounding active rooted configurations.
-/

namespace Erdos207

open Finset

/-- Forbidden configurations which are one triangle away from lying in the
chosen family. -/
noncomputable def activeForbiddenConfigurations
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) :
    ForbiddenFamilyOn V := by
  classical
  exact F.filter fun S ↦ ∃ T ∈ S, S.erase T ⊆ P

@[simp]
lemma mem_activeForbiddenConfigurations_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P S : TripleSystemOn V} :
    S ∈ activeForbiddenConfigurations F P ↔
      S ∈ F ∧ ∃ T ∈ S, S.erase T ⊆ P := by
  classical
  simp [activeForbiddenConfigurations]

/-- Active forbidden configurations whose missing triangle contains a fixed
pair.  This is the rooted threat count controlled by KSSS well-spreadness. -/
noncomputable def rootedActiveForbiddenConfigurations
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    ForbiddenFamilyOn V := by
  classical
  exact F.filter fun S ↦ ∃ T ∈ S,
    u ∈ T.1 ∧ v ∈ T.1 ∧ S.erase T ⊆ P

@[simp]
lemma mem_rootedActiveForbiddenConfigurations_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P S : TripleSystemOn V} {u v : V} :
    S ∈ rootedActiveForbiddenConfigurations F P u v ↔
      S ∈ F ∧ ∃ T ∈ S,
        u ∈ T.1 ∧ v ∈ T.1 ∧ S.erase T ⊆ P := by
  classical
  simp [rootedActiveForbiddenConfigurations]

/-- All triangles completing at least one forbidden configuration. -/
noncomputable def forbiddenCompletionTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) :
    TripleSystemOn V := by
  classical
  exact univ.filter fun T ↦ CompletesForbidden F P T

@[simp]
lemma mem_forbiddenCompletionTriangles_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {T : TripleOn V} :
    T ∈ forbiddenCompletionTriangles F P ↔ CompletesForbidden F P T := by
  classical
  simp [forbiddenCompletionTriangles]

/-- Every completing triangle lies in the union of the active forbidden
configurations. -/
lemma forbiddenCompletionTriangles_subset_active_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} :
    forbiddenCompletionTriangles F P ⊆
      (activeForbiddenConfigurations F P).biUnion id := by
  intro T hT
  obtain ⟨S, hSF, hTS, hSerase⟩ :=
    mem_forbiddenCompletionTriangles_iff.mp hT
  exact mem_biUnion.mpr ⟨S,
    mem_activeForbiddenConfigurations_iff.mpr
      ⟨hSF, T, hTS, hSerase⟩, hTS⟩

/-- Union-bound count for completing triangles. -/
theorem card_forbiddenCompletionTriangles_le_sum_active
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} :
    (forbiddenCompletionTriangles F P).card ≤
      ∑ S ∈ activeForbiddenConfigurations F P, S.card := by
  calc
    (forbiddenCompletionTriangles F P).card ≤
        ((activeForbiddenConfigurations F P).biUnion id).card :=
      card_le_card forbiddenCompletionTriangles_subset_active_biUnion
    _ ≤ ∑ S ∈ activeForbiddenConfigurations F P, S.card :=
      card_biUnion_le

/-- Third-vertex forbidden blockers inject into the global set of completing
triangles. -/
theorem card_forbiddenBlockedThirdVertices_le_completionTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (forbiddenBlockedThirdVertices F A P huv).card ≤
      (forbiddenCompletionTriangles F P).card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  have hsub : (forbiddenBlockedThirdVertices F A P huv).map e ⊆
      forbiddenCompletionTriangles F P := by
    intro T hT
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
    exact mem_forbiddenCompletionTriangles_iff.mpr
      (mem_forbiddenBlockedThirdVertices_iff.mp hw).2
  simpa using card_le_card hsub

/-- Exact rooted-configuration bound for the forbidden third-vertex loss. -/
theorem card_forbiddenBlockedThirdVertices_le_sum_active
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (forbiddenBlockedThirdVertices F A P huv).card ≤
      ∑ S ∈ activeForbiddenConfigurations F P, S.card :=
  (card_forbiddenBlockedThirdVertices_le_completionTriangles
    (F := F) (A := A) (P := P) huv).trans
      card_forbiddenCompletionTriangles_le_sum_active

/-- A forbidden third-vertex blocker belongs to the union of the active
configurations rooted at the displayed pair. -/
lemma mapped_forbiddenBlocked_subset_rooted_active_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    let e : ThirdVertex u v ↪ TripleOn V :=
      ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
    (forbiddenBlockedThirdVertices F A P huv).map e ⊆
      (rootedActiveForbiddenConfigurations F P u v).biUnion id := by
  dsimp
  intro T hT
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
  obtain ⟨S, hSF, hTS, hSerase⟩ :=
    (mem_forbiddenBlockedThirdVertices_iff.mp hw).2
  apply mem_biUnion.mpr
  exact ⟨S, mem_rootedActiveForbiddenConfigurations_iff.mpr
    ⟨hSF, thirdVertexTriple huv w, hTS,
      left_mem_thirdVertexTriple huv w,
      right_mem_thirdVertexTriple huv w, hSerase⟩, hTS⟩

/-- Rooted union-bound count for forbidden third vertices. -/
theorem card_forbiddenBlockedThirdVertices_le_sum_rooted_active
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (forbiddenBlockedThirdVertices F A P huv).card ≤
      ∑ S ∈ rootedActiveForbiddenConfigurations F P u v, S.card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  have hsub := mapped_forbiddenBlocked_subset_rooted_active_biUnion
    (F := F) (A := A) (P := P) huv
  calc
    (forbiddenBlockedThirdVertices F A P huv).card =
        ((forbiddenBlockedThirdVertices F A P huv).map e).card := by simp
    _ ≤ ((rootedActiveForbiddenConfigurations F P u v).biUnion id).card :=
      card_le_card hsub
    _ ≤ ∑ S ∈ rootedActiveForbiddenConfigurations F P u v, S.card :=
      card_biUnion_le

theorem card_forbiddenBlockedThirdVertices_le_mul_rooted_active
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k) :
    (forbiddenBlockedThirdVertices F A P huv).card ≤
      (rootedActiveForbiddenConfigurations F P u v).card * k := by
  calc
    (forbiddenBlockedThirdVertices F A P huv).card ≤
        ∑ S ∈ rootedActiveForbiddenConfigurations F P u v, S.card :=
      card_forbiddenBlockedThirdVertices_le_sum_rooted_active huv
    _ ≤ ∑ _S ∈ rootedActiveForbiddenConfigurations F P u v, k := by
      apply sum_le_sum
      intro S hS
      exact hcard S
        (mem_rootedActiveForbiddenConfigurations_iff.mp hS).1
    _ = (rootedActiveForbiddenConfigurations F P u v).card * k := by simp

/-- If all forbidden configurations have size at most `k`, only the number
of active configurations remains to be bounded. -/
theorem card_forbiddenBlockedThirdVertices_le_mul_active
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k) :
    (forbiddenBlockedThirdVertices F A P huv).card ≤
      (activeForbiddenConfigurations F P).card * k := by
  calc
    (forbiddenBlockedThirdVertices F A P huv).card ≤
        ∑ S ∈ activeForbiddenConfigurations F P, S.card :=
      card_forbiddenBlockedThirdVertices_le_sum_active huv
    _ ≤ ∑ _S ∈ activeForbiddenConfigurations F P, k := by
      apply sum_le_sum
      intro S hS
      exact hcard S (mem_activeForbiddenConfigurations_iff.mp hS).1
    _ = (activeForbiddenConfigurations F P).card * k := by simp

/-- Every absorber-induced minimal outside part has at most `q` triangles. -/
lemma card_le_cutoff_of_mem_absorberErdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V}
    (hS : S ∈ absorberErdosForbiddenConfigurationsOn q B) :
    S.card ≤ q := by
  obtain ⟨_hne, r, _hr4, hrq, E, hE, _hEpacking, hEB⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp hS
  have hsub : S ⊆ E := by
    rw [← hEB]
    exact sdiff_subset
  have hcard := card_le_card hsub
  rw [hE.1.1] at hcard
  omega

/-- Bounding active rooted configurations is sufficient for the numerical
maximality criterion. -/
theorem graphSupportedOn_of_maximal_active_count_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V} {k : ℕ}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (hmax : legalAvailable F P A = ∅)
    (hfamily : ∀ S ∈ F, S.card ≤ k)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (coveredGraph P).degree u + (coveredGraph P).degree v +
          (activeForbiddenConfigurations F P).card * k <
        (candidateThirdVertices A huv.1.ne).card) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  apply graphSupportedOn_of_maximal_degree_forbidden_lt
    hpacking havoid hmax
  intro u v huv houtside
  have hforbidden := card_forbiddenBlockedThirdVertices_le_mul_active
    (F := F) (A := A) (P := P) huv.1.ne hfamily
  have hsurplus := hcount huv houtside
  omega

/-- Canonical absorber-relative version: after maximality, only one uniform
bound on the number of active induced configurations remains. -/
theorem graphSupportedOn_of_maximal_absorber_active_count_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (havoid : AvoidsForbidden P
      (absorberErdosForbiddenConfigurationsOn q B))
    (hmax : legalAvailable
      (absorberErdosForbiddenConfigurationsOn q B) P
      (outsideAvailableTriangles H B) = ∅)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (coveredGraph P).degree u + (coveredGraph P).degree v +
          (activeForbiddenConfigurations
            (absorberErdosForbiddenConfigurationsOn q B) P).card * q <
        (candidateThirdVertices
          (outsideAvailableTriangles H B) huv.1.ne).card) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  apply graphSupportedOn_of_maximal_active_count_lt
    hpacking havoid hmax
  · exact fun S hS ↦ card_le_cutoff_of_mem_absorberErdosForbidden hS
  · exact hcount

/-- The useful rooted form of the canonical maximality criterion. -/
theorem graphSupportedOn_of_maximal_absorber_rooted_active_count_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (havoid : AvoidsForbidden P
      (absorberErdosForbiddenConfigurationsOn q B))
    (hmax : legalAvailable
      (absorberErdosForbiddenConfigurationsOn q B) P
      (outsideAvailableTriangles H B) = ∅)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (coveredGraph P).degree u + (coveredGraph P).degree v +
          (rootedActiveForbiddenConfigurations
            (absorberErdosForbiddenConfigurationsOn q B) P u v).card * q <
        (candidateThirdVertices
          (outsideAvailableTriangles H B) huv.1.ne).card) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  apply graphSupportedOn_of_maximal_degree_forbidden_lt
    hpacking havoid hmax
  intro u v huv houtside
  have hforbidden :=
    card_forbiddenBlockedThirdVertices_le_mul_rooted_active
      (F := absorberErdosForbiddenConfigurationsOn q B)
      (A := outsideAvailableTriangles H B) (P := P) huv.1.ne
      (fun S hS ↦ card_le_cutoff_of_mem_absorberErdosForbidden hS)
  have hsurplus := hcount huv houtside
  omega

end Erdos207
