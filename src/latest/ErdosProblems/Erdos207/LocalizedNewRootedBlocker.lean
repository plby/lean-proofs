/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedBlocker

/-!
# Newly activated localized rooted obstructions

At a cover-down stage every proposed triangle belongs to the old available
family.  It therefore did not complete a forbidden configuration before the
stage began.  A forbidden obstruction at the end of the stage must use at
least one genuinely new triangle in its remainder.  This file records that
essential relative form of the rooted obstruction count.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Forbidden configurations rooted at `u,v`, localized to third vertices in
`U`, whose designated missing triangle belongs to `A`, and which became
active strictly after enlarging `Pold` to `P`. -/
noncomputable def rootedNewActiveForbiddenConfigurationsIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Pold P A : TripleSystemOn V)
    (u v : V) (U : Finset V) : ForbiddenFamilyOn V := by
  classical
  exact F.filter fun C ↦ ∃ T ∈ C,
    T ∈ A ∧ u ∈ T.1 ∧ v ∈ T.1 ∧
      (∃ w ∈ T.1, w ∈ U ∧ w ≠ u ∧ w ≠ v) ∧
      C.erase T ⊆ P ∧ ¬ C.erase T ⊆ Pold

@[simp]
lemma mem_rootedNewActiveForbiddenConfigurationsIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A C : TripleSystemOn V}
    {u v : V} {U : Finset V} :
    C ∈ rootedNewActiveForbiddenConfigurationsIn F Pold P A u v U ↔
      C ∈ F ∧ ∃ T ∈ C,
        T ∈ A ∧ u ∈ T.1 ∧ v ∈ T.1 ∧
          (∃ w ∈ T.1, w ∈ U ∧ w ≠ u ∧ w ≠ v) ∧
          C.erase T ⊆ P ∧ ¬ C.erase T ⊆ Pold := by
  classical
  simp [rootedNewActiveForbiddenConfigurationsIn]

/-- Uniform cap on newly activated rooted configurations.  The missing
triangle is required to belong to the old available family `A`. -/
def NewRootedActiveCapsGoodIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Pold P A : TripleSystemOn V)
    (U : Finset V) (r : ℕ) : Prop :=
  ∀ u v : V, u ≠ v →
    (rootedNewActiveForbiddenConfigurationsIn F Pold P A u v U).card ≤ r

/-- A cap on a larger third-vertex set implies the corresponding cap on a
smaller set. -/
lemma NewRootedActiveCapsGoodIn.mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A : TripleSystemOn V}
    {U U' : Finset V} {r : ℕ}
    (hcap : NewRootedActiveCapsGoodIn F Pold P A U' r)
    (hUU' : U ⊆ U') :
    NewRootedActiveCapsGoodIn F Pold P A U r := by
  intro u v huv
  apply (card_le_card ?_).trans (hcap u v huv)
  intro C hC
  obtain ⟨hCF, T, hTC, hTA, huT, hvT, hthird, hP, hnotOld⟩ :=
    mem_rootedNewActiveForbiddenConfigurationsIn_iff.mp hC
  obtain ⟨w, hwT, hwU, hwu, hwv⟩ := hthird
  exact mem_rootedNewActiveForbiddenConfigurationsIn_iff.mpr
    ⟨hCF, T, hTC, hTA, huT, hvT,
      ⟨w, hwT, hUU' hwU, hwu, hwv⟩, hP, hnotOld⟩

/-- Restricting the old available family can only remove newly activated
rooted configurations. -/
lemma NewRootedActiveCapsGoodIn.mono_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A A' : TripleSystemOn V}
    {U : Finset V} {r : ℕ}
    (hcap : NewRootedActiveCapsGoodIn F Pold P A U r)
    (hAA' : A' ⊆ A) :
    NewRootedActiveCapsGoodIn F Pold P A' U r := by
  intro u v huv
  apply (card_le_card ?_).trans (hcap u v huv)
  intro C hC
  obtain ⟨hCF, T, hTC, hTA', huT, hvT, hthird, hP, hnotOld⟩ :=
    mem_rootedNewActiveForbiddenConfigurationsIn_iff.mp hC
  exact mem_rootedNewActiveForbiddenConfigurationsIn_iff.mpr
    ⟨hCF, T, hTC, hAA' hTA', huT, hvT, hthird, hP, hnotOld⟩

/-- Every forbidden blocker for an old-available triangle is newly active,
provided no old-available triangle completed a forbidden configuration over
the old packing. -/
lemma mapped_forbiddenBlockedIn_subset_rooted_new_activeIn_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V)
    (hold : ∀ T ∈ A, ¬ CompletesForbidden F Pold T) :
    let e : ThirdVertex u v ↪ TripleOn V :=
      ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
    (forbiddenBlockedThirdVerticesIn F A P huv U).map e ⊆
      (rootedNewActiveForbiddenConfigurationsIn
        F Pold P A u v U).biUnion id := by
  dsimp
  intro T hT
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
  have hw' := mem_forbiddenBlockedThirdVerticesIn_iff.mp hw
  have hblocked := mem_forbiddenBlockedThirdVertices_iff.mp hw'.1
  obtain ⟨C, hCF, hTC, hCerase⟩ := hblocked.2
  have hthird :
      ∃ x ∈ (thirdVertexTriple huv w : Finset V),
        x ∈ U ∧ x ≠ u ∧ x ≠ v :=
    ⟨w.1, third_mem_thirdVertexTriple huv w, hw'.2, w.2.1, w.2.2⟩
  have hnotOld : ¬ C.erase (thirdVertexTriple huv w) ⊆ Pold := by
    intro hsub
    exact hold _ hblocked.1 ⟨C, hCF, hTC, hsub⟩
  apply mem_biUnion.mpr
  refine ⟨C, mem_rootedNewActiveForbiddenConfigurationsIn_iff.mpr
    ⟨hCF, thirdVertexTriple huv w, hTC, hblocked.1,
      left_mem_thirdVertexTriple huv w,
      right_mem_thirdVertexTriple huv w, hthird, hCerase, hnotOld⟩, hTC⟩

/-- Union-bound count for the newly activated localized rooted family. -/
theorem card_forbiddenBlockedThirdVerticesIn_le_sum_rooted_new_activeIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V)
    (hold : ∀ T ∈ A, ¬ CompletesForbidden F Pold T) :
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
      ∑ C ∈ rootedNewActiveForbiddenConfigurationsIn
        F Pold P A u v U, C.card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  calc
    (forbiddenBlockedThirdVerticesIn F A P huv U).card =
        ((forbiddenBlockedThirdVerticesIn F A P huv U).map e).card := by simp
    _ ≤ ((rootedNewActiveForbiddenConfigurationsIn
          F Pold P A u v U).biUnion id).card :=
      card_le_card
        (mapped_forbiddenBlockedIn_subset_rooted_new_activeIn_biUnion
          huv U hold)
    _ ≤ ∑ C ∈ rootedNewActiveForbiddenConfigurationsIn
          F Pold P A u v U, C.card := card_biUnion_le

/-- If forbidden configurations have size at most `k`, the number of
localized forbidden third vertices is controlled by the number of newly
activated rooted configurations, rather than by all configurations already
active over the old packing. -/
theorem card_forbiddenBlockedThirdVerticesIn_le_mul_rooted_new_activeIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Pold P A : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V) {k : ℕ}
    (hold : ∀ T ∈ A, ¬ CompletesForbidden F Pold T)
    (hcard : ∀ C ∈ F, C.card ≤ k) :
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
      (rootedNewActiveForbiddenConfigurationsIn
        F Pold P A u v U).card * k := by
  calc
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
        ∑ C ∈ rootedNewActiveForbiddenConfigurationsIn
          F Pold P A u v U, C.card :=
      card_forbiddenBlockedThirdVerticesIn_le_sum_rooted_new_activeIn
        huv U hold
    _ ≤ ∑ _C ∈ rootedNewActiveForbiddenConfigurationsIn
          F Pold P A u v U, k := by
      apply sum_le_sum
      intro C hC
      exact hcard C
        (mem_rootedNewActiveForbiddenConfigurationsIn_iff.mp hC).1
    _ = (rootedNewActiveForbiddenConfigurationsIn
          F Pold P A u v U).card * k := by simp

end

end Erdos207
