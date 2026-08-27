/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomGreedy
import ErdosProblems.Erdos207.ForbiddenCompletionCount

/-!
# Rooted obstruction counts localized to a third-vertex set

The internal cover of an outside edge only proposes third vertices in the
next vortex set.  Hence forbidden configurations whose missing triangle has
some other third vertex cannot obstruct that cover.  This file records the
localized rooted family and a reserve-wedge legality lemma which charges
only blockers lying in the actual candidate set.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Active forbidden configurations rooted at `u,v` whose missing triangle
has its third vertex in `U`. -/
noncomputable def rootedActiveForbiddenConfigurationsIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (u v : V) (U : Finset V) : ForbiddenFamilyOn V := by
  classical
  exact F.filter fun C ↦ ∃ T ∈ C,
    u ∈ T.1 ∧ v ∈ T.1 ∧
      (∃ w ∈ T.1, w ∈ U ∧ w ≠ u ∧ w ≠ v) ∧ C.erase T ⊆ P

@[simp]
lemma mem_rootedActiveForbiddenConfigurationsIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P C : TripleSystemOn V}
    {u v : V} {U : Finset V} :
    C ∈ rootedActiveForbiddenConfigurationsIn F P u v U ↔
      C ∈ F ∧ ∃ T ∈ C,
        u ∈ T.1 ∧ v ∈ T.1 ∧
          (∃ w ∈ T.1, w ∈ U ∧ w ≠ u ∧ w ≠ v) ∧ C.erase T ⊆ P := by
  classical
  simp [rootedActiveForbiddenConfigurationsIn]

/-- Enlarging the permitted third-vertex set only enlarges the localized
active rooted family. -/
lemma rootedActiveForbiddenConfigurationsIn_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {u v : V} {U U' : Finset V} (hUU' : U ⊆ U') :
    rootedActiveForbiddenConfigurationsIn F P u v U ⊆
      rootedActiveForbiddenConfigurationsIn F P u v U' := by
  intro C hC
  obtain ⟨hCF, T, hTC, huT, hvT, hthird, hrem⟩ :=
    mem_rootedActiveForbiddenConfigurationsIn_iff.mp hC
  obtain ⟨w, hwT, hwU, hwu, hwv⟩ := hthird
  exact mem_rootedActiveForbiddenConfigurationsIn_iff.mpr
    ⟨hCF, T, hTC, huT, hvT,
      ⟨w, hwT, hUU' hwU, hwu, hwv⟩, hrem⟩

/-- Forbidden third vertices restricted to a prescribed ordinary-vertex
set. -/
noncomputable def forbiddenBlockedThirdVerticesIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    Finset (ThirdVertex u v) := by
  classical
  exact (forbiddenBlockedThirdVertices F A P huv).filter fun w ↦ w.1 ∈ U

@[simp]
lemma mem_forbiddenBlockedThirdVerticesIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} {huv : u ≠ v} {U : Finset V}
    {w : ThirdVertex u v} :
    w ∈ forbiddenBlockedThirdVerticesIn F A P huv U ↔
      w ∈ forbiddenBlockedThirdVertices F A P huv ∧ w.1 ∈ U := by
  classical
  simp [forbiddenBlockedThirdVerticesIn]

/-- Pair-conflict third vertices restricted to a prescribed ordinary-vertex
set. -/
noncomputable def edgeBlockedThirdVerticesIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) {u v : V} (huv : u ≠ v)
    (U : Finset V) : Finset (ThirdVertex u v) := by
  classical
  exact (edgeBlockedThirdVertices A P huv).filter fun w ↦ w.1 ∈ U

@[simp]
lemma mem_edgeBlockedThirdVerticesIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {U : Finset V} {w : ThirdVertex u v} :
    w ∈ edgeBlockedThirdVerticesIn A P huv U ↔
      w ∈ edgeBlockedThirdVertices A P huv ∧ w.1 ∈ U := by
  classical
  simp [edgeBlockedThirdVerticesIn]

/-- A localized forbidden blocker belongs to the union of the localized
active rooted configurations. -/
lemma mapped_forbiddenBlockedIn_subset_rooted_activeIn_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    let e : ThirdVertex u v ↪ TripleOn V :=
      ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
    (forbiddenBlockedThirdVerticesIn F A P huv U).map e ⊆
      (rootedActiveForbiddenConfigurationsIn F P u v U).biUnion id := by
  dsimp
  intro T hT
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
  have hw' := mem_forbiddenBlockedThirdVerticesIn_iff.mp hw
  obtain ⟨C, hCF, hTC, hCerase⟩ :=
    (mem_forbiddenBlockedThirdVertices_iff.mp hw'.1).2
  apply mem_biUnion.mpr
  refine ⟨C, mem_rootedActiveForbiddenConfigurationsIn_iff.mpr
    ⟨hCF, thirdVertexTriple huv w, hTC,
      left_mem_thirdVertexTriple huv w,
      right_mem_thirdVertexTriple huv w, ?_, hCerase⟩, hTC⟩
  exact ⟨w.1, third_mem_thirdVertexTriple huv w, hw'.2, w.2.1, w.2.2⟩

/-- Localized rooted union bound for the number of forbidden third
vertices. -/
theorem card_forbiddenBlockedThirdVerticesIn_le_sum_rooted_activeIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
      ∑ C ∈ rootedActiveForbiddenConfigurationsIn F P u v U, C.card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  calc
    (forbiddenBlockedThirdVerticesIn F A P huv U).card =
        ((forbiddenBlockedThirdVerticesIn F A P huv U).map e).card := by simp
    _ ≤ ((rootedActiveForbiddenConfigurationsIn F P u v U).biUnion id).card :=
      card_le_card
        (mapped_forbiddenBlockedIn_subset_rooted_activeIn_biUnion huv U)
    _ ≤ ∑ C ∈ rootedActiveForbiddenConfigurationsIn F P u v U, C.card :=
      card_biUnion_le

/-- If forbidden configurations have size at most `k`, the localized
forbidden loss is at most the localized rooted count times `k`. -/
theorem card_forbiddenBlockedThirdVerticesIn_le_mul_rooted_activeIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (U : Finset V) {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k) :
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
      (rootedActiveForbiddenConfigurationsIn F P u v U).card * k := by
  calc
    (forbiddenBlockedThirdVerticesIn F A P huv U).card ≤
        ∑ C ∈ rootedActiveForbiddenConfigurationsIn F P u v U, C.card :=
      card_forbiddenBlockedThirdVerticesIn_le_sum_rooted_activeIn huv U
    _ ≤ ∑ _C ∈ rootedActiveForbiddenConfigurationsIn F P u v U, k := by
      apply sum_le_sum
      intro C hC
      exact hcard C
        (mem_rootedActiveForbiddenConfigurationsIn_iff.mp hC).1
    _ = (rootedActiveForbiddenConfigurationsIn F P u v U).card * k := by
      simp

/-- Reserve-wedge legality only charges blockers which themselves lie in
the active reserve candidate set. -/
theorem card_activeReserveLegalThirdVertices_ge_of_localized_blocked_add_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {G : SimpleGraph V} {U S : Finset V} {u v : V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (huvLeave : (leaveGraph P).Adj u v)
    (hu : u ∉ U) (hv : v ∉ U) (hSU : S ⊆ U)
    (omega : Sym2 V → Bool)
    (hA : ∀ w, ∀ hwS : w ∈ S,
      let w' : ThirdVertex u v :=
        ⟨w, fun h ↦ hu (h ▸ hSU hwS),
          fun h ↦ hv (h ▸ hSU hwS)⟩
      thirdVertexTriple huvLeave.ne w' ∈ A)
    (D : ℕ)
    (hcount :
      (edgeBlockedThirdVerticesIn A P huvLeave.ne S ∪
        forbiddenBlockedThirdVerticesIn F A P huvLeave.ne S).card + D ≤
      (activeReserveWedgeVertices G U S u v omega).card) :
    D ≤ (activeReserveLegalThirdVertices F G U S omega P
      u v huvLeave.ne).card := by
  classical
  let C := activeReserveWedgeVertices G U S u v omega
  let e : {w // w ∈ C} ↪ ThirdVertex u v :=
    { toFun := fun w ↦ ⟨w.1,
        fun h ↦ hu (h ▸ hSU
          (mem_activeReserveWedgeVertices_iff.mp w.2).1),
        fun h ↦ hv (h ▸ hSU
          (mem_activeReserveWedgeVertices_iff.mp w.2).1)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ThirdVertex u v ↦ z.1) hxy }
  let C' : Finset (ThirdVertex u v) := C.attach.map e
  have hcardC' : C'.card = C.card := by simp [C']
  let blocked : Finset (ThirdVertex u v) :=
    edgeBlockedThirdVerticesIn A P huvLeave.ne S ∪
      forbiddenBlockedThirdVerticesIn F A P huvLeave.ne S
  have hsub : C' ⊆
      activeReserveLegalThirdVertices F G U S omega P
          u v huvLeave.ne ∪ blocked := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hw
    have hxS := (mem_activeReserveWedgeVertices_iff.mp x.2).1
    let z : ThirdVertex u v :=
      ⟨x.1, fun h ↦ hu (h ▸ hSU hxS), fun h ↦ hv (h ▸ hSU hxS)⟩
    have heq : e x = z := by apply Subtype.ext; rfl
    rw [heq]
    have hzA : thirdVertexTriple huvLeave.ne z ∈ A := hA x.1 hxS
    by_cases hlegal : IsLegalExtension F P (thirdVertexTriple huvLeave.ne z)
    · exact mem_union.mpr (Or.inl
        (mem_activeReserveLegalThirdVertices_iff.mpr ⟨x.2, hlegal⟩))
    · have hnotselected : thirdVertexTriple huvLeave.ne z ∉ P := by
        intro hselected
        exact huvLeave.2 ⟨thirdVertexTriple huvLeave.ne z, hselected,
          left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
          huvLeave.ne⟩
      by_cases hedge :
          ¬ TriangleAvoidsGraph (coveredGraph P)
            (thirdVertexTriple huvLeave.ne z)
      · apply mem_union.mpr
        apply Or.inr
        apply mem_union.mpr
        apply Or.inl
        exact mem_edgeBlockedThirdVerticesIn_iff.mpr
          ⟨mem_edgeBlockedThirdVertices_iff.mpr ⟨hzA, hedge⟩, hxS⟩
      · have hforbidden : CompletesForbidden F P
            (thirdVertexTriple huvLeave.ne z) := by
          by_contra hnotForbidden
          apply hlegal
          exact (isLegalExtension_iff hpacking havoid _).mpr
            ⟨hnotselected, not_not.mp hedge, hnotForbidden⟩
        apply mem_union.mpr
        apply Or.inr
        apply mem_union.mpr
        apply Or.inr
        exact mem_forbiddenBlockedThirdVerticesIn_iff.mpr
          ⟨mem_forbiddenBlockedThirdVertices_iff.mpr
            ⟨hzA, hforbidden⟩, hxS⟩
  have hcard := card_le_card hsub
  have hunion := card_union_le
    (activeReserveLegalThirdVertices F G U S omega P u v huvLeave.ne)
    blocked
  have hblocked : blocked.card + D ≤ C.card := by
    simpa only [blocked, C] using hcount
  omega

end

end Erdos207
