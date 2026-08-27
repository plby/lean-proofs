/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterTypicalityUpdate
import ErdosProblems.Erdos207.ForbiddenCompletionCount
import ErdosProblems.Erdos207.GreedyObstructionCount
import ErdosProblems.Erdos207.InternalEdgeReserve

/-!
# Deterministic decomposition of master-step extension loss

An old extension vertex can fail at the next stage for only three reasons:
it is already a vertex of the rooted pattern, one of its incident graph
edges was removed, or its canonical triangle completes a forbidden
configuration.  This is the deterministic content of the T2--T3 split in
KSSS Proposition 10.6.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Vertices whose edge to some vertex of the rooted pattern is lost when
passing from `G` to `G'`. -/
def removedAroundPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (G G' : SimpleGraph V) (U : Finset V) (Q : SimpleGraph V) : Finset V :=
  (graphSupportFinset Q).biUnion fun v =>
    neighborsIn G U v \ neighborsIn G' U v

/-- Third vertices which complete a forbidden configuration over at least
one edge of the rooted pattern.  `attach` supplies the proof that the two
canonical endpoints are distinct. -/
def forbiddenAroundPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (Q : SimpleGraph V) : Finset V :=
  (graphEdges Q).attach.biUnion fun e =>
    (forbiddenBlockedThirdVertices F A P
      (out_fst_ne_snd_of_mem_graphEdges e.2)).image Subtype.val

lemma endpoint_mem_graphSupportFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q : SimpleGraph V} {e : Sym2 V} (he : e ∈ graphEdges Q) :
    e.out.1 ∈ graphSupportFinset Q ∧ e.out.2 ∈ graphSupportFinset Q := by
  have hadj := graph_adj_out_of_mem_graphEdges he
  exact ⟨mem_graphSupportFinset_iff.mpr ⟨e.out.2, hadj⟩,
    mem_graphSupportFinset_iff.mpr ⟨e.out.1, hadj.symm⟩⟩

lemma card_removedAroundPattern_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G G' : SimpleGraph V) (U : Finset V) (Q : SimpleGraph V) :
    (removedAroundPattern G G' U Q).card ≤
      ∑ v ∈ graphSupportFinset Q,
        (neighborsIn G U v \ neighborsIn G' U v).card := by
  exact card_biUnion_le

lemma card_removedAroundPattern_le_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {G G' : SimpleGraph V} {U : Finset V} {Q : SimpleGraph V} {a : Nat}
    (hcap : ∀ v ∈ graphSupportFinset Q,
      (neighborsIn G U v \ neighborsIn G' U v).card ≤ a) :
    (removedAroundPattern G G' U Q).card ≤
      (graphSupportFinset Q).card * a := by
  calc
    (removedAroundPattern G G' U Q).card ≤
        ∑ v ∈ graphSupportFinset Q,
          (neighborsIn G U v \ neighborsIn G' U v).card :=
      card_removedAroundPattern_le_sum G G' U Q
    _ ≤ ∑ _v ∈ graphSupportFinset Q, a := by
      apply sum_le_sum
      intro v hv
      exact hcap v hv
    _ = (graphSupportFinset Q).card * a := by simp

lemma card_forbiddenAroundPattern_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V)
    (Q : SimpleGraph V) :
    (forbiddenAroundPattern F A P Q).card ≤
      ∑ e ∈ (graphEdges Q).attach,
        (forbiddenBlockedThirdVertices F A P
          (out_fst_ne_snd_of_mem_graphEdges e.2)).card := by
  unfold forbiddenAroundPattern
  calc
    ((graphEdges Q).attach.biUnion fun e =>
        (forbiddenBlockedThirdVertices F A P
          (out_fst_ne_snd_of_mem_graphEdges e.2)).image Subtype.val).card
        ≤ ∑ e ∈ (graphEdges Q).attach,
            ((forbiddenBlockedThirdVertices F A P
              (out_fst_ne_snd_of_mem_graphEdges e.2)).image
                Subtype.val).card := card_biUnion_le
    _ = ∑ e ∈ (graphEdges Q).attach,
          (forbiddenBlockedThirdVertices F A P
            (out_fst_ne_snd_of_mem_graphEdges e.2)).card := by
      apply sum_congr rfl
      intro e he
      rw [card_image_of_injective _ Subtype.val_injective]

lemma card_forbiddenAroundPattern_le_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {Q : SimpleGraph V} {q r : Nat}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hroot : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurations F P e.out.1 e.out.2).card ≤ r) :
    (forbiddenAroundPattern F A P Q).card ≤
      (graphEdges Q).card * (r * q) := by
  calc
    (forbiddenAroundPattern F A P Q).card ≤
        ∑ e ∈ (graphEdges Q).attach,
          (forbiddenBlockedThirdVertices F A P
            (out_fst_ne_snd_of_mem_graphEdges e.2)).card :=
      card_forbiddenAroundPattern_le_sum F A P Q
    _ ≤ ∑ _e ∈ (graphEdges Q).attach, r * q := by
      apply sum_le_sum
      intro e he
      exact (card_forbiddenBlockedThirdVertices_le_mul_rooted_active
        (out_fst_ne_snd_of_mem_graphEdges e.2) hFcard).trans
          (Nat.mul_le_mul_right q (hroot e.1 e.2))
    _ = (graphEdges Q).card * (r * q) := by simp

/-- The exact deterministic T2--T3 obstruction decomposition for a master
step. -/
theorem extensionLoss_subset_support_union_removed_union_forbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F) :
    iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar ⊆
      graphSupportFinset Q ∪
        (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
          forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q) := by
  intro x hx
  have hxold := (mem_sdiff.mp hx).1
  have hxnotnew := (mem_sdiff.mp hx).2
  by_contra hxnotbad
  have hxnotbad' : x ∉ graphSupportFinset Q ∪
      (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
        forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q) := hxnotbad
  simp only [mem_union, not_or] at hxnotbad'
  rcases hxnotbad' with ⟨hxnotSupport, hxnotRemoved, hxnotForbidden⟩
  apply hxnotnew
  rw [mem_iterationExtensionVertices_iff]
  refine ⟨(mem_iterationExtensionVertices_iff.mp hxold).1, ?_⟩
  intro e he
  have hab := out_fst_ne_snd_of_mem_graphEdges he
  let a : V := e.out.1
  let b : V := e.out.2
  have habQ : Q.Adj a b := graph_adj_out_of_mem_graphEdges he
  have habNew : (updatedStageGraph G U M).Adj a b := hQ habQ
  have hendsSupport : a ∈ graphSupportFinset Q ∧
      b ∈ graphSupportFinset Q := endpoint_mem_graphSupportFinset he
  have hxa : x ≠ a := by
    intro h
    exact hxnotSupport (h ▸ hendsSupport.1)
  have hxb : x ≠ b := by
    intro h
    exact hxnotSupport (h ▸ hendsSupport.2)
  let w : ThirdVertex a b := ⟨x, hxa, hxb⟩
  obtain ⟨T, hTA, hxT, heT⟩ :=
    (mem_iterationExtensionVertices_iff.mp hxold).2 e he
  have habT : a ∈ T.1 ∧ b ∈ T.1 ∧ a ≠ b := by
    have heT' := heT
    rw [← e.out_eq] at heT'
    exact mk_mem_tripleEdgeFinset_iff.mp heT'
  have hcanonical : thirdVertexTriple hab w = T := by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [thirdVertexTriple, tripleOfThree, mem_insert,
        mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact habT.1
      · exact habT.2.1
      · exact hxT
    · rw [T.2]
      exact (thirdVertexTriple hab w).2.ge
  have hxaG : G.Adj a x := by
    exact htri T hTA a habT.1 x hxT hxa.symm
  have hxbG : G.Adj b x := by
    exact htri T hTA b habT.2.1 x hxT hxb.symm
  have hxUstar := (mem_iterationExtensionVertices_iff.mp hxold).1
  have hxaNew : (updatedStageGraph G U M).Adj a x := by
    have hxOldNeighbor : x ∈ neighborsIn G Ustar a :=
      mem_neighborsIn_iff.mpr ⟨hxUstar, hxaG⟩
    have hxNotDifference : x ∉
        neighborsIn G Ustar a \
          neighborsIn (updatedStageGraph G U M) Ustar a := by
      intro hxDifference
      apply hxnotRemoved
      exact mem_biUnion.mpr ⟨a, hendsSupport.1, hxDifference⟩
    have hxNewNeighbor : x ∈
        neighborsIn (updatedStageGraph G U M) Ustar a := by
      by_contra hnot
      exact hxNotDifference (mem_sdiff.mpr ⟨hxOldNeighbor, hnot⟩)
    exact (mem_neighborsIn_iff.mp hxNewNeighbor).2
  have hxbNew : (updatedStageGraph G U M).Adj b x := by
    have hxOldNeighbor : x ∈ neighborsIn G Ustar b :=
      mem_neighborsIn_iff.mpr ⟨hxUstar, hxbG⟩
    have hxNotDifference : x ∉
        neighborsIn G Ustar b \
          neighborsIn (updatedStageGraph G U M) Ustar b := by
      intro hxDifference
      apply hxnotRemoved
      exact mem_biUnion.mpr ⟨b, hendsSupport.2, hxDifference⟩
    have hxNewNeighbor : x ∈
        neighborsIn (updatedStageGraph G U M) Ustar b := by
      by_contra hnot
      exact hxNotDifference (mem_sdiff.mpr ⟨hxOldNeighbor, hnot⟩)
    exact (mem_neighborsIn_iff.mp hxNewNeighbor).2
  have hnewLeave : updatedStageGraph G U M ≤
      leaveGraph (I ∪ (D ∪ M)) :=
    updatedStageGraph_le_leave_enlarged hGleave
  have hrootLeave := hnewLeave habNew
  have hxaLeave := hnewLeave hxaNew
  have hxbLeave := hnewLeave hxbNew
  have hlegal : IsLegalExtension F (I ∪ (D ∪ M)) T := by
    rw [← hcanonical]
    apply (isLegalExtension_iff hpacking havoid _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro hmem
      exact hrootLeave.2 (coveredGraph_adj.mpr
        ⟨thirdVertexTriple hab w, hmem,
          left_mem_thirdVertexTriple hab w,
          right_mem_thirdVertexTriple hab w, hab⟩)
    · rw [triangleAvoidsGraph_thirdVertexTriple_iff]
      exact ⟨hrootLeave.2, hxaLeave.2, hxbLeave.2⟩
    · intro hcomplete
      apply hxnotForbidden
      unfold forbiddenAroundPattern
      apply mem_biUnion.mpr
      refine ⟨⟨e, he⟩, mem_attach _ _, mem_image.mpr ?_⟩
      refine ⟨w, ?_, rfl⟩
      exact mem_forbiddenBlockedThirdVertices_iff.mpr
        ⟨hcanonical ▸ hTA, hcomplete⟩
  have hTU : T.1 ⊆ U := by
    intro y hy
    have hy' : y ∈ (thirdVertexTriple hab w).1 := hcanonical ▸ hy
    simp only [thirdVertexTriple, tripleOfThree, mem_insert,
      mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl
    · exact (updatedStageGraph_supported G U M habNew).1
    · exact (updatedStageGraph_supported G U M habNew).2
    · exact hUstar hxUstar
  exact ⟨T, mem_updatedStageAvailable_iff.mpr ⟨hTA, hlegal, hTU⟩,
    hxT, heT⟩

/-- Cardinal form of the deterministic decomposition.  A uniform incident
edge-loss cap and a uniform rooted-active-configuration cap suffice for the
full rooted extension-loss estimate. -/
theorem card_extensionLoss_le_of_caps
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V} {a r q : Nat}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hedgeCap : ∀ v ∈ graphSupportFinset Q,
      (neighborsIn G Ustar v \
        neighborsIn (updatedStageGraph G U M) Ustar v).card ≤ a)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hrootCap : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurations F (I ∪ (D ∪ M))
        e.out.1 e.out.2).card ≤ r) :
    ((iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar).card) ≤
      (graphSupportFinset Q).card +
        (graphSupportFinset Q).card * a +
          (graphEdges Q).card * (r * q) := by
  have hsub := extensionLoss_subset_support_union_removed_union_forbidden
    hQ hUstar htri hGleave hpacking havoid
  have hremoved :
      (removedAroundPattern G (updatedStageGraph G U M) Ustar Q).card ≤
        (graphSupportFinset Q).card * a :=
    card_removedAroundPattern_le_mul hedgeCap
  have hforbidden :
      (forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q).card ≤
        (graphEdges Q).card * (r * q) :=
    card_forbiddenAroundPattern_le_mul hFcard hrootCap
  have hunionInner :
      (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
        forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q).card ≤
      (graphSupportFinset Q).card * a +
        (graphEdges Q).card * (r * q) := by
    exact (card_union_le _ _).trans (Nat.add_le_add hremoved hforbidden)
  have houter := card_union_le (graphSupportFinset Q)
    (removedAroundPattern G (updatedStageGraph G U M) Ustar Q ∪
      forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q)
  have hloss := card_le_card hsub
  omega

/-- `ℝ≥0` form used directly by `MasterTypicalityLossEvent`. -/
theorem extensionLoss_nnreal_le_of_caps
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U Ustar : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V} {a r q : Nat}
    {target : NNReal}
    (hQ : Q ≤ updatedStageGraph G U M)
    (hUstar : Ustar ⊆ U)
    (htri : ConsistsOfTriangles G A)
    (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hedgeCap : ∀ v ∈ graphSupportFinset Q,
      (neighborsIn G Ustar v \
        neighborsIn (updatedStageGraph G U M) Ustar v).card ≤ a)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hrootCap : ∀ e ∈ graphEdges Q,
      (rootedActiveForbiddenConfigurations F (I ∪ (D ∪ M))
        e.out.1 e.out.2).card ≤ r)
    (hnumeric : ((graphSupportFinset Q).card : NNReal) +
        (graphSupportFinset Q).card * a +
          (graphEdges Q).card * (r * q) ≤ target) :
    (((iterationExtensionVertices A Q Ustar \
        iterationExtensionVertices
          (updatedStageAvailable F U A I D M) Q Ustar).card : NNReal) ≤
      target) := by
  have hnat := card_extensionLoss_le_of_caps hQ hUstar htri hGleave
    hpacking havoid hedgeCap hFcard hrootCap
  have hcast :
      (((iterationExtensionVertices A Q Ustar \
          iterationExtensionVertices
            (updatedStageAvailable F U A I D M) Q Ustar).card : Nat) :
          NNReal) ≤
        ((graphSupportFinset Q).card : NNReal) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) := by
    exact_mod_cast hnat
  exact hcast.trans hnumeric

end

end Erdos207
