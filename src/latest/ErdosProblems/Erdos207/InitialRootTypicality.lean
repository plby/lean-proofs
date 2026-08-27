/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PaddedAbsorberRootBounds
import ErdosProblems.Erdos207.InitialTypicalityFromLoss
import ErdosProblems.Erdos207.InternalEdgeReserve
import ErdosProblems.Erdos207.MasterExtensionLoss

/-!
# Initial typicality on the padded absorber roots

The complete graph minus the absorber loses only a constant number of roots
at each endpoint.  Likewise, for one fixed available pair, every unavailable
root is an endpoint, an absorber neighbor, or one of the six localized
bank/forbidden candidates.  Unioning these sets over a bounded graph pattern
gives the small-vortex extension bound.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

noncomputable def initialRootBadForPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) {u v : V} (huv : u ≠ v) : Finset V :=
  {u, v} ∪ (absorberRootNeighborSet H X u ∪
    (absorberRootNeighborSet H X v ∪
      absorberRootPairObstructionSet q B X huv))

lemma card_initialRootBadForPair_le_thirtySix
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    {u v : V} (huv : u ≠ v) :
    (initialRootBadForPair q H X B huv).card ≤ 36 := by
  have hpair : ({u, v} : Finset V).card ≤ 2 := by
    simp [huv]
  have hu := hroot.1 u
  have hv := hroot.1 v
  have hob := hroot.2 u v huv
  calc
    (initialRootBadForPair q H X B huv).card
        ≤ ({u, v} : Finset V).card +
          (absorberRootNeighborSet H X u ∪
            (absorberRootNeighborSet H X v ∪
              absorberRootPairObstructionSet q B X huv)).card :=
      card_union_le _ _
    _ ≤ ({u, v} : Finset V).card +
        ((absorberRootNeighborSet H X u).card +
          ((absorberRootNeighborSet H X v).card +
            (absorberRootPairObstructionSet q B X huv).card)) := by
      gcongr
      exact (card_union_le _ _).trans
        (Nat.add_le_add_left (card_union_le _ _)
          (absorberRootNeighborSet H X u).card)
    _ ≤ 36 := by omega

lemma root_mem_initialRootBadForPair_of_not_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {u v x : V} (huv : u ≠ v)
    (huvG : (graphDifference (SimpleGraph.completeGraph V) H).Adj u v)
    (hxX : x ∈ X)
    (hnot : ∀ w : ThirdVertex u v, w.1 = x →
      thirdVertexTriple huv w ∉
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available) :
    x ∈ initialRootBadForPair q H X B huv := by
  by_cases hxu : x = u
  · subst x
    exact mem_union_left _ (by simp)
  by_cases hxv : x = v
  · subst x
    exact mem_union_left _ (by simp)
  let w : ThirdVertex u v := ⟨x, hxu, hxv⟩
  by_cases hux : H.Adj u x
  · apply mem_union_right
    apply mem_union_left
    exact mem_absorberRootNeighborSet_iff.mpr ⟨hxX, hux.symm⟩
  by_cases hvx : H.Adj v x
  · apply mem_union_right
    apply mem_union_right
    apply mem_union_left
    exact mem_absorberRootNeighborSet_iff.mpr ⟨hxX, hvx.symm⟩
  have hnotHuv : ¬ H.Adj u v := by
    exact huvG.2.2
  have hTavoid : TriangleAvoidsGraph H (thirdVertexTriple huv w) :=
    (triangleAvoidsGraph_thirdVertexTriple_iff H huv w).mpr
      ⟨hnotHuv, hux, hvx⟩
  have hTnotAvailable := hnot w rfl
  have hobs : thirdVertexTriple huv w ∈ B ∨
      CompletesForbidden
        (absorberErdosForbiddenConfigurationsOn q B) ∅
        (thirdVertexTriple huv w) := by
    by_cases hTB : thirdVertexTriple huv w ∈ B
    · exact Or.inl hTB
    right
    by_contra hnotComplete
    apply hTnotAvailable
    apply mem_legalAvailable_iff.mpr
    refine ⟨mem_outsideAvailableTriangles_iff.mpr ⟨hTB, hTavoid⟩, ?_⟩
    have hpacking : IsPackingOn (∅ : TripleSystemOn V) := by
      intro _ _ _ R hR
      simp at hR
    have havoid : AvoidsForbidden (∅ : TripleSystemOn V)
        (absorberErdosForbiddenConfigurationsOn q B) := by
      intro S hSF hSempty
      obtain ⟨U, hUS⟩ := absorberErdosForbidden_nonempty hSF
      simpa using hSempty hUS
    rw [isLegalExtension_iff hpacking havoid]
    refine ⟨by simp, ?_, hnotComplete⟩
    simp [TriangleAvoidsGraph, coveredGraph]
  apply mem_union_right
  apply mem_union_right
  apply mem_union_right
  exact mem_absorberRootPairObstructionSet_iff.mpr
    ⟨hxX, w, rfl, hobs⟩

/-- The union of all constant pair-obstruction sets over the edges of a
rooted pattern, together with the pattern vertices themselves. -/
noncomputable def initialRootBadForPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (Q : SimpleGraph V) : Finset V :=
  graphSupportFinset Q ∪
    (graphEdges Q).attach.biUnion fun e ↦
      initialRootBadForPair q H X B
        (out_fst_ne_snd_of_mem_graphEdges e.2)

lemma card_graphEdges_le_graphSupportFinset_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) :
    (graphEdges Q).card ≤ (graphSupportFinset Q).card ^ 2 := by
  let outEmbedding : Sym2 V ↪ V × V :=
    ⟨fun e ↦ e.out, by
      intro e f hef
      rw [← e.out_eq, ← f.out_eq]
      exact congrArg (fun p : V × V ↦ s(p.1, p.2)) hef⟩
  let edgeEmbedding : {e : Sym2 V // e ∈ graphEdges Q} ↪ V × V :=
    (Function.Embedding.subtype _).trans outEmbedding
  have hsub : (graphEdges Q).attach.map edgeEmbedding ⊆
      (graphSupportFinset Q).product (graphSupportFinset Q) := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hp
    have hends := endpoint_mem_graphSupportFinset e.2
    exact mem_product.mpr hends
  calc
    (graphEdges Q).card = (graphEdges Q).attach.card := by simp
    _ = ((graphEdges Q).attach.map edgeEmbedding).card := by simp
    _ ≤ ((graphSupportFinset Q).product
        (graphSupportFinset Q)).card := card_le_card hsub
    _ = (graphSupportFinset Q).card ^ 2 := by simp [pow_two]

lemma card_initialRootBadForPattern_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (Q : SimpleGraph V) :
    (initialRootBadForPattern q H X B Q).card ≤
      (graphSupportFinset Q).card + (graphEdges Q).card * 36 := by
  calc
    (initialRootBadForPattern q H X B Q).card ≤
        (graphSupportFinset Q).card +
          ((graphEdges Q).attach.biUnion fun e ↦
            initialRootBadForPair q H X B
              (out_fst_ne_snd_of_mem_graphEdges e.2)).card :=
      card_union_le _ _
    _ ≤ (graphSupportFinset Q).card +
        ∑ e ∈ (graphEdges Q).attach,
          (initialRootBadForPair q H X B
            (out_fst_ne_snd_of_mem_graphEdges e.2)).card := by
      gcongr
      exact card_biUnion_le
    _ ≤ (graphSupportFinset Q).card +
        ∑ _e ∈ (graphEdges Q).attach, 36 := by
      gcongr with e he
      exact card_initialRootBadForPair_le_thirtySix hroot _
    _ = (graphSupportFinset Q).card + (graphEdges Q).card * 36 := by
      simp

lemma initial_root_extension_loss_subset_pattern_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H) :
    X \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q X ⊆
      initialRootBadForPattern q H X B Q := by
  intro x hx
  have hxX := (mem_sdiff.mp hx).1
  have hxnotExtension := (mem_sdiff.mp hx).2
  by_cases hxSupport : x ∈ graphSupportFinset Q
  · change x ∈ graphSupportFinset Q ∪ _
    exact mem_union_left _ hxSupport
  change x ∈ graphSupportFinset Q ∪ _
  apply mem_union_right
  by_contra hxnotBad
  apply hxnotExtension
  rw [mem_iterationExtensionVertices_iff]
  refine ⟨hxX, ?_⟩
  intro e he
  have hends := endpoint_mem_graphSupportFinset he
  have hxe₁ : x ≠ e.out.1 := fun h ↦ hxSupport (h ▸ hends.1)
  have hxe₂ : x ≠ e.out.2 := fun h ↦ hxSupport (h ▸ hends.2)
  have heG : (graphDifference (SimpleGraph.completeGraph V) H).Adj
      e.out.1 e.out.2 := hQ (graph_adj_out_of_mem_graphEdges he)
  have hxnotPair : x ∉ initialRootBadForPair q H X B
      (out_fst_ne_snd_of_mem_graphEdges he) := by
    intro hxPair
    apply hxnotBad
    exact mem_biUnion.mpr ⟨⟨e, he⟩, mem_attach _ _, hxPair⟩
  have hnotAll : ¬ ∀ w : ThirdVertex e.out.1 e.out.2, w.1 = x →
      thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges he) w ∉
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available := by
    intro hall
    exact hxnotPair
      (root_mem_initialRootBadForPair_of_not_available
        (out_fst_ne_snd_of_mem_graphEdges he) heG hxX hall)
  push Not at hnotAll
  obtain ⟨w, hwx, hwA⟩ := hnotAll
  refine ⟨thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges he) w,
    hwA, ?_, ?_⟩
  · rw [← hwx]
    exact third_mem_thirdVertexTriple _ _
  · have hs : s(e.out.1, e.out.2) ∈
        tripleEdgeFinset
          (thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges he) w) :=
      mk_mem_tripleEdgeFinset_iff.mpr
      ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
        out_fst_ne_snd_of_mem_graphEdges he⟩
    simpa only [e.out_eq] using hs

theorem card_initial_root_extension_loss_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hQsupport : (graphSupportFinset Q).card ≤ h) :
    (X \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q X).card ≤
      h + h ^ 2 * 36 := by
  have hloss : (X \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q X).card ≤
      (initialRootBadForPattern q H X B Q).card :=
    card_le_card (initial_root_extension_loss_subset_pattern_bad
      (q := q) (X := X) (B := B) hQ)
  have hbad := card_initialRootBadForPattern_le hroot Q
  have hedge := card_graphEdges_le_graphSupportFinset_sq Q
  have hsq : (graphSupportFinset Q).card ^ 2 ≤ h ^ 2 := by
    gcongr
  omega

/-! ## Ambient-layer losses -/

/-- The ambient vertices ruled out for one available pair by an absorber edge
or by the support of the absorber bank.  The subtype is projected back to the
ambient vertex type so that these sets can be unioned over a graph pattern. -/
noncomputable def initialAmbientBadForPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (B : TripleSystemOn V)
    {u v : V} (huv : u ≠ v) : Finset V :=
  (absorberEdgeBlockedThirdVertices H huv ∪
    bankSupportThirdVertices B huv).image fun w ↦ w.1

lemma card_initialAmbientBadForPair_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V} {C : ℕ}
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    {u v : V} (huv : u ≠ v) (huvH : ¬ H.Adj u v) :
    (initialAmbientBadForPair H B huv).card ≤ 3 * C := by
  have hedge := card_absorberEdgeBlockedThirdVertices_le_degree_add
    (H := H) huv huvH
  have hbank := card_bankSupportThirdVertices_le (B := B) huv
  calc
    (initialAmbientBadForPair H B huv).card ≤
        (absorberEdgeBlockedThirdVertices H huv ∪
          bankSupportThirdVertices B huv).card := card_image_le
    _ ≤ (absorberEdgeBlockedThirdVertices H huv).card +
          (bankSupportThirdVertices B huv).card := card_union_le _ _
    _ ≤ (H.degree u + H.degree v) + (verticesOn B).card := by omega
    _ ≤ 3 * C := by
      have hu := hdegree u
      have hv := hdegree v
      omega

lemma third_mem_initialAmbientBadForPair_of_not_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V}
    {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) (w : ThirdVertex u v)
    (hnot : thirdVertexTriple huv w ∉
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available) :
    w.1 ∈ initialAmbientBadForPair H B huv := by
  have hwNotLegal : w ∉ legalThirdVertices
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) ∅ huv := by
    intro hw
    apply hnot
    exact mem_legalAvailable_iff.mpr (mem_legalThirdVertices_iff.mp hw)
  have hwBad : w ∈ absorberEdgeBlockedThirdVertices H huv ∪
      bankSupportThirdVertices B huv :=
    initial_illegal_third_subset_edge_union_bankSupport huv
      (mem_sdiff.mpr ⟨mem_univ w, hwNotLegal⟩)
  exact mem_image.mpr ⟨w, hwBad, rfl⟩

/-- The union of all ambient pair-obstruction sets over a bounded pattern,
together with the vertices already occupied by that pattern. -/
noncomputable def initialAmbientBadForPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (B : TripleSystemOn V)
    (Q : SimpleGraph V) : Finset V :=
  graphSupportFinset Q ∪
    (graphEdges Q).attach.biUnion fun e ↦
      initialAmbientBadForPair H B
        (out_fst_ne_snd_of_mem_graphEdges e.2)

lemma card_initialAmbientBadForPattern_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V} {C : ℕ}
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    (Q : SimpleGraph V)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H) :
    (initialAmbientBadForPattern H B Q).card ≤
      (graphSupportFinset Q).card + (graphEdges Q).card * (3 * C) := by
  calc
    (initialAmbientBadForPattern H B Q).card ≤
        (graphSupportFinset Q).card +
          ((graphEdges Q).attach.biUnion fun e ↦
            initialAmbientBadForPair H B
              (out_fst_ne_snd_of_mem_graphEdges e.2)).card :=
      card_union_le _ _
    _ ≤ (graphSupportFinset Q).card +
        ∑ e ∈ (graphEdges Q).attach,
          (initialAmbientBadForPair H B
            (out_fst_ne_snd_of_mem_graphEdges e.2)).card := by
      gcongr
      exact card_biUnion_le
    _ ≤ (graphSupportFinset Q).card +
        ∑ _e ∈ (graphEdges Q).attach, 3 * C := by
      gcongr with e he
      apply card_initialAmbientBadForPair_le hdegree hbankSupport
      exact (hQ (graph_adj_out_of_mem_graphEdges e.2)).2.2
    _ = (graphSupportFinset Q).card +
        (graphEdges Q).card * (3 * C) := by simp

lemma initial_ambient_extension_loss_subset_pattern_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V}
    {B : TripleSystemOn V} {Q : SimpleGraph V} :
    univ \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q univ ⊆
      initialAmbientBadForPattern H B Q := by
  intro x hx
  have hxnotExtension := (mem_sdiff.mp hx).2
  by_cases hxSupport : x ∈ graphSupportFinset Q
  · exact mem_union_left _ hxSupport
  apply mem_union_right
  by_contra hxnotBad
  apply hxnotExtension
  rw [mem_iterationExtensionVertices_iff]
  refine ⟨mem_univ x, ?_⟩
  intro e he
  have hends := endpoint_mem_graphSupportFinset he
  have hxe₁ : x ≠ e.out.1 := fun h ↦ hxSupport (h ▸ hends.1)
  have hxe₂ : x ≠ e.out.2 := fun h ↦ hxSupport (h ▸ hends.2)
  let w : ThirdVertex e.out.1 e.out.2 := ⟨x, hxe₁, hxe₂⟩
  have hxnotPair : x ∉ initialAmbientBadForPair H B
      (out_fst_ne_snd_of_mem_graphEdges he) := by
    intro hxPair
    apply hxnotBad
    exact mem_biUnion.mpr ⟨⟨e, he⟩, mem_attach _ _, hxPair⟩
  have hwA : thirdVertexTriple
      (out_fst_ne_snd_of_mem_graphEdges he) w ∈
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available := by
    by_contra hnot
    exact hxnotPair
      (third_mem_initialAmbientBadForPair_of_not_available
        (out_fst_ne_snd_of_mem_graphEdges he) w hnot)
  refine ⟨thirdVertexTriple
      (out_fst_ne_snd_of_mem_graphEdges he) w, hwA, ?_, ?_⟩
  · exact third_mem_thirdVertexTriple _ _
  · have hs : s(e.out.1, e.out.2) ∈
        tripleEdgeFinset
          (thirdVertexTriple
            (out_fst_ne_snd_of_mem_graphEdges he) w) :=
      mk_mem_tripleEdgeFinset_iff.mpr
        ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
          out_fst_ne_snd_of_mem_graphEdges he⟩
    simpa only [e.out_eq] using hs

theorem card_initial_ambient_extension_loss_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hQsupport : (graphSupportFinset Q).card ≤ h) :
    (univ \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q univ).card ≤
      h + h ^ 2 * (3 * C) := by
  have hloss : (univ \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q univ).card ≤
      (initialAmbientBadForPattern H B Q).card :=
    card_le_card (initial_ambient_extension_loss_subset_pattern_bad
      (q := q))
  have hbad := card_initialAmbientBadForPattern_le
    hdegree hbankSupport Q hQ
  have hedge := card_graphEdges_le_graphSupportFinset_sq Q
  have hsq : (graphSupportFinset Q).card ^ 2 ≤ h ^ 2 := by
    gcongr
  calc
    (univ \ iterationExtensionVertices
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)).available Q univ).card
        ≤ (initialAmbientBadForPattern H B Q).card := hloss
    _ ≤ (graphSupportFinset Q).card +
        (graphEdges Q).card * (3 * C) := hbad
    _ ≤ h + (graphSupportFinset Q).card ^ 2 * (3 * C) := by
      exact Nat.add_le_add hQsupport (Nat.mul_le_mul_right (3 * C) hedge)
    _ ≤ h + h ^ 2 * (3 * C) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right (3 * C) hsq) h

/-! ## Initial degree losses -/

lemma initial_ambient_degree_loss_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    univ \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph V) H) univ v ⊆
      insert v (H.neighborFinset v) := by
  intro x hx
  have hxNotNeighbor := (mem_sdiff.mp hx).2
  by_cases hxv : x = v
  · exact mem_insert.mpr (Or.inl hxv)
  apply mem_insert.mpr
  right
  rw [SimpleGraph.mem_neighborFinset]
  by_contra hxNotH
  apply hxNotNeighbor
  apply mem_neighborsIn_iff.mpr
  refine ⟨mem_univ x, ?_⟩
  refine ⟨?_, Ne.symm hxv, hxNotH⟩
  simpa using Ne.symm hxv

lemma card_initial_ambient_degree_loss_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {C : ℕ} (hdegree : ∀ x, H.degree x ≤ C) (v : V) :
    (univ \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) univ v).card ≤
        C + 1 := by
  calc
    (univ \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) univ v).card
        ≤ (insert v (H.neighborFinset v)).card :=
      card_le_card (initial_ambient_degree_loss_subset H v)
    _ ≤ (H.neighborFinset v).card + 1 := card_insert_le _ _
    _ = H.degree v + 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ C + 1 := Nat.add_le_add_right (hdegree v) 1

lemma initial_root_degree_loss_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (v : V) :
    X \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph V) H) X v ⊆
      insert v (absorberRootNeighborSet H X v) := by
  intro x hx
  have hxX := (mem_sdiff.mp hx).1
  have hxNotNeighbor := (mem_sdiff.mp hx).2
  by_cases hxv : x = v
  · exact mem_insert.mpr (Or.inl hxv)
  apply mem_insert.mpr
  right
  apply mem_absorberRootNeighborSet_iff.mpr
  refine ⟨hxX, ?_⟩
  have hxH : H.Adj v x := by
    by_contra hxNotH
    apply hxNotNeighbor
    apply mem_neighborsIn_iff.mpr
    refine ⟨hxX, ?_⟩
    refine ⟨?_, Ne.symm hxv, hxNotH⟩
    simpa using Ne.symm hxv
  exact hxH.symm

lemma card_initial_root_degree_loss_le_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {q : ℕ} {B : TripleSystemOn V}
    (hroot : HasPaddedAbsorberRootBounds q H X B) (v : V) :
    (X \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) X v).card ≤ 15 := by
  calc
    (X \ neighborsIn
      (graphDifference (SimpleGraph.completeGraph V) H) X v).card
        ≤ (insert v (absorberRootNeighborSet H X v)).card :=
      card_le_card (initial_root_degree_loss_subset H X v)
    _ ≤ (absorberRootNeighborSet H X v).card + 1 := card_insert_le _ _
    _ ≤ 15 := by
      have hv := hroot.1 v
      omega

/-! ## The one-stage initial vortex -/

/-- The two-level vortex used in the final finite construction: the outer
level is the whole ambient vertex set, and the inner level is the flexible
root set of the padded absorber. -/
noncomputable def oneStageVortex
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) : Vortex V 1 where
  U i := if i = 0 then univ else X
  root := by simp
  antitone := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp
    have hj : j ≠ 0 := by
      intro hj
      subst j
      apply hi
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hij
    simpa [hi, hj]

@[simp]
lemma oneStageVortex_U_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) :
    (oneStageVortex X).U (0 : Fin 2) = univ := by
  simp [oneStageVortex]

@[simp]
lemma oneStageVortex_U_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) :
    (oneStageVortex X).U (1 : Fin 2) = X := by
  simp [oneStageVortex]

/-- Exact initial iteration typicality for the ambient/root two-level
vortex, reduced to four transparent scalar inequalities. -/
theorem initial_oneStage_isIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hbankSupport : (verticesOn B).card ≤ C)
    {xi : ℝ≥0} (hxi : xi ≤ 1)
    (hAmbientDegree : (C + 1 : ℝ≥0) ≤
      xi * (Fintype.card V : ℝ≥0))
    (hRootDegree : (15 : ℝ≥0) ≤ xi * (X.card : ℝ≥0))
    (hAmbientExtension : (h + h ^ 2 * (3 * C) : ℝ≥0) ≤
      xi * (Fintype.card V : ℝ≥0))
    (hRootExtension : (h + h ^ 2 * 36 : ℝ≥0) ≤
      xi * (X.card : ℝ≥0)) :
    IsIterationTypical (oneStageVortex X) (0 : Fin 2)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available
      1 1 xi h := by
  apply initialIterationTypical_of_loss_bounds
    (W := oneStageVortex X) (k := (0 : Fin 2))
    (G := graphDifference (SimpleGraph.completeGraph V) H)
    (A := (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available)
    xi hxi h
  · intro i _hki v _hv
    have hi : i = 0 := Fin.eq_zero i
    subst i
    have hnat := card_initial_ambient_degree_loss_le hdegree v
    have hcast :
        ((univ \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H) univ v).card :
            ℝ≥0) ≤ (C + 1 : ℝ≥0) := by
      exact_mod_cast hnat
    simpa [oneStageVortex] using hcast.trans hAmbientDegree
  · intro i _hki v _hv
    have hi : i = 0 := Fin.eq_zero i
    subst i
    have hnat := card_initial_root_degree_loss_le_fifteen hroot v
    have hcast :
        ((X \ neighborsIn
          (graphDifference (SimpleGraph.completeGraph V) H) X v).card :
            ℝ≥0) ≤ (15 : ℝ≥0) := by
      exact_mod_cast hnat
    simpa [oneStageVortex] using hcast.trans hRootDegree
  · intro i _hki iStar hiStar Q hQ _hQsupported hQcard
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rcases hiStar with rfl | rfl
    · have hnat := card_initial_ambient_extension_loss_le
        (q := q) hdegree hbankSupport hQ hQcard
      have hcast :
          ((univ \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q univ).card :
              ℝ≥0) ≤ (h + h ^ 2 * (3 * C) : ℝ≥0) := by
        exact_mod_cast hnat
      simpa [oneStageVortex] using hcast.trans hAmbientExtension
    · have hnat := card_initial_root_extension_loss_le hroot hQ hQcard
      have hcast :
          ((X \ iterationExtensionVertices
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available Q X).card :
              ℝ≥0) ≤ (h + h ^ 2 * 36 : ℝ≥0) := by
        exact_mod_cast hnat
      simpa [oneStageVortex] using hcast.trans hRootExtension

/-- The explicit padded high-girth absorber carries the complete initial
typicality certificate once the four elementary size inequalities hold. -/
theorem exists_paddedAbsorber_with_initial_oneStage_typicality
    {q h m n : ℕ} {xi : ℝ≥0}
    (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n)
    (hxi : xi ≤ 1)
    (hAmbientDegree :
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156 + 1 : ℕ) : ℝ≥0) ≤ xi * (n : ℝ≥0))
    (hRootDegree : (15 : ℝ≥0) ≤ xi * (m : ℝ≥0))
    (hAmbientExtension :
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * m) ^ 156)) : ℕ) : ℝ≥0) ≤ xi * (n : ℝ≥0))
    (hRootExtension :
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * (m : ℝ≥0)) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n),
        X.card = m ∧ HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          (verticesOn B).card ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * m) ^ 156) ^ 3 ∧
          HasPaddedAbsorberRootBounds q H X B ∧
          IsIterationTypical (oneStageVortex X) (0 : Fin 2)
            (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available
            1 1 xi h := by
  obtain ⟨H, X, B, hXcard, hA, hlocal, hBsupport, hdegree,
      hBcard, hroot⟩ :=
    exists_paddedEfficientAbsorber_with_rootBounds hm hfit
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hRootDegreeX : (15 : ℝ≥0) ≤ xi * (X.card : ℝ≥0) := by
    simpa only [hXcard] using hRootDegree
  have hRootExtensionX : (h + h ^ 2 * 36 : ℝ≥0) ≤
      xi * (X.card : ℝ≥0) := by
    simpa only [hXcard] using hRootExtension
  refine ⟨H, X, B, hXcard, hA, hlocal, hBsupport, hdegree,
    hBcard, hroot, ?_⟩
  exact initial_oneStage_isIterationTypical hroot hdegree hBsupport hxi
    (by
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        hAmbientDegree)
    hRootDegreeX
    (by
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat] using hAmbientExtension)
    hRootExtensionX

end

end Erdos207
