/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerCutWord

/-!
# Genuine-source owner replacement at a cut-edge head

The final backward edge is already removed by the auxiliary cut. Removing
exactly that step preserves all other signed occurrences. Restoring the
actual source prefix yields a biunique, realizable relation with the exact
source-minus-edge-head balance relative to the cut-deleted other owners.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

def entrySwitchEdges (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) : Set (V × V) :=
  (((L.familyEdges \ H.edgeSet) \ C) \
    directedSignedEdgeSet .backward (A.entrySteps u v hfinish)) ∪ A.forwardEdges

def entrySourceEdges (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) : Set (V × V) :=
  A.entrySwitchEdges u v hfinish C ∪ A.sourcePrefix.edgeSet

private theorem entry_retained_subset_retained (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (heC : (u, v) ∈ C) :
    (((L.familyEdges \ H.edgeSet) \ C) \
      directedSignedEdgeSet .backward (A.entrySteps u v hfinish)) ⊆
      (L.familyEdges \ H.edgeSet) \ L.representedEdges A.tail := by
  intro e he
  refine ⟨he.1.1, ?_⟩
  rw [A.entrySteps_backward_partition hs u v hfinish]
  rintro (hback | hlast)
  · exact he.2 hback
  · have heq : e = (u, v) := Set.mem_singleton_iff.1 hlast
    exact he.1.2 (heq.symm ▸ heC)

theorem entrySwitchEdges_subset_switch (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (heC : (u, v) ∈ C) : A.entrySwitchEdges u v hfinish C ⊆ A.switchEdges :=
  Set.union_subset_union (A.entry_retained_subset_retained hs u v hfinish C heC)
    Set.Subset.rfl

theorem entrySourceEdges_subset_source (hs : p.start ∈ L.lambda.source)
    (u v : V) (hfinish : p.finish = .edge u v) (C : Set (V × V))
    (heC : (u, v) ∈ C) : A.entrySourceEdges u v hfinish C ⊆ A.sourceEdges :=
  Set.union_subset_union (A.entrySwitchEdges_subset_switch hs u v hfinish C heC)
    Set.Subset.rfl

theorem entrySwitchEdges_biUnique
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) (heC : (u, v) ∈ C) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.entrySwitchEdges u v hfinish C) := by
  have hsub := A.entrySwitchEdges_subset_switch hs u v hfinish C heC
  have hbi := A.switchEdges_biUnique hL hH
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1 (hsub h₁) (hsub h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2 (hsub h₁) (hsub h₂)⟩

theorem entrySourceEdges_biUnique
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) (heC : (u, v) ∈ C) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.entrySourceEdges u v hfinish C) := by
  have hsub := A.entrySourceEdges_subset_source hs u v hfinish C heC
  have hbi := A.sourceEdges_biUnique hL hH
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1 (hsub h₁) (hsub h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2 (hsub h₁) (hsub h₂)⟩

theorem entrySwitchEdges_balance
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) (heC : (u, v) ∈ C)
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) (x : V) :
    edgeBalance (A.entrySwitchEdges u v hfinish C) x =
      edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
        propInt (x = A.anchor) - propInt (x = v) := by
  have hB := A.entrySteps_backward_subset_cut_reference hL hH hs u v hfinish C hcut
  have hbase : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ (L.familyEdges \ H.edgeSet) \ C) :=
    ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.1.1 h₂.1.1,
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.1.1 h₂.1.1⟩
  have hbi := A.entrySwitchEdges_biUnique hL hH hs u v hfinish C heC
  have hdisj := (A.retained_disjoint_forward hL).mono_left
    (A.entry_retained_subset_retained hs u v hfinish C heC)
  have hcalc := edgeBalance_sdiff_union_eq_add_sub hB hbase.2 hbase.1
    hbi.2 hbi.1 hdisj x
  have hdelta := A.entrySteps_direction_balance hL hH hs u v hfinish x
  change edgeBalance ((((L.familyEdges \ H.edgeSet) \ C) \
    directedSignedEdgeSet .backward (A.entrySteps u v hfinish)) ∪ A.forwardEdges) x = _
  omega

/-- The actual source prefix changes the anchor boundary to the true source. -/
theorem entrySourceEdges_balance
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) (heC : (u, v) ∈ C)
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) (x : V) :
    edgeBalance (A.entrySourceEdges u v hfinish C) x =
      edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
        propInt (x = H.initial) - propInt (x = v) := by
  have hswitch := A.entrySwitchEdges_biUnique hL hH hs u v hfinish C heC
  have hsource := A.entrySourceEdges_biUnique hL hH hs u v hfinish C heC
  have hdisj := (A.switchEdges_disjoint_prefix hH).mono_left
    (A.entrySwitchEdges_subset_switch hs u v hfinish C heC)
  have hadd := edgeBalance_sdiff_union_eq_add_sub
    (E := A.entrySwitchEdges u v hfinish C) (B := ∅) (F := A.sourcePrefix.edgeSet)
    (Set.empty_subset _) hswitch.2 hswitch.1
    (by simpa only [Set.sdiff_empty, entrySourceEdges] using hsource.2)
    (by simpa only [Set.sdiff_empty, entrySourceEdges] using hsource.1)
    (by simpa only [Set.sdiff_empty] using hdisj) x
  have hempty : edgeBalance (∅ : Set (V × V)) x = 0 := by
    simp [edgeBalance, HasOutgoing, HasIncoming, propInt]
  have hcalc : edgeBalance (A.entrySourceEdges u v hfinish C) x =
      edgeBalance (A.entrySwitchEdges u v hfinish C) x +
        edgeBalance A.sourcePrefix.edgeSet x := by
    simpa only [Set.sdiff_empty, entrySourceEdges, hempty, sub_zero] using hadd
  rw [hcalc, A.entrySwitchEdges_balance hL hH hs u v hfinish C heC hcut x,
    A.sourcePrefix_balance]
  omega

/-- Actual path/ray realization at the cut-edge head, for both source kinds. -/
theorem exists_entrySourceSwitchWarp
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) (u v : V) (hfinish : p.finish = .edge u v)
    (C : Set (V × V)) (heC : (u, v) ∈ C)
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∈ p.support → e = (u, v)) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      Alternating.familyEdges W = A.entrySourceEdges u v hfinish C \
        cyclicEdges (A.entrySourceEdges u v hfinish C) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (Alternating.familyEdges W) x =
        edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
          propInt (x = H.initial) - propInt (x = v) := by
  have hsub := A.entrySourceEdges_subset_source hs u v hfinish C heC
  have hreverse : ¬ ContainsReverseDirectedRay (A.entrySourceEdges u v hfinish C) := by
    rintro ⟨r, hr⟩
    exact A.sourceEdges_not_containsReverseDirectedRay hH ⟨r, fun n ↦ hsub (hr n)⟩
  obtain ⟨W, hW, hWE, hWI, hbalance⟩ :=
    GroundingFinitePerturbationRooting.exists_warp_with_edges_sdiff_cyclic
      (A.entrySourceEdges u v hfinish C) (hsub.trans A.sourceEdges_subset_adj)
      (A.entrySourceEdges_biUnique hL hH hs u v hfinish C heC) hreverse
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hbalance]
  exact A.entrySourceEdges_balance hL hH hs u v hfinish C heC hcut x

#print axioms entrySourceEdges_balance
#print axioms exists_entrySourceSwitchWarp

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
