/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerSwitchRealization

/-!
# Owner transactions whose raw path avoids every cut-edge gadget

For old-vertex requests the full attached word is retained. All backward
edges avoid the cut, and the actual cut switch is a subrelation of the
already checked owner switch. The genuine source prefix is unchanged.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

def cutSwitchEdges (C : Set (V × V)) : Set (V × V) :=
  (((L.familyEdges \ H.edgeSet) \ C) \ L.representedEdges A.tail) ∪ A.forwardEdges

def cutSourceEdges (C : Set (V × V)) : Set (V × V) :=
  A.cutSwitchEdges C ∪ A.sourcePrefix.edgeSet

theorem cutSwitchEdges_subset_switch (C : Set (V × V)) :
    A.cutSwitchEdges C ⊆ A.switchEdges := by
  intro e he
  rcases he with he | he
  · exact Or.inl ⟨he.1.1, he.2⟩
  · exact Or.inr he

theorem cutSourceEdges_subset_source (C : Set (V × V)) :
    A.cutSourceEdges C ⊆ A.sourceEdges :=
  Set.union_subset_union (A.cutSwitchEdges_subset_switch C) Set.Subset.rfl

theorem cutSwitchEdges_biUnique (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (C : Set (V × V)) : Relator.BiUnique (fun x y ↦ (x, y) ∈ A.cutSwitchEdges C) := by
  have hsub := A.cutSwitchEdges_subset_switch C
  have hbi := A.switchEdges_biUnique hL hH
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1 (hsub h₁) (hsub h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2 (hsub h₁) (hsub h₂)⟩

theorem cutSourceEdges_biUnique (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (C : Set (V × V)) : Relator.BiUnique (fun x y ↦ (x, y) ∈ A.cutSourceEdges C) := by
  have hsub := A.cutSourceEdges_subset_source C
  have hbi := A.sourceEdges_biUnique hL hH
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1 (hsub h₁) (hsub h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2 (hsub h₁) (hsub h₂)⟩

theorem cutSwitchEdges_balance (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V} (ht : L.gadgetExit p.finish = some t)
    (C : Set (V × V))
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∉ p.support) (x : V) :
    edgeBalance (A.cutSwitchEdges C) x = edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
      propInt (x = A.anchor) - propInt (x = t) := by
  have hB : L.representedEdges A.tail ⊆ (L.familyEdges \ H.edgeSet) \ C := by
    intro e he
    exact ⟨A.backward_subset_ownerDeleted hH he,
      fun heC ↦ hcut e heC (A.tail_support_subset he.1)⟩
  have hbase : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ (L.familyEdges \ H.edgeSet) \ C) :=
    ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.1.1 h₂.1.1,
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.1.1 h₂.1.1⟩
  have hbi := A.cutSwitchEdges_biUnique hL hH C
  have hretained : (((L.familyEdges \ H.edgeSet) \ C) \ L.representedEdges A.tail) ⊆
      (L.familyEdges \ H.edgeSet) \ L.representedEdges A.tail := by
    intro e he
    exact ⟨he.1.1, he.2⟩
  have hdisj := (A.retained_disjoint_forward hL).mono_left hretained
  have hcalc := edgeBalance_sdiff_union_eq_add_sub hB hbase.2 hbase.1
    hbi.2 hbi.1 hdisj x
  have hdelta := A.direction_balance hL hH hs ht x
  change edgeBalance ((((L.familyEdges \ H.edgeSet) \ C) \
    L.representedEdges A.tail) ∪ A.forwardEdges) x = _
  omega

/-- All cuts avoiding the signed suffix preserve the exact genuine-source balance. -/
theorem cutSourceEdges_balance (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V} (ht : L.gadgetExit p.finish = some t)
    (C : Set (V × V))
    (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∉ p.support) (x : V) :
    edgeBalance (A.cutSourceEdges C) x = edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
      propInt (x = H.initial) - propInt (x = t) := by
  have hswitch := A.cutSwitchEdges_biUnique hL hH C
  have hsource := A.cutSourceEdges_biUnique hL hH C
  have hdisj := (A.switchEdges_disjoint_prefix hH).mono_left
    (A.cutSwitchEdges_subset_switch C)
  have hadd := edgeBalance_sdiff_union_eq_add_sub
    (E := A.cutSwitchEdges C) (B := ∅) (F := A.sourcePrefix.edgeSet)
    (Set.empty_subset _) hswitch.2 hswitch.1
    (by simpa only [Set.sdiff_empty, cutSourceEdges] using hsource.2)
    (by simpa only [Set.sdiff_empty, cutSourceEdges] using hsource.1)
    (by simpa only [Set.sdiff_empty] using hdisj) x
  have hempty : edgeBalance (∅ : Set (V × V)) x = 0 := by
    simp [edgeBalance, HasOutgoing, HasIncoming, propInt]
  have hcalc : edgeBalance (A.cutSourceEdges C) x =
      edgeBalance (A.cutSwitchEdges C) x + edgeBalance A.sourcePrefix.edgeSet x := by
    simpa only [Set.sdiff_empty, cutSourceEdges, hempty, sub_zero] using hadd
  rw [hcalc, A.cutSwitchEdges_balance hL hH hs ht C hcut x, A.sourcePrefix_balance]
  omega

/-- Actual path/ray realization without an omitted final gadget. -/
theorem exists_cutSourceSwitchWarp (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V} (ht : L.gadgetExit p.finish = some t)
    (C : Set (V × V)) (hcut : ∀ e ∈ C, LambdaVertex.edge e.1 e.2 ∉ p.support) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      Alternating.familyEdges W = A.cutSourceEdges C \ cyclicEdges (A.cutSourceEdges C) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (Alternating.familyEdges W) x =
        edgeBalance ((L.familyEdges \ H.edgeSet) \ C) x +
          propInt (x = H.initial) - propInt (x = t) := by
  have hsub := A.cutSourceEdges_subset_source C
  have hreverse : ¬ ContainsReverseDirectedRay (A.cutSourceEdges C) := by
    rintro ⟨r, hr⟩
    exact A.sourceEdges_not_containsReverseDirectedRay hH ⟨r, fun n ↦ hsub (hr n)⟩
  obtain ⟨W, hW, hWE, hWI, hbalance⟩ :=
    GroundingFinitePerturbationRooting.exists_warp_with_edges_sdiff_cyclic
      (A.cutSourceEdges C) (hsub.trans A.sourceEdges_subset_adj)
      (A.cutSourceEdges_biUnique hL hH C) hreverse
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hbalance]
  exact A.cutSourceEdges_balance hL hH hs ht C hcut x

#print axioms cutSourceEdges_balance
#print axioms exists_cutSourceSwitchWarp

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
