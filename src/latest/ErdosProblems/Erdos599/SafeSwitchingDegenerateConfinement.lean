/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# Degenerate switching paths stay on the forward warp

The paper's `safeisnondegenerate` observation uses a short two-colour
argument.  Colour the retained reference edges `B` and the inserted forward
edges `F`.  If a finite switched path begins and ends with `F`, every `B`
block would be bracketed by two `F` edges.  Switching safeness excludes such
a block, so the whole path uses forward edges and hence lies on one member of
the forward warp.

This file deliberately says nothing about which member of an imaginary-edge
hammock is selected.  Applying the result to a particular assigned route
still requires an explicit switched-path witness for that route.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u}

namespace SwitchingCore

private theorem Walk.finish_not_mem_dropLast_of_isPath
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath) :
    b ∉ p.support.dropLast := by
  intro hb
  have hne := hp.rel_dropLast_getLast hb
  exact hne p.getLast_support.symm

/-- In a locally bi-unique two-colour relation with no nonempty
`F-B⁺-F` sandwich, a finite path with an outgoing `F` edge at its start and
an incoming `F` edge at its finish contains no `B` edge.  The endpoint
`F` edges need not themselves belong to the path; this is the form used for
a degenerate switching path between two exposed forward contacts. -/
theorem finitePath_edgeSet_subset_right_of_noForwardSandwich
    {D : Digraph V} (B F : Set (V × V))
    (hdisj : Disjoint B F)
    (hbiunique : Relator.BiUnique (fun x y => (x, y) ∈ B ∪ F))
    (hno : NoForwardSandwich (D := D) B F)
    (p : FinitePath D) (hcover : p.edgeSet ⊆ B ∪ F)
    (hstart : ∃ y, (p.start, y) ∈ F)
    (hfinish : ∃ x, (x, p.finish) ∈ F) :
    p.edgeSet ⊆ F := by
  classical
  intro e he
  rcases hcover he with heB | heF
  · let BTail : Set V :=
      {x | ∃ y, (x, y) ∈ p.edgeSet ∧ (x, y) ∈ B}
    have hstart_not_BTail : p.start ∉ BTail := by
      rintro ⟨y, _hpy, hyB⟩
      obtain ⟨z, hzF⟩ := hstart
      have hyz : y = z := hbiunique.2 (Or.inl hyB) (Or.inr hzF)
      subst z
      exact Set.disjoint_left.1 hdisj hyB hzF
    have hmeetB : p.walk.Meets BTail := by
      refine ⟨e.1, (p.edgeSet_subset_support_prod he).1, ?_⟩
      exact ⟨e.2, he, heB⟩
    let q := p.firstHit BTail hmeetB
    have hqfinishB : q.finish ∈ BTail :=
      p.firstHit_finish_mem BTail hmeetB
    obtain ⟨y, hqyP, hqyB⟩ := hqfinishB
    have hqne : q.start ≠ q.finish := by
      intro h
      apply hstart_not_BTail
      have hpq : p.start = q.finish := by
        calc
          p.start = q.start := rfl
          _ = q.finish := h
      rw [hpq]
      exact ⟨y, hqyP, hqyB⟩
    obtain ⟨a, haq⟩ :=
      FinitePath.exists_edge_to_of_mem_of_ne_start q q.finish_mem_support
        hqne.symm
    have hap : (a, q.finish) ∈ p.edgeSet :=
      p.firstHit_edgeSet_subset BTail hmeetB haq
    have haF : (a, q.finish) ∈ F := by
      rcases hcover hap with haB | haF
      · have haTail : a ∈ BTail := ⟨q.finish, hap, haB⟩
        have haBefore : a ∈ q.walk.support.dropLast :=
          Walk.edge_fst_mem_support_dropLast q.walk haq
        exact False.elim
          ((p.firstHit_no_mem_before BTail hmeetB haBefore) haTail)
      · exact haF
    have hqfinish_ne_pfinish : q.finish ≠ p.finish := by
      intro h
      have hdrop : q.finish ∈ p.walk.support.dropLast :=
        Walk.edge_fst_mem_support_dropLast p.walk hqyP
      rw [h] at hdrop
      exact (Walk.finish_not_mem_dropLast_of_isPath p.walk p.isPath) hdrop
    have hqfinishP : q.finish ∈ p.support :=
      p.firstHit_support_subset BTail hmeetB q.finish_mem_support
    let r := p.suffixFrom q.finish hqfinishP
    have hrne : r.start ≠ r.finish := by
      simpa [r] using hqfinish_ne_pfinish
    obtain ⟨c, hcr⟩ :=
      FinitePath.exists_edge_to_of_mem_of_ne_start r r.finish_mem_support
        hrne.symm
    have hcp : (c, r.finish) ∈ p.edgeSet :=
      p.suffixFrom_edgeSet_subset q.finish hqfinishP hcr
    have hcF : (c, r.finish) ∈ F := by
      rcases hcover hcp with hcB | hcF
      · obtain ⟨d, hdF⟩ := hfinish
        have hfinish_eq : r.finish = p.finish := by simp [r]
        have hdFr : (d, r.finish) ∈ F := by
          simpa [hfinish_eq] using hdF
        have hcd : c = d := hbiunique.1 (Or.inl hcB)
          (Or.inr hdFr)
        subst d
        exact False.elim
          (Set.disjoint_left.1 hdisj hcB hdFr)
      · exact hcF
    let FTail : Set V := {x | ∃ y, (x, y) ∈ F}
    have hqfinish_not_FTail : q.finish ∉ FTail := by
      rintro ⟨z, hzF⟩
      have hyz : y = z := hbiunique.2 (Or.inl hqyB) (Or.inr hzF)
      subst z
      exact Set.disjoint_left.1 hdisj hqyB hzF
    have hmeetF : r.walk.Meets FTail := by
      refine ⟨c, (r.edgeSet_subset_support_prod hcr).1, ?_⟩
      exact ⟨r.finish, hcF⟩
    let s := r.firstHit FTail hmeetF
    have hsfinishF : s.finish ∈ FTail :=
      r.firstHit_finish_mem FTail hmeetF
    obtain ⟨b, hbF⟩ := hsfinishF
    have hsne : s.start ≠ s.finish := by
      intro h
      apply hqfinish_not_FTail
      have hqs : q.finish = s.finish := by
        calc
          q.finish = r.start := by simp [r]
          _ = s.start := rfl
          _ = s.finish := h
      rw [hqs]
      exact ⟨b, hbF⟩
    have hsB : s.edgeSet ⊆ B := by
      intro f hf
      have hfr : f ∈ r.edgeSet :=
        r.firstHit_edgeSet_subset FTail hmeetF hf
      have hfp : f ∈ p.edgeSet :=
        p.suffixFrom_edgeSet_subset q.finish hqfinishP hfr
      rcases hcover hfp with hfB | hfF
      · exact hfB
      · have hfTail : f.1 ∈ FTail := ⟨f.2, hfF⟩
        have hfBefore : f.1 ∈ s.walk.support.dropLast :=
          Walk.edge_fst_mem_support_dropLast s.walk hf
        exact False.elim
          ((r.firstHit_no_mem_before FTail hmeetF hfBefore) hfTail)
    apply False.elim
    apply hno s hsne hsB a b
    · change (a, r.start) ∈ F
      simpa [r] using haF
    · exact hbF
  · exact heF

variable {Gamma : DWeb V}

/-- Forward edges of a bracket alternating path lie in the family-edge
relation of its forward warp. -/
theorem IsBracketAlternating.directionEdges_forward_subset_familyEdges
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (h : IsBracketAlternating U Y Q) :
    Q.directionEdges .forward ⊆ familyEdges U := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  rcases he with ⟨l, hlQ, hldir, hel⟩
  rcases h.2 l hlQ hldir with ⟨u, huU, hlu⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨u, huU, hlu.2 hel⟩

/-- Formal source `safeisnondegenerate` core.  A nontrivial finite path in
the switched relation, bracketed at both endpoints by forward edges of the
same switching-safe alternating path, is a fragment of one member of the
forward warp `U`. -/
theorem finiteSwitchedPath_isFragmentOf_forwardWarp
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hU : Gamma.IsWarp U) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hBracket : IsBracketAlternating U Y Q)
    (hSafe : IsSwitchingSafe Y Q)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ switchedEdges Y Q)
    (hstart : ∃ y, (p.start, y) ∈ Q.directionEdges .forward)
    (hfinish : ∃ x, (x, p.finish) ∈ Q.directionEdges .forward) :
    IsFragmentOf p U := by
  let B : Set (V × V) :=
    familyEdges Y \ Q.directionEdges .backward
  let F : Set (V × V) := Q.directionEdges .forward
  have hSwitch := hSafe.isSwitchingAlternating
  have hswitched : switchedEdges Y Q = B ∪ F := by
    simpa [B, F] using hSwitch.switchedEdges_eq
  have hdisj : Disjoint B F := by
    rw [Set.disjoint_left]
    intro e heB heF
    exact Set.disjoint_left.1
      hSwitch.forwardLinksOff.directionEdges_disjoint heF heB.1
  have hbiunique : Relator.BiUnique (fun x y => (x, y) ∈ B ∪ F) := by
    simpa only [← hswitched] using hSwitch.switchedEdges_biUnique
  have hno : NoForwardSandwich (D := Gamma.graph) B F := by
    simpa [B, F] using
      isSwitchingSafe_noForwardSandwich hYfinite hSafe
  have hpF : p.edgeSet ⊆ F :=
    finitePath_edgeSet_subset_right_of_noForwardSandwich B F hdisj hbiunique
      hno p (by simpa only [← hswitched] using hp)
      (by simpa [F] using hstart) (by simpa [F] using hfinish)
  apply finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hU p hpne
  exact hpF.trans (by
    simpa [F] using
      IsBracketAlternating.directionEdges_forward_subset_familyEdges hBracket)

end SwitchingCore
end Alternating
end Erdos599
