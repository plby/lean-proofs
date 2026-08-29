/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeIntervalRestriction
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Source-changing extraction from a finite reference-balanced relation

An interval-convex removed relation and a finite original forward
subrelation, balanced at every reference vertex, give an original safe word
to any negative exterior boundary. This is not a claim that the saturated
Hall family has zero interior defects.
-/

namespace Erdos599.Alternating.ColouredSafeBalancedTerminalExtraction

open Set DirectedPath TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem exists_finiteEdgeSubwarp
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {F : Set (V × V)} (hF : F.Finite) (hFW : F ⊆ familyEdges W) :
    ∃ H : Set Gamma.DPath, Gamma.IsWarp H ∧ Gamma.HasFiniteCharacter H ∧
      (Gamma.vertexSet H).Finite ∧ familyEdges H = F ∧ isolatedVertices H = ∅ := by
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ F) :=
    ⟨fun _ _ _ h₁ h₂ ↦ (IsWarp.familyEdges_biUnique hW).1 (hFW h₁) (hFW h₂),
      fun _ _ _ h₁ h₂ ↦ (IsWarp.familyEdges_biUnique hW).2 (hFW h₁) (hFW h₂)⟩
  have hcycle : ¬ContainsDirectedCycle F := by
    rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hW hWfin ⟨C, hC.trans hFW⟩
  have hreverse : ¬ContainsReverseDirectedRay F := by
    rintro ⟨r, hr⟩
    exact SwitchingCore.familyEdges_not_containsReverseDirectedRay hW hWfin
      ⟨r, fun n ↦ hFW (hr n)⟩
  obtain ⟨H, hH, hHE, hHI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma F ∅ (hFW.trans (familyEdges_subset_adj W)) hbi hcycle hreverse
      (fun _ h ↦ h.elim)
  have hHV : (Gamma.vertexSet H).Finite := by
    apply ((hF.image Prod.fst).union (hF.image Prod.snd)).subset
    intro x hx
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hH,
      hHI, hHE, Set.empty_union] at hx
    rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inr ⟨(y, x), hy, rfl⟩
    · exact Or.inl ⟨(x, y), hy, rfl⟩
  have hHfin : Gamma.HasFiniteCharacter H := by
    intro p hp
    cases p with
    | inl q => exact ⟨q, rfl⟩
    | inr r =>
        exact False.elim (hHV.not_infinite
          (Set.infinite_of_injective_forall_mem r.injective
            (fun n ↦ ⟨Sum.inr r, hp, r.apply_mem_support n⟩)))
  exact ⟨H, hH, hHfin, hHV, hHE, hHI⟩

private theorem vertexSet_subset_of_edges_subset_of_noIsolated
    {H : Set Gamma.DPath} (hH : Gamma.IsWarp H) (hHI : isolatedVertices H = ∅)
    (hHY : familyEdges H ⊆ familyEdges Y) : Gamma.vertexSet H ⊆ Gamma.vertexSet Y := by
  intro x hx
  rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hH,
    hHI, Set.empty_union] at hx
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact (familyEdges_subset_vertexSet_prod Y (hHY hy)).2
  · exact (familyEdges_subset_vertexSet_prod Y (hHY hy)).1

/-- The finite relation argument changes only the source. It retains both
the prescribed terminal and literal original forward ownership. -/
theorem exists_safeWord_to_negativeBoundary
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {F R : Set (V × V)} (hF : F.Finite) (hR : R.Finite)
    (hFW : F ⊆ familyEdges W) (hRY : R ⊆ familyEdges Y)
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hin : ∀ {a b x : V}, (a, x) ∈ F → (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F → (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (hbalance : ∀ x ∈ Gamma.vertexSet Y, edgeBalance F x = edgeBalance R x)
    {t : V} (htOff : t ∉ Gamma.vertexSet Y) (ht : edgeBalance F t = -1) :
    ∃ s, s ∉ Gamma.vertexSet Y ∧ edgeBalance F s = 1 ∧
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧ Q.forwardEdges ⊆ F := by
  obtain ⟨H, hH, hHfin, hHV, hHE, hHI⟩ := exists_finiteEdgeSubwarp hW hWfin hF hFW
  obtain ⟨K, hK, hKfin, hKV, hKE, hKI, howners⟩ :=
    ColouredSafeIntervalRestriction.exists_intervalRestriction hY hYfin hR hRY hinterval
  have hKsub : Gamma.vertexSet K ⊆ Gamma.vertexSet Y :=
    vertexSet_subset_of_edges_subset_of_noIsolated hK hKI (hKE ▸ hRY)
  have hHinitial (x : V) : x ∈ Gamma.initialSet H ↔ edgeBalance F x = 1 := by
    rw [TerminalContactSwitch.mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hH,
      hHI, hHE]
    simp only [Set.notMem_empty, false_or]
  have hHterminal (x : V) : x ∈ Gamma.terminalFrontier H ↔ edgeBalance F x = -1 := by
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp hH,
      hHI, hHE]
    simp only [Set.notMem_empty, false_or]
  have hKinitial (x : V) : x ∈ Gamma.initialSet K ↔ edgeBalance R x = 1 := by
    rw [TerminalContactSwitch.mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hK,
      hKI, hKE]
    simp only [Set.notMem_empty, false_or]
  have hKterminal (x : V) : x ∈ Gamma.terminalFrontier K ↔ edgeBalance R x = -1 := by
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp hK,
      hKI, hKE]
    simp only [Set.notMem_empty, false_or]
  have hterm : Gamma.terminalFrontier K ⊆ Gamma.terminalFrontier H := by
    intro x hx
    apply (hHterminal x).mpr
    exact (hbalance x (hKsub (terminalFrontier_subset_vertexSet K hx))).trans
      ((hKterminal x).mp hx)
  have hinit : Gamma.initialSet H ∩ Gamma.vertexSet K ⊆ Gamma.initialSet K := by
    intro x hx
    apply (hKinitial x).mpr
    exact (hbalance x (hKsub hx.2)).symm.trans ((hHinitial x).mp hx.1)
  obtain ⟨s, hs, Q, hQ, hfirst, hlast⟩ :=
    ColouredSafeFiniteDuality.exists_safeWord_to_terminal hH hK hHfin hKfin hHV hKV
      hterm hinit ⟨(hHterminal t).mpr ht, fun hx ↦ htOff (hKsub hx)⟩
  have hsBalance : edgeBalance F s = 1 := (hHinitial s).mp hs.1
  have hsOff : s ∉ Gamma.vertexSet Y := by
    intro hsY
    have hsK : s ∈ Gamma.initialSet K :=
      (hKinitial s).mpr ((hbalance s hsY).symm.trans hsBalance)
    exact hs.2 (initialSet_subset_vertexSet K hsK)
  have hHW : familyEdges H ⊆ familyEdges W := hHE ▸ hFW
  refine ⟨s, hsOff, hsBalance, Q.retypeEdges hHW (hKE ▸ hRY), ?_, hfirst, hlast, ?_⟩
  · apply ColouredSafeIntervalRestriction.promote_safeWord hHW hKE hRY howners
      (fun h he ↦ hin (hHE ▸ h) he) (fun h he ↦ hout (hHE ▸ h) he)
      (fun h ↦ hpure (hHE ▸ h)) Q hQ
  · exact hHE ▸ Q.forwardEdges_subset_familyEdges

#print axioms exists_finiteEdgeSubwarp
#print axioms exists_safeWord_to_negativeBoundary

end Erdos599.Alternating.ColouredSafeBalancedTerminalExtraction
