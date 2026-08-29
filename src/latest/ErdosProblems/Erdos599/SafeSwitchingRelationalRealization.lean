/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalConfinement

/-!
# Exact finite-warp realization of an interval-convex relational switch

This assembles the two-colour path-component argument without an alternating
path compiler. Both colour relations lie in finite-character warps; interval
convexity and local biuniqueness prevent mixed infinite components and cycles.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact realization using a no-sandwich certificate, which may be
inherited from a larger reference without localizing an entire word. -/
theorem exists_finiteWarp_realizing_incidence_noForwardSandwich
    {W Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hno : NoForwardSandwich (D := Gamma.graph) (familyEdges Y \ R) F)
    (I : Set V)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      familyEdges U = E ∧ isolatedVertices U = I ∧ Gamma.HasFiniteCharacter U := by
  let B := familyEdges Y \ R
  have hgraph : B ∪ F ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    rintro e (hB | hF')
    · exact familyEdges_subset_adj Y hB.1
    · exact familyEdges_subset_adj W (hF hF')
  have hdisj : Disjoint B F := retained_disjoint_inserted_of_incidence hin
  have hBcycle : ¬ContainsDirectedCycle B := by
    rintro ⟨C, hC⟩
    exact familyEdges_not_containsDirectedCycle hY hYfinite
      ⟨C, hC.trans Set.sdiff_subset⟩
  have hBray : ¬ContainsDirectedRay B := by
    rintro ⟨r, hr⟩
    exact familyEdges_not_containsDirectedRay hY hYfinite
      ⟨r, hr.trans Set.sdiff_subset⟩
  have hBreverse : ¬ContainsReverseDirectedRay B := by
    rintro ⟨r, hr⟩
    exact familyEdges_not_containsReverseDirectedRay hY hYfinite
      ⟨r, fun n ↦ (hr n).1⟩
  have hFcycle : ¬ContainsDirectedCycle F := by
    rintro ⟨C, hC⟩
    exact familyEdges_not_containsDirectedCycle hW hWfinite ⟨C, hC.trans hF⟩
  have hFray : ¬ContainsDirectedRay F := by
    rintro ⟨r, hr⟩
    exact familyEdges_not_containsDirectedRay hW hWfinite ⟨r, hr.trans hF⟩
  have hFreverse : ¬ContainsReverseDirectedRay F := by
    rintro ⟨r, hr⟩
    exact familyEdges_not_containsReverseDirectedRay hW hWfinite
      ⟨r, fun n ↦ hF (hr n)⟩
  have hcycle : ¬ContainsDirectedCycle E := by
    rw [hE]
    exact union_not_containsDirectedCycle B F hgraph hdisj hno hBcycle hFcycle
  have hray : ¬ContainsDirectedRay E := by
    rw [hE]
    exact union_not_containsDirectedRay B F hgraph hno hBray hFray
  have hreverse : ¬ContainsReverseDirectedRay E := by
    rw [hE]
    exact union_not_containsReverseDirectedRay B F hgraph hno hBreverse hFreverse
  exact RelationDecomposition.DWeb.exists_finiteWarp_realizing_biUnique
    Gamma E I (by simpa only [hE] using hgraph) hunique hcycle hray hreverse hI

/-- The interval-switch API, with its original hypotheses and conclusion. -/
theorem exists_finiteWarp_realizing_incidence_intervalSwitch
    {W Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (I : Set V)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      familyEdges U = E ∧ isolatedVertices U = I ∧ Gamma.HasFiniteCharacter U :=
  exists_finiteWarp_realizing_incidence_noForwardSandwich hW hY hWfinite hYfinite
    hF hin hE hunique
    (noForwardSandwich_of_incidence_intervalConvex hY hin hout hinterval hpure) I hI

/-- Backwards-compatible disjoint-edge specialization. -/
theorem exists_finiteWarp_realizing_intervalSwitch
    {W Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (_hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (hFdisj : Disjoint F (familyEdges Y))
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (I : Set V)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      familyEdges U = E ∧ isolatedVertices U = I ∧ Gamma.HasFiniteCharacter U :=
  exists_finiteWarp_realizing_incidence_intervalSwitch hW hY hWfinite hYfinite hF
    (incoming_mem_removed hE hunique hFdisj)
    (outgoing_mem_removed hE hunique hFdisj) hE hunique hinterval hpure I hI

#print axioms exists_finiteWarp_realizing_incidence_noForwardSandwich
#print axioms exists_finiteWarp_realizing_incidence_intervalSwitch
#print axioms exists_finiteWarp_realizing_intervalSwitch

end Erdos599.Alternating.SwitchingCore.RelationalInterval
