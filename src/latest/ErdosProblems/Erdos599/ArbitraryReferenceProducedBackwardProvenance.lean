/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArbitraryReferenceFracturedAssignment
import ErdosProblems.Erdos599.FracturedAssignmentProducedBackwardProvenance

/-!
# Produced backward provenance for a reference containing rays

The arbitrary-reference compiler runs the concrete projection against the
finite proxy.  A nontrivial backward link cannot be owned by a singleton ray
proxy, so every indexed proxy owner canonically promotes to a finite member
of the original reference.  Warp uniqueness preserves injectivity of owners.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Z Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}

namespace HasIndexedBackwardProvenance

/-- Indexed provenance in particular supplies ordinary backward ownership. -/
theorem backwardLinksOn
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y)) :
    BackwardLinksOn (finiteProxyReference Y) Q := by
  intro l hl hd
  rw [P.certificate.links_eq_range] at hl
  obtain ⟨i, rfl⟩ := hl
  exact ⟨P.certificate.owner i hd, P.certificate.owner_mem i hd,
    P.certificate.isSubpath i hd⟩

/-- The finite original-reference owner selected for one indexed backward
link. -/
noncomputable def finiteOriginalOwner
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y))
    (i : P.Index) (hd : (P.certificate.link i).direction = .backward) :
    FinitePath Gamma.graph :=
  (backwardLink_has_finiteOriginalOwner P.backwardLinksOn
    (by rw [P.certificate.links_eq_range]; exact ⟨i, rfl⟩) hd).choose

theorem finiteOriginalOwner_mem
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y))
    (i : P.Index) (hd : (P.certificate.link i).direction = .backward) :
    (.inl (P.finiteOriginalOwner i hd) : Gamma.DPath) ∈ Y :=
  (backwardLink_has_finiteOriginalOwner P.backwardLinksOn
    (by rw [P.certificate.links_eq_range]; exact ⟨i, rfl⟩) hd).choose_spec.1

theorem finiteOriginalOwner_isSubpath
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y))
    (i : P.Index) (hd : (P.certificate.link i).direction = .backward) :
    (P.certificate.link i).path.IsSubpathOf
      (.inl (P.finiteOriginalOwner i hd) : Gamma.DPath) :=
  (backwardLink_has_finiteOriginalOwner P.backwardLinksOn
    (by rw [P.certificate.links_eq_range]; exact ⟨i, rfl⟩) hd).choose_spec.2

/-- The proxy owner used by the concrete compiler is the unchanged finite
path selected above; singleton ray proxies cannot carry a nontrivial link. -/
theorem proxyOwner_eq_finiteOriginalOwner
    (hY : Gamma.IsWarp Y)
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y))
    (i : P.Index) (hd : (P.certificate.link i).direction = .backward) :
    P.certificate.owner i hd =
      (.inl (P.finiteOriginalOwner i hd) : Gamma.DPath) := by
  let p : Gamma.DPath := .inl (P.finiteOriginalOwner i hd)
  have hpProxy : p ∈ finiteProxyReference Y := by
    exact ⟨p, P.finiteOriginalOwner_mem i hd, by
      simp [p, finiteProxyPath]⟩
  obtain ⟨t, ht⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
    (P.certificate.link i).path
    (P.certificate.link i).path.start_mem_support
    (P.certificate.link i).nontrivial
  apply DWeb.IsWarp.eq_of_mem_support (finiteProxyReference_isWarp hY)
    (P.certificate.owner_mem i hd) hpProxy
  · exact ((P.certificate.owner i hd).edgeSet_subset_support_prod
      ((P.certificate.isSubpath i hd).2 ht)).1
  · exact (p.edgeSet_subset_support_prod
      ((P.finiteOriginalOwner_isSubpath i hd).2 ht)).1

/-- Promote the actual indexed compiler certificate from the finite proxy to
the original ray-containing reference. -/
noncomputable def liftFiniteProxy
    (hY : Gamma.IsWarp Y)
    (P : HasIndexedBackwardProvenance Q (finiteProxyReference Y)) :
    HasIndexedBackwardProvenance Q Y :=
  ⟨P.Index, {
    link := P.certificate.link
    links_eq_range := P.certificate.links_eq_range
    owner := fun i hd => .inl (P.finiteOriginalOwner i hd)
    owner_mem := P.finiteOriginalOwner_mem
    isSubpath := P.finiteOriginalOwner_isSubpath
    owner_unique := by
      intro i j hi hj howner
      apply P.certificate.owner_unique i j hi hj
      exact (P.proxyOwner_eq_finiteOriginalOwner hY i hi).trans
        (howner.trans (P.proxyOwner_eq_finiteOriginalOwner hY j hj).symm) }⟩

end HasIndexedBackwardProvenance

namespace ProducedBracketFracturedAssignment

/-- Reindex the produced assignment to the full-reference source domain and
promote every retained compiler owner.  Assigned traces are unchanged. -/
noncomputable def liftFiniteProxy
    {F : FracturedWarp Gamma}
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (B : ProducedBracketFracturedAssignment F (finiteProxyReference Y)) :
    ProducedBracketFracturedAssignment F Y where
  bracket := B.bracket.liftFiniteProxy hboundary hY
  backward z := by
    change HasIndexedBackwardProvenance
      (B.bracket.assignment.assigned (toFiniteProxySource z)) Y
    exact (B.backward (toFiniteProxySource z)).liftFiniteProxy hY

end ProducedBracketFracturedAssignment

/-- The actual finite/infinite projection compiler, with indexed owners
retained, for an arbitrary boundary-aligned reference warp. -/
theorem exists_producedBracketFracturedAssignment_anyReference
    (F : FracturedWarp Gamma)
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (hFfinite : Gamma.HasFiniteCharacter F.paths)
    (hFedgeFinite : Gamma.HasFiniteCharacter F.edgeWarp)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.paths) :
    Nonempty (ProducedBracketFracturedAssignment F Y) := by
  have hinitialProxy :
      Gamma.initialSet (finiteProxyReference Y) ⊆
        Gamma.initialSet F.paths := by
    rwa [initialSet_finiteProxyReference]
  obtain ⟨B⟩ := exists_producedBracketFracturedAssignment F
    (_root_.Erdos599.Blueprint.LinkageBlueprint.BoundaryAligned.finiteProxyReference
      hboundary)
    (finiteProxyReference_isWarp hY) hFfinite hFedgeFinite
    (finiteProxyReference_hasFiniteCharacter Y) hinitialProxy
  exact ⟨B.liftFiniteProxy hboundary hY⟩

namespace OutsideFracturedWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- Cut-facing arbitrary-reference form of the provenance-preserving
compiler. -/
theorem exists_producedBracketFracturedAssignment_anyReference
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (ProducedBracketFracturedAssignment F.holes Y) :=
  FracturedAssignmentPeel.exists_producedBracketFracturedAssignment_anyReference
    F.holes hboundary hY F.finiteCharacter F.edgeWarpFiniteCharacter hinitial

end OutsideFracturedWarp

#print axioms HasIndexedBackwardProvenance.liftFiniteProxy
#print axioms ProducedBracketFracturedAssignment.liftFiniteProxy
#print axioms exists_producedBracketFracturedAssignment_anyReference
#print axioms OutsideFracturedWarp.exists_producedBracketFracturedAssignment_anyReference

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599

