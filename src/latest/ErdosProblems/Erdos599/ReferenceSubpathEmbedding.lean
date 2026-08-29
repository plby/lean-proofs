/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayEndpointCoveredClaim2

/-!
# Internal safeness under injective reference-owner embeddings

A local reference interval may start in the middle of its global owner.
Prefix-based transport is consequently too restrictive.  The exact facts
needed are an injective owner map, support and edge containment, and a global
warp.  They preserve internal safeness but do not assert the exposed
endpoint clauses of full safeness.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}

/-- Each local reference member has its own global owner and is a subpath
of that owner, in the exact support-and-edge sense used by alternation. -/
structure ReferenceSubpathEmbedding
    (Gamma : DWeb V) (Local Global : Set Gamma.DPath) where
  owner : Local → Global
  owner_injective : Function.Injective owner
  support_subset : ∀ p, p.1.support ⊆ (owner p).1.support
  edgeSet_subset : ∀ p, p.1.edgeSet ⊆ (owner p).1.edgeSet
  global_isWarp : Gamma.IsWarp Global

namespace ReferenceSubpathEmbedding

variable {Gamma : DWeb V} {Local Global : Set Gamma.DPath}

theorem familyEdges_subset
    (E : ReferenceSubpathEmbedding Gamma Local Global) :
    familyEdges Local ⊆ familyEdges Global := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2,
    E.edgeSet_subset ⟨p, hp⟩ hep⟩

/-- A local backward fragment is a fragment of its actual global owner. -/
theorem fragment_global
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {f : FinitePath Gamma.graph} (hf : IsFragmentOf f Local) :
    IsFragmentOf f Global := by
  obtain ⟨p, hp, hfp⟩ := hf
  exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2,
    hfp.1.trans (E.support_subset ⟨p, hp⟩),
    hfp.2.trans (E.edgeSet_subset ⟨p, hp⟩)⟩

/-- Two local members with a common global owner are the same member. -/
theorem eq_of_owner_support_inter
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {p q : Local} {x : V}
    (hxp : x ∈ (E.owner p).1.support)
    (hxq : x ∈ (E.owner q).1.support) : p = q := by
  apply E.owner_injective
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support E.global_isWarp
    (E.owner p).2 (E.owner q).2 hxp hxq

/-- Backward edges see exactly the unique local interval inside one global
owner; disjoint global owners cannot contribute another local fragment. -/
theorem backward_inter_owner_eq
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph} (hback : BackwardLinksOn Local Q)
    (p : Local) :
    Q.directionEdges .backward ∩ (E.owner p).1.edgeSet =
      Q.directionEdges .backward ∩ p.1.edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨heBack, heOwner⟩
    have heBack' := heBack
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heBack'
    obtain ⟨l, hl, hdir, hel⟩ := heBack'
    obtain ⟨q, hq, hlq⟩ := hback l hl hdir
    have heq : e ∈ q.edgeSet := hlq.2 hel
    have hqEq : (⟨q, hq⟩ : Local) = p :=
      E.eq_of_owner_support_inter
        (E.support_subset ⟨q, hq⟩ (q.edgeSet_subset_support_prod heq).1)
        ((E.owner p).1.edgeSet_subset_support_prod heOwner).1
    refine ⟨heBack, ?_⟩
    have hval : q = p.1 := congrArg Subtype.val hqEq
    rwa [← hval]
  · rintro e ⟨heBack, hep⟩
    exact ⟨heBack, E.edgeSet_subset p hep⟩

/-- Every local backward edge interval remains an interval of its global
owner.  Owners with no backward edge contact have empty intersection. -/
theorem backwardIntervals_global
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph} (hQ : InternallySafe Local Q) :
    ∀ p ∈ Global,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p := by
  classical
  intro p hp
  by_cases hempty : Q.directionEdges .backward ∩ p.edgeSet = ∅
  · exact Or.inl hempty
  obtain ⟨e, heBack, hep⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  simp only [AltPath.directionEdges, Set.mem_iUnion] at heBack
  obtain ⟨l, hl, hdir, hel⟩ := heBack
  obtain ⟨q, hq, hlq⟩ := hQ.2.1 l hl hdir
  let qs : Local := ⟨q, hq⟩
  have howner : (E.owner qs).1 = p := by
    apply DWeb.IsWarp.eq_of_mem_support E.global_isWarp (E.owner qs).2 hp
    · exact E.support_subset qs (hlq.1 (l.path.edgeSet_subset_support_prod hel).1)
    · exact (p.edgeSet_subset_support_prod hep).1
  have heq : Q.directionEdges .backward ∩ p.edgeSet =
      Q.directionEdges .backward ∩ q.edgeSet := by
    rw [← howner]
    exact E.backward_inter_owner_eq hQ.2.1 qs
  rw [heq]
  rcases hQ.2.2.1 q hq with hnone | ⟨f, hfq, hinter⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨f, ⟨?_, ?_⟩, hinter⟩
    · rw [← howner]
      exact hfq.1.trans (E.support_subset qs)
    · rw [← howner]
      exact hfq.2.trans (E.edgeSet_subset qs)

/-- Internal safeness transports without any assumption about the exposed
endpoints.  Covered endpoints are handled by the separate classification. -/
theorem internallySafe
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph} (hQ : InternallySafe Local Q) :
    InternallySafe Global Q := by
  refine ⟨E.global_isWarp, ?_, E.backwardIntervals_global hQ, ?_, ?_⟩
  · intro l hl hdir
    exact E.fragment_global (hQ.2.1 l hl hdir)
  · rintro ⟨r, hr⟩
    exact hQ.2.2.2.1 ⟨r, hr.trans (by
      intro e he
      exact ⟨he.1, fun heLocal => he.2 (E.familyEdges_subset heLocal)⟩)⟩
  · rintro ⟨c, hc⟩
    exact hQ.2.2.2.2 ⟨c, hc.trans (by
      intro e he
      exact ⟨he.1, fun heLocal => he.2 (E.familyEdges_subset heLocal)⟩)⟩

end ReferenceSubpathEmbedding

#print axioms ReferenceSubpathEmbedding.backward_inter_owner_eq
#print axioms ReferenceSubpathEmbedding.backwardIntervals_global
#print axioms ReferenceSubpathEmbedding.internallySafe

end Erdos599.Blueprint
