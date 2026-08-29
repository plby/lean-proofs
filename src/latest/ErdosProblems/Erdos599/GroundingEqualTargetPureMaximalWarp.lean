/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualAvoidingMaximalWarp
import ErdosProblems.Erdos599.GroundingTargetPureChronology

/-!
# Target-pure maximal avoiding warps

Ambient equal-stage decoding uses first-target chronology.  Consequently the
collision-avoiding Zorn family must itself consist of target-pure paths.
Maximality is tested only on target-pure candidates, but every clean
source--target path still meets its carrier: truncate that candidate at its
first target and invoke maximality on the normalized prefix.

The conclusion is deliberately carrier intersection.  Maximality can place
the normalized prefix in the family; it does not imply that an unnormalized
candidate with a tail beyond its first target is itself a family member.
-/

noncomputable section

open Set

namespace Erdos599
namespace Popular

open DirectedPath
open PopularAuxiliary

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A source-restricted maximal target-pure warp in the auxiliary web whose
members all avoid `X`. -/
structure MaximalTargetPureAvoidingRestrictedXSWarp
    (L : Input Gamma I) (A X : Set (Input.LambdaVertex V I))
    extends FiniteWarp L.lambda where
  starts_in_allowed : ∀ {p}, p ∈ paths → p.start ∈ A
  ends_in_target : ∀ {p}, p ∈ paths → p.finish ∈ L.lambda.target
  paths_targetPure : ∀ {p}, p ∈ paths → L.IsTargetPure p
  paths_avoid : ∀ {p}, p ∈ paths → Disjoint p.support X
  maximal_disjoint : ∀ (p : FinitePath L.lambda.graph),
    p.start ∈ A → p.finish ∈ L.lambda.target → L.IsTargetPure p →
    Disjoint p.support X →
    Disjoint p.support (finiteVertexSet paths) → p ∈ paths

namespace MaximalTargetPureAvoidingRestrictedXSWarp

variable {L : Input Gamma I}
  {A X : Set (Input.LambdaVertex V I)}

/-- Forget maximality, target purity, and avoidance. -/
def toXSWarp (M : MaximalTargetPureAvoidingRestrictedXSWarp L A X)
    (hA : A ⊆ L.lambda.source) :
    XSWarp L.lambda L.lambda.target where
  paths := M.paths
  disjoint := M.disjoint
  starts_in_source hp := hA (M.starts_in_allowed hp)
  ends_in_target := M.ends_in_target

/-- The carrier remains disjoint from the prescribed auxiliary collision
set. -/
theorem finiteVertexSet_disjoint
    (M : MaximalTargetPureAvoidingRestrictedXSWarp L A X) :
    Disjoint (finiteVertexSet M.paths) X := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpM, hxp⟩ hxX
  exact Set.disjoint_left.1 (M.paths_avoid hpM) hxp hxX

/-- Every clean admissible source--target candidate meets the target-pure
maximal carrier.  The candidate itself need not be target-pure. -/
theorem finiteVertexSet_meets
    (M : MaximalTargetPureAvoidingRestrictedXSWarp L A X)
    (p : FinitePath L.lambda.graph) (hpA : p.start ∈ A)
    (hpT : p.finish ∈ L.lambda.target)
    (hpX : Disjoint p.support X) :
    (p.support ∩ finiteVertexSet M.paths).Nonempty := by
  let hmeet : p.walk.Meets L.lambda.target :=
    ⟨p.finish, p.finish_mem_support, hpT⟩
  let q := p.firstHit L.lambda.target hmeet
  have hqSupport : q.support ⊆ p.support :=
    p.firstHit_support_subset L.lambda.target hmeet
  have hqA : q.start ∈ A := by
    change p.start ∈ A
    exact hpA
  have hqT : q.finish ∈ L.lambda.target :=
    p.firstHit_finish_mem L.lambda.target hmeet
  have hqPure : L.IsTargetPure q :=
    L.firstHit_target_isTargetPure p hmeet
  have hqX : Disjoint q.support X :=
    hpX.mono hqSupport Set.Subset.rfl
  by_contra hempty
  have hpCarrier : Disjoint p.support (finiteVertexSet M.paths) := by
    rw [Set.disjoint_left]
    intro x hxp hxM
    exact hempty ⟨x, hxp, hxM⟩
  have hqCarrier : Disjoint q.support (finiteVertexSet M.paths) :=
    hpCarrier.mono hqSupport Set.Subset.rfl
  have hqM : q ∈ M.paths :=
    M.maximal_disjoint q hqA hqT hqPure hqX hqCarrier
  exact hempty ⟨p.start, p.start_mem_support,
    ⟨q, hqM, q.start_mem_support⟩⟩

end MaximalTargetPureAvoidingRestrictedXSWarp

/-- Zorn-extend a target-pure seed warp among paths avoiding `X`. -/
theorem XSWarp.exists_maximalTargetPureAvoidingRestricted_extension
    {L : Input Gamma I} {A X : Set (Input.LambdaVertex V I)}
    (P : XSWarp L.lambda L.lambda.target)
    (hPA : ∀ {p}, p ∈ P.paths → p.start ∈ A)
    (hPure : ∀ {p}, p ∈ P.paths → L.IsTargetPure p)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalTargetPureAvoidingRestrictedXSWarp L A X,
      P.paths ⊆ M.paths := by
  let Good : Set (Set (FinitePath L.lambda.graph)) :=
    {Q | P.paths ⊆ Q ∧
      Q.PairwiseDisjoint FinitePath.support ∧
      (∀ {p}, p ∈ Q → p.start ∈ A) ∧
      (∀ {p}, p ∈ Q → p.finish ∈ L.lambda.target) ∧
      (∀ {p}, p ∈ Q → L.IsTargetPure p) ∧
      (∀ {p}, p ∈ Q → Disjoint p.support X)}
  have hseed : Good P.paths :=
    ⟨Set.Subset.rfl, P.disjoint, hPA, P.ends_in_target,
      hPure, hPX⟩
  obtain ⟨Q, hPQ, hQmax⟩ := zorn_subset_nonempty Good (by
    intro c hcGood hcChain hcne
    refine ⟨⋃₀ c, ?_, fun Q hQc ↦ Set.subset_sUnion_of_mem hQc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨Q, hQc⟩ := hcne
      exact (hcGood hQc).1.trans (Set.subset_sUnion_of_mem hQc)
    · intro p hp q hq hpq
      obtain ⟨Pset, hPc, hpP⟩ := Set.mem_sUnion.1 hp
      obtain ⟨Qset, hQc, hqQ⟩ := Set.mem_sUnion.1 hq
      by_cases hPQset : Pset = Qset
      · subst Qset
        exact (hcGood hPc).2.1 hpP hqQ hpq
      · rcases hcChain hPc hQc hPQset with hPQ | hQP
        · exact (hcGood hQc).2.1 (hPQ hpP) hqQ hpq
        · exact (hcGood hPc).2.1 hpP (hQP hqQ) hpq
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2.2 hpQ) P.paths hseed
  refine ⟨{
      paths := Q
      disjoint := hQmax.1.2.1
      starts_in_allowed := hQmax.1.2.2.1
      ends_in_target := hQmax.1.2.2.2.1
      paths_targetPure := hQmax.1.2.2.2.2.1
      paths_avoid := hQmax.1.2.2.2.2.2
      maximal_disjoint := ?_ }, hPQ⟩
  intro p hpA hpT hpPure hpX hpdisj
  let Q' : Set (FinitePath L.lambda.graph) := insert p Q
  have hQ'disjoint : Q'.PairwiseDisjoint FinitePath.support := by
    intro q hq r hr hqr
    simp only [Q', Set.mem_insert_iff] at hq hr
    rcases hq with rfl | hqQ
    · rcases hr with rfl | hrQ
      · exact False.elim (hqr rfl)
      · exact Set.disjoint_left.2 fun x hxp hxr ↦
          Set.disjoint_left.1 hpdisj hxp ⟨r, hrQ, hxr⟩
    · rcases hr with rfl | hrQ
      · exact Set.disjoint_left.2 fun x hxq hxp ↦
          Set.disjoint_left.1 hpdisj hxp ⟨q, hqQ, hxq⟩
      · exact hQmax.1.2.1 hqQ hrQ hqr
  have hQ'good : Good Q' := by
    refine ⟨hQmax.1.1.trans (Set.subset_insert p Q), hQ'disjoint,
      ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpA
      · exact hQmax.1.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpT
      · exact hQmax.1.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpPure
      · exact hQmax.1.2.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpX
      · exact hQmax.1.2.2.2.2.2 hqQ
  have hQ'sub : Q' ⊆ Q := hQmax.2 hQ'good (Set.subset_insert p Q)
  exact hQ'sub (Set.mem_insert p Q)

/-- Reserve one member of a target-pure avoiding seed warp and maximize the
remaining paths over all other auxiliary sources. -/
theorem XSWarp.exists_maximalTargetPureAvoiding_extension_erase
    {L : Input Gamma I} {X : Set (Input.LambdaVertex V I)}
    (P : XSWarp L.lambda L.lambda.target)
    {q : FinitePath L.lambda.graph} (hq : q ∈ P.paths)
    (hPure : ∀ {p}, p ∈ P.paths → L.IsTargetPure p)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalTargetPureAvoidingRestrictedXSWarp L
        (L.lambda.source \ {q.start}) X,
      P.paths \ {q} ⊆ M.paths := by
  have hstarts : ∀ {p}, p ∈ (P.erasePath q).paths →
      p.start ∈ L.lambda.source \ {q.start} := by
    intro p hp
    exact P.erasePath_starts_in_source_sdiff_singleton hq hp
  have hpure : ∀ {p}, p ∈ (P.erasePath q).paths →
      L.IsTargetPure p := by
    intro p hp
    exact hPure hp.1
  have havoids : ∀ {p}, p ∈ (P.erasePath q).paths →
      Disjoint p.support X := by
    intro p hp
    exact hPX hp.1
  simpa only [XSWarp.erasePath] using
    (P.erasePath q).exists_maximalTargetPureAvoidingRestricted_extension
      hstarts hpure havoids

/-- Maximize a target-pure avoiding seed while reserving one point of the
forbidden collision carrier as an unused auxiliary source.  This is the
direct form consumed by the stationary thinning output, whose selected
subwarp already avoids the reserved path's collision carrier. -/
theorem XSWarp.exists_maximalTargetPureAvoiding_reserving
    {L : Input Gamma I} {X : Set (Input.LambdaVertex V I)}
    (P : XSWarp L.lambda L.lambda.target)
    {r : Input.LambdaVertex V I} (hrX : r ∈ X)
    (hPure : ∀ {p}, p ∈ P.paths → L.IsTargetPure p)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalTargetPureAvoidingRestrictedXSWarp L
        (L.lambda.source \ {r}) X,
      P.paths ⊆ M.paths := by
  exact P.exists_maximalTargetPureAvoidingRestricted_extension
    (fun {_} hp ↦
      P.starts_in_source_sdiff_singleton_of_avoids hrX hPX hp)
    hPure hPX

end Popular
end Erdos599

#print axioms Erdos599.Popular.XSWarp.exists_maximalTargetPureAvoidingRestricted_extension
#print axioms Erdos599.Popular.XSWarp.exists_maximalTargetPureAvoiding_extension_erase
#print axioms Erdos599.Popular.XSWarp.exists_maximalTargetPureAvoiding_reserving
#print axioms Erdos599.Popular.MaximalTargetPureAvoidingRestrictedXSWarp.finiteVertexSet_meets
#print axioms Erdos599.Popular.MaximalTargetPureAvoidingRestrictedXSWarp.finiteVertexSet_disjoint
