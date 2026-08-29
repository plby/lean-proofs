/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualTargetPureMaximalWarp
import ErdosProblems.Erdos599.GroundingDecodedCarrier

/-!
# Decoded-carrier-compatible maximal warps

Auxiliary vertex-disjointness alone does not make simultaneous decoded
routes vertex-disjoint in the original graph.  This file performs the Zorn
extension inside the stronger class whose members are disjoint both in
auxiliary support and in `decodedVertexCarrier`.

Maximality then gives the active-closure dichotomy.  Every clean admissible
source--target candidate either meets the selected auxiliary carrier or has
decoded-carrier contact with a selected member.  Otherwise its first-target
prefix could be inserted while preserving both disjointness invariants.
-/

noncomputable section

open Set

namespace Erdos599
namespace Popular

open DirectedPath
open PopularAuxiliary

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Decoded carriers are monotone under inclusion of auxiliary supports. -/
theorem decodedVertexCarrier_mono_support
    {L : Input Gamma I} {p q : FinitePath L.lambda.graph}
    (hpq : p.support ⊆ q.support) :
    L.decodedVertexCarrier p ⊆ L.decodedVertexCarrier q := by
  intro x hx
  simp only [Input.decodedVertexCarrier, Set.mem_iUnion] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨a, hpq ha, hxa⟩

/-- A target-pure avoiding maximal auxiliary warp whose decoded carriers are
also pairwise disjoint. -/
structure MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (L : Input Gamma I) (A X : Set (Input.LambdaVertex V I))
    extends FiniteWarp L.lambda where
  decoded_disjoint : paths.PairwiseDisjoint L.decodedVertexCarrier
  starts_in_allowed : ∀ {p}, p ∈ paths → p.start ∈ A
  ends_in_target : ∀ {p}, p ∈ paths → p.finish ∈ L.lambda.target
  paths_targetPure : ∀ {p}, p ∈ paths → L.IsTargetPure p
  paths_avoid : ∀ {p}, p ∈ paths → Disjoint p.support X
  maximal_disjoint : ∀ (p : FinitePath L.lambda.graph),
    p.start ∈ A → p.finish ∈ L.lambda.target → L.IsTargetPure p →
    Disjoint p.support X →
    Disjoint p.support (finiteVertexSet paths) →
    (∀ q ∈ paths,
      Disjoint (L.decodedVertexCarrier p) (L.decodedVertexCarrier q)) →
    p ∈ paths

namespace MaximalDecodedTargetPureAvoidingRestrictedXSWarp

variable {L : Input Gamma I}
  {A X : Set (Input.LambdaVertex V I)}

/-- Forget the stronger maximality data while retaining the literal family. -/
def toXSWarp
    (M : MaximalDecodedTargetPureAvoidingRestrictedXSWarp L A X)
    (hA : A ⊆ L.lambda.source) :
    XSWarp L.lambda L.lambda.target where
  paths := M.paths
  disjoint := M.disjoint
  starts_in_source hp := hA (M.starts_in_allowed hp)
  ends_in_target := M.ends_in_target

/-- The selected auxiliary carrier avoids `X`. -/
theorem finiteVertexSet_disjoint
    (M : MaximalDecodedTargetPureAvoidingRestrictedXSWarp L A X) :
    Disjoint (finiteVertexSet M.paths) X := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpM, hxp⟩ hxX
  exact Set.disjoint_left.1 (M.paths_avoid hpM) hxp hxX

/-- The active-closure contact dichotomy.  A clean admissible candidate meets
the family either literally in the auxiliary web or after decoding. -/
theorem support_meets_or_decodedCarrier_meets
    (M : MaximalDecodedTargetPureAvoidingRestrictedXSWarp L A X)
    (p : FinitePath L.lambda.graph) (hpA : p.start ∈ A)
    (hpT : p.finish ∈ L.lambda.target)
    (hpX : Disjoint p.support X) :
    (p.support ∩ finiteVertexSet M.paths).Nonempty ∨
      ∃ q ∈ M.paths,
        (L.decodedVertexCarrier p ∩
          L.decodedVertexCarrier q).Nonempty := by
  classical
  by_cases hsupport :
      (p.support ∩ finiteVertexSet M.paths).Nonempty
  · exact Or.inl hsupport
  right
  by_contra hdecoded
  push Not at hdecoded
  let hmeet : p.walk.Meets L.lambda.target :=
    ⟨p.finish, p.finish_mem_support, hpT⟩
  let r := p.firstHit L.lambda.target hmeet
  have hrSupport : r.support ⊆ p.support :=
    p.firstHit_support_subset L.lambda.target hmeet
  have hrA : r.start ∈ A := by
    change p.start ∈ A
    exact hpA
  have hrT : r.finish ∈ L.lambda.target :=
    p.firstHit_finish_mem L.lambda.target hmeet
  have hrPure : L.IsTargetPure r :=
    L.firstHit_target_isTargetPure p hmeet
  have hrX : Disjoint r.support X :=
    hpX.mono hrSupport Set.Subset.rfl
  have hpCarrier : Disjoint p.support (finiteVertexSet M.paths) := by
    rw [Set.disjoint_left]
    intro x hxp hxM
    exact hsupport ⟨x, hxp, hxM⟩
  have hrCarrier : Disjoint r.support (finiteVertexSet M.paths) :=
    hpCarrier.mono hrSupport Set.Subset.rfl
  have hrDecoded : ∀ q ∈ M.paths,
      Disjoint (L.decodedVertexCarrier r)
        (L.decodedVertexCarrier q) := by
    intro q hq
    rw [Set.disjoint_left]
    intro x hxr hxq
    have hxinter : x ∈ L.decodedVertexCarrier p ∩
        L.decodedVertexCarrier q :=
      ⟨decodedVertexCarrier_mono_support hrSupport hxr, hxq⟩
    rw [hdecoded q hq] at hxinter
    exact hxinter
  have hrM : r ∈ M.paths :=
    M.maximal_disjoint r hrA hrT hrPure hrX hrCarrier hrDecoded
  exact hsupport ⟨p.start, p.start_mem_support,
    ⟨r, hrM, r.start_mem_support⟩⟩

end MaximalDecodedTargetPureAvoidingRestrictedXSWarp

/-- Zorn extension preserving auxiliary disjointness, decoded-carrier
disjointness, target purity, and avoidance of `X`. -/
theorem XSWarp.exists_maximalDecodedTargetPureAvoidingRestricted_extension
    {L : Input Gamma I} {A X : Set (Input.LambdaVertex V I)}
    (P : XSWarp L.lambda L.lambda.target)
    (hDecoded : P.paths.PairwiseDisjoint L.decodedVertexCarrier)
    (hPA : ∀ {p}, p ∈ P.paths → p.start ∈ A)
    (hPure : ∀ {p}, p ∈ P.paths → L.IsTargetPure p)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalDecodedTargetPureAvoidingRestrictedXSWarp L A X,
      P.paths ⊆ M.paths := by
  let Good : Set (Set (FinitePath L.lambda.graph)) :=
    {Q | P.paths ⊆ Q ∧
      Q.PairwiseDisjoint FinitePath.support ∧
      Q.PairwiseDisjoint L.decodedVertexCarrier ∧
      (∀ {p}, p ∈ Q → p.start ∈ A) ∧
      (∀ {p}, p ∈ Q → p.finish ∈ L.lambda.target) ∧
      (∀ {p}, p ∈ Q → L.IsTargetPure p) ∧
      (∀ {p}, p ∈ Q → Disjoint p.support X)}
  have hseed : Good P.paths :=
    ⟨Set.Subset.rfl, P.disjoint, hDecoded, hPA,
      P.ends_in_target, hPure, hPX⟩
  obtain ⟨Q, hPQ, hQmax⟩ := zorn_subset_nonempty Good (by
    intro c hcGood hcChain hcne
    refine ⟨⋃₀ c, ?_, fun Q hQc ↦ Set.subset_sUnion_of_mem hQc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro p hp q hq hpq
      obtain ⟨Pset, hPc, hpP⟩ := Set.mem_sUnion.1 hp
      obtain ⟨Qset, hQc, hqQ⟩ := Set.mem_sUnion.1 hq
      by_cases hPQset : Pset = Qset
      · subst Qset
        exact (hcGood hPc).2.2.1 hpP hqQ hpq
      · rcases hcChain hPc hQc hPQset with hPQ | hQP
        · exact (hcGood hQc).2.2.1 (hPQ hpP) hqQ hpq
        · exact (hcGood hPc).2.2.1 hpP (hQP hqQ) hpq
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2.2.2 hpQ) P.paths hseed
  refine ⟨{
      paths := Q
      disjoint := hQmax.1.2.1
      decoded_disjoint := hQmax.1.2.2.1
      starts_in_allowed := hQmax.1.2.2.2.1
      ends_in_target := hQmax.1.2.2.2.2.1
      paths_targetPure := hQmax.1.2.2.2.2.2.1
      paths_avoid := hQmax.1.2.2.2.2.2.2
      maximal_disjoint := ?_ }, hPQ⟩
  intro p hpA hpT hpPure hpX hpSupport hpDecoded
  let Q' : Set (FinitePath L.lambda.graph) := insert p Q
  have hQ'support : Q'.PairwiseDisjoint FinitePath.support := by
    intro q hq r hr hqr
    simp only [Q', Set.mem_insert_iff] at hq hr
    rcases hq with rfl | hqQ
    · rcases hr with rfl | hrQ
      · exact False.elim (hqr rfl)
      · exact Set.disjoint_left.2 fun x hxp hxr ↦
          Set.disjoint_left.1 hpSupport hxp ⟨r, hrQ, hxr⟩
    · rcases hr with rfl | hrQ
      · exact Set.disjoint_left.2 fun x hxq hxp ↦
          Set.disjoint_left.1 hpSupport hxp ⟨q, hqQ, hxq⟩
      · exact hQmax.1.2.1 hqQ hrQ hqr
  have hQ'decoded : Q'.PairwiseDisjoint L.decodedVertexCarrier := by
    intro q hq r hr hqr
    simp only [Q', Set.mem_insert_iff] at hq hr
    rcases hq with rfl | hqQ
    · rcases hr with rfl | hrQ
      · exact False.elim (hqr rfl)
      · exact hpDecoded r hrQ
    · rcases hr with rfl | hrQ
      · exact (hpDecoded q hqQ).symm
      · exact hQmax.1.2.2.1 hqQ hrQ hqr
  have hQ'good : Good Q' := by
    refine ⟨hQmax.1.1.trans (Set.subset_insert p Q), hQ'support,
      hQ'decoded, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpA
      · exact hQmax.1.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpT
      · exact hQmax.1.2.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpPure
      · exact hQmax.1.2.2.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpX
      · exact hQmax.1.2.2.2.2.2.2 hqQ
  have hQ'sub : Q' ⊆ Q := hQmax.2 hQ'good (Set.subset_insert p Q)
  exact hQ'sub (Set.mem_insert p Q)

/-- Reserve a point of the forbidden carrier while performing the decoded
compatible maximal extension. -/
theorem XSWarp.exists_maximalDecodedTargetPureAvoiding_reserving
    {L : Input Gamma I} {X : Set (Input.LambdaVertex V I)}
    (P : XSWarp L.lambda L.lambda.target)
    (hDecoded : P.paths.PairwiseDisjoint L.decodedVertexCarrier)
    {r : Input.LambdaVertex V I} (hrX : r ∈ X)
    (hPure : ∀ {p}, p ∈ P.paths → L.IsTargetPure p)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalDecodedTargetPureAvoidingRestrictedXSWarp L
        (L.lambda.source \ {r}) X,
      P.paths ⊆ M.paths := by
  exact P.exists_maximalDecodedTargetPureAvoidingRestricted_extension
    hDecoded
    (fun {_} hp ↦
      P.starts_in_source_sdiff_singleton_of_avoids hrX hPX hp)
    hPure hPX

end Popular
end Erdos599

#print axioms Erdos599.Popular.XSWarp.exists_maximalDecodedTargetPureAvoidingRestricted_extension
#print axioms Erdos599.Popular.XSWarp.exists_maximalDecodedTargetPureAvoiding_reserving
#print axioms Erdos599.Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp.support_meets_or_decodedCarrier_meets
