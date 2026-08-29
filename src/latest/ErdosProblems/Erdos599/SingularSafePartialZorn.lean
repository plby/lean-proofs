/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeCompletedMachine
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# A Zorn reduction for singular safe batches

The singleton safe-link theorem gives a successor operation on safely
deletable target linkages.  The only obstruction to iterating that operation
through an arbitrary designated source set is the limit step: deletion of
the union of an increasing chain of safely chosen carriers must remain
unhindered.

This file makes that reduction exact.  Under the chain-limit assertion,
Zorn's lemma gives a maximal safe partial linkage.  A further application of
the singleton safe-link theorem extends it at every omitted designated
source, so maximality forces the linkage to cover the entire set.  All path
and linkage compatibility at a chain union is proved here; the only premise
left to a future switching/limit argument is residual unhinderedness itself.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafePartialZorn

open RegularSafeCompletion SingularSafeDesignatedLinkage
  SingularSafeCompletedMachine

universe u

variable {V : Type u}

/-- A safely deletable target linkage on some subset of the designated set.
The subset is recorded intrinsically as the initial set of the family. -/
def IsSafePartial (G : DWeb V) (A : Set V) (P : Set G.DPath) : Prop :=
  G.initialSet P ⊆ A ∧
    IsLinkageBetween G (G.initialSet P) G.target P ∧
      (G.delete (G.vertexSet P)).IsUnhindered

namespace IsSafePartial

variable {G : DWeb V} {A : Set V} {P : Set G.DPath}

theorem initial_subset (hP : IsSafePartial G A P) :
    G.initialSet P ⊆ A :=
  hP.1

theorem linkage (hP : IsSafePartial G A P) :
    IsLinkageBetween G (G.initialSet P) G.target P :=
  hP.2.1

theorem residual (hP : IsSafePartial G A P) :
    (G.delete (G.vertexSet P)).IsUnhindered :=
  hP.2.2

end IsSafePartial

/-- A safe designated linkage is, after forgetting that it already covers
all of `A`, a safe partial linkage. -/
theorem isSafePartial_of_safeDesignated
    {G : DWeb V} {A B : Set V}
    (S : SafeDesignatedLinkage G A) (hAB : A ⊆ B) :
    IsSafePartial G B S.paths := by
  refine ⟨?_, ?_, S.residual_unhindered⟩
  · rw [S.initialSet]
    exact hAB
  · rw [S.initialSet]
    exact S.linkage

/-- The exact infinitary continuity property needed by the Zorn argument.
All members of the chain are already safe partial linkages; the assertion is
only that deleting the carrier of their union remains unhindered. -/
def SafePartialChainResidual (G : DWeb V) (A : Set V) : Prop :=
  ∀ c : Set (Set G.DPath), IsChain (· ⊆ ·) c → c.Nonempty →
    (∀ P ∈ c, IsSafePartial G A P) →
      (G.delete (G.vertexSet (⋃₀ c))).IsUnhindered

/-- The union of a chain of warp families is a warp. -/
theorem isWarp_sUnion_of_chain
    {G : DWeb V} {c : Set (Set G.DPath)}
    (hc : IsChain (· ⊆ ·) c)
    (hwarp : ∀ P ∈ c, G.IsWarp P) :
    G.IsWarp (⋃₀ c) := by
  intro p hp q hq hpq
  obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
  obtain ⟨Q, hQc, hqQ⟩ := Set.mem_sUnion.1 hq
  by_cases hPQ : P = Q
  · subst Q
    exact hwarp P hPc hpP hqQ hpq
  · rcases hc hPc hQc hPQ with hPQsub | hQPsub
    · exact hwarp Q hQc (hPQsub hpP) hqQ hpq
    · exact hwarp P hPc hpP (hQPsub hqQ) hpq

/-- Finite character is inherited pointwise by a union. -/
theorem hasFiniteCharacter_sUnion
    {G : DWeb V} {c : Set (Set G.DPath)}
    (hfinite : ∀ P ∈ c, G.HasFiniteCharacter P) :
    G.HasFiniteCharacter (⋃₀ c) := by
  intro p hp
  obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
  exact hfinite P hPc hpP

/-- Every structural part of safety is continuous along an inclusion chain.
The residual conclusion is precisely the explicitly supplied chain-limit
premise. -/
theorem isSafePartial_sUnion
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {c : Set (Set G.DPath)}
    (hc : IsChain (· ⊆ ·) c) (_hcne : c.Nonempty)
    (hgood : ∀ P ∈ c, IsSafePartial G A P)
    (hlimit : (G.delete (G.vertexSet (⋃₀ c))).IsUnhindered) :
    IsSafePartial G A (⋃₀ c) := by
  have hwarp : G.IsWarp (⋃₀ c) :=
    isWarp_sUnion_of_chain hc (fun P hPc ↦ (hgood P hPc).linkage.isWarp)
  have hfinite : G.HasFiniteCharacter (⋃₀ c) :=
    hasFiniteCharacter_sUnion
      (fun P hPc ↦ (hgood P hPc).linkage.finiteCharacter)
  have hinitial : G.initialSet (⋃₀ c) ⊆ A := by
    rintro a ⟨p, hp, rfl⟩
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    exact (hgood P hPc).initial_subset ⟨p, hpP, rfl⟩
  have hterminal : G.terminalFrontier (⋃₀ c) ⊆ G.target := by
    rintro a ⟨p, hp, hpa⟩
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    exact (hgood P hPc).linkage.terminalFrontier_subset
      ⟨p, hpP, hpa⟩
  have hboundary :
      SliceSpliceSource.MeetsOnlyAtTerminal G (⋃₀ c) G.target := by
    intro p hp x hxp hxTarget
    exact hNorm.terminal?_eq_of_mem_path p hxp hxTarget
  have hlink : IsLinkageBetween G (G.initialSet (⋃₀ c))
      G.target (⋃₀ c) :=
    (SliceSpliceSource.tightLinkageBetween_of_structural
      hNorm (hinitial.trans hA) hwarp hfinite rfl hterminal hboundary).1
  exact ⟨hinitial, hlink, hlimit⟩

/-- Under the chain-limit residual assertion, the singleton safe-link theorem
upgrades to a safely deletable linkage for the whole designated set. -/
theorem exists_safeDesignatedLinkage_of_chainResidual
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    (hchain : SafePartialChainResidual G A) :
    Nonempty (SafeDesignatedLinkage G A) := by
  let Good : Set (Set G.DPath) := {P | IsSafePartial G A P}
  have hempty : IsSafePartial G A ∅ := by
    exact isSafePartial_of_safeDesignated
      (A := ∅) (B := A) (SingularSafeDesignatedLinkage.empty G hG)
      (Set.empty_subset A)
  obtain ⟨P, _hemptyP, hPmax⟩ := zorn_subset_nonempty Good (by
    intro c hcGood hcChain hcne
    refine ⟨⋃₀ c, ?_, fun Q hQc ↦ Set.subset_sUnion_of_mem hQc⟩
    exact isSafePartial_sUnion hNorm hA hcChain hcne
      (fun Q hQc ↦ hcGood hQc)
      (hchain c hcChain hcne (fun Q hQc ↦ hcGood hQc))) ∅ hempty
  have hP : IsSafePartial G A P := hPmax.1
  have hcover : G.initialSet P = A := by
    apply Set.Subset.antisymm hP.initial_subset
    intro a haA
    by_contra haInitial
    have haSource : a ∈ G.source := hA haA
    have haFresh : a ∉ G.vertexSet P :=
      source_not_mem_vertexSet_of_not_mem_initialSet hNorm
        hP.linkage haSource haInitial
    obtain ⟨c⟩ := exists_safeCompletionChoice G (G.vertexSet P)
      hP.residual haSource haFresh
    have hcross : Disjoint (G.vertexSet P) (G.vertexSet c.family) := by
      rw [c.vertexSet_family]
      exact c.avoids.symm
    have hlink : IsLinkageBetween G
        (G.initialSet P ∪ {a}) G.target (P ∪ c.family) :=
      linkage_union_of_disjoint hNorm
        (hP.initial_subset.trans hA) (Set.singleton_subset_iff.2 haSource)
        hP.linkage c.family_isLinkageBetween hcross
    have hnew : IsSafePartial G A (P ∪ c.family) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hlink.initialSet_eq]
        exact Set.union_subset hP.initial_subset
          (Set.singleton_subset_iff.2 haA)
      · rw [hlink.initialSet_eq]
        exact hlink
      · rw [G.vertexSet_union, c.vertexSet_family]
        exact c.next_unhindered
    have hnewP : P ∪ c.family ⊆ P :=
      hPmax.2 hnew Set.subset_union_left
    have hcP : c.family ⊆ P :=
      Set.subset_union_right.trans hnewP
    apply haInitial
    have haFamily : a ∈ G.initialSet c.family := by
      rw [c.family_isLinkageBetween.initialSet_eq]
      exact Set.mem_singleton a
    obtain ⟨q, hqFamily, hqa⟩ := haFamily
    exact ⟨q, hcP hqFamily, hqa⟩
  refine ⟨{
    paths := P
    linkage := ?_
    residual_unhindered := hP.residual }⟩
  rw [← hcover]
  exact hP.linkage

/-! ## Machine-facing formulation -/

/-- Chain-limit residual safety, uniformly in every deleted residual and
every request set below the induction cardinal. -/
def SafePartialChainResidualBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      SafePartialChainResidual (G.delete X) A

/-- The chain-limit assertion supplies exactly the safe-batch selector
consumed by `SingularSafeCompletedMachine`. -/
theorem safeBatchSelectionBelow_of_chainResidual
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hchain : SafePartialChainResidualBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  obtain ⟨S⟩ := exists_safeDesignatedLinkage_of_chainResidual
    (G.delete X) (isNormalized_delete hNorm X) hresidual hA
    (hchain X A hresidual hA hAcard)
  exact ⟨SafeBatchInDeletion.ofSafeDesignated S⟩

/-- Public singular extension wrapper: after the finite path geometry and
the row recursion have been discharged, the whole singular branch reduces
to the one chain-limit residual assertion on the normalized web. -/
theorem singularExtensionClauseAt_of_safePartialChainResidual
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hchain : SafePartialChainResidualBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
  exact safeBatchSelectionBelow_of_chainResidual
    Gamma.normalized_isNormalized hchain

#print axioms exists_safeDesignatedLinkage_of_chainResidual
#print axioms safeBatchSelectionBelow_of_chainResidual
#print axioms singularExtensionClauseAt_of_safePartialChainResidual

end SingularSafePartialZorn
end CardinalInduction
end Erdos599
