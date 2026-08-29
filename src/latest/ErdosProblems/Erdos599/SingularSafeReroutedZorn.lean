/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafePartialZorn
import ErdosProblems.Erdos599.SingularCertifiedSafeHistory

/-!
# The exact strength of rerouted safe-chain upper bounds

Literal inclusion of safely deletable path families is not continuous at an
infinite limit.  A natural repair is to order only their covered source sets
and allow every upper bound to choose a completely new linkage.  This file
shows that this repair is sound, but also that it is not a separate
compactness lemma: for a fixed designated set, existence of such rerouted
upper bounds is equivalent to existence of the final safe designated
linkage.

Thus a Zorn proof may use global rerouting at limits, but constructing those
upper bounds already contains the missing infinite selection theorem.  In
particular, lower-cardinal retargeting supplies fresh upper linkages only
while the union of the covered domains remains below the induction cardinal;
the cofinal-size union is the genuine singular obstruction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeReroutedZorn

open SingularCertifiedSafeHistory SingularSafeCompletedMachine
  SingularSafeDesignatedLinkage SingularSafePartialZorn

universe u

variable {V : Type u}

/-- A source set which is covered by some ambiently safe partial linkage.
Only the covered domain is retained, so a later upper bound is free to
reroute every path. -/
def SafelyCoverableDomain (G : DWeb V) (A S : Set V) : Prop :=
  ∃ P : Set G.DPath,
    IsSafePartial G A P ∧ G.initialSet P = S

/-- Chain upper bounds in the order of covered source domains.  Unlike
`SafePartialChainResidual`, this assertion does not retain the union of the
old path families: the witness for `U` may be a global rerouting. -/
def ReroutedSafeDomainChainUpperBounds (G : DWeb V) (A : Set V) : Prop :=
  ∀ c : Set (Set V),
    c ⊆ {S | SafelyCoverableDomain G A S} →
      IsChain (· ⊆ ·) c →
        ∃ U, SafelyCoverableDomain G A U ∧
          ∀ S ∈ c, S ⊆ U

theorem safelyCoverableDomain_subset
    {G : DWeb V} {A S : Set V}
    (hS : SafelyCoverableDomain G A S) : S ⊆ A := by
  obtain ⟨P, hP, rfl⟩ := hS
  exact hP.initial_subset

/-- The empty covered domain is always safely coverable in an unhindered
web. -/
theorem safelyCoverableDomain_empty
    (G : DWeb V) (hG : G.IsUnhindered) (A : Set V) :
    SafelyCoverableDomain G A ∅ := by
  let E : SafeDesignatedLinkage G ∅ :=
    SingularSafeDesignatedLinkage.empty G hG
  refine ⟨E.paths, isSafePartial_of_safeDesignated E (Set.empty_subset A), ?_⟩
  exact E.initialSet

/-- A fresh designated source strictly enlarges a safely coverable domain.
The successor is allowed to reroute only by the certified safe-link
construction, although the surrounding domain order does not remember path
inclusion. -/
theorem safelyCoverableDomain_insert
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A S : Set V} (hA : A ⊆ G.source)
    (hS : SafelyCoverableDomain G A S)
    {a : V} (haA : a ∈ A) (haS : a ∉ S) :
    SafelyCoverableDomain G A (insert a S) := by
  obtain ⟨P, hP, hPS⟩ := hS
  let old : SafeDesignatedLinkage G S :=
    { paths := P
      linkage := by
        rw [← hPS]
        exact hP.linkage
      residual_unhindered := hP.residual }
  have hSsource : S ⊆ G.source :=
    (safelyCoverableDomain_subset ⟨P, hP, hPS⟩).trans hA
  obtain ⟨E⟩ := exists_certifiedSafeDesignatedExtension
    G hNorm old hSsource (hA haA) haS
  refine ⟨E.extended.paths, ?_, E.extended.initialSet⟩
  exact isSafePartial_of_safeDesignated E.extended
    (Set.insert_subset haA (safelyCoverableDomain_subset
      ⟨P, hP, hPS⟩))

/-- Rerouted domain-chain upper bounds give a safe linkage on the entire
designated set by Zorn.  No union of path families is formed. -/
theorem exists_safeDesignatedLinkage_of_reroutedDomainUpperBounds
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    (hupper : ReroutedSafeDomainChainUpperBounds G A) :
    Nonempty (SafeDesignatedLinkage G A) := by
  let Good : Set (Set V) := {S | SafelyCoverableDomain G A S}
  have hempty : ∅ ∈ Good := safelyCoverableDomain_empty G hG A
  have hzorn : ∀ c ⊆ Good, IsChain (· ⊆ ·) c →
      ∃ U ∈ Good, ∀ S ∈ c, S ⊆ U := by
    intro c hc hchain
    exact hupper c hc hchain
  obtain ⟨S, hS, hSmax⟩ := zorn_subset Good hzorn
  have hSA : S ⊆ A := safelyCoverableDomain_subset hS
  have hAS : A ⊆ S := by
    intro a haA
    by_contra haS
    have hinsert : insert a S ∈ Good :=
      safelyCoverableDomain_insert hNorm hA hS haA haS
    have hsub : insert a S ⊆ S :=
      hSmax hinsert (Set.subset_insert a S)
    exact haS (hsub (Set.mem_insert a S))
  have hSeq : S = A := Set.Subset.antisymm hSA hAS
  obtain ⟨P, hP, hPS⟩ := hS
  refine ⟨{
    paths := P
    linkage := ?_
    residual_unhindered := hP.residual }⟩
  rw [← hSeq, ← hPS]
  exact hP.linkage

/-- A final safe designated linkage is itself a greatest safely coverable
domain, and therefore bounds every domain chain. -/
theorem reroutedDomainUpperBounds_of_safeDesignated
    {G : DWeb V} {A : Set V}
    (L : SafeDesignatedLinkage G A) :
    ReroutedSafeDomainChainUpperBounds G A := by
  intro c hc _hchain
  refine ⟨A, ?_, ?_⟩
  · exact ⟨L.paths,
      isSafePartial_of_safeDesignated L Set.Subset.rfl,
      L.initialSet⟩
  · intro S hSc
    exact safelyCoverableDomain_subset (hc hSc)

/-- On a normalized unhindered web, global rerouted upper bounds for safe
domains are equivalent to the final safe-selection theorem.  This is the
precise audit boundary for a non-literal Zorn construction. -/
theorem reroutedSafeDomainChainUpperBounds_iff
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) :
    ReroutedSafeDomainChainUpperBounds G A ↔
      Nonempty (SafeDesignatedLinkage G A) := by
  constructor
  · exact exists_safeDesignatedLinkage_of_reroutedDomainUpperBounds
      G hNorm hG hA
  · rintro ⟨L⟩
    exact reroutedDomainUpperBounds_of_safeDesignated L

/-! ## Machine-facing uniform form -/

/-- Rerouted safe-domain upper bounds in every deleted residual and for
every request set below the induction cardinal. -/
def ReroutedSafeDomainChainUpperBoundsBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      ReroutedSafeDomainChainUpperBounds (G.delete X) A

/-- The uniform rerouted-domain assertion compiles to the safe-batch
selector used by the singular completed-row machine. -/
theorem safeBatchSelectionBelow_of_reroutedDomainUpperBounds
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hupper : ReroutedSafeDomainChainUpperBoundsBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  obtain ⟨L⟩ := exists_safeDesignatedLinkage_of_reroutedDomainUpperBounds
    (G.delete X) (isNormalized_delete hNorm X) hresidual hA
      (hupper X A hresidual hA hAcard)
  exact ⟨SafeBatchInDeletion.ofSafeDesignated L⟩

/-- Conversely, the safe-batch selector supplies a greatest domain in each
instance.  Hence allowing global rerouting does not make the chain-upper
principle weaker than the selector. -/
theorem reroutedDomainUpperBoundsBelow_of_safeBatchSelection
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa) :
    ReroutedSafeDomainChainUpperBoundsBelow G kappa := by
  intro X A hresidual hA hAcard
  obtain ⟨B⟩ := hselect X A hresidual hA hAcard
  exact reroutedDomainUpperBounds_of_safeDesignated B.toSafeDesignated

/-- Machine-facing equivalence: a non-literal domain-Zorn construction is
exactly as strong as `SafeBatchSelectionBelow`. -/
theorem reroutedDomainUpperBoundsBelow_iff_safeBatchSelection
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}} :
    ReroutedSafeDomainChainUpperBoundsBelow G kappa ↔
      SafeBatchSelectionBelow G kappa := by
  exact ⟨safeBatchSelectionBelow_of_reroutedDomainUpperBounds hNorm,
    reroutedDomainUpperBoundsBelow_of_safeBatchSelection⟩

#print axioms reroutedSafeDomainChainUpperBounds_iff
#print axioms reroutedDomainUpperBoundsBelow_iff_safeBatchSelection

end SingularSafeReroutedZorn
end CardinalInduction
end Erdos599
