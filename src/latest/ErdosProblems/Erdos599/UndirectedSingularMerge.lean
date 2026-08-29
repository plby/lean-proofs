/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.AharoniBerger
import ErdosProblems.Erdos599.UndirectedFiniteEndpoint

/-!
# Componentwise enlargement of a linkage

Two finite-character warps have countable alternating components.  This
file records the resulting exact enlargement operation in the form useful
for a singular-cardinal construction.  If `Y` links `D` and `W` links a
larger set `E`, retain `W` precisely in the alternating components meeting
the newly requested sources `E \ D`, and retain `Y` everywhere else.

The result links all of `E`, agrees literally with `Y` outside the affected
components, and, at an uncountable regular bound, changes fewer than the
bound many paths whenever `E \ D` has size below the bound.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace UndirectedSingularMerge

open CardinalInduction
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}

/-- Enlarge an old linkage by replacing precisely the alternating
components which meet a newly requested source. -/
def nestedComponentMerge (G : DWeb V) (W Y : Set G.DPath)
    (D E : Set V) : Set G.DPath :=
  componentMixedFamily G W Y (E \ D)

/-- Componentwise exchange turns a linkage of `D` and a linkage of a
larger set `E` into a linkage of `E`. -/
theorem nestedComponentMerge_isLinkageBetween
    (G : DWeb V) {W Y : Set G.DPath} {D E T : Set V}
    (hY : IsLinkageBetween G D T Y)
    (hW : IsLinkageBetween G E T W) (hDE : D ⊆ E) :
    IsLinkageBetween G E T (nestedComponentMerge G W Y D E) := by
  have hset : E \ (E \ D) = D := by
    ext x
    constructor
    · rintro ⟨hxE, hxNot⟩
      by_contra hxD
      exact hxNot ⟨hxE, hxD⟩
    · intro hxD
      exact ⟨hDE hxD, fun hx ↦ hx.2 hxD⟩
  unfold nestedComponentMerge
  apply componentMixedFamily_isLinkageBetween_of_complement G hW
      (A := E) (E := E \ D)
  · simpa only [hset] using hY
  · exact Set.sdiff_subset

/-- Outside the components meeting the new sources, the enlarged family
is literally the old family. -/
theorem mem_nestedComponentMerge_iff_of_initial_not_mem
    (G : DWeb V) {W Y : Set G.DPath} {D E : Set V} {p : G.DPath}
    (hp : p.initial ∉
      exceptionalComponentVertices G W Y (E \ D)) :
    p ∈ nestedComponentMerge G W Y D E ↔ p ∈ Y := by
  simp only [nestedComponentMerge, componentMixedFamily, initialPart,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
  tauto

/-- Every genuinely new member is a member of `W` retained in an affected
alternating component. -/
theorem nestedComponentMerge_diff_subset
    (G : DWeb V) (W Y : Set G.DPath) (D E : Set V) :
    nestedComponentMerge G W Y D E \ Y ⊆
      initialPart G W (exceptionalComponentVertices G W Y (E \ D)) := by
  rintro p ⟨hp, hpNotY⟩
  change p ∈ initialPart G W
      (exceptionalComponentVertices G W Y (E \ D)) ∪
    initialPart G Y
      (exceptionalComponentVertices G W Y (E \ D))ᶜ at hp
  rcases hp with hpW | hpY
  · exact hpW
  · exact (hpNotY hpY.1).elim

/-- The carrier of every genuinely new member lies wholly in the union of
affected alternating components. -/
theorem support_subset_exceptional_of_mem_merge_diff
    (G : DWeb V) {W Y : Set G.DPath} {D E : Set V} {p : G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hp : p ∈ nestedComponentMerge G W Y D E \ Y) :
    p.support ⊆ exceptionalComponentVertices G W Y (E \ D) := by
  have hpW := nestedComponentMerge_diff_subset G W Y D E hp
  exact path_support_subset_exceptionalComponents_left hWfinite
    hpW.1 p.initial_mem_support hpW.2

/-- At a regular uncountable bound, adding a small source batch affects
only a small union of alternating components. -/
theorem mk_exceptionalComponentVertices_new_lt
    {kappa : Cardinal.{u}} (G : DWeb V)
    {W Y : Set G.DPath} {D E : Set V}
    (hregular : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (hWfinite : G.HasFiniteCharacter W)
    (hYfinite : G.HasFiniteCharacter Y)
    (hnew : #(↥(E \ D)) < kappa) :
    #(exceptionalComponentVertices G W Y (E \ D)) < kappa :=
  mk_exceptionalComponentVertices_lt hregular huncountable
    hW hY hWfinite hYfinite hnew

/-- Consequently the enlargement introduces fewer than `kappa` genuinely
new paths. -/
theorem mk_nestedComponentMerge_diff_lt
    {kappa : Cardinal.{u}} (G : DWeb V)
    {W Y : Set G.DPath} {D E : Set V}
    (hregular : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (hWfinite : G.HasFiniteCharacter W)
    (hYfinite : G.HasFiniteCharacter Y)
    (hnew : #(↥(E \ D)) < kappa) :
    #(↥(nestedComponentMerge G W Y D E \ Y)) < kappa := by
  exact (Cardinal.mk_subtype_mono
      (nestedComponentMerge_diff_subset G W Y D E)).trans_lt
    (mk_componentMixedFamily_left_lt G hregular huncountable
      hW hY hWfinite hYfinite hnew)

#print axioms nestedComponentMerge_isLinkageBetween
#print axioms mem_nestedComponentMerge_iff_of_initial_not_mem
#print axioms support_subset_exceptional_of_mem_merge_diff
#print axioms mk_nestedComponentMerge_diff_lt

end UndirectedSingularMerge

namespace AharoniBerger

open CardinalInduction

/-- Below the current induction cardinal, the lower unhindered-linkability
hypothesis already implies the full directed Menger conclusion for an
arbitrary web.  A maximal wave first replaces the arbitrary web by its loose
(hence unhindered) quotient; the quotient source is no larger than the
original source, so lower induction links it and the canonical splice closes
the original web. -/
theorem directedMengerConclusion_of_source_lt
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hsource : #G.source < kappa) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_wave
  let Q := G.quotient (concreteMaximalSeparator G M)
  have hQloose : Q.IsLoose := by
    dsimp only [Q]
    rw [concreteMaximalSeparator_eq_essential]
    exact G.quotient_essentialTerminalFrontier_isLoose_of_isMax
      M.property hMmax
  have hQunhindered : Q.IsUnhindered :=
    concrete_isUnhindered_of_isLoose Q hQloose
  have hQcard : #Q.source < kappa := by
    rw [show Q.source = concreteMaximalSeparator G M by
      exact quotient_concreteMaximalSeparator_source G M]
    exact (mk_concreteMaximalSeparator_le_source G M).trans_lt hsource
  have hQinduction : CardinalInductionAt Q #Q.source :=
    hlower #Q.source hQcard Q hQunhindered
  obtain ⟨L, hL⟩ := linkable_of_cardinalInductionAt_source Q hQinduction
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

/-- If a maximal wave has a separator strictly smaller than the ambient
source, the lower-cardinal induction hypothesis already closes the web.
This is the exact strict-cardinality branch of the maximal-separator
reduction; the remaining singular difficulty is therefore confined to
maximal separators of full source cardinality. -/
theorem directedMengerConclusion_of_maximalSeparator_lt_source
    (G : DWeb V) (M : G.Wave) (hMmax : IsMax M)
    (hlower : UniversalCardinalInductionBelow V #G.source)
    (hseparator : #(concreteMaximalSeparator G M) < #G.source) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  let Q := G.quotient (concreteMaximalSeparator G M)
  have hQloose : Q.IsLoose := by
    dsimp only [Q]
    rw [concreteMaximalSeparator_eq_essential]
    exact G.quotient_essentialTerminalFrontier_isLoose_of_isMax
      M.property hMmax
  have hQunhindered : Q.IsUnhindered :=
    concrete_isUnhindered_of_isLoose Q hQloose
  have hQcard : #Q.source < #G.source := by
    rw [show Q.source = concreteMaximalSeparator G M by
      exact quotient_concreteMaximalSeparator_source G M]
    exact hseparator
  have hQinduction : CardinalInductionAt Q #Q.source :=
    hlower #Q.source hQcard Q hQunhindered
  obtain ⟨L, hL⟩ := linkable_of_cardinalInductionAt_source Q hQinduction
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

/-- Existential wrapper for the strict maximal-separator branch. -/
theorem directedMengerConclusion_of_exists_maximalSeparator_lt_source
    (G : DWeb V)
    (hlower : UniversalCardinalInductionBelow V #G.source)
    (hsmall : ∃ M : G.Wave, IsMax M ∧
      #(concreteMaximalSeparator G M) < #G.source) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨M, hMmax, hseparator⟩ := hsmall
  exact directedMengerConclusion_of_maximalSeparator_lt_source
    G M hMmax hlower hseparator

#print axioms directedMengerConclusion_of_source_lt
#print axioms directedMengerConclusion_of_maximalSeparator_lt_source
#print axioms directedMengerConclusion_of_exists_maximalSeparator_lt_source

end AharoniBerger
end Erdos599
