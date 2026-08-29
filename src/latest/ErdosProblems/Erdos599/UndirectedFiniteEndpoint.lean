/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AharoniBerger
import ErdosProblems.Erdos599.CountableExtensionFinal
import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage

/-!
# The finite-endpoint branch of Erdős--Menger

This file gives an unconditional use of the maximal-wave and safe-link APIs.
If the source of a concrete web is finite, the essential frontier of a
maximal wave is finite as well.  The normalized maximal-wave quotient can
therefore be linked by the finite iteration of Theorem 6.1.  The standard
maximal-wave splice then produces the exact orthogonal packing--separator
pair.

This is useful in the undirected specialization because reversal exchanges
the two endpoint sets; in particular, either finite endpoint is enough.
-/

noncomputable section

namespace Erdos599
namespace AharoniBerger

open Cardinal Set DirectedPath

universe u

variable {V : Type u}

/-- The initial-vertex map injects a warp into its initial set. -/
theorem mk_family_le_initialSet_of_isWarp
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W) :
    #W ≤ #(G.initialSet W) := by
  let f : W → (G.initialSet W) := fun p ↦
    ⟨p.1.initial, p.1, p.2, rfl⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_initial_eq G hW p.2 q.2
  exact congrArg Subtype.val hpq

/-- The terminal frontier is no larger than its path family. -/
theorem mk_terminalFrontier_le_family
    (G : DWeb V) (W : Set G.DPath) :
    #(G.terminalFrontier W) ≤ #W := by
  let f : (G.terminalFrontier W) → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact Option.some.inj <| calc
    some x.1 = G.terminal? (f x).1 := hx.symm
    _ = G.terminal? (f y).1 := congrArg (fun p : W ↦ G.terminal? p.1) hxy
    _ = some y.1 := hy

/-- Cardinal version of the finite/countable frontier estimates. -/
theorem mk_terminalFrontier_le_initialSet_of_isWarp
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W) :
    #(G.terminalFrontier W) ≤ #(G.initialSet W) :=
  (mk_terminalFrontier_le_family G W).trans
    (mk_family_le_initialSet_of_isWarp G hW)

/-- Conversely, every initial vertex chooses a member beginning there.  No
warp hypothesis is needed in this direction. -/
theorem mk_initialSet_le_family
    (G : DWeb V) (W : Set G.DPath) :
    #(G.initialSet W) ≤ #W := by
  let f : (G.initialSet W) → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact calc
    x.1 = (f x).1.initial := hx.symm
    _ = (f y).1.initial := congrArg (fun p : W ↦ p.1.initial) hxy
    _ = y.1 := hy

/-- If every member of a warp has a terminal vertex, the terminal map is
injective.  Thus the family is no larger than its terminal frontier. -/
theorem mk_family_le_terminalFrontier_of_isWarp_of_hasTerminal
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    (hterminal : ∀ p ∈ W, ∃ t, G.terminal? p = some t) :
    #W ≤ #(G.terminalFrontier W) := by
  let f : W → (G.terminalFrontier W) := fun p ↦
    ⟨Classical.choose (hterminal p.1 p.2), p.1, p.2,
      Classical.choose_spec (hterminal p.1 p.2)⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  by_contra hpne
  have htermEq : (f p).1 = (f q).1 := congrArg Subtype.val hpq
  have hpterm := Classical.choose_spec (hterminal p.1 p.2)
  have hqterm := Classical.choose_spec (hterminal q.1 q.2)
  have hpSupport : (f p).1 ∈ p.1.support :=
    G.terminal_mem_support hpterm
  have hqSupport : (f p).1 ∈ q.1.support := by
    rw [htermEq]
    exact G.terminal_mem_support hqterm
  exact Set.disjoint_left.1 (hW p.2 q.2 hpne) hpSupport hqSupport

/-- In an unhindered web the essential part of a wave starts at every
source and all of its members have terminals.  Consequently its terminal
frontier has *exactly* the source cardinal.  In particular, the usual
maximal-wave separator bound cannot be a strict cardinal drop in the hard
unhindered case. -/
theorem mk_terminalFrontier_essentialWarpPart_eq_source
    (G : DWeb V) (hG : G.IsUnhindered) (M : G.Wave) :
    #(G.terminalFrontier (G.essentialWarpPart M.1)) = #G.source := by
  let W : Set G.DPath := G.essentialWarpPart M.1
  have hWave : G.IsWave W := essentialWarpPart_isWave G M
  have hInitial : G.initialSet W = G.source :=
    (G.isUnhindered_iff.mp hG W hWave)
  have hTerminal : ∀ p ∈ W, ∃ t, G.terminal? p = some t := by
    intro p hp
    obtain ⟨t, hpt, _ht⟩ := hp.2
    exact ⟨t, hpt⟩
  apply le_antisymm
  · calc
      #(G.terminalFrontier W) ≤ #(G.initialSet W) :=
        mk_terminalFrontier_le_initialSet_of_isWarp G hWave.1
      _ = #G.source := by rw [hInitial]
  · rw [← hInitial]
    exact (mk_initialSet_le_family G W).trans
      (mk_family_le_terminalFrontier_of_isWarp_of_hasTerminal
        G hWave.1 hTerminal)

/-- Cardinal equality for the canonical separator retained from any wave
in an unhindered web. -/
theorem mk_concreteMaximalSeparator_eq_source_of_unhindered
    (G : DWeb V) (hG : G.IsUnhindered) (M : G.Wave) :
    #(concreteMaximalSeparator G M) = #G.source :=
  mk_terminalFrontier_essentialWarpPart_eq_source G hG M

/-- Equivalently, quotienting an unhindered web by the canonical frontier
of a wave does not lower the source cardinal. -/
theorem mk_quotient_concreteMaximalSeparator_source_eq_source_of_unhindered
    (G : DWeb V) (hG : G.IsUnhindered) (M : G.Wave) :
    #(G.quotient (concreteMaximalSeparator G M)).source = #G.source := by
  rw [quotient_concreteMaximalSeparator_source G M]
  exact mk_concreteMaximalSeparator_eq_source_of_unhindered G hG M

#print axioms mk_initialSet_le_family
#print axioms mk_family_le_terminalFrontier_of_isWarp_of_hasTerminal
#print axioms mk_terminalFrontier_essentialWarpPart_eq_source
#print axioms mk_concreteMaximalSeparator_eq_source_of_unhindered
#print axioms mk_quotient_concreteMaximalSeparator_source_eq_source_of_unhindered

/-- The essential frontier retained from a maximal wave has cardinal at
most the cardinal of the source, without any regularity assumption. -/
theorem mk_concreteMaximalSeparator_le_source
    (G : DWeb V) (M : G.Wave) :
    #(concreteMaximalSeparator G M) ≤ #G.source := by
  let W : Set G.DPath := G.essentialWarpPart M.1
  have hWave : G.IsWave W := essentialWarpPart_isWave G M
  exact (mk_terminalFrontier_le_initialSet_of_isWarp G hWave.1).trans
    (Cardinal.mk_subtype_mono hWave.2.1)

/-- A warp whose initial vertices lie in a finite set has only finitely many
members.  The initial-vertex map is injective on a warp. -/
theorem finite_of_isWarp_of_initialSet_finite
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    (hinit : (G.initialSet W).Finite) : W.Finite := by
  apply Set.Finite.of_finite_image
  · simpa only [DWeb.initialSet] using hinit
  · intro p hp q hq hpq
    exact DWeb.IsWarp.eq_of_initial_eq G hW hp hq hpq

/-- The terminal frontier of a finite family is finite.  Rays contribute no
terminal, so no finite-character hypothesis is needed. -/
theorem terminalFrontier_finite_of_family_finite
    (G : DWeb V) {W : Set G.DPath} (hW : W.Finite) :
    (G.terminalFrontier W).Finite := by
  have himage : (G.terminal? '' W).Finite := hW.image G.terminal?
  have hpreimage : (some ⁻¹' (G.terminal? '' W)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hpW, hpx⟩
  exact ⟨p, hpW, hpx⟩

/-- Countable analogue of `finite_of_isWarp_of_initialSet_finite`. -/
theorem countable_of_isWarp_of_initialSet_countable
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    (hinit : (G.initialSet W).Countable) : W.Countable := by
  apply Set.countable_of_injective_of_countable_image
  · intro p hp q hq hpq
    exact DWeb.IsWarp.eq_of_initial_eq G hW hp hq hpq
  · simpa only [DWeb.initialSet] using hinit

/-- The terminal frontier of a countable family is countable. -/
theorem terminalFrontier_countable_of_family_countable
    (G : DWeb V) {W : Set G.DPath} (hW : W.Countable) :
    (G.terminalFrontier W).Countable := by
  have himage : (G.terminal? '' W).Countable := hW.image G.terminal?
  have hpreimage : (some ⁻¹' (G.terminal? '' W)).Countable :=
    himage.preimage (Option.some_injective V)
  apply hpreimage.mono
  rintro x ⟨p, hpW, hpx⟩
  exact ⟨p, hpW, hpx⟩

/-- The essential frontier of a wave is finite when the ambient source is
finite. -/
theorem concreteMaximalSeparator_finite_of_source_finite
    (G : DWeb V) (M : G.Wave) (hsource : G.source.Finite) :
    (concreteMaximalSeparator G M).Finite := by
  let W : Set G.DPath := G.essentialWarpPart M.1
  have hWave : G.IsWave W := essentialWarpPart_isWave G M
  have hinit : (G.initialSet W).Finite :=
    hsource.subset hWave.2.1
  have hfamily : W.Finite :=
    finite_of_isWarp_of_initialSet_finite G hWave.1 hinit
  exact terminalFrontier_finite_of_family_finite G hfamily

/-- Countable source implies countable essential maximal-wave frontier. -/
theorem concreteMaximalSeparator_countable_of_source_countable
    (G : DWeb V) (M : G.Wave) (hsource : G.source.Countable) :
    (concreteMaximalSeparator G M).Countable := by
  let W : Set G.DPath := G.essentialWarpPart M.1
  have hWave : G.IsWave W := essentialWarpPart_isWave G M
  have hinit : (G.initialSet W).Countable :=
    hsource.mono hWave.2.1
  have hfamily : W.Countable :=
    countable_of_isWarp_of_initialSet_countable G hWave.1 hinit
  exact terminalFrontier_countable_of_family_countable G hfamily

/-- Every unhindered web with finite source is linkable.  Normalize the web,
iterate the safe one-source completion over the finite source, and forget the
normalization. -/
theorem isLinkable_of_isUnhindered_of_source_finite
    (G : DWeb V) (hG : G.IsUnhindered) (hsource : G.source.Finite) :
    CardinalInduction.IsLinkable G := by
  have hsourceNorm : G.normalized.source.Finite := by
    simpa using hsource
  obtain ⟨S⟩ :=
    CardinalInduction.SingularSafeDesignatedLinkage.exists_finite
      G.normalized G.normalized_isNormalized hG.normalized
      hsourceNorm (Set.Subset.rfl : G.normalized.source ⊆ G.normalized.source)
  apply CardinalInduction.IsLinkable.of_normalized
  exact ⟨S.paths, S.linkage⟩

/-- Every unhindered web with countable source is linkable.  This is the
unconditional FIFO construction from the countable extension clause,
specialized to the whole source and the empty complementary linkage. -/
theorem isLinkable_of_isUnhindered_of_source_countable
    (G : DWeb V) (hG : G.IsUnhindered) (hsource : G.source.Countable) :
    CardinalInduction.IsLinkable G := by
  have hcard : #G.source ≤ Cardinal.aleph0 :=
    Cardinal.le_aleph0_iff_set_countable.2 hsource
  apply CardinalInduction.extensionClauseAt_countable G hG hcard
    G.source Set.Subset.rfl rfl
  refine ⟨∅, ?_⟩
  simpa using CardinalInduction.empty_linkage G

/-- Unconditional exact directed Menger conclusion for a concrete web with
finite source. -/
theorem directedMengerConclusion_of_source_finite
    (G : DWeb V) (hsource : G.source.Finite) :
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
  have hQsource : Q.source.Finite := by
    rw [show Q.source = concreteMaximalSeparator G M by
      exact quotient_concreteMaximalSeparator_source G M]
    exact concreteMaximalSeparator_finite_of_source_finite G M hsource
  obtain ⟨L, hL⟩ :=
    isLinkable_of_isUnhindered_of_source_finite Q hQunhindered hQsource
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

/-- Unconditional exact directed Menger conclusion for a concrete web with
countable source. -/
theorem directedMengerConclusion_of_source_countable
    (G : DWeb V) (hsource : G.source.Countable) :
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
  have hQsource : Q.source.Countable := by
    rw [show Q.source = concreteMaximalSeparator G M by
      exact quotient_concreteMaximalSeparator_source G M]
    exact concreteMaximalSeparator_countable_of_source_countable G M hsource
  obtain ⟨L, hL⟩ :=
    isLinkable_of_isUnhindered_of_source_countable Q hQunhindered hQsource
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

#print axioms directedMengerConclusion_of_source_finite
#print axioms directedMengerConclusion_of_source_countable

end AharoniBerger

namespace ABPath

open SimpleGraph

/-- Reverse an undirected endpoint path. -/
def reverse {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : ABPath G B A where
  start := p.finish
  finish := p.start
  walk := p.walk.reverse
  isPath := p.isPath.reverse
  start_mem := p.finish_mem
  finish_mem := p.start_mem

@[simp] theorem supportSet_reverse {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.reverse.supportSet = p.supportSet := by
  ext x
  change x ∈ p.walk.reverse.support ↔ x ∈ p.walk.support
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]

@[simp] theorem reverse_reverse {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.reverse.reverse = p := by
  cases p
  simp [reverse]

/-- Endpoint reversal is an equivalence between the two orientations of an
undirected endpoint path. -/
def reverseEquiv (G : SimpleGraph V) (A B : Set V) :
    ABPath G A B ≃ ABPath G B A where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

end ABPath

namespace UndirectedFiniteEndpoint

open SimpleGraph

/-- Reverse every member of an undirected path family. -/
def reverseFamily {G : SimpleGraph V} {A B : Set V}
    (P : Set (ABPath G A B)) : Set (ABPath G B A) :=
  ABPath.reverse '' P

theorem isPathPacking_reverseFamily
    {G : SimpleGraph V} {A B : Set V} {P : Set (ABPath G A B)}
    (hP : IsPathPacking P) : IsPathPacking (reverseFamily P) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint p₀.reverse.supportSet q₀.reverse.supportSet
  rw [ABPath.supportSet_reverse, ABPath.supportSet_reverse]
  apply hP hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

theorem isABSeparator_reverse
    {G : SimpleGraph V} {A B S : Set V}
    (hS : IsABSeparator G A B S) : IsABSeparator G B A S := by
  intro q
  obtain ⟨v, hvS, hvq⟩ := hS q.reverse
  exact ⟨v, hvS, by simpa using hvq⟩

theorem isOrthogonal_reverseFamily
    {G : SimpleGraph V} {A B S : Set V} {P : Set (ABPath G A B)}
    (hS : IsOrthogonal P S) : IsOrthogonal (reverseFamily P) S := by
  constructor
  · intro v hv
    have hv' := hS.1 hv
    simp only [Set.mem_iUnion] at hv' ⊢
    obtain ⟨p, hp, hvp⟩ := hv'
    exact ⟨p.reverse, ⟨p, hp, rfl⟩, by simpa using hvp⟩
  · intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨v, hv, huniq⟩ := hS.2 p₀ hp₀
    refine ⟨v, by simpa using hv, ?_⟩
    intro w hw
    apply huniq w
    simpa using hw

/-- Symmetry of the exact undirected Menger conclusion. -/
theorem conclusion_symm
    {G : SimpleGraph V} {A B : Set V}
    (h : ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S) :
    ∃ (P : Set (ABPath G B A)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G B A S ∧ IsOrthogonal P S := by
  obtain ⟨P, S, hP, hsep, horth⟩ := h
  exact ⟨reverseFamily P, S, isPathPacking_reverseFamily hP,
    isABSeparator_reverse hsep, isOrthogonal_reverseFamily horth⟩

/-- Erdős--Menger for an arbitrary graph when the left endpoint set is
finite.  No finiteness of the graph is assumed. -/
theorem erdos_599_of_left_finite
    (G : SimpleGraph V) (A B : Set V) (hAfinite : A.Finite) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  let web : DWeb V :=
    { graph := DirectedPath.bidirect G
      source := A
      target := B }
  apply Bridge.exists_orthogonal_pathPacking_of_directed
  exact AharoniBerger.directedMengerConclusion_of_source_finite
    web hAfinite

/-- Erdős--Menger for an arbitrary graph when the right endpoint set is
finite, obtained from the finite-left theorem by undirected reversal. -/
theorem erdos_599_of_right_finite
    (G : SimpleGraph V) (A B : Set V) (hBfinite : B.Finite) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  exact conclusion_symm
    (erdos_599_of_left_finite G B A hBfinite)

/-- Erdős--Menger for an arbitrary graph when the left endpoint set is
countable. -/
theorem erdos_599_of_left_countable
    (G : SimpleGraph V) (A B : Set V) (hAcountable : A.Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  let web : DWeb V :=
    { graph := DirectedPath.bidirect G
      source := A
      target := B }
  apply Bridge.exists_orthogonal_pathPacking_of_directed
  exact AharoniBerger.directedMengerConclusion_of_source_countable
    web hAcountable

/-- Erdős--Menger for an arbitrary graph when the right endpoint set is
countable. -/
theorem erdos_599_of_right_countable
    (G : SimpleGraph V) (A B : Set V) (hBcountable : B.Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  exact conclusion_symm
    (erdos_599_of_left_countable G B A hBcountable)

#print axioms erdos_599_of_left_finite
#print axioms erdos_599_of_right_finite
#print axioms erdos_599_of_left_countable
#print axioms erdos_599_of_right_countable

end UndirectedFiniteEndpoint
end Erdos599
