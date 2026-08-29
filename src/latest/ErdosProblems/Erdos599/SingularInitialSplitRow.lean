/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMergedReentry

/-!
# The initial split row for the singular target matrix

The first target row needs no previously frozen target components.  Start
with the trivial full-source linkage and the separating stop-over consisting
of the whole source.  Its quotient is unhindered.  The lower-cardinal
half-way clause, followed by the concrete merged re-entry, then constructs
each initial target column together with its split certificate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularInitialSplitRow

open SingularExtension SingularMatrix SingularBoundarySplit
  SingularContinuation SingularTargetRowMachine SingularMergedReentry
  SliceSpliceSource

universe u

variable {V : Type u}

/-- The trivial full-source family is a separating half-way row at the
whole source of a normalized unhindered web. -/
theorem trivialSource_separatingStopover
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized) :
    IsSeparatingHalfwayStopover G
      (G.trivialPath '' G.source) G.source := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hlink : IsLinkageBetween G G.source G.source
      (G.trivialPath '' G.source) := by
    refine ⟨G.isWarp_trivialPaths G.source, ?_,
      G.initialSet_trivialPaths G.source, ?_, ?_⟩
    · rintro p ⟨a, ha, rfl⟩
      exact ⟨DirectedPath.FinitePath.trivial G.graph a, rfl⟩
    · rw [G.terminalFrontier_trivialPaths]
    · rintro p ⟨a, ha, rfl⟩
      refine ⟨DirectedPath.FinitePath.trivial G.graph a, rfl, ?_, ?_⟩
      · simp only [DirectedPath.FinitePath.support_trivial,
          DirectedPath.FinitePath.trivial_start,
          DirectedPath.FinitePath.trivial_finish]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_union, Set.mem_insert_iff]
        constructor
        · exact fun hx ↦ Or.inl hx.1
        · intro hx
          rcases hx with hxa | hxa <;> subst x <;>
            exact ⟨rfl, Or.inl ha⟩
      · simp only [DirectedPath.FinitePath.support_trivial,
          DirectedPath.FinitePath.trivial_start]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun hx ↦ hx.1
        · intro hx
          subst x
          exact ⟨rfl, ha⟩
  have hminimal : IsTrimmedSeparator G G.source := by
    apply Set.Subset.antisymm
    · exact G.essential_subset G.source
    · exact source_subset_essential_source_of_unhindered G hG
  have hseparator : IsSeparatorFrom G G.source G.source := by
    intro a ha
    exact G.subset_roof G.source ha
  exact ⟨⟨hlink, hseparator, hminimal,
    quotient_source_isUnhindered G hNoEnter hG⟩, hseparator⟩

/-- The trivial full-source row is terminal-clean at the source boundary. -/
theorem trivialSource_terminalClean (G : DWeb V) :
    TerminalCleanAt G (G.trivialPath '' G.source) G.source := by
  rintro p ⟨a, _ha, rfl⟩ x hx _hxSource
  have hxa : x = a := by
    simpa only [G.support_trivialPath, Set.mem_singleton_iff] using hx
  subst x
  exact G.terminal?_trivialPath a

/-- One initial column, with its target links and future split certificate. -/
theorem exists_initialSplitColumn
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {B : Set V} (hB : B ⊆ G.source)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    (hrhoKappa : rho < kappa) (hBcard : #B = rho) :
    ∃ M : Set G.DPath,
      G.IsWarp M ∧ G.HasFiniteCharacter M ∧
      G.initialSet M = G.source ∧ LinksToTarget G M B ∧
      Nonempty (SplitStopover G M) := by
  let W : Set G.DPath := G.trivialPath '' G.source
  let D : Set V := G.source
  have hD : IsSeparatingHalfwayStopover G W D :=
    trivialSource_separatingStopover hG hNorm
  have hclean : TerminalCleanAt G W D := trivialSource_terminalClean G
  let A := requestedFrontier G W B
  have hAcard : #A = rho := by
    dsimp only [A]
    rw [mk_requestedFrontier_eq hD.linkage hB, hBcard]
  have hAsub : A ⊆ (G.quotient D).source :=
    SingularTargetRowMachine.requestedFrontier_subset_quotientSource hD
  have hlowerRho := hlower rho hrhoKappa
    (G.quotient D) hD.quotient_unhindered
  obtain ⟨U, hU⟩ := hlowerRho.halfway hrho A hAsub hAcard
  obtain ⟨E, M, _hE, _hheight, hMwarp, hMfinite, _hforward,
      hMinitial, hMlinks, hMsplit⟩ :=
    exists_mergedReentry_to_requestedFrontier
      hNorm hD hclean hB hU
  exact ⟨M, hMwarp, hMfinite, hMinitial, hMlinks, hMsplit⟩

/-- The simultaneous initial row used by the private-state target machine. -/
theorem exists_initialSplitTargetRowStage
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    ∃ S : SplitTargetRowStage G (Index kappa),
      S.row.sources = sourceLayer A₀ kappa hcard hkappa hsingular := by
  let A : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard hkappa hsingular
  have hex : ∀ i, ∃ M : Set G.DPath,
      G.IsWarp M ∧ G.HasFiniteCharacter M ∧
      G.initialSet M = G.source ∧ LinksToTarget G M (A i) ∧
      Nonempty (SplitStopover G M) := by
    intro i
    apply exists_initialSplitColumn hlower hkappa hsingular hG hNorm
    · exact (sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans hA₀
    · exact scale_infinite kappa hkappa hsingular i
    · exact scale_below kappa hkappa hsingular i
    · exact sourceLayer_card A₀ kappa hcard hkappa hsingular i
  let M : Index kappa → Set G.DPath := fun i ↦ Classical.choose (hex i)
  let R : TargetRowStage G (Index kappa) :=
    { sources := A
      paths := M
      isWarp := fun i ↦ (Classical.choose_spec (hex i)).1
      finiteCharacter := fun i ↦ (Classical.choose_spec (hex i)).2.1
      initialSet := fun i ↦ (Classical.choose_spec (hex i)).2.2.1
      links := fun i ↦ (Classical.choose_spec (hex i)).2.2.2.1 }
  let S : SplitTargetRowStage G (Index kappa) :=
    { row := R
      split := fun i ↦ Classical.choice
        (Classical.choose_spec (hex i)).2.2.2.2 }
  exact ⟨S, rfl⟩

end SingularInitialSplitRow
end CardinalInduction
end Erdos599
