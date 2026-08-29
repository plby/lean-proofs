/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.PopularSwitching

/-!
# Grounded thinning of the Section 8 local fans

The finite-source part of the auxiliary web contains terminals recorded at
both grounded and hanging obstruction stages.  The stationary input used by
the grounding switch must be thinned to the grounded stages.  This loses only
the nonstationary set `phiHanging` (source Lemma 7.15), so every stationary
joined family retains a stationary grounded-source subfamily.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)

private abbrev I := L.popularAuxiliaryInput hL.legal
private abbrev U := L.popularAuxiliaryIndexed hL

/-- Every auxiliary source carries the obstruction stage at which its
finite terminal or grounded-ray proxy was recorded. -/
theorem popularAuxiliary_sourceIndex_mem_phi
    (x : (I L hL).lambda.source) :
    (U L hL).f x ∈ L.phi := by
  rcases x with ⟨x, hx⟩
  cases x with
  | old a =>
      let xa : L.finiteTerminalSet :=
        ⟨a, L.groundedFiniteTerminalSet_subset_finiteTerminalSet
          (((I L hL).mem_lambda_source_old a).1 hx)⟩
      change L.finiteTerminalStage xa ∈ L.phi
      exact (L.finiteTerminalStage_spec xa).1.1
  | edge a b =>
      exact False.elim ((I L hL).not_mem_lambda_source_edge a b hx)
  | proxy i =>
      change L.groundedInfiniteStage i ∈ L.phi
      exact (L.bookkeeping.mem_phi_iff_exists_chosen
        hL.legal.validBookkeeping).2
          ⟨i.1, (L.groundedInfiniteStage_spec i).2⟩

/-- Paths whose auxiliary initial vertex represents a grounded obstruction
record.  The existential source proof makes this predicate independent of
the particular joined family in which the path is considered. -/
def groundedSourcePaths :
    Set (FinitePath (I L hL).lambda.graph) :=
  {p | ∃ hp : p.start ∈ (I L hL).lambda.source,
    (U L hL).f ⟨p.start, hp⟩ ∈ L.phiGround}

/-- An initial index excluded by `groundedSourcePaths` is a hanging
obstruction stage. -/
theorem restrictedIndices_compl_groundedSourcePaths_subset_phiHanging
    {T : Set (I L hL).LV}
    (F : Popular.JoinedFamily (I L hL).lambda T) :
    Popular.initialIndicesOf (U L hL)
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)ᶜ).paths
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)ᶜ).starts_in_source ⊆
      L.phiHanging := by
  rintro a ⟨p, hp, hpa⟩
  have hpNotGround : p ∉ L.groundedSourcePaths hL := hp.2
  have hpSource : p.start ∈ (I L hL).lambda.source :=
    (PopularSwitching.restrictPaths F
      (L.groundedSourcePaths hL)ᶜ).starts_in_source hp
  have haPhi : a ∈ L.phi := by
    rw [← hpa]
    exact L.popularAuxiliary_sourceIndex_mem_phi hL ⟨p.start, hpSource⟩
  have haNotGround : a ∉ L.phiGround := by
    intro haGround
    apply hpNotGround
    exact ⟨hpSource, by simpa only [hpa] using haGround⟩
  exact ⟨haPhi, haNotGround⟩

/-- The non-grounded part of any auxiliary joined family has
nonstationary initial-index set. -/
theorem nongroundedSourceIndices_nonstationary
    {T : Set (I L hL).LV}
    (F : Popular.JoinedFamily (I L hL).lambda T) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf (U L hL)
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)ᶜ).paths
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)ᶜ).starts_in_source) := by
  intro h
  exact (L.phiHanging_not_stationary_of_legal hL.legal.regular
      hL.legal.uncountable hL.legal)
    (h.mono
      (L.restrictedIndices_compl_groundedSourcePaths_subset_phiHanging hL F))

/-- Restricting a stationary joined family to genuinely grounded source
records preserves stationarity. -/
theorem groundedSource_subfamily_stationary
    {T : Set (I L hL).LV}
    (F : Popular.JoinedFamily (I L hL).lambda T)
    (hF : IsStationaryBelow kappa
      (Popular.initialIndicesOf (U L hL) F.paths F.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (U L hL)
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)).paths
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)).starts_in_source) := by
  let N := Popular.initialIndicesOf (U L hL)
    (PopularSwitching.restrictPaths F
      (L.groundedSourcePaths hL)ᶜ).paths
    (PopularSwitching.restrictPaths F
      (L.groundedSourcePaths hL)ᶜ).starts_in_source
  have hdiff : IsStationaryBelow kappa
      (Popular.initialIndicesOf (U L hL) F.paths F.starts_in_source \ N) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hF
        (L.nongroundedSourceIndices_nonstationary hL F)
  apply hdiff.mono
  rintro a ⟨⟨p, hpF, hpa⟩, haN⟩
  have hpGround : p ∈ L.groundedSourcePaths hL := by
    by_contra hpBad
    let hpNG : p ∈ (PopularSwitching.restrictPaths F
        (L.groundedSourcePaths hL)ᶜ).paths := ⟨hpF, hpBad⟩
    apply haN
    refine ⟨p, hpNG, ?_⟩
    have hs :
        (⟨p.start,
          (PopularSwitching.restrictPaths F
            (L.groundedSourcePaths hL)ᶜ).starts_in_source hpNG⟩ :
              (I L hL).lambda.source) =
          ⟨p.start, F.starts_in_source hpF⟩ := Subtype.ext rfl
    exact (congrArg (U L hL).f hs).trans hpa
  let hpG : p ∈ (PopularSwitching.restrictPaths F
      (L.groundedSourcePaths hL)).paths := ⟨hpF, hpGround⟩
  refine ⟨p, hpG, ?_⟩
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths F
          (L.groundedSourcePaths hL)).starts_in_source hpG⟩ :
            (I L hL).lambda.source) =
        ⟨p.start, F.starts_in_source hpF⟩ := Subtype.ext rfl
  exact (congrArg (U L hL).f hs).trans hpa

end KappaLadder
end DWeb
end Erdos599
