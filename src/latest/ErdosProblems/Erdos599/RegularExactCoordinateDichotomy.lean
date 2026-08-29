/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularExactWeakRowExtension

/-!
# The finite/infinite exact regular coordinate dichotomy

The half-way construction is needed only while the current ladder frontier
is infinite.  If it is finite, the lower induction already links the whole
source of the essential stage web to its target.  This file packages those
two honest alternatives without asking for a right-tight later slice in the
finite branch.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

universe u

variable {V : Type u}

/-- At each exact regular coordinate, either the residual stage is already
fully linkable or source 9.15 supplies a later tight annular candidate. -/
def HasExactCoordinateDichotomy
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) : Prop :=
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF base hbase
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  ∀ (Sigma : Set (Ladder.Stage kappa)),
    Stationary.IsClubBelow kappa Sigma →
    Disjoint Sigma L.phi →
    ∀ delta, (L.stageWeb delta).IsUnhindered → ∀ gamma,
      (∃ W : Set (L.stageWeb delta).DPath,
          IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
            (L.stageWeb delta).target W) ∨
        ∃ beta ∈ Sigma, delta < beta ∧ ∃ T,
          SliceCandidate.IsAnnularSliceCandidate
            G L request delta beta gamma T

/-- The infinite-frontier source provider and the lower induction together
give the total coordinate dichotomy. -/
theorem hasExactCoordinateDichotomy_of_infiniteProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (hprovider : HasExactAnnularCoordinateProvider G hregular huncountable
      hNorm hlower F hF base hbase) :
    HasExactCoordinateDichotomy G hregular huncountable hNorm hlower
      F hF base hbase := by
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF base hbase
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro Sigma hSigma havoid delta hstage gamma
  by_cases hinfinite : aleph0 ≤ #(L.frontier delta)
  · exact Or.inr (hprovider Sigma hSigma havoid delta hstage
      hinfinite gamma)
  · left
    have hfinite : #(L.frontier delta) < aleph0 := lt_of_not_ge hinfinite
    have hsmall : #(L.frontier delta) < kappa :=
      hfinite.trans huncountable
    exact SliceCandidate.exists_stageFullLinkage_of_lower lower L delta
      hstage hsmall

end RegularExtension
end CardinalInduction
end Erdos599

