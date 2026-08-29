/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.PopularIndexedDichotomy

/-!
# The repaired index dichotomy for grounding

This file instantiates the weak indexed-popularity theorem on the literal
successor-normalized ladder bookkeeping.  The output keeps the exact
obstruction set: it is either the usual popular separator, a stationary
strict subwarp, or a stationary subwarp all of whose paths join a source
record to a marker with exactly the same ladder stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The true chronology proposition for the literal auxiliary web. -/
def AuxiliaryNonincreasing (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance) : Prop :=
  (L.popularAuxiliaryIndexed hL).Nonincreasing

/-- The exact three-way replacement for the invalid unconditional strict
descent assertion. -/
theorem popularAuxiliary_strict_or_equal_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).strictSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).strictSubwarp P).starts_in_source)) ∨
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
    Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  let U := L.popularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      hstrong | hseparator
  · rcases U.stronglyPopular_target_strict_or_equal hmono hstrong with
        hstrict | hequal
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl hequal)
  · exact Or.inr (Or.inr hseparator)

/-- The sharp two-way form of the repaired index dichotomy.  The apparent
stationary strict alternative above is impossible by pressing down on that
subwarp alone, so weak chronology leaves only a stationary same-index warp
or the popular separator used by the grounding construction. -/
theorem popularAuxiliary_equal_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
    Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  let U := L.popularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      hstrong | hseparator
  · exact Or.inl (U.stronglyPopular_target_equal hmono hstrong)
  · exact Or.inr hseparator

/-- An equal-subwarp path begins at a recorded finite terminal or an
infinite proxy and ends at a marker born at exactly that source stage. -/
theorem equalSubwarp_path_sameStage
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    {p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths) :
    (∃ (x : L.groundedFiniteTerminalSet)
      (y : (L.popularAuxiliaryInput hL.legal).targetMarkers),
      p.start = .old x.1 ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = L.finiteTerminalIndex x) ∨
    (∃ (i : L.groundedInfiniteRecords)
      (y : (L.popularAuxiliaryInput hL.legal).targetMarkers),
      p.start = .proxy i ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = L.groundedInfiniteStage i) := by
  let I := L.popularAuxiliaryInput hL.legal
  have hpSource : p.start ∈ I.lambda.source :=
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hp
  have hpTarget : p.finish ∈ I.lambda.target :=
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P).ends_in_target hp
  have hindex := (L.popularAuxiliaryIndexed hL).equalSubwarp_index_eq P hp
  obtain ⟨y, hyTarget, hfinish⟩ := I.finish_of_mem_lambda_target p hpTarget
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let ys : I.targetMarkers := ⟨y, hyTarget⟩
  rcases I.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · left
    let xs : L.groundedFiniteTerminalSet := ⟨x, hxFinite⟩
    refine ⟨xs, ys, hstart, hfinish, ?_⟩
    have hs :
        (L.popularAuxiliaryIndexed hL).f
            ⟨p.start,
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
                hp⟩ =
          (L.popularAuxiliaryIndexed hL).f
            ⟨.old x, (I.mem_lambda_source_old x).2 hxFinite⟩ := by
      apply congrArg (L.popularAuxiliaryIndexed hL).f
      exact Subtype.ext hstart
    have ht :
        (L.popularAuxiliaryIndexed hL).g
            ⟨p.finish,
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).ends_in_target
                hp⟩ =
          (L.popularAuxiliaryIndexed hL).g
            ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg (L.popularAuxiliaryIndexed hL).g
      exact Subtype.ext hfinish
    have heq := ht.symm.trans (hindex.trans hs)
    change L.markerStage ⟨y, hyMarker⟩ = L.finiteTerminalIndex xs
    exact heq
  · right
    refine ⟨i, ys, hstart, hfinish, ?_⟩
    have hs :
        (L.popularAuxiliaryIndexed hL).f
            ⟨p.start,
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
                hp⟩ =
          (L.popularAuxiliaryIndexed hL).f
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := by
      apply congrArg (L.popularAuxiliaryIndexed hL).f
      exact Subtype.ext hstart
    have ht :
        (L.popularAuxiliaryIndexed hL).g
            ⟨p.finish,
              ((L.popularAuxiliaryIndexed hL).equalSubwarp P).ends_in_target
                hp⟩ =
          (L.popularAuxiliaryIndexed hL).g
            ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg (L.popularAuxiliaryIndexed hL).g
      exact Subtype.ext hfinish
    have heq := ht.symm.trans (hindex.trans hs)
    change L.markerStage ⟨y, hyMarker⟩ = L.groundedInfiniteStage i
    exact heq

end KappaLadder
end DWeb
end Erdos599
