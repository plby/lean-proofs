/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyResidualDegree
import ErdosProblems.Erdos207.AvailabilityUpperTrajectory
import ErdosProblems.Erdos207.OuterOnlyExactAvailability
import ErdosProblems.Erdos207.InitialAggregatePairIncidence

/-!
# Sharp initialization of the scheduled outer-only process

The generic initializer bounds a live pair star by the ambient vertex count
and the entire available family by all ambient triples.  At the first hybrid
level both losses are fatal.  Here the pair cap is the number of vertices
outside the protected level, and the availability cap keeps the exact factor
three from summing pair degrees.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Initialize all clauses of the sharp active predicate from monotone
absorber cutoffs, the exact outer-only pair cap, and the pair-sum upper bound
for the total available family. -/
theorem timedSharpScheduledAggregatePairBandActive_outerOnly_initial_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc m Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {H G : SimpleGraph V} {X U : Finset V} {B A : TripleSystemOn V}
    (hq : 4 ≤ q)
    (hA2 : HasAbsorberLocalization q Mloc H X B)
    (htri : ConsistsOfTriangles G A)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hfloor : HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hKpair : pairTwoAwayThreatExtensionCoefficient q B ≤ Kpair)
    (hKglobal : twoAwayThreatExtensionCoefficient q Mloc H X B ≤ Kglobal)
    (hKinc : initialAggregatePairTwoAwayCoefficient q B *
      Fintype.card V ≤ Kinc)
    (hOuterDelta : (univ \ U).card ≤ Delta)
    (hdelta : delta ≤ m + 1)
    (hI : Fintype.card (TripleOn V) *
      twoAwayThreatExtensionCoefficient q Mloc H X B ≤ I)
    (D d Mschedule u : ℕ → ℕ)
    (hDcutPos : 0 < Dcut)
    (hDcut : Dcut ≤
      (Nat.choose (Fintype.card V) 2 -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * (m + 1) / 3)
    (hD : D 0 ≤
      (Nat.choose (Fintype.card V) 2 -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * d 0 / 3)
    (hd : d 0 ≤ m + 1)
    (hu : (univ \ U).card ≤ u 0)
    (hM : ((Nat.choose (Fintype.card V) 2 -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * u 0) / 3 ≤
        Mschedule 0) :
    timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      Kpair Kglobal Kinc Delta delta I Dcut D d Mschedule u 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
  have hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀ :=
    absorberGreedyInitialState_invariant F (outerOnlyAvailable U A)
      (fun _C hC ↦ absorberErdosForbidden_nonempty hC)
  have hchosen : S₀.chosen = ∅ := by
    simp [S₀, absorberGreedyInitialState]
  have hDcutAvailable : Dcut ≤ S₀.available.card := by
    apply scheduled_available_floor_outerOnly_exact (i := 0) hAbs₀ htri houtside
      (by simp [hchosen]) hfloor
    simpa only [Nat.mul_zero, Nat.sub_zero] using hDcut
  have hpairD : HasAvailablePairFloor (d 0) S₀ := by
    intro P hP halive
    exact hd.trans (hfloor P hP halive)
  have hDAvailable : D 0 ≤ S₀.available.card := by
    apply scheduled_available_floor_outerOnly_exact (i := 0) hAbs₀ htri houtside
      (by simp [hchosen]) hpairD
    simpa only [Nat.mul_zero, Nat.sub_zero] using hD
  have hpairOuter : HasAvailablePairCutoff (univ \ U).card S₀ :=
    hasAvailablePairCutoff_outerOnly_card hAbs₀
  have hpairDelta : HasAvailablePairCutoff Delta S₀ :=
    hpairOuter.mono hOuterDelta
  have hpairU : HasAvailablePairCutoff (u 0) S₀ :=
    hpairOuter.mono hu
  have hglobal₀ : HasTwoAwayCutoff F
      (twoAwayThreatExtensionCoefficient q Mloc H X B) S₀ :=
    hasTwoAwayCutoff_absorber_of_chosen_empty hA2 hchosen
  have hglobal : HasTwoAwayCutoff F Kglobal S₀ := by
    intro T hT
    exact (hglobal₀ T hT).trans hKglobal
  have htotal : totalAvailableTwoAwayIncidences F S₀ ≤ I :=
    (totalAvailableTwoAwayIncidences_le_card_mul_of_cutoff
      hglobal₀).trans hI
  have hnonempty : S₀.available.Nonempty := by
    rw [← card_pos]
    exact hDcutPos.trans_le hDcutAvailable
  have havailable : S₀.available.card ≤ Mschedule 0 := by
    apply scheduled_available_ceiling_outerOnly_exact (i := 0) hAbs₀ htri
      (by simp [hchosen]) hpairU
    simpa only [Nat.mul_zero, Nat.sub_zero] using hM
  unfold timedSharpScheduledAggregatePairBandActive
  refine ⟨?_, hpairU⟩
  unfold timedFullyScheduledAggregatePairBandActive
  refine ⟨?_, havailable⟩
  unfold timedScheduledAggregatePairBandActive
  refine ⟨?_, hDAvailable, ?_⟩
  · unfold timedAggregateAveragePairBandActive
    refine ⟨?_, ?_⟩
    · unfold timedAveragePairBandActive
      refine ⟨?_, htotal, by simpa only [S₀, F] using hDcutAvailable⟩
      refine ⟨hnonempty, hpairDelta, ?_, hglobal, ?_⟩
      · intro T hT P hPcard hnot
        exact (hasPairTwoAwayCutoff_absorber_of_chosen_empty hchosen
          T hT P hPcard hnot).trans hKpair
      · intro P hPcard hPnonempty
        exact hdelta.trans (hfloor P hPcard hPnonempty)
    · intro P hPcard
      exact (hasPairStarTwoAwayIncidenceCutoff_absorber_of_chosen_empty_linear
        hq hchosen P hPcard).trans hKinc
  · exact fun P hPcard hPnonempty ↦
      hd.trans (hfloor P hPcard hPnonempty)

end

end Erdos207
