/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ExternalWeightedOnePoint

/-!
# Canonical-walk weighted one-site estimate

This file lifts the finite thinning estimate to the canonical planar walk.
The shifted deletion starts after the first direction, so that case is
conditioned on the four possible first directions and uses independence of
the first coordinate from the following paired segment.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalWeightedOnePointCanonical

open LazyDecomposition ExternalWalk ExternalOnePoint ExternalGreenRenewal
open ExternalThickCount ExternalProposition44 ExternalCountTransport
open ExternalHLOZOnePoint ExternalWeightedOnePoint

noncomputable section

attribute [local instance] Classical.propDecidable

lemma measurableSet_candidate_orientedExternalVisitedSites
    (o : Orientation) (n k : ℕ) (x : Point) :
    MeasurableSet
      (candidateEvent (fun s ↦ orientedExternalVisitedSites o s n)
        (orientedLargeEvent o n k) x) :=
  (measurableSet_member_orientedExternalVisitedSites o n x).inter
    (measurableSet_orientedLargeEvent o n k x)

theorem fairSteps_even_weighted_oneSite (n N k : ℕ) (q : ℝ≥0∞)
    (hnN : n / 2 ≤ N)
    (hone : externalBlocks .even {η |
      k ≤ externalOriginLocalTime .even η N} ≤ q) (x : Point) :
    fairSteps (trajectory ⁻¹'
        candidateEvent (fun s ↦ orientedExternalVisitedSites .even s n)
          (orientedLargeEvent .even n k) x) ≤
      q * fairSteps (trajectory ⁻¹'
        memberEvent (fun s ↦ orientedExternalVisitedSites .even s n) x) := by
  have h := fairSteps_pairedSegment_weighted .even x 0 (n / 2) N k q hnN hone
  rw [show trajectory ⁻¹'
      candidateEvent (fun s ↦ orientedExternalVisitedSites .even s n)
        (orientedLargeEvent .even n k) x =
      {ω | HasGoodExtracted .even (retainedCandidateProperty .even x k)
        (pairedSegment 0 (n / 2) ω)} by
        ext ω
        exact even_candidateEvent_iff_hasGoodExtracted ω n k x,
    show trajectory ⁻¹'
      memberEvent (fun s ↦ orientedExternalVisitedSites .even s n) x =
      {ω | HasGoodExtracted .even (retainedMemberProperty .even x)
        (pairedSegment 0 (n / 2) ω)} by
        ext ω
        exact even_memberEvent_iff_hasGoodExtracted ω n x]
  exact h

theorem simpleRandomWalk_even_weighted_oneSite (n N k : ℕ) (q : ℝ≥0∞)
    (hnN : n / 2 ≤ N)
    (hone : externalBlocks .even {η |
      k ≤ externalOriginLocalTime .even η N} ≤ q) (x : Point) :
    simpleRandomWalk
        (candidateEvent (fun s ↦ orientedExternalVisitedSites .even s n)
          (orientedLargeEvent .even n k) x) ≤
      q * simpleRandomWalk
        (memberEvent (fun s ↦ orientedExternalVisitedSites .even s n) x) := by
  rw [simpleRandomWalk,
    Measure.map_apply measurable_trajectory
      (measurableSet_candidate_orientedExternalVisitedSites .even n k x),
    Measure.map_apply measurable_trajectory
      (measurableSet_member_orientedExternalVisitedSites .even n x)]
  exact fairSteps_even_weighted_oneSite n N k q hnN hone x

lemma trajectory_one (omega : StepPath) :
    trajectory omega 1 = directionVector (omega 0) := by
  rw [show 1 = 0 + 1 by omega, trajectory_succ, trajectory_zero]
  simp

lemma indepFun_firstDirection_pairedSegment (a : ℕ) :
    IndepFun (fun omega : StepPath ↦ omega 0) (pairedSegment 1 a) fairSteps := by
  let first : (Fin 1 → Direction) → Direction := fun u ↦ u 0
  let pair : (Fin (2 * a) → Direction) → Fin a → ExternalWalk.Block :=
    fun u j ↦
      (u ⟨2 * (j : ℕ), by omega⟩, u ⟨2 * (j : ℕ) + 1, by omega⟩)
  have h := (indepFun_stepPrefix_stepBlock 1 (2 * a)).comp
    (measurable_of_countable first) (measurable_of_countable pair)
  convert h using 1
  · funext omega
    rfl
  · funext omega j
    simp only [Function.comp_apply, pair, stepBlock, pairedSegment]
    congr 1

lemma fairSteps_firstDirection_mass (d : Direction) :
    fairSteps {omega : StepPath | omega 0 = d} = 1 / 4 := by
  calc
    fairSteps {omega : StepPath | omega 0 = d} =
        (fairSteps.map (fun omega : StepPath ↦ omega 0)) {d} := by
      rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton d)]
      rfl
    _ = fairStep {d} := by rw [fairSteps_eval]
    _ = 1 / 4 := fairStep_singleton d

lemma fairSteps_firstDirection_inter_hasGood (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (a : ℕ)
    (d : Direction) :
    fairSteps ({omega : StepPath | omega 0 = d} ∩
        {omega | HasGoodExtracted o B (pairedSegment 1 a omega)}) =
      (1 / 4 : ℝ≥0∞) *
        fairSteps {omega | HasGoodExtracted o B (pairedSegment 1 a omega)} := by
  let G : Set (Fin a → ExternalWalk.Block) := {u | HasGoodExtracted o B u}
  have h := (indepFun_firstDirection_pairedSegment a).measure_inter_preimage_eq_mul
    ({d} : Set Direction) G (measurableSet_singleton d)
      (Set.to_countable G).measurableSet
  have hfirst : (fun omega : StepPath ↦ omega 0) ⁻¹' ({d} : Set Direction) =
      {omega : StepPath | omega 0 = d} := by
    ext omega
    simp
  have hgood : pairedSegment 1 a ⁻¹' G =
      {omega | HasGoodExtracted o B (pairedSegment 1 a omega)} := by
    rfl
  rw [hfirst, hgood, fairSteps_firstDirection_mass] at h
  exact h

lemma firstDirection_partition (E : Set StepPath) :
    (⋃ d ∈ (Finset.univ : Finset Direction),
      ({omega : StepPath | omega 0 = d} ∩ E)) = E := by
  ext omega
  simp

lemma firstDirection_pieces_pairwiseDisjoint (E : Set StepPath) :
    Set.PairwiseDisjoint (Finset.univ : Finset Direction)
      (fun d ↦ {omega : StepPath | omega 0 = d} ∩ E) := by
  intro d hd e he hde
  change Disjoint ({omega : StepPath | omega 0 = d} ∩ E)
    ({omega : StepPath | omega 0 = e} ∩ E)
  rw [Set.disjoint_left]
  intro omega homegaD homegaE
  exact hde (homegaD.1.symm.trans homegaE.1)

theorem fairSteps_shifted_weighted_oneSite (n N k : ℕ) (hn : 0 < n)
    (q : ℝ≥0∞) (hnN : (n - 1) / 2 ≤ N)
    (hone : externalBlocks .shifted {eta |
      k ≤ externalOriginLocalTime .shifted eta N} ≤ q) (x : Point) :
    fairSteps (trajectory ⁻¹'
        candidateEvent (fun s ↦ orientedExternalVisitedSites .shifted s n)
          (orientedLargeEvent .shifted n k) x) ≤
      q * fairSteps (trajectory ⁻¹'
        memberEvent (fun s ↦ orientedExternalVisitedSites .shifted s n) x) := by
  let E : Set StepPath := trajectory ⁻¹'
    candidateEvent (fun s ↦ orientedExternalVisitedSites .shifted s n)
      (orientedLargeEvent .shifted n k) x
  let M : Set StepPath := trajectory ⁻¹'
    memberEvent (fun s ↦ orientedExternalVisitedSites .shifted s n) x
  let HE : Direction → Set StepPath :=
    fun d ↦ {omega | omega 0 = d} ∩ E
  let HM : Direction → Set StepPath :=
    fun d ↦ {omega | omega 0 = d} ∩ M
  have hEcand (d : Direction) : HE d =
      {omega | omega 0 = d} ∩
        {omega | HasGoodExtracted .shifted
          (retainedCandidateProperty .shifted (x - directionVector d) k)
          (pairedSegment 1 ((n - 1) / 2) omega)} := by
    ext omega
    simp only [HE, E, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hd, hcandidate⟩
      refine ⟨hd, ?_⟩
      have h := (shifted_candidateEvent_iff_hasGoodExtracted omega n k hn x).1
        hcandidate
      simpa only [trajectory_one, hd] using h
    · rintro ⟨hd, hcandidate⟩
      refine ⟨hd, ?_⟩
      apply (shifted_candidateEvent_iff_hasGoodExtracted omega n k hn x).2
      simpa only [trajectory_one, hd] using hcandidate
  have hMmem (d : Direction) : HM d =
      {omega | omega 0 = d} ∩
        {omega | HasGoodExtracted .shifted
          (retainedMemberProperty .shifted (x - directionVector d))
          (pairedSegment 1 ((n - 1) / 2) omega)} := by
    ext omega
    simp only [HM, M, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hd, hmember⟩
      refine ⟨hd, ?_⟩
      have h := (shifted_memberEvent_iff_hasGoodExtracted omega n hn x).1 hmember
      simpa only [trajectory_one, hd] using h
    · rintro ⟨hd, hmember⟩
      refine ⟨hd, ?_⟩
      apply (shifted_memberEvent_iff_hasGoodExtracted omega n hn x).2
      simpa only [trajectory_one, hd] using hmember
  have hpiece (d : Direction) :
      fairSteps (HE d) ≤ q * fairSteps (HM d) := by
    rw [hEcand d, hMmem d,
      fairSteps_firstDirection_inter_hasGood,
      fairSteps_firstDirection_inter_hasGood]
    have hraw := fairSteps_pairedSegment_weighted .shifted
      (x - directionVector d) 1 ((n - 1) / 2) N k q hnN hone
    calc
      (1 / 4 : ℝ≥0∞) * fairSteps
          {omega | HasGoodExtracted .shifted
            (retainedCandidateProperty .shifted (x - directionVector d) k)
            (pairedSegment 1 ((n - 1) / 2) omega)} ≤
        (1 / 4 : ℝ≥0∞) * (q * fairSteps
          {omega | HasGoodExtracted .shifted
            (retainedMemberProperty .shifted (x - directionVector d))
            (pairedSegment 1 ((n - 1) / 2) omega)}) :=
        by gcongr
      _ = q * ((1 / 4 : ℝ≥0∞) * fairSteps
          {omega | HasGoodExtracted .shifted
            (retainedMemberProperty .shifted (x - directionVector d))
            (pairedSegment 1 ((n - 1) / 2) omega)}) := by ac_rfl
  have hEmeas : MeasurableSet E :=
    (measurableSet_candidate_orientedExternalVisitedSites .shifted n k x).preimage
      measurable_trajectory
  have hMmeas : MeasurableSet M :=
    (measurableSet_member_orientedExternalVisitedSites .shifted n x).preimage
      measurable_trajectory
  have hHEmeas : ∀ d ∈ (Finset.univ : Finset Direction),
      MeasurableSet (HE d) := by
    intro d hd
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      hEmeas
  have hHMmeas : ∀ d ∈ (Finset.univ : Finset Direction),
      MeasurableSet (HM d) := by
    intro d hd
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      hMmeas
  have hHEdis : Set.PairwiseDisjoint (Finset.univ : Finset Direction) HE := by
    simpa only [HE] using firstDirection_pieces_pairwiseDisjoint E
  have hHMdis : Set.PairwiseDisjoint (Finset.univ : Finset Direction) HM := by
    simpa only [HM] using firstDirection_pieces_pairwiseDisjoint M
  have hEunion : (⋃ d ∈ (Finset.univ : Finset Direction), HE d) = E := by
    simpa only [HE] using firstDirection_partition E
  have hMunion : (⋃ d ∈ (Finset.univ : Finset Direction), HM d) = M := by
    simpa only [HM] using firstDirection_partition M
  change fairSteps E ≤ q * fairSteps M
  calc
    fairSteps E = fairSteps (⋃ d ∈ (Finset.univ : Finset Direction), HE d) :=
      congrArg fairSteps hEunion.symm
    _ = ∑ d ∈ (Finset.univ : Finset Direction), fairSteps (HE d) :=
      measure_biUnion_finset hHEdis hHEmeas
    _ ≤ ∑ d ∈ (Finset.univ : Finset Direction), q * fairSteps (HM d) :=
      Finset.sum_le_sum fun d hd ↦ hpiece d
    _ = q * ∑ d ∈ (Finset.univ : Finset Direction), fairSteps (HM d) := by
      rw [Finset.mul_sum]
    _ = q * fairSteps (⋃ d ∈ (Finset.univ : Finset Direction), HM d) := by
      rw [measure_biUnion_finset hHMdis hHMmeas]
    _ = q * fairSteps M := by rw [hMunion]

theorem simpleRandomWalk_shifted_weighted_oneSite (n N k : ℕ)
    (hn : 0 < n) (q : ℝ≥0∞) (hnN : (n - 1) / 2 ≤ N)
    (hone : externalBlocks .shifted {eta |
      k ≤ externalOriginLocalTime .shifted eta N} ≤ q) (x : Point) :
    simpleRandomWalk
        (candidateEvent (fun s ↦ orientedExternalVisitedSites .shifted s n)
          (orientedLargeEvent .shifted n k) x) ≤
      q * simpleRandomWalk
        (memberEvent (fun s ↦ orientedExternalVisitedSites .shifted s n) x) := by
  rw [simpleRandomWalk,
    Measure.map_apply measurable_trajectory
      (measurableSet_candidate_orientedExternalVisitedSites .shifted n k x),
    Measure.map_apply measurable_trajectory
      (measurableSet_member_orientedExternalVisitedSites .shifted n x)]
  exact fairSteps_shifted_weighted_oneSite n N k hn q hnN hone x

theorem hlozOnePointRate44_ne_top (m : ℕ) :
    hlozOnePointRate44 m ≠ ∞ := by
  unfold hlozOnePointRate44
  exact ENNReal.ofReal_ne_top

/-- The exact weighted one-site premise needed by the deterministic-time
version of HLOZ Proposition 4.8, simultaneously valid for either deletion
orientation once the proved one-point level lies below the thick level. -/
theorem eventually_simpleRandomWalk_hloz_weightedOneSite44
    (o : Orientation) :
    ∀ᶠ m : ℕ in atTop, ∀ x : Point,
      simpleRandomWalk
          (candidateEvent
            (fun s ↦ orientedExternalVisitedSites o s (hlozCutoff44 m))
            (orientedLargeEvent o (hlozCutoff44 m) (hlozThickLevel44 m)) x) ≤
        hlozOnePointRate44 m * simpleRandomWalk
          (memberEvent
            (fun s ↦ orientedExternalVisitedSites o s (hlozCutoff44 m)) x) := by
  filter_upwards
      [eventually_hlozOnePointLevel44_le_thickLevel44,
       hlozSharpExternalOnePointTail44 o]
      with m hlevel hone
  intro x
  have hthick : externalBlocks o {eta |
      hlozThickLevel44 m ≤
        externalOriginLocalTime o eta (hlozCutoff44 m)} ≤
      hlozOnePointRate44 m :=
    (measure_mono fun eta heta ↦ hlevel.trans heta).trans hone
  cases o with
  | even =>
      exact simpleRandomWalk_even_weighted_oneSite
        (hlozCutoff44 m) (hlozCutoff44 m) (hlozThickLevel44 m)
        (hlozOnePointRate44 m) (Nat.div_le_self _ _) hthick x
  | shifted =>
      apply simpleRandomWalk_shifted_weighted_oneSite
        (hlozCutoff44 m) (hlozCutoff44 m) (hlozThickLevel44 m)
        (levelCutoffTime_pos hlozDelta44 m) (hlozOnePointRate44 m)
      · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
      · exact hthick

end


end Erdos1165.ExternalWeightedOnePointCanonical
