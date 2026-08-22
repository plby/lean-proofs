/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedExternalLocalTime
import ErdosProblems.Erdos1165.TilingStoppedWeightedOnePoint
import ErdosProblems.Erdos1165.ExternalHLOZOnePoint

/-!
# Proposition 4.4 for endpoint-oriented source coordinates

The source `Theta` screen sees the endpoint chain of a specified temporal
pairing.  This file proves the corresponding relevant-site estimate directly
from the stopped, weighted one-site theorem.  In particular, it does not pass
through the older phase-free external path and it does not retain a
path-to-external-chain transport premise.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedProposition44

open ExternalProposition44 ExternalThickCount HLOZSourceOrientedExternalLocalTime
open LazyDecomposition TilingExternalPhaseSplit TilingLazyDecomposition
open TilingStoppedWeightedOnePoint
open SpatialInsertionFiber ExternalWalk ExternalWeightedOnePointCanonical
open ExternalOnePoint

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-- The oriented endpoint-chain local-time tail at one spatial site. -/
def sourceExternalLargeEvent (t : DominoTiling) (o : Orientation)
    (n threshold : ℕ) (x : Point) : Set WalkPath :=
  {s | threshold ≤ tilingSourceExternalBaseLocalTime t o s n x}

/-- The literal endpoint-oriented thick-site count before removing a
distinguished finite set. -/
def sourceExternalThickCount (t : DominoTiling) (o : Orientation)
    (s : WalkPath) (n threshold : ℕ) : ℕ :=
  candidateCount (fun s ↦ tilingSourceExternalVisitedSites t o s n)
    (sourceExternalLargeEvent t o n threshold) s

lemma measurable_tilingSourceExternalVisitedSites
    (t : DominoTiling) (o : Orientation) (n : ℕ) :
    Measurable fun s : WalkPath ↦ tilingSourceExternalVisitedSites t o s n := by
  exact (measurable_of_countable fun u : Fin (n + 1) → Point ↦
    (phasedExternalVertexVisitedSites t o .endpoint
      (finitePathList u)).filter (OrientationCompatible o)).comp
        (measurable_pathPrefix n)

lemma measurableSet_member_tilingSourceExternalVisitedSites
    (t : DominoTiling) (o : Orientation) (n : ℕ) (x : Point) :
    MeasurableSet
      (memberEvent (fun s ↦ tilingSourceExternalVisitedSites t o s n) x) := by
  exact measurable_tilingSourceExternalVisitedSites t o n
    ((Set.to_countable {v : Finset Point | x ∈ v}).measurableSet)

lemma measurable_tilingSourceExternalBaseLocalTime
    (t : DominoTiling) (o : Orientation) (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦
      tilingSourceExternalBaseLocalTime t o s n x := by
  exact (measurable_of_countable fun u : Fin (n + 1) → Point ↦
    phasedExternalVertexLocalTime t o .endpoint (finitePathList u) x).comp
      (measurable_pathPrefix n)

lemma measurableSet_sourceExternalLargeEvent
    (t : DominoTiling) (o : Orientation) (n threshold : ℕ) (x : Point) :
    MeasurableSet (sourceExternalLargeEvent t o n threshold x) := by
  exact measurableSet_le measurable_const
    (measurable_tilingSourceExternalBaseLocalTime t o n x)

lemma tilingExternalPath_length_le (t : DominoTiling) (p : List Point) :
    (tilingExternalPath t p).length ≤ p.length := by
  have h := tilingExternalPath_length_add_lazyPoints_length t p
  omega

lemma endpointPhaseVertices_length_le (p : List Point) :
    (phaseVertices .endpoint p).length ≤ p.length := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [phaseVertices, endpointPhaseVertices]
  | cons_cons a b rest ih _ =>
      simp [phaseVertices, endpointPhaseVertices] at ih ⊢
      omega

lemma sourceExternalVisitedSites_card_le
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ) :
    (tilingSourceExternalVisitedSites t o s n).card ≤ n + 1 := by
  calc
    (tilingSourceExternalVisitedSites t o s n).card ≤
        (phasedExternalVertexVisitedSites t o .endpoint
          (finitePathList (pathPrefix s n))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (phasedExternalVertexPath t o .endpoint
          (finitePathList (pathPrefix s n))).length := List.toFinset_card_le _
    _ ≤ (tilingExternalPath t
          (phasedInput o (finitePathList (pathPrefix s n)))).length :=
      endpointPhaseVertices_length_le _
    _ ≤ (phasedInput o (finitePathList (pathPrefix s n))).length :=
      tilingExternalPath_length_le t _
    _ ≤ n + 1 := by
      cases o <;> simp [phasedInput, finitePathList]

theorem lintegral_sourceExternalVisitedSites_card_le
    (t : DominoTiling) (o : Orientation) (n : ℕ) :
    ∫⁻ s, ((tilingSourceExternalVisitedSites t o s n).card : ℝ≥0∞)
        ∂simpleRandomWalk ≤ (n + 1 : ℕ) := by
  calc
    ∫⁻ s, ((tilingSourceExternalVisitedSites t o s n).card : ℝ≥0∞)
        ∂simpleRandomWalk ≤
        ∫⁻ _s : WalkPath, ((n + 1 : ℕ) : ℝ≥0∞)
          ∂simpleRandomWalk := by
      apply lintegral_mono
      intro s
      change ((tilingSourceExternalVisitedSites t o s n).card : ℝ≥0∞) ≤
        ((n + 1 : ℕ) : ℝ≥0∞)
      exact_mod_cast sourceExternalVisitedSites_card_le t o s n
    _ = (n + 1 : ℕ) := by simp

lemma trajectory_preimage_sourceMember_even
    (t : DominoTiling) (n : ℕ) (x : Point)
    (hx : OrientationCompatible .even x) :
    trajectory ⁻¹'
        memberEvent (fun s ↦ tilingSourceExternalVisitedSites t .even s n) x =
      evenStoppedTilingEndpointMember t (fun _ ↦ n) x := by
  ext omega
  simp only [Set.mem_preimage, memberEvent, Set.mem_ofPred_eq,
    mem_tilingSourceExternalVisitedSites_iff, hx,
    evenStoppedTilingEndpointMember]
  simp only [true_and]
  change 0 < phasedExternalVertexLocalTime t .even .endpoint
      (finitePathList (pathPrefix (trajectory omega) n)) x ↔ _
  rw [phasedExternalEndpointLocalTime_even]
  simp [tilingDeletedMemberProperty_iff_mem_rawEndpointPath,
    tilingRawEndpointPath, listLocalTime]

lemma trajectory_preimage_sourceLarge_even
    (t : DominoTiling) (n threshold : ℕ) (x : Point) :
    trajectory ⁻¹' sourceExternalLargeEvent t .even n threshold x =
      evenStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x := by
  ext omega
  simp only [Set.mem_preimage, sourceExternalLargeEvent, Set.mem_ofPred_eq,
    tilingSourceExternalBaseLocalTime, prefixTilingSourceExternalBaseLocalTime,
    evenStoppedTilingEndpointLarge]
  rw [phasedExternalEndpointLocalTime_even]
  rfl

lemma trajectory_preimage_sourceMember_shifted
    (t : DominoTiling) (n : ℕ) (x : Point)
    (hx : OrientationCompatible .shifted x) :
    trajectory ⁻¹'
        memberEvent (fun s ↦ tilingSourceExternalVisitedSites t .shifted s n) x =
      shiftedStoppedTilingEndpointMember t (fun _ ↦ n) x := by
  ext omega
  simp only [Set.mem_preimage, memberEvent, Set.mem_ofPred_eq,
    mem_tilingSourceExternalVisitedSites_iff, hx,
    shiftedStoppedTilingEndpointMember]
  by_cases hn : n = 0
  · subst n
    simp only [true_and, Nat.lt_irrefl, false_and, iff_false]
    change ¬(0 < listLocalTime
      (phasedExternalVertexPath t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) 0))) x)
    rw [phasedExternalEndpointPath_shifted_zero]
    simp [listLocalTime]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp only [hnpos, true_and]
    change 0 < phasedExternalVertexLocalTime t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x ↔ _
    rw [phasedExternalEndpointLocalTime_shifted t omega n hnpos]
    rw [trajectory_one]
    simp [tilingDeletedMemberProperty_iff_mem_rawEndpointPath,
      tilingRawEndpointPath, listLocalTime]

lemma trajectory_preimage_sourceLarge_shifted
    (t : DominoTiling) (n threshold : ℕ) (x : Point)
    (hthreshold : 0 < threshold) :
    trajectory ⁻¹' sourceExternalLargeEvent t .shifted n threshold x =
      shiftedStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x := by
  ext omega
  simp only [Set.mem_preimage, sourceExternalLargeEvent, Set.mem_ofPred_eq,
    shiftedStoppedTilingEndpointLarge]
  by_cases hn : n = 0
  · subst n
    rw [show tilingSourceExternalBaseLocalTime t .shifted
        (trajectory omega) 0 x = 0 by rfl]
    simp [Nat.not_le.mpr hthreshold]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp only [hnpos, true_and]
    change threshold ≤ phasedExternalVertexLocalTime t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x ↔ _
    rw [phasedExternalEndpointLocalTime_shifted t omega n hnpos]
    rw [trajectory_one]
    rfl

/-- Uniform weighted one-site estimate for the literal source endpoint
chain, for any of the six spatial tilings and either temporal orientation. -/
theorem simpleRandomWalk_sourceEndpoint_weighted_oneSite
    (t : DominoTiling) (o : Orientation) (n N threshold : ℕ)
    (q : ℝ≥0∞) (hnN : n ≤ N) (hthreshold : 0 < threshold)
    (hone : externalBlocks .even {η |
      threshold ≤ externalOriginLocalTime .even η N} ≤ q)
    (x : Point) :
    simpleRandomWalk
        (candidateEvent
          (fun s ↦ tilingSourceExternalVisitedSites t o s n)
          (sourceExternalLargeEvent t o n threshold) x) ≤
      q * simpleRandomWalk
        (memberEvent
          (fun s ↦ tilingSourceExternalVisitedSites t o s n) x) := by
  let member := memberEvent
    (fun s ↦ tilingSourceExternalVisitedSites t o s n) x
  let large := sourceExternalLargeEvent t o n threshold x
  have hmember : MeasurableSet member :=
    measurableSet_member_tilingSourceExternalVisitedSites t o n x
  have hlarge : MeasurableSet large :=
    measurableSet_sourceExternalLargeEvent t o n threshold x
  change simpleRandomWalk (member ∩ large) ≤ q * simpleRandomWalk member
  by_cases hx : OrientationCompatible o x
  · rw [simpleRandomWalk,
      Measure.map_apply measurable_trajectory (hmember.inter hlarge),
      Measure.map_apply measurable_trajectory hmember]
    cases o with
    | even =>
        have hlargeStep : MeasurableSet
            (evenStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x) := by
          rw [← trajectory_preimage_sourceLarge_even t n threshold x]
          exact hlarge.preimage measurable_trajectory
        rw [preimage_inter,
          show trajectory ⁻¹' member =
              evenStoppedTilingEndpointMember t (fun _ ↦ n) x by
            exact trajectory_preimage_sourceMember_even t n x hx,
          show trajectory ⁻¹' large =
              evenStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x by
            exact trajectory_preimage_sourceLarge_even t n threshold x]
        exact fairSteps_evenStoppedTilingEndpoint_weighted_oneSite
          t (fun _ ↦ n) N threshold q x (isFiniteStoppingTime_const n)
          (fun _ ↦ (Nat.div_le_self n 2).trans hnN)
          hlargeStep hone
    | shifted =>
        have hlargeStep : MeasurableSet
            (shiftedStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x) := by
          rw [← trajectory_preimage_sourceLarge_shifted t n threshold x
            hthreshold]
          exact hlarge.preimage measurable_trajectory
        rw [preimage_inter,
          show trajectory ⁻¹' member =
              shiftedStoppedTilingEndpointMember t (fun _ ↦ n) x by
            exact trajectory_preimage_sourceMember_shifted t n x hx,
          show trajectory ⁻¹' large =
              shiftedStoppedTilingEndpointLarge t (fun _ ↦ n) threshold x by
            exact trajectory_preimage_sourceLarge_shifted t n threshold x
              hthreshold]
        exact fairSteps_shiftedStoppedTilingEndpoint_weighted_oneSite
          t (fun _ ↦ n) N threshold q x (isFiniteStoppingTime_const n)
          (fun _ ↦ (Nat.div_le_self (n - 1) 2).trans
            ((Nat.sub_le n 1).trans hnN))
          hlargeStep hone
  · have hempty : member = ∅ := by
      ext s
      simp only [member, memberEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      rw [mem_tilingSourceExternalVisitedSites_iff]
      exact fun hs ↦ hx hs.1
    simp only [member, hempty, empty_inter,
      measure_empty, mul_zero, le_refl]

/-- Tonelli--Markov estimate for the literal source endpoint chain. -/
theorem simpleRandomWalk_sourceExternalThickCount_gt_le
    (t : DominoTiling) (o : Orientation) (n threshold J : ℕ)
    (q : ℝ≥0∞) (hthreshold : 0 < threshold)
    (hone : externalBlocks .even {η |
      threshold ≤ externalOriginLocalTime .even η n} ≤ q) :
    simpleRandomWalk {s | J < sourceExternalThickCount t o s n threshold} ≤
      q * (↑(n + 1) : ℝ≥0∞) / (↑(J + 1) : ℝ≥0∞) := by
  exact measure_candidateCount_gt_le_succ simpleRandomWalk
    (fun s ↦ tilingSourceExternalVisitedSites t o s n)
    (sourceExternalLargeEvent t o n threshold) q (↑(n + 1) : ℝ≥0∞) J
    (measurableSet_member_tilingSourceExternalVisitedSites t o n)
    (measurableSet_sourceExternalLargeEvent t o n threshold)
    (simpleRandomWalk_sourceEndpoint_weighted_oneSite t o n n threshold q
      le_rfl hthreshold hone)
    (lintegral_sourceExternalVisitedSites_card_le t o n)

lemma sourceCandidateSites_card_le_thickCount
    (t : DominoTiling) (o : Orientation)
    (cutoff threshold : ℕ) (distinguished : WalkPath → Finset Point)
    (s : WalkPath) :
    (tilingSourceExternalCandidateSites t o cutoff threshold distinguished s).card
      ≤ sourceExternalThickCount t o s cutoff threshold := by
  classical
  unfold sourceExternalThickCount candidateCount sourceExternalLargeEvent
  rw [tilingSourceExternalCandidateSites]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

theorem sourceCandidateOverflow_subset_thickCount
    (t : DominoTiling) (o : Orientation)
    (cutoff threshold budget : ℕ)
    (distinguished : WalkPath → Finset Point) :
    tilingSourceExternalCandidateOverflow t o cutoff threshold budget
        distinguished ⊆
      {s | budget < sourceExternalThickCount t o s cutoff threshold} := by
  intro s hs
  exact hs.trans_le
    (sourceCandidateSites_card_le_thickCount t o cutoff threshold distinguished s)

/-- Premise-free, all-six, orientation-indexed Proposition 4.4 payment. -/
theorem eventually_sourceCandidateOverflow_lt_failureRate
    (t : DominoTiling) (o : Orientation)
    (distinguished : ℕ → WalkPath → Finset Point) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingSourceExternalCandidateOverflow t o
            (hlozCutoff44 m) (hlozThickLevel44 m) (hlozSiteBudget44 m)
            (distinguished m)) <
        hlozFailureRate44 m := by
  filter_upwards [eventually_hlozOnePointLevel44_le_thickLevel44,
      eventually_hlozMarkovRate44_lt_failureRate44,
      ExternalHLOZOnePoint.hlozSharpExternalOnePointTail44 .even]
      with m hlevel harith hone
  have hthreshold : 0 < hlozThickLevel44 m := by
    unfold hlozThickLevel44
    exact Nat.succ_pos _
  have htail : externalBlocks .even {η |
      hlozThickLevel44 m ≤
        externalOriginLocalTime .even η (hlozCutoff44 m)} ≤
      hlozOnePointRate44 m :=
    (measure_mono fun _ h ↦ hlevel.trans h).trans hone
  calc
    simpleRandomWalk
        (tilingSourceExternalCandidateOverflow t o
          (hlozCutoff44 m) (hlozThickLevel44 m) (hlozSiteBudget44 m)
          (distinguished m)) ≤
        simpleRandomWalk {s | hlozSiteBudget44 m <
          sourceExternalThickCount t o s (hlozCutoff44 m)
            (hlozThickLevel44 m)} :=
      measure_mono (sourceCandidateOverflow_subset_thickCount t o
        (hlozCutoff44 m) (hlozThickLevel44 m) (hlozSiteBudget44 m)
        (distinguished m))
    _ ≤ hlozOnePointRate44 m * (hlozCutoff44 m + 1) /
          (↑(hlozSiteBudget44 m + 1) : ℝ≥0∞) :=
      by
        simpa only [Nat.cast_add, Nat.cast_one] using
          simpleRandomWalk_sourceExternalThickCount_gt_le t o
            (hlozCutoff44 m) (hlozThickLevel44 m) (hlozSiteBudget44 m)
            (hlozOnePointRate44 m) hthreshold htail
    _ < hlozFailureRate44 m := harith

end

end Erdos1165.HLOZSourceOrientedProposition44
