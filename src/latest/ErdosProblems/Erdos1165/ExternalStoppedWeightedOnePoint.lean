/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ExternalWeightedOnePointCanonical

/-!
# Deterministic-cap domination for stopped external local time

The random-clock screen may overcount its visited set by the oriented range
at a deterministic cap.  At a site in the selected checkerboard class, the
deleted endpoint list only grows when the ordinary-time prefix grows.  Thus
a stopped large-local-time event below the cap is contained in the fixed-cap
large event, and the canonical weighted one-site theorem applies directly.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.ExternalStoppedWeightedOnePoint

open LazyDecomposition ExternalWalk ExternalOnePoint ExternalGreenRenewal
open ExternalThickCount ExternalProposition44 ExternalCountTransport
open ExternalHLOZOnePoint ExternalWeightedOnePoint
open ExternalWeightedOnePointCanonical

noncomputable section

attribute [local instance] Classical.propDecidable

lemma pairedSegmentList_prefix (omega : StepPath) (start : ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    List.ofFn (pairedSegment start a omega) <+:
      List.ofFn (pairedSegment start b omega) := by
  have htake : pairedSegment start a omega =
      Fin.take a hab (pairedSegment start b omega) := by
    funext j
    simp [Fin.take, pairedSegment]
  rw [htake, Fin.ofFn_take_eq_take_ofFn]
  exact List.take_prefix _ _

lemma deleteRemovableBlocks_prefix (o : Orientation)
    {as bs : List PathInsertion.Block} (h : as <+: bs) :
    PathInsertion.deleteRemovableBlocks o as <+:
      PathInsertion.deleteRemovableBlocks o bs := by
  exact h.filter _

lemma blockEndpointPath_prefix_append (x : Point)
    (as tail : List PathInsertion.Block) :
    blockEndpointPath x as <+: blockEndpointPath x (as ++ tail) := by
  induction as generalizing x with
  | nil =>
      cases tail with
      | nil => exact ⟨[], rfl⟩
      | cons b bs => exact ⟨blockEndpointPath (PathInsertion.blockEnd x b) bs, rfl⟩
  | cons b bs ih =>
      obtain ⟨r, hr⟩ := ih (PathInsertion.blockEnd x b)
      refine ⟨r, ?_⟩
      simpa only [blockEndpointPath_cons, List.cons_append] using
        congrArg (List.cons x) hr

lemma blockEndpointPath_prefix_of_prefix (x : Point)
    {as bs : List PathInsertion.Block} (h : as <+: bs) :
    blockEndpointPath x as <+: blockEndpointPath x bs := by
  obtain ⟨tail, rfl⟩ := h
  exact blockEndpointPath_prefix_append x as tail

lemma filtered_orientedExternalPath_even_prefix (omega : StepPath)
    {n N : ℕ} (hnN : n ≤ N) :
    (orientedExternalPath .even (pathPrefix (trajectory omega) n)).filter
        (orientationClass .even) <+:
      (orientedExternalPath .even (pathPrefix (trajectory omega) N)).filter
        (orientationClass .even) := by
  rw [filtered_orientedExternalPath_even_blocks,
    filtered_orientedExternalPath_even_blocks]
  apply blockEndpointPath_prefix_of_prefix
  apply deleteRemovableBlocks_prefix
  apply pairedSegmentList_prefix
  exact Nat.div_le_div_right hnN

lemma filtered_orientedExternalPath_shifted_prefix (omega : StepPath)
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (orientedExternalPath .shifted (pathPrefix (trajectory omega) n)).filter
        (orientationClass .shifted) <+:
      (orientedExternalPath .shifted (pathPrefix (trajectory omega) N)).filter
        (orientationClass .shifted) := by
  have hN : 0 < N := hn.trans_le hnN
  rw [filtered_orientedExternalPath_shifted_blocks omega n hn,
    filtered_orientedExternalPath_shifted_blocks omega N hN]
  apply blockEndpointPath_prefix_of_prefix
  apply deleteRemovableBlocks_prefix
  apply pairedSegmentList_prefix
  exact Nat.div_le_div_right (Nat.sub_le_sub_right hnN 1)

lemma shifted_orientedExternalLocalTime_zero (omega : StepPath) (x : Point) :
    orientedExternalLocalTime .shifted (trajectory omega) 0 x = 0 := by
  simp [orientedExternalLocalTime, orientedExternalPath, shiftedExternalPath,
    shiftedInput, finitePathList, pathPrefix, listLocalTime, externalPath]

/-- At a compatible endpoint site, oriented deleted local time is monotone
in the ordinary-time prefix.  Incomplete final directions are on the
opposite checkerboard class and therefore do not affect this statement. -/
theorem orientedExternalLocalTime_mono_of_orientationClass
    (o : Orientation) (omega : StepPath) {n N : ℕ} (hnN : n ≤ N)
    (x : Point) (hx : orientationClass o x) :
    orientedExternalLocalTime o (trajectory omega) n x ≤
      orientedExternalLocalTime o (trajectory omega) N x := by
  cases o with
  | even =>
      unfold orientedExternalLocalTime
      calc
        listLocalTime
            (orientedExternalPath .even (pathPrefix (trajectory omega) n)) x =
          listLocalTime
            ((orientedExternalPath .even
              (pathPrefix (trajectory omega) n)).filter
                (orientationClass .even)) x :=
          (listLocalTime_filter_orientationClass .even _ hx).symm
        _ ≤ listLocalTime
            ((orientedExternalPath .even
              (pathPrefix (trajectory omega) N)).filter
                (orientationClass .even)) x := by
          exact (filtered_orientedExternalPath_even_prefix omega hnN).count_le x
        _ = listLocalTime
            (orientedExternalPath .even (pathPrefix (trajectory omega) N)) x :=
          listLocalTime_filter_orientationClass .even _ hx
  | shifted =>
      by_cases hn : n = 0
      · subst n
        rw [shifted_orientedExternalLocalTime_zero]
        exact Nat.zero_le _
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        unfold orientedExternalLocalTime
        calc
          listLocalTime
              (orientedExternalPath .shifted (pathPrefix (trajectory omega) n)) x =
            listLocalTime
              ((orientedExternalPath .shifted
                (pathPrefix (trajectory omega) n)).filter
                  (orientationClass .shifted)) x :=
            (listLocalTime_filter_orientationClass .shifted _ hx).symm
          _ ≤ listLocalTime
              ((orientedExternalPath .shifted
                (pathPrefix (trajectory omega) N)).filter
                  (orientationClass .shifted)) x := by
            exact (filtered_orientedExternalPath_shifted_prefix
              omega hnpos hnN).count_le x
          _ = listLocalTime
              (orientedExternalPath .shifted (pathPrefix (trajectory omega) N)) x :=
            listLocalTime_filter_orientationClass .shifted _ hx

/-- The stopped external large event, evaluated at a path-dependent ordinary
time `tau`. -/
def stoppedOrientedLargeEvent (o : Orientation)
    (tau : WalkPath → ℕ) (threshold : ℕ) (x : Point) : Set WalkPath :=
  {s | threshold ≤ orientedExternalLocalTime o s (tau s) x}

/-- On canonical increment paths, a stopped candidate using the deterministic
cap range is contained in the corresponding fixed-cap candidate event. -/
lemma trajectory_candidateEvent_stopped_subset_fixed (o : Orientation)
    (tau : WalkPath → ℕ) (cap threshold : ℕ)
    (htau : ∀ s, tau s ≤ cap) (x : Point) :
    trajectory ⁻¹'
        candidateEvent (fun s ↦ orientedExternalVisitedSites o s cap)
          (stoppedOrientedLargeEvent o tau threshold) x ⊆
      trajectory ⁻¹'
        candidateEvent (fun s ↦ orientedExternalVisitedSites o s cap)
          (orientedLargeEvent o cap threshold) x := by
  rintro omega ⟨hmember, hlarge⟩
  refine ⟨hmember, ?_⟩
  have hx : orientationClass o x := by
    change x ∈ orientedExternalVisitedSites o (trajectory omega) cap at hmember
    unfold orientedExternalVisitedSites at hmember
    exact (Finset.mem_filter.mp hmember).2
  change threshold ≤ orientedExternalLocalTime o (trajectory omega) cap x
  exact hlarge.trans (orientedExternalLocalTime_mono_of_orientationClass
    o omega (htau (trajectory omega)) x hx)

/-- Direct dynamic-screen `hweightedOneSite` input: the visited set is the
deterministic-cap oriented range, while the large event may use any measurable
path-dependent time bounded by that cap. -/
theorem simpleRandomWalk_stoppedLarge_weighted_oneSite
    (o : Orientation) (tau : WalkPath → ℕ) (cap threshold : ℕ)
    (q : ℝ≥0∞) (hcap : 0 < cap) (htau : ∀ s, tau s ≤ cap)
    (hlarge : ∀ x, MeasurableSet (stoppedOrientedLargeEvent o tau threshold x))
    (hone : externalBlocks o {eta |
      threshold ≤ externalOriginLocalTime o eta cap} ≤ q) (x : Point) :
    simpleRandomWalk
        (candidateEvent (fun s ↦ orientedExternalVisitedSites o s cap)
          (stoppedOrientedLargeEvent o tau threshold) x) ≤
      q * simpleRandomWalk
        (memberEvent (fun s ↦ orientedExternalVisitedSites o s cap) x) := by
  let stoppedCandidate :=
    candidateEvent (fun s ↦ orientedExternalVisitedSites o s cap)
      (stoppedOrientedLargeEvent o tau threshold) x
  let fixedCandidate :=
    candidateEvent (fun s ↦ orientedExternalVisitedSites o s cap)
      (orientedLargeEvent o cap threshold) x
  have hstoppedMeas : MeasurableSet stoppedCandidate :=
    (measurableSet_member_orientedExternalVisitedSites o cap x).inter (hlarge x)
  have hfixedMeas : MeasurableSet fixedCandidate :=
    measurableSet_candidate_orientedExternalVisitedSites o cap threshold x
  have hfixed : simpleRandomWalk fixedCandidate ≤
      q * simpleRandomWalk
        (memberEvent (fun s ↦ orientedExternalVisitedSites o s cap) x) := by
    cases o with
    | even =>
        exact simpleRandomWalk_even_weighted_oneSite cap cap threshold q
          (Nat.div_le_self _ _) hone x
    | shifted =>
        apply simpleRandomWalk_shifted_weighted_oneSite cap cap threshold
          hcap q
        · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
        · exact hone
  calc
    simpleRandomWalk stoppedCandidate =
        fairSteps (trajectory ⁻¹' stoppedCandidate) := by
      rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hstoppedMeas]
    _ ≤ fairSteps (trajectory ⁻¹' fixedCandidate) := by
      apply measure_mono
      exact trajectory_candidateEvent_stopped_subset_fixed
        o tau cap threshold htau x
    _ = simpleRandomWalk fixedCandidate := by
      rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hfixedMeas]
    _ ≤ q * simpleRandomWalk
        (memberEvent (fun s ↦ orientedExternalVisitedSites o s cap) x) := hfixed

/-- HLOZ-parameter form for stopped clocks.  The stopped threshold may be
larger than the one-point level; no new tail estimate is assumed. -/
theorem eventually_simpleRandomWalk_hloz_stoppedLarge_weightedOneSite44
    (o : Orientation) :
    ∀ᶠ m : ℕ in atTop, ∀ (tau : WalkPath → ℕ) (threshold : ℕ),
      hlozOnePointLevel44 m ≤ threshold →
      (∀ s, tau s ≤ hlozCutoff44 m) →
      (∀ x, MeasurableSet (stoppedOrientedLargeEvent o tau threshold x)) →
      ∀ x : Point,
        simpleRandomWalk
            (candidateEvent
              (fun s ↦ orientedExternalVisitedSites o s (hlozCutoff44 m))
              (stoppedOrientedLargeEvent o tau threshold) x) ≤
          hlozOnePointRate44 m * simpleRandomWalk
            (memberEvent
              (fun s ↦ orientedExternalVisitedSites o s (hlozCutoff44 m)) x) := by
  filter_upwards [hlozSharpExternalOnePointTail44 o] with m hone
  intro tau threshold hthreshold htau hlarge x
  have htail : externalBlocks o {eta |
      threshold ≤ externalOriginLocalTime o eta (hlozCutoff44 m)} ≤
      hlozOnePointRate44 m :=
    (measure_mono fun eta heta ↦ hthreshold.trans heta).trans hone
  exact simpleRandomWalk_stoppedLarge_weighted_oneSite o tau
    (hlozCutoff44 m) threshold (hlozOnePointRate44 m)
    (levelCutoffTime_pos hlozDelta44 m) htau hlarge htail x

end

end Erdos1165.ExternalStoppedWeightedOnePoint
