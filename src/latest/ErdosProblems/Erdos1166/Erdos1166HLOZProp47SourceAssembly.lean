import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceObjects

/-!
The source-shaped deterministic and probabilistic assembly of HLOZ
Proposition 4.7.  No exceptional event in this file is defined as the
complement of the desired final cover: every component records a concrete
failure appearing in the source proof.
-/

namespace Erdos1166.HLOZProp47SourceAssembly

open Filter MeasureTheory Set
open HLOZFoundation HLOZDecomposition HLOZPairing HLOZScreeningAssembly
open HLOZPairing.ScreeningBridge
open HLOZProp47Parameters HLOZProp47SourceObjects

abbrev StageIndex := Fin 3

def stageNumber (r : StageIndex) : ℕ := r.1 + 1

/-- Select the mesh exponent used at one of the three successive gaps. -/
def tripleAlphaIndex (a : AlphaTriple) (r : StageIndex) : AlphaIndex :=
  match r.1 with
  | 0 => a.1
  | 1 => a.2.1
  | _ => a.2.2

@[simp] theorem tripleAlphaIndex_zero (a : AlphaTriple) :
    tripleAlphaIndex a 0 = a.1 := rfl

@[simp] theorem tripleAlphaIndex_one (a : AlphaTriple) :
    tripleAlphaIndex a 1 = a.2.1 := rfl

@[simp] theorem tripleAlphaIndex_two (a : AlphaTriple) :
    tripleAlphaIndex a 2 = a.2.2 := rfl

/-- The source history `M_m^k ∩ Π_{m,i}^k`: the first `k` level-`m`
creation sites occur before level `m+1`, and their first `k` creation
sites are free in the selected domino tiling. -/
noncomputable def prefixPairingEvent
    (m : ℕ) (i : Fin 6) (k : ℕ) : Set (ℕ → Site) :=
  hlozThresholdTimeEventK m k ∩
    {s | PairFree (pairingRelation i) (levelCreationSitesUpTo s m k)}

theorem measurable_levelCreationSitesUpTo (m k : ℕ) :
    Measurable fun s : ℕ → Site ↦ levelCreationSitesUpTo s m k := by
  rw [measurable_finset_iff]
  intro x
  simp only [levelCreationSitesUpTo, Finset.mem_image]
  apply Measurable.exists
  intro j
  exact measurable_const.and
    (measurableSet_setOfPred.mp
      (measurableSet_eq_fun (measurable_levelCreationSite m j) measurable_const))

theorem measurableSet_prefixPairingEvent (m : ℕ) (i : Fin 6) (k : ℕ) :
    MeasurableSet (prefixPairingEvent m i k) := by
  apply (measurableSet_lt
    (isStoppingTime_firstKSitesReachLevel m k).measurable'
    (isStoppingTime_firstKSitesReachLevel (m + 1) 1).measurable').inter
  exact measurableSet_setOfPred.mpr
    ((measurable_of_countable fun A : Finset Site ↦
      PairFree (pairingRelation i) A).comp
        (measurable_levelCreationSitesUpTo m k))

theorem prefixPairingEvent_four (m : ℕ) (i : Fin 6) :
    prefixPairingEvent m i 4 = firstFourPairingEvent m i := by
  rw [prefixPairingEvent, firstFourPairingEvent,
    hlozThresholdTimeEventK_four, hlozThresholdTimeEvent_eq]

private theorem pairFree_mono {r : Site → Site → Prop} {A B : Finset Site}
    (hAB : A ⊆ B) (hB : PairFree r B) : PairFree r A := by
  intro x hx y hy hxy
  exact hB x (hAB hx) y (hAB hy) hxy

private theorem levelCreationSitesUpTo_mono
    (s : ℕ → Site) (m : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    levelCreationSitesUpTo s m k ⊆ levelCreationSitesUpTo s m l := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
    (Finset.mem_Icc.mp hj).2.trans hkl⟩, rfl⟩

/-- A longer free creation-site history contains every shorter one.  This
is the stopped-history monotonicity used when Equation (4.47) forgets the
extra `(k+1)`-st creation required by the surrounding Proposition-4.7
failure and restarts instead at `T_m^k`, as in the source proof. -/
theorem prefixPairingEvent_mono
    (m : ℕ) (i : Fin 6) {k l : ℕ} (hkl : k ≤ l) :
    prefixPairingEvent m i l ⊆ prefixPairingEvent m i k := by
  intro s hs
  refine ⟨(firstKSitesReachLevel_mono_k s m hkl).trans_lt hs.1, ?_⟩
  exact pairFree_mono (levelCreationSitesUpTo_mono s m hkl) hs.2

private theorem firstFour_mem_prefixPairingEvent
    {s : ℕ → Site} {m : ℕ} {i : Fin 6} (hs : s ∈ firstFourPairingEvent m i)
    {k : ℕ} (hk : k ≤ 4) : s ∈ prefixPairingEvent m i k := by
  refine ⟨?_, pairFree_mono (levelCreationSitesUpTo_mono s m hk) hs.2⟩
  have hfour : s ∈ hlozThresholdTimeEventK m 4 := by
    rw [hlozThresholdTimeEventK_four, hlozThresholdTimeEvent_eq]
    exact hs.1
  exact (firstKSitesReachLevel_mono_k s m hk).trans_lt hfour

/-- The source event for one selected gap.  Below `κ₂` this is the
near-favourite screen from (4.37); above `κ₂` it is the direct
avoidance/distance event from (4.36).  Profiles are indexed by the chosen
tiling, so transporting the `e₁/X₁` decomposition to the other five tilings
is an explicit input rather than an implicit symmetry assumption. -/
noncomputable def prop47StageEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (i : Fin 6) (m : ℕ) (r : StageIndex) (alpha : ℝ) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    if alpha ≤ kappaTwo then
      lowScaleStageEvent (profiles i) (cStar i) i m (stageNumber r) alpha
    else
      hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
        distanceBinEvent m (stageNumber r) alpha

theorem measurableSet_prop47StageEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (i : Fin 6) (m : ℕ) (r : StageIndex) (alpha : ℝ) :
    MeasurableSet (prop47StageEvent profiles cStar i m r alpha) := by
  rw [prop47StageEvent]
  apply (measurableSet_prefixPairingEvent m i (stageNumber r + 1)).inter
  split_ifs
  · exact measurableSet_lowScaleStageEvent
      (profiles i) (cStar i) i m (stageNumber r) alpha
  · exact (measurableSet_hlozDirectAvoidanceEvent m (stageNumber r + 1)).inter
      (measurableSet_distanceBinEvent m (stageNumber r) alpha)

/-- The first `n` selected distance screens, for a fixed exponent triple. -/
noncomputable def prop47History
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) : ℕ → Set (ℕ → Site) :=
  screeningHistory (prefixPairingEvent m i 1) fun n ↦
    if h : n < 3 then
      prop47StageEvent profiles cStar i m ⟨n, h⟩
        (alphaValue (tripleAlphaIndex a ⟨n, h⟩))
    else univ

@[simp] theorem prop47History_zero
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) :
    prop47History profiles cStar m i a 0 = prefixPairingEvent m i 1 := rfl

theorem measurableSet_prop47History
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (n : ℕ) :
    MeasurableSet (prop47History profiles cStar m i a n) := by
  induction n with
  | zero => exact measurableSet_prefixPairingEvent m i 1
  | succ n ih =>
      rw [prop47History, screeningHistory_succ]
      apply ih.inter
      by_cases hn : n < 3
      · simp only [hn, dite_true]
        exact measurableSet_prop47StageEvent profiles cStar i m ⟨n, hn⟩
          (alphaValue (tripleAlphaIndex a ⟨n, hn⟩))
      · simp [hn]

/-! Concrete exceptional events. -/

/-- The large-distance alternative separated before the mesh union. -/
def farGapEvent (m : ℕ) (i : Fin 6) (r : StageIndex) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    {s | Real.exp m < siteDistance
      (levelCreationSite s m (stageNumber r))
      (levelCreationSite s m (stageNumber r + 1))}

theorem measurableSet_farGapEvent (m : ℕ) (i : Fin 6) (r : StageIndex) :
    MeasurableSet (farGapEvent m i r) := by
  apply (measurableSet_prefixPairingEvent m i (stageNumber r + 1)).inter
  apply measurableSet_setOfPred.mpr
  have hp : Measurable fun s : ℕ → Site ↦
      (levelCreationSite s m (stageNumber r),
        levelCreationSite s m (stageNumber r + 1)) :=
    (measurable_levelCreationSite m (stageNumber r)).prodMk
      (measurable_levelCreationSite m (stageNumber r + 1))
  have hsq : Measurable fun s : ℕ → Site ↦
      siteSquaredDistance (levelCreationSite s m (stageNumber r))
        (levelCreationSite s m (stageNumber r + 1)) :=
    (measurable_of_countable fun p : Site × Site ↦
      siteSquaredDistance p.1 p.2).comp hp
  have hd : Measurable fun s : ℕ → Site ↦
      siteDistance (levelCreationSite s m (stageNumber r))
        (levelCreationSite s m (stageNumber r + 1)) :=
    (measurable_of_countable fun n : ℕ ↦ Real.sqrt n).comp hsq
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const hd)

/-- The explicit failures of the three good factors in the low-scale side
of (4.37): next-site candidate membership, empty `Theta`, and the
near-favourite cardinality bound. -/
def lowStageFailureEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha ∩
    ((nextCreationIsCandidateEvent i m (stageNumber r) (alpha + delta))ᶜ ∪
      stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r) ∪
      {s | Real.log m ^ 2 <
        ((nearFavoriteSites i s m (stageNumber r) kappaOne).card : ℝ)})

/-- Lemma 4.10 failure: the next creation site misses the screened
near-favourite candidate set. -/
def lemma410FailureEvent
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha ∩
    (nextCreationIsCandidateEvent i m (stageNumber r) (alpha + delta))ᶜ

/-- Proposition 4.5 failure at the stopped history: one of the two
external/lazy profile comparisons is violated. -/
def prop45FailureEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha ∩
    stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r)

/-- Lemmas 4.11--4.12 failure: the screened near-favourite candidate
set exceeds the logarithmic-square bound used by Proposition 4.9. -/
def lemma411412FailureEvent
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) : Set (ℕ → Site) :=
  prefixPairingEvent m i (stageNumber r + 1) ∩
    hlozDirectAvoidanceEvent m (stageNumber r + 1) ∩
    distanceBinEvent m (stageNumber r) alpha ∩
    {s | Real.log m ^ 2 <
      ((nearFavoriteSites i s m (stageNumber r) kappaOne).card : ℝ)}

theorem lowStageFailureEvent_eq_source_failures
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    lowStageFailureEvent profiles cStar m i r alpha =
      lemma410FailureEvent m i r alpha ∪
      prop45FailureEvent profiles cStar m i r alpha ∪
      lemma411412FailureEvent m i r alpha := by
  ext s
  simp only [lowStageFailureEvent, lemma410FailureEvent, prop45FailureEvent,
    lemma411412FailureEvent, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  aesop

theorem measurableSet_lowStageFailureEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (r : StageIndex) (alpha : ℝ) :
    MeasurableSet (lowStageFailureEvent profiles cStar m i r alpha) := by
  apply (((measurableSet_prefixPairingEvent m i (stageNumber r + 1)).inter
    (measurableSet_hlozDirectAvoidanceEvent m (stageNumber r + 1))).inter
    (measurableSet_distanceBinEvent m (stageNumber r) alpha)).inter
  apply ((measurableSet_nextCreationIsCandidateEvent
    i m (stageNumber r) (alpha + delta)).compl.union
      (measurableSet_stoppedThetaEvent (profiles i) (cStar i) m (stageNumber r))).union
  exact measurableSet_setOfPred.mpr
    ((measurable_of_countable fun A : Finset Site ↦
      Real.log m ^ 2 < (A.card : ℝ)).comp
        (measurable_nearFavoriteSites i m (stageNumber r) kappaOne))

/-- The complete but non-tautological exceptional event used by the source
cover: a far gap, or one of the three named low-scale screening failures. -/
noncomputable def prop47ExceptionalEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) : Set (ℕ → Site) :=
  (⋃ r : StageIndex, farGapEvent m i r) ∪
    ⋃ r : StageIndex, ⋃ a : AlphaIndex,
      if alphaValue a ≤ kappaTwo then
        lowStageFailureEvent profiles cStar m i r (alphaValue a)
      else ∅

theorem measurableSet_prop47ExceptionalEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) :
    MeasurableSet (prop47ExceptionalEvent profiles cStar m i) := by
  apply (MeasurableSet.iUnion fun r ↦ measurableSet_farGapEvent m i r).union
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro a
  split_ifs
  · exact measurableSet_lowStageFailureEvent profiles cStar m i r (alphaValue a)
  · exact MeasurableSet.empty

private theorem threshold_finite_of_firstFour
    {s : ℕ → Site} {m : ℕ} {i : Fin 6}
    (hs : s ∈ firstFourPairingEvent m i) {k : ℕ} (hk : k ≤ 4) :
    firstKSitesReachLevel m k s ≠ ⊤ := by
  have hthreshold : s ∈ hlozThresholdTimeEvent m := by
    rw [hlozThresholdTimeEvent_eq]
    exact hs.1
  have hfour : firstKSitesReachLevel m 4 s ≠ ⊤ := ne_top_of_lt hthreshold
  intro hkTop
  have hle := firstKSitesReachLevel_mono_k s m hk
  rw [hkTop] at hle
  exact hfour (top_unique hle)

private theorem levelCreationSite_ne_next_of_firstFour
    {s : ℕ → Site} {m : ℕ} {i : Fin 6}
    (hs : s ∈ firstFourPairingEvent m i) {k : ℕ}
    (hk : 1 ≤ k) (hnext : k + 1 ≤ 4) :
    levelCreationSite s m k ≠ levelCreationSite s m (k + 1) := by
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    have hfirst : s ∈ hlozFourSitesReachLevelFirst 0 := hs.1
    rw [hlozFourSitesReachLevelFirst_zero_empty] at hfirst
    exact hfirst.elim
  exact levelCreationSite_ne_of_lt s m hm (by omega) (by omega)
    (threshold_finite_of_firstFour hs hnext)

private theorem mem_exceptional_of_far
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {s : ℕ → Site} {m : ℕ} {i : Fin 6} {r : StageIndex}
    (hfar : s ∈ farGapEvent m i r) :
    s ∈ prop47ExceptionalEvent profiles cStar m i := by
  apply Or.inl
  exact Set.mem_iUnion_of_mem r hfar

private theorem mem_exceptional_of_lowFailure
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {s : ℕ → Site} {m : ℕ} {i : Fin 6} {r : StageIndex}
    {a : AlphaIndex} (ha : alphaValue a ≤ kappaTwo)
    (hfail : s ∈ lowStageFailureEvent profiles cStar m i r (alphaValue a)) :
    s ∈ prop47ExceptionalEvent profiles cStar m i := by
  apply Or.inr
  apply Set.mem_iUnion_of_mem r
  apply Set.mem_iUnion_of_mem a
  simp [ha, hfail]

private theorem stage_or_exceptional
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {s : ℕ → Site} {m : ℕ} {i : Fin 6} (hs : s ∈ firstFourPairingEvent m i)
    (r : StageIndex) (a : AlphaIndex)
    (havoid : s ∈ hlozDirectAvoidanceEvent m (stageNumber r + 1))
    (hbin : s ∈ distanceBinEvent m (stageNumber r) (alphaValue a)) :
    s ∈ prop47StageEvent profiles cStar i m r (alphaValue a) ∨
      s ∈ prop47ExceptionalEvent profiles cStar m i := by
  have hprefix : s ∈ prefixPairingEvent m i (stageNumber r + 1) :=
    firstFour_mem_prefixPairingEvent hs (by
      simp only [stageNumber]
      omega)
  by_cases ha : alphaValue a ≤ kappaTwo
  · by_cases hcand : s ∈
        nextCreationIsCandidateEvent i m (stageNumber r) (alphaValue a + delta)
    · by_cases htheta : s ∈ stoppedThetaEvent
          (profiles i) (cStar i) m (stageNumber r)
      · apply Or.inr
        apply mem_exceptional_of_lowFailure profiles cStar ha
        exact ⟨⟨⟨hprefix, havoid⟩, hbin⟩, Or.inl (Or.inr htheta)⟩
      · by_cases hcard : Real.log m ^ 2 <
            ((nearFavoriteSites i s m (stageNumber r) kappaOne).card : ℝ)
        · apply Or.inr
          apply mem_exceptional_of_lowFailure profiles cStar ha
          exact ⟨⟨⟨hprefix, havoid⟩, hbin⟩, Or.inr hcard⟩
        · apply Or.inl
          rw [prop47StageEvent, if_pos ha]
          refine ⟨hprefix, ⟨⟨⟨⟨havoid, hbin⟩, hcand⟩, ?_⟩,
            le_of_not_gt hcard⟩⟩
          exact Finset.not_nonempty_iff_eq_empty.mp htheta
    · apply Or.inr
      apply mem_exceptional_of_lowFailure profiles cStar ha
      exact ⟨⟨⟨hprefix, havoid⟩, hbin⟩, Or.inl (Or.inl hcand)⟩
  · apply Or.inl
    rw [prop47StageEvent, if_neg ha]
    exact ⟨hprefix, havoid, hbin⟩

/-- Deterministic source cover of the exact first-four pairing event by the
explicit exceptional event and the full `960^3` final histories. -/
theorem firstFourPairingEvent_subset_exceptional_union_histories
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) :
    firstFourPairingEvent m i ⊆
      prop47ExceptionalEvent profiles cStar m i ∪
        ⋃ a ∈ screeningTripleGrid, prop47History profiles cStar m i a 3 := by
  intro s hs
  have havoid (r : StageIndex) :
      s ∈ hlozDirectAvoidanceEvent m (stageNumber r + 1) := by
    apply hlozThresholdTimeEventK_imp_directAvoidance s m 4
    · by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      have hfirst : s ∈ hlozFourSitesReachLevelFirst 0 := hs.1
      rw [hlozFourSitesReachLevelFirst_zero_empty] at hfirst
      exact hfirst.elim
    · simp [stageNumber]
    · have : stageNumber r ≤ 3 := by
        simp only [stageNumber]
        omega
      omega
    · simpa [hlozThresholdTimeEventK_four] using
        (show s ∈ hlozThresholdTimeEvent m by
          rw [hlozThresholdTimeEvent_eq]
          exact hs.1)
  have chooseBin (r : StageIndex) :
      s ∈ farGapEvent m i r ∨
        ∃ a : AlphaIndex,
          s ∈ distanceBinEvent m (stageNumber r) (alphaValue a) := by
    by_cases hfar : Real.exp m < siteDistance
        (levelCreationSite s m (stageNumber r))
        (levelCreationSite s m (stageNumber r + 1))
    · exact Or.inl ⟨firstFour_mem_prefixPairingEvent hs (by
        simp only [stageNumber]
        omega), hfar⟩
    · apply Or.inr
      apply distanceBinEvent_fullGrid_cover
      · exact threshold_finite_of_firstFour hs (by
          simp only [stageNumber]
          omega)
      · exact threshold_finite_of_firstFour hs (by
          simp only [stageNumber]
          omega)
      · exact levelCreationSite_ne_next_of_firstFour hs (by
          simp only [stageNumber]
          omega) (by simp only [stageNumber]; omega)
      · exact le_of_not_gt hfar
  rcases chooseBin 0 with hfar | ⟨a₀, ha₀⟩
  · exact Or.inl (mem_exceptional_of_far profiles cStar hfar)
  rcases chooseBin 1 with hfar | ⟨a₁, ha₁⟩
  · exact Or.inl (mem_exceptional_of_far profiles cStar hfar)
  rcases chooseBin 2 with hfar | ⟨a₂, ha₂⟩
  · exact Or.inl (mem_exceptional_of_far profiles cStar hfar)
  rcases stage_or_exceptional profiles cStar hs 0 a₀ (havoid 0) ha₀ with h₀ | hbad
  · rcases stage_or_exceptional profiles cStar hs 1 a₁ (havoid 1) ha₁ with h₁ | hbad
    · rcases stage_or_exceptional profiles cStar hs 2 a₂ (havoid 2) ha₂ with h₂ | hbad
      · apply Or.inr
        let a : AlphaTriple := (a₀, a₁, a₂)
        apply Set.mem_iUnion_of_mem a
        apply Set.mem_iUnion_of_mem (by simp [screeningTripleGrid])
        change s ∈ ((prefixPairingEvent m i 1 ∩
          prop47StageEvent profiles cStar i m 0 (alphaValue a₀)) ∩
          prop47StageEvent profiles cStar i m 1 (alphaValue a₁)) ∩
          prop47StageEvent profiles cStar i m 2 (alphaValue a₂)
        exact ⟨⟨⟨firstFour_mem_prefixPairingEvent hs (by omega), h₀⟩, h₁⟩, h₂⟩
      · exact Or.inl hbad
    · exact Or.inl hbad
  · exact Or.inl hbad

/-- The last recursive history really is a subevent of
`M_m^4 ∩ Π_{m,i}^4`; the earlier histories only contain the corresponding
one-, two-, and three-site prefixes. -/
theorem prop47History_three_subset_firstFour
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) :
    prop47History profiles cStar m i a 3 ⊆ firstFourPairingEvent m i := by
  intro s hs
  change s ∈ (((prefixPairingEvent m i 1 ∩
    prop47StageEvent profiles cStar i m 0 (alphaValue a.1)) ∩
    prop47StageEvent profiles cStar i m 1 (alphaValue a.2.1)) ∩
    prop47StageEvent profiles cStar i m 2 (alphaValue a.2.2)) at hs
  have hprefix : s ∈ prefixPairingEvent m i 4 := hs.2.1
  rwa [prefixPairingEvent_four] at hprefix

/-! The only remaining inputs are the source probability estimates. -/

/-- The finite prefactor produced when the three gaps and all 960 mesh
values are union-bounded. -/
def prop47FailurePrefactor
    (farCoeff lemma410Coeff prop45Coeff lemma411412Coeff : ℕ) : ℕ :=
  3 * farCoeff + 3 * 960 *
    (lemma410Coeff + prop45Coeff + lemma411412Coeff)

/-- Assemble the four source exceptional estimates at one fixed level.
No independence is used here, only the finite union bound. -/
theorem prop47ExceptionalEvent_measure_le_of_source_failures
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6)
    (farCoeff lemma410Coeff prop45Coeff lemma411412Coeff : ℕ)
    (hFar : ∀ r : StageIndex,
      simpleRandomWalkLaw (farGapEvent m i r) ≤
        sourceExceptionalRateWithPrefactor m farCoeff kappa)
    (hLemma410 : ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw (lemma410FailureEvent m i r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m lemma410Coeff kappa)
    (hProp45 : ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent profiles cStar m i r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m prop45Coeff kappa)
    (hLemma411412 : ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma411412FailureEvent m i r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m lemma411412Coeff kappa) :
    simpleRandomWalkLaw (prop47ExceptionalEvent profiles cStar m i) ≤
      sourceExceptionalRateWithPrefactor m
        (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
          lemma411412Coeff) kappa := by
  have hLowFailure (r : StageIndex) (a : AlphaIndex) :
      simpleRandomWalkLaw
          (if alphaValue a ≤ kappaTwo then
            lowStageFailureEvent profiles cStar m i r (alphaValue a)
          else ∅) ≤
        sourceExceptionalRateWithPrefactor m
          (lemma410Coeff + prop45Coeff + lemma411412Coeff) kappa := by
    by_cases ha : alphaValue a ≤ kappaTwo
    · rw [if_pos ha, lowStageFailureEvent_eq_source_failures]
      calc
        simpleRandomWalkLaw
            (lemma410FailureEvent m i r (alphaValue a) ∪
              prop45FailureEvent profiles cStar m i r (alphaValue a) ∪
              lemma411412FailureEvent m i r (alphaValue a)) ≤
            (simpleRandomWalkLaw (lemma410FailureEvent m i r (alphaValue a)) +
              simpleRandomWalkLaw
                (prop45FailureEvent profiles cStar m i r (alphaValue a))) +
              simpleRandomWalkLaw
                (lemma411412FailureEvent m i r (alphaValue a)) := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
        _ ≤ sourceExceptionalRateWithPrefactor m lemma410Coeff kappa +
              sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
              sourceExceptionalRateWithPrefactor m lemma411412Coeff kappa := by
          gcongr
          · exact hLemma410 r a ha
          · exact hProp45 r a ha
          · exact hLemma411412 r a ha
        _ = sourceExceptionalRateWithPrefactor m
              (lemma410Coeff + prop45Coeff + lemma411412Coeff) kappa := by
          simp only [sourceExceptionalRateWithPrefactor]
          push_cast
          ring
    · rw [if_neg ha, measure_empty]
      exact bot_le
  rw [prop47ExceptionalEvent]
  calc
    simpleRandomWalkLaw
        ((⋃ r : StageIndex, farGapEvent m i r) ∪
          ⋃ r : StageIndex, ⋃ a : AlphaIndex,
            if alphaValue a ≤ kappaTwo then
              lowStageFailureEvent profiles cStar m i r (alphaValue a)
            else ∅) ≤
        simpleRandomWalkLaw (⋃ r : StageIndex, farGapEvent m i r) +
          simpleRandomWalkLaw (⋃ r : StageIndex, ⋃ a : AlphaIndex,
            if alphaValue a ≤ kappaTwo then
              lowStageFailureEvent profiles cStar m i r (alphaValue a)
            else ∅) := measure_union_le _ _
    _ ≤ (∑ r : StageIndex, simpleRandomWalkLaw (farGapEvent m i r)) +
          ∑ r : StageIndex, ∑ a : AlphaIndex,
            simpleRandomWalkLaw
              (if alphaValue a ≤ kappaTwo then
                lowStageFailureEvent profiles cStar m i r (alphaValue a)
              else ∅) := by
      gcongr
      · exact measure_iUnion_fintype_le _ _
      · exact (measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun r _ ↦ measure_iUnion_fintype_le _ _)
    _ ≤ (∑ _r : StageIndex,
            sourceExceptionalRateWithPrefactor m farCoeff kappa) +
          ∑ _r : StageIndex, ∑ _a : AlphaIndex,
            sourceExceptionalRateWithPrefactor m
              (lemma410Coeff + prop45Coeff + lemma411412Coeff) kappa := by
      exact add_le_add
        (Finset.sum_le_sum fun r _ ↦ hFar r)
        (Finset.sum_le_sum fun r _ ↦
          Finset.sum_le_sum fun a _ ↦ hLowFailure r a)
    _ = sourceExceptionalRateWithPrefactor m
          (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
            lemma411412Coeff) kappa := by
      simp only [sourceExceptionalRateWithPrefactor, prop47FailurePrefactor,
        StageIndex, AlphaIndex, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      push_cast
      ring

/-- The eventual probability estimate for the explicit union of the
large-gap and low-scale screening failures.  Its individual summands are
the estimates supplied by Proposition 4.5 and Lemmas 4.10--4.12. -/
def Prop47ExceptionalEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (errorCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6,
    simpleRandomWalkLaw (prop47ExceptionalEvent profiles cStar m i) ≤
      sourceExceptionalRateWithPrefactor m errorCoeff kappa

/-- Eventual large-gap estimate used before the distance mesh
decomposition. -/
def Prop47FarGapEstimate (farCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    simpleRandomWalkLaw (farGapEvent m i r) ≤
      sourceExceptionalRateWithPrefactor m farCoeff kappa

/-- Eventual Lemma 4.10 estimate for missing the low-scale candidate
screen. -/
def Prop47Lemma410Estimate (lemma410Coeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw (lemma410FailureEvent m i r (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m lemma410Coeff kappa

/-- Eventual Proposition 4.5 estimate for stopped profile imbalance. -/
def Prop47Prop45Estimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (prop45Coeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw
        (prop45FailureEvent profiles cStar m i r (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m prop45Coeff kappa

/-- Eventual Lemmas 4.11--4.12 estimate for the logarithmic-square
candidate-cardinality screen. -/
def Prop47Lemma411412Estimate (lemma411412Coeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw
        (lemma411412FailureEvent m i r (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m lemma411412Coeff kappa

/-- The conditional low-distance estimate in the `α ≤ κ₂` branch of
(4.37), after the candidate and `Theta` screens. -/
def Prop47LowStageEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff errorCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    StageBound simpleRandomWalkLaw (sourceStageRate m stageCoeff kappa)
      (sourceExceptionalRateWithPrefactor m errorCoeff kappa)
      (prop47History profiles cStar m i a r.1)
      (prop47History profiles cStar m i a (r.1 + 1))

/-- The direct high-distance conditional estimate in the `α > κ₂`
branch of (4.36). -/
def Prop47HighStageEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff errorCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    kappaTwo < alphaValue (tripleAlphaIndex a r) →
    StageBound simpleRandomWalkLaw (sourceStageRate m stageCoeff kappa)
      (sourceExceptionalRateWithPrefactor m errorCoeff kappa)
      (prop47History profiles cStar m i a r.1)
      (prop47History profiles cStar m i a (r.1 + 1))

/-- Enlarging the natural stage prefactor only weakens a low-stage bound.
This lets the final assembly choose one common prefactor for independently
proved low- and high-distance estimates. -/
theorem prop47LowStageEstimate_mono_stageCoeff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {stageCoeff stageCoeff' errorCoeff : ℕ}
    (hcoeff : stageCoeff ≤ stageCoeff')
    (h : Prop47LowStageEstimate profiles cStar stageCoeff errorCoeff) :
    Prop47LowStageEstimate profiles cStar stageCoeff' errorCoeff := by
  filter_upwards [h] with m hm
  intro i a r halpha
  have hs := hm i a r halpha
  refine ⟨hs.nested, hs.measure_le.trans ?_⟩
  gcongr
  unfold HLOZPairing.ScreeningBridge.sourceStageRate
  gcongr

/-- The analogous monotonicity statement for the high-distance stage. -/
theorem prop47HighStageEstimate_mono_stageCoeff
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    {stageCoeff stageCoeff' errorCoeff : ℕ}
    (hcoeff : stageCoeff ≤ stageCoeff')
    (h : Prop47HighStageEstimate profiles cStar stageCoeff errorCoeff) :
    Prop47HighStageEstimate profiles cStar stageCoeff' errorCoeff := by
  filter_upwards [h] with m hm
  intro i a r halpha
  have hs := hm i a r halpha
  refine ⟨hs.nested, hs.measure_le.trans ?_⟩
  gcongr
  unfold HLOZPairing.ScreeningBridge.sourceStageRate
  gcongr

set_option linter.constructorNameAsVariable false in
/-- Proposition 4.7 closes from the explicit exceptional-event estimate and
the low/high conditional estimates supplied respectively by
Propositions 4.5, 4.8, 4.9 and Lemmas 4.10--4.12. -/
theorem hlozPlanarConclusion_of_prop47_source_estimates
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff errorCoeff : ℕ)
    (hExceptional : Prop47ExceptionalEstimate profiles cStar errorCoeff)
    (hLow : Prop47LowStageEstimate profiles cStar stageCoeff errorCoeff)
    (hHigh : Prop47HighStageEstimate profiles cStar stageCoeff errorCoeff) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_eventually_prop47_single_stage_estimates
      stageCoeff errorCoeff (prop47ExceptionalEvent profiles cStar)
      (fun m i a ↦ prop47History profiles cStar m i a 0)
      (fun m i a ↦ prop47History profiles cStar m i a 1)
      (fun m i a ↦ prop47History profiles cStar m i a 2)
      (fun m i a ↦ prop47History profiles cStar m i a 3)
  · exact firstFourPairingEvent_subset_exceptional_union_histories profiles cStar
  · filter_upwards [hExceptional, hLow, hHigh] with m hEx hL hH
    intro i
    refine ⟨hEx i, ?_, ?_, ?_⟩
    · intro a _ha
      exact (le_or_gt (alphaValue a.1) kappaTwo).elim
        (hL i a 0) (hH i a 0)
    · intro a _ha
      exact (le_or_gt (alphaValue a.2.1) kappaTwo).elim
        (hL i a 1) (hH i a 1)
    · intro a _ha
      exact (le_or_gt (alphaValue a.2.2) kappaTwo).elim
        (hL i a 2) (hH i a 2)

set_option linter.constructorNameAsVariable false in
/-- Fully source-decomposed Proposition 4.7 interface.  The four named
exceptional estimates are first assembled by a finite union bound; the
only other inputs are the low/high one-stage conditional estimates from
Propositions 4.8--4.9 and the direct high-distance argument. -/
theorem hlozPlanarConclusion_of_prop47_named_source_estimates
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff farCoeff lemma410Coeff prop45Coeff lemma411412Coeff : ℕ)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hProp45 : Prop47Prop45Estimate profiles cStar prop45Coeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (hLow : Prop47LowStageEstimate profiles cStar stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        lemma411412Coeff))
    (hHigh : Prop47HighStageEstimate profiles cStar stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        lemma411412Coeff)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_prop47_source_estimates profiles cStar
      stageCoeff (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        lemma411412Coeff) ?_ hLow hHigh
  filter_upwards [hFar, hLemma410, hProp45, hLemma411412] with
    m hFarM hLemma410M hProp45M hLemma411412M
  intro i
  exact prop47ExceptionalEvent_measure_le_of_source_failures
    profiles cStar m i farCoeff lemma410Coeff prop45Coeff lemma411412Coeff
    (hFarM i) (hLemma410M i) (hProp45M i) (hLemma411412M i)

end Erdos1166.HLOZProp47SourceAssembly
