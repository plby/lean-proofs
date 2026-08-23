import ErdosProblems.Erdos1166.Erdos1166HLOZProp47HighStageConnector
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixAExactExit
import ErdosProblems.Erdos1166.Erdos1166HLOZGreenBounds
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Canonical
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Race
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedPairRuns

namespace Erdos1166.HLOZProp47HighEscape

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open HLOZFoundation HLOZDecomposition KilledGreen
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp47SourceAssembly HLOZProp47HighStageConnector
open HLOZPairing.ScreeningBridge
open HLOZScreeningAssembly
open HLOZPairingProfiles HLOZProp47Canonical
open HLOZPairing

/-- The finite-prefix property actually used from the canonical deletion
profiles.  The value at time `n` may inspect the one incomplete terminal
pair, hence the deliberate `n + 1`. -/
def OneStepAdaptedProfiles (profiles : Fin 6 → ExternalProfilePair) : Prop :=
  ∀ i n x,
    Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ (profiles i).unprimed s n x) ∧
    Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ (profiles i).primed s n x)

theorem deletionProfilePair_oneStepAdapted (D : DeletionData) :
    OneStepAdaptedProfiles (fun _ ↦ deletionProfilePair D) := by
  intro _i n x
  change
    Measurable[canonicalFiltration (n + 1)]
        (fun s ↦ deletionExternalLocalTime D true s n x) ∧
      Measurable[canonicalFiltration (n + 1)]
        (fun s ↦ deletionExternalLocalTime D false s n x)
  have hadapt (forward : Bool) :
      Measurable[canonicalFiltration (n + 1)]
        (fun s ↦ deletionExternalLocalTime D forward s n x) := by
    apply measurable_of_prefix
    unfold PrefixDependent
    intro s t hst
    unfold deletionExternalLocalTime deletionRetainedTimes
    change ((Finset.range (n + 1) \
        deletionRemovedTimes D forward s n).filter
          fun j ↦ s j = x).card =
      ((Finset.range (n + 1) \
        deletionRemovedTimes D forward t n).filter
          fun j ↦ t j = x).card
    rw [deletionRemovedTimes_congr hst le_rfl]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hj
    rw [hst j (by
      have := Finset.mem_sdiff.mp hj
      exact Nat.le_of_lt (Finset.mem_range.mp this.1))]
  exact ⟨hadapt true, hadapt false⟩

theorem canonicalProfiles_oneStepAdapted :
    OneStepAdaptedProfiles canonicalProfiles := by
  intro i n x
  exact deletionProfilePair_oneStepAdapted (pairingDeletion i) i n x

/-- The literal source family is equally one-step adapted.  For the two
column tilings it reuses the temporal `X₁` pair, exactly as in (2.12). -/
theorem sourceCanonicalProfiles_oneStepAdapted :
    OneStepAdaptedProfiles sourceCanonicalProfiles := by
  intro i n x
  fin_cases i
  · exact deletionProfilePair_oneStepAdapted
      (xDeletion HLOZPairing.east) (⟨0, by omega⟩ : Fin 6) n x
  · exact deletionProfilePair_oneStepAdapted
      (xDeletion HLOZPairing.north) (⟨1, by omega⟩ : Fin 6) n x
  · exact deletionProfilePair_oneStepAdapted
      (xDeletion HLOZPairing.west) (⟨2, by omega⟩ : Fin 6) n x
  · exact deletionProfilePair_oneStepAdapted
      (xDeletion HLOZPairing.south) (⟨3, by omega⟩ : Fin 6) n x
  · simp only [id]
    rw [sourceCanonicalProfiles_y, ← canonicalProfiles_xEast]
    exact canonicalProfiles_oneStepAdapted (⟨0, by omega⟩ : Fin 6) n x
  · simp only [id]
    rw [sourceCanonicalProfiles_y', ← canonicalProfiles_xEast]
    exact canonicalProfiles_oneStepAdapted (⟨0, by omega⟩ : Fin 6) n x

private theorem firstK_succ_le_next (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (fun s ↦ firstKSitesReachLevel m k s + 1) ≤
      (fun s ↦ firstKSitesReachLevel m (k + 1) s) := by
  intro s
  by_cases hnext : firstKSitesReachLevel m (k + 1) s = ⊤
  · simp [hnext]
  · have hlt := firstKSitesReachLevel_strict_mono_k s m hk
      (Nat.lt_succ_self k) hnext
    apply (ENat.add_one_le_iff ?_).mpr hlt
    exact ne_top_of_lt hlt

private theorem measurable_stoppedVisitedSites
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime canonicalFiltration τ) :
    Measurable[hτ.measurableSpace]
      (fun s ↦ visitedSites s (τ s).untopA) := by
  letI : MeasurableSpace (ℕ → Site) := hτ.measurableSpace
  rw [measurable_finset_iff]
  intro x
  have heq : (fun s ↦ x ∈ visitedSites s (τ s).untopA) =
      (fun s ↦ 0 < localTime s (τ s).untopA x) := by
    funext s
    apply propext
    constructor
    · exact localTime_pos_of_mem_visitedSites
    · intro h
      by_contra hx
      rw [localTime_eq_zero_of_not_mem_visitedSites hx] at h
      omega
  rw [heq]
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const
    (HLOZLemma410Race.measurable_stoppedLocalTime hτ x))

private theorem measurable_levelCreationSite_at_threshold
    (m : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (fun s ↦ levelCreationSite s m j) := by
  let hj := isStoppingTime_firstKSitesReachLevel m j
  let hk := isStoppingTime_firstKSitesReachLevel m k
  exact (HLOZLemma410Race.measurable_stoppedCoordinate hj).mono
    (hj.measurableSpace_mono hk (fun s ↦
      firstKSitesReachLevel_mono_k s m hjk)) le_rfl

private theorem measurable_levelCreationSitesUpTo_at_threshold
    (m k : ℕ) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (fun s ↦ levelCreationSitesUpTo s m k) := by
  letI : MeasurableSpace (ℕ → Site) :=
    (isStoppingTime_firstKSitesReachLevel m k).measurableSpace
  rw [measurable_finset_iff]
  intro x
  simp only [levelCreationSitesUpTo, Finset.mem_image]
  apply Measurable.exists
  intro j
  by_cases hj : j ∈ Finset.Icc 1 k
  · simp only [hj, true_and]
    exact measurableSet_setOfPred.mp (measurableSet_eq_fun
      (measurable_levelCreationSite_at_threshold m
        (Finset.mem_Icc.mp hj).2) measurable_const)
  · simp [hj]

private theorem measurable_creationDominoEndpoints_at_threshold
    (i : Fin 6) (m k : ℕ) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (fun s ↦ creationDominoEndpoints i s m k) := by
  have h := (measurable_of_countable
    (fun A : Finset Site ↦ A.image (distinguishedEndpoint i))).comp
      (measurable_levelCreationSitesUpTo_at_threshold m k)
  convert h using 1
  funext s
  ext x
  simp [creationDominoEndpoints, levelCreationSitesUpTo]

private theorem measurable_nearFavoriteSites_at_threshold
    (i : Fin 6) (m k : ℕ) (alpha : ℝ) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (fun s ↦ nearFavoriteSites i s m k alpha) := by
  let hT := isStoppingTime_firstKSitesReachLevel m k
  letI : MeasurableSpace (ℕ → Site) := hT.measurableSpace
  rw [measurable_finset_iff]
  intro x
  rw [show (fun s ↦ x ∈ nearFavoriteSites i s m k alpha) =
      (fun s ↦ x ∈ visitedSites s (firstKSitesReachLevel m k s).untopA ∧
        firstKSitesReachLevel m k s ≠ ⊤ ∧
        distinguishedEndpoint i x ∉ creationDominoEndpoints i s m k ∧
        (m : ℝ) - (m : ℝ) ^ alpha <
          localTime s (firstKSitesReachLevel m k s).untopA x ∧
        (localTime s (firstKSitesReachLevel m k s).untopA x : ℝ) < m) by
    funext s
    unfold nearFavoriteSites directCreationTime
    rw [Finset.mem_filter]]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp (measurable_stoppedVisitedSites hT)
  · apply Measurable.and
    · exact measurableSet_setOfPred.mp
        ((measurableSet_singleton (⊤ : WithTop ℕ)).preimage hT.measurable).compl
    · apply Measurable.and
      · exact measurableSet_setOfPred.mp ((measurableSet_setOfPred.mpr
          ((measurable_finset_mem (distinguishedEndpoint i x)).comp
            (measurable_creationDominoEndpoints_at_threshold i m k))).compl)
      · apply Measurable.and <;> apply measurableSet_setOfPred.mp
        · exact measurableSet_lt measurable_const
            ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
              (HLOZLemma410Race.measurable_stoppedLocalTime hT x))
        · exact measurableSet_lt
            ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp
              (HLOZLemma410Race.measurable_stoppedLocalTime hT x)) measurable_const

private theorem measurable_oneStepAtStoppingDefault
    {σ : (ℕ → Site) → WithTop ℕ} (hσ : IsStoppingTime canonicalFiltration σ)
    {u : ℕ → (ℕ → Site) → ℕ}
    (hu : ∀ n, Measurable[canonicalFiltration (n + 1)] (u n)) :
    Measurable[(hσ.add_const' 1).measurableSpace]
      (fun s ↦ if σ s = ⊤ then 0 else u (σ s).untopA s) := by
  classical
  let v : ℕ → (ℕ → Site) → ℕ
    | 0 => fun _ ↦ 0
    | n + 1 => u n
  have hv : StronglyAdapted canonicalFiltration v := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact (hu n).stronglyMeasurable
  have hstop := measurable_stoppedValue
    hv.isStronglyProgressive_of_discrete (hσ.add_const' 1)
  have htop : MeasurableSet[(hσ.add_const' 1).measurableSpace]
      {s | σ s = ⊤} := by
    have hσtop : MeasurableSet[hσ.measurableSpace] {s | σ s = ⊤} :=
      measurableSet_eq_fun hσ.measurable measurable_const
    exact (hσ.measurableSpace_mono (hσ.add_const' 1)
      (fun s ↦ le_add_right (le_refl (σ s)))) _ hσtop
  have hg : Measurable[(hσ.add_const' 1).measurableSpace]
      (fun s ↦ if σ s = ⊤ then (0 : ℕ)
        else stoppedValue v (fun ω ↦ σ ω + 1) s) :=
    Measurable.ite htop measurable_const hstop
  convert hg using 1
  funext s
  unfold stoppedValue v
  cases hs : σ s with
  | top => simp [hs]
  | coe n => simp [hs]

private theorem measurable_stoppedThetaHalfSites_at_succ
    (external : (ℕ → Site) → ℕ → Site → ℕ)
    (hexternal : ∀ n x, Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ external s n x))
    (parity : Site → Prop) (upper : Bool) (cStar : ℝ)
    (m k : ℕ) :
    Measurable[((isStoppingTime_firstKSitesReachLevel m k).add_const' 1).measurableSpace]
      (fun s ↦ stoppedThetaHalfSites external parity upper cStar s m k) := by
  classical
  let hT := isStoppingTime_firstKSitesReachLevel m k
  have hTsucc : hT.measurableSpace ≤ (hT.add_const' 1).measurableSpace :=
    hT.measurableSpace_mono (hT.add_const' 1)
      (fun s ↦ le_add_right (le_refl _))
  letI : MeasurableSpace (ℕ → Site) := (hT.add_const' 1).measurableSpace
  rw [measurable_finset_iff]
  intro x
  let extAt : (ℕ → Site) → ℕ := fun s ↦
    if firstKSitesReachLevel m k s = ⊤ then 0
    else external s (firstKSitesReachLevel m k s).untopA x
  have hext : Measurable extAt :=
    measurable_oneStepAtStoppingDefault hT (fun n ↦ hexternal n x)
  have hvisited := (measurable_stoppedVisitedSites hT).mono hTsucc le_rfl
  have hlocal := (HLOZLemma410Race.measurable_stoppedLocalTime hT x).mono
    hTsucc le_rfl
  have hfinite : Measurable fun s ↦ firstKSitesReachLevel m k s ≠ ⊤ :=
    measurableSet_setOfPred.mp
      (((measurableSet_singleton (⊤ : WithTop ℕ)).preimage
        (hT.measurable.mono hTsucc le_rfl)).compl)
  rw [show (fun s ↦ x ∈
      stoppedThetaHalfSites external parity upper cStar s m k) =
      (fun s ↦
        x ∈ visitedSites s (firstKSitesReachLevel m k s).untopA ∧
        firstKSitesReachLevel m k s ≠ ⊤ ∧ parity x ∧
        thetaBandLower m ≤
          localTime s (firstKSitesReachLevel m k s).untopA x ∧
        (localTime s (firstKSitesReachLevel m k s).untopA x : ℝ) < m ∧
        if upper then
          (15 : ℝ) / 16 * m + cStar * (m : ℝ) ^ (1 - kappaOne) < extAt s
        else (extAt s : ℝ) ≤ (15 : ℝ) / 16 * thetaBandLower m -
          cStar * (m : ℝ) ^ (1 - kappaOne)) by
    funext s
    unfold stoppedThetaHalfSites directCreationTime extAt
    rw [Finset.mem_filter]
    by_cases hfin : firstKSitesReachLevel m k s = ⊤ <;> simp [hfin]]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp hvisited
  · apply hfinite.and
    apply measurable_const.and
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (measurableSet_le measurable_const
        ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp hlocal))
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (measurableSet_lt
        ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp hlocal)
        measurable_const)
    cases upper with
    | false =>
        exact measurableSet_setOfPred.mp (measurableSet_le
          ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp hext)
          measurable_const)
    | true =>
        exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const
          ((measurable_of_countable fun q : ℕ ↦ (q : ℝ)).comp hext))

private theorem measurable_stoppedThetaHalfSites_at_next
    (external : (ℕ → Site) → ℕ → Site → ℕ)
    (hexternal : ∀ n x, Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ external s n x))
    (parity : Site → Prop) (upper : Bool) (cStar : ℝ)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (fun s ↦ stoppedThetaHalfSites external parity upper cStar s m k) := by
  let hT := isStoppingTime_firstKSitesReachLevel m k
  let hnext := isStoppingTime_firstKSitesReachLevel m (k + 1)
  exact (measurable_stoppedThetaHalfSites_at_succ external hexternal parity upper
    cStar m k).mono
      ((hT.add_const' 1).measurableSpace_mono hnext
        (firstK_succ_le_next m k hm hk)) le_rfl

private theorem measurable_stoppedThetaSites_at_succ
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (i : Fin 6) (m k : ℕ) :
    Measurable[((isStoppingTime_firstKSitesReachLevel m k).add_const' 1).measurableSpace]
      (fun s ↦ stoppedThetaSites (profiles i) (cStar i) s m k) := by
  unfold stoppedThetaSites
  exact (measurable_of_countable
    (fun q : Finset Site × Finset Site × Finset Site × Finset Site ↦
      q.1 ∪ q.2.1 ∪ q.2.2.1 ∪ q.2.2.2)).comp
        ((measurable_stoppedThetaHalfSites_at_succ
          (profiles i).unprimed (fun n x ↦ (hadapt i n x).1)
          (profiles i).unprimedSites false (cStar i) m k).prodMk
        ((measurable_stoppedThetaHalfSites_at_succ
          (profiles i).unprimed (fun n x ↦ (hadapt i n x).1)
          (profiles i).unprimedSites true (cStar i) m k).prodMk
        ((measurable_stoppedThetaHalfSites_at_succ
          (profiles i).primed (fun n x ↦ (hadapt i n x).2)
          (profiles i).primedSites false (cStar i) m k).prodMk
        (measurable_stoppedThetaHalfSites_at_succ
          (profiles i).primed (fun n x ↦ (hadapt i n x).2)
          (profiles i).primedSites true (cStar i) m k))))

/-- The exact low-scale screen belongs to `F_(T_k+1)`: its only information
beyond `T_k` is the completion status of the terminal deletion pair. -/
theorem measurableSet_lowScaleScreenEvent_at_succ
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (i : Fin 6) (m k : ℕ) (beta : ℝ) :
    MeasurableSet[
      ((isStoppingTime_firstKSitesReachLevel m k).add_const' 1).measurableSpace]
      (lowScaleScreenEvent (profiles i) (cStar i) i m k beta) := by
  let hT := isStoppingTime_firstKSitesReachLevel m k
  have hTsucc : hT.measurableSpace ≤ (hT.add_const' 1).measurableSpace :=
    hT.measurableSpace_mono (hT.add_const' 1)
      (fun s ↦ le_add_right (le_refl _))
  letI : MeasurableSpace (ℕ → Site) := (hT.add_const' 1).measurableSpace
  have hnear (gamma : ℝ) :=
    (measurable_nearFavoriteSites_at_threshold i m k gamma).mono hTsucc le_rfl
  unfold lowScaleScreenEvent
  exact (measurableSet_setOfPred.mpr
    ((measurable_of_countable fun A : Finset Site ↦ A.Nonempty).comp
      (hnear beta))).inter
    ((measurableSet_eq_fun
      (measurable_stoppedThetaSites_at_succ profiles hadapt cStar i m k)
      measurable_const).inter
      (measurableSet_le
        ((measurable_of_countable fun A : Finset Site ↦ (A.card : ℝ)).comp
          (hnear kappaOne)) measurable_const))

private theorem measurable_stoppedThetaSites_at_next
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (i : Fin 6) (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (fun s ↦ stoppedThetaSites (profiles i) (cStar i) s m k) := by
  unfold stoppedThetaSites
  exact (measurable_of_countable
    (fun q : Finset Site × Finset Site × Finset Site × Finset Site ↦
      q.1 ∪ q.2.1 ∪ q.2.2.1 ∪ q.2.2.2)).comp
        ((measurable_stoppedThetaHalfSites_at_next
          (profiles i).unprimed (fun n x ↦ (hadapt i n x).1)
          (profiles i).unprimedSites false (cStar i) m k hm hk).prodMk
        ((measurable_stoppedThetaHalfSites_at_next
          (profiles i).unprimed (fun n x ↦ (hadapt i n x).1)
          (profiles i).unprimedSites true (cStar i) m k hm hk).prodMk
        ((measurable_stoppedThetaHalfSites_at_next
          (profiles i).primed (fun n x ↦ (hadapt i n x).2)
          (profiles i).primedSites false (cStar i) m k hm hk).prodMk
        (measurable_stoppedThetaHalfSites_at_next
          (profiles i).primed (fun n x ↦ (hadapt i n x).2)
          (profiles i).primedSites true (cStar i) m k hm hk))))

/-- The low-scale screen is measurable after exposing exactly the one
incomplete terminal increment used by the canonical deletion profiles. -/
theorem measurableSet_lowScaleScreenEvent_at_next
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (i : Fin 6) (m k : ℕ) (beta : ℝ)
    (hm : 0 < m) (hk : 0 < k) :
    MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (lowScaleScreenEvent (profiles i) (cStar i) i m k beta) := by
  let hT := isStoppingTime_firstKSitesReachLevel m k
  let hnext := isStoppingTime_firstKSitesReachLevel m (k + 1)
  have hTnext : hT.measurableSpace ≤ hnext.measurableSpace :=
    hT.measurableSpace_mono hnext
      (fun s ↦ firstKSitesReachLevel_mono_k s m (Nat.le_succ k))
  letI : MeasurableSpace (ℕ → Site) := hnext.measurableSpace
  have hnear (gamma : ℝ) :=
    (measurable_nearFavoriteSites_at_threshold i m k gamma).mono hTnext le_rfl
  unfold lowScaleScreenEvent
  exact (measurableSet_setOfPred.mpr
    ((measurable_of_countable fun A : Finset Site ↦ A.Nonempty).comp
      (hnear beta))).inter
    ((measurableSet_eq_fun
      (measurable_stoppedThetaSites_at_next profiles hadapt cStar i m k hm hk)
      measurable_const).inter
      (measurableSet_le
        ((measurable_of_countable fun A : Finset Site ↦ (A.card : ℝ)).comp
          (hnear kappaOne)) measurable_const))

private theorem measurableSet_prefixPairingEvent_at_threshold
    (m : ℕ) (i : Fin 6) (k : ℕ) :
    MeasurableSet[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (prefixPairingEvent m i k) := by
  letI : MeasurableSpace (ℕ → Site) :=
    (isStoppingTime_firstKSitesReachLevel m k).measurableSpace
  exact (Erdos1166.measurableSet_hlozMAtThreshold m k).inter
    (measurableSet_setOfPred.mpr
      ((measurable_of_countable fun A : Finset Site ↦
        PairFree (pairingRelation i) A).comp
          (measurable_levelCreationSitesUpTo_at_threshold m k)))

private theorem measurable_creationPair_at_next (m k : ℕ) :
    Measurable[
      (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (fun s : ℕ → Site ↦
      (levelCreationSite s m k, levelCreationSite s m (k + 1))) :=
    (measurable_levelCreationSite_at_threshold m
      (j := k) (k := k + 1) (Nat.le_succ k)).prodMk
      (measurable_levelCreationSite_at_threshold m
        (j := k + 1) (k := k + 1) le_rfl)

private def distancePairSet (m : ℕ) (alpha : ℝ) : Set (Site × Site) :=
  {p | distanceBinLower m alpha ≤ siteDistance p.1 p.2 ∧
    siteDistance p.1 p.2 ≤ distanceBinUpper m alpha}

private theorem measurable_thresholdFinite_at_next (m k : ℕ) :
    Measurable[
      (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (fun s : ℕ → Site ↦ firstKSitesReachLevel m k s ≠ ⊤) := by
  let hT := isStoppingTime_firstKSitesReachLevel m k
  let hnext := isStoppingTime_firstKSitesReachLevel m (k + 1)
  letI : MeasurableSpace (ℕ → Site) := hnext.measurableSpace
  have hTnext : hT.measurableSpace ≤ hnext.measurableSpace :=
    hT.measurableSpace_mono hnext
      (fun s ↦ firstKSitesReachLevel_mono_k s m (Nat.le_succ k))
  exact measurableSet_setOfPred.mp
    (((measurableSet_singleton (⊤ : WithTop ℕ)).preimage
      (hT.measurable.mono hTnext le_rfl)).compl)

private theorem measurableSet_distanceBinEvent_at_next
    (m k : ℕ) (alpha : ℝ) :
    MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m (k + 1)).measurableSpace]
      (distanceBinEvent m k alpha) := by
  let hnext := isStoppingTime_firstKSitesReachLevel m (k + 1)
  letI : MeasurableSpace (ℕ → Site) := hnext.measurableSpace
  have hpair : Measurable fun s : ℕ → Site ↦
      (levelCreationSite s m k, levelCreationSite s m (k + 1)) :=
    measurable_creationPair_at_next m k
  have hbounds : MeasurableSet
      ((fun s : ℕ → Site ↦
        (levelCreationSite s m k, levelCreationSite s m (k + 1))) ⁻¹'
          distancePairSet m alpha) :=
    (MeasurableSet.of_discrete : MeasurableSet (distancePairSet m alpha)).preimage hpair
  have hnextfinite : MeasurableSet {s : ℕ → Site |
      firstKSitesReachLevel m (k + 1) s ≠ ⊤} :=
    ((measurableSet_singleton (⊤ : WithTop ℕ)).preimage
      hnext.measurable).compl
  have heq : distanceBinEvent m k alpha =
      {s | firstKSitesReachLevel m k s ≠ ⊤} ∩
        ({s | firstKSitesReachLevel m (k + 1) s ≠ ⊤} ∩
          (fun s ↦ (levelCreationSite s m k,
            levelCreationSite s m (k + 1))) ⁻¹' distancePairSet m alpha) := by
    rfl
  rw [heq]
  exact (measurableSet_setOfPred.mpr
    (measurable_thresholdFinite_at_next m k)).inter (hnextfinite.inter hbounds)

private theorem prefixPairingEvent_subset_directAvoidance
    (m : ℕ) (i : Fin 6) (k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    prefixPairingEvent m i (k + 1) ⊆
      hlozDirectAvoidanceEvent m (k + 1) := by
  intro s hs
  exact ((mem_hlozThresholdTimeEventK_iff_finite_and_directAvoidance
    s m (k + 1) hm (by omega)).mp hs.1).2 (k + 1) (by omega) le_rfl

private theorem measurableSet_prop47StageEvent_at_next
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (i : Fin 6) (m : ℕ)
    (r : StageIndex) (alpha : ℝ) (hm : 0 < m) :
    MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m (stageNumber r + 1)).measurableSpace]
      (prop47StageEvent profiles cStar i m r alpha) := by
  let k := stageNumber r
  have hk : 0 < k := by simp [k, stageNumber]
  let hT := isStoppingTime_firstKSitesReachLevel m k
  let hnext := isStoppingTime_firstKSitesReachLevel m (k + 1)
  change MeasurableSet[hnext.measurableSpace]
    (prop47StageEvent profiles cStar i m r alpha)
  letI : MeasurableSpace (ℕ → Site) := hnext.measurableSpace
  have hTnext : hT.measurableSpace ≤ hnext.measurableSpace :=
    hT.measurableSpace_mono hnext
      (fun s ↦ firstKSitesReachLevel_mono_k s m (Nat.le_succ k))
  have hprefix := measurableSet_prefixPairingEvent_at_threshold m i (k + 1)
  have hdist := measurableSet_distanceBinEvent_at_next m k alpha
  have hnear (beta : ℝ) :=
    (measurable_nearFavoriteSites_at_threshold i m k beta).mono hTnext le_rfl
  have hsite := measurable_levelCreationSite_at_threshold m
    (j := k + 1) (k := k + 1) le_rfl
  have hcand : MeasurableSet[hnext.measurableSpace]
      (nextCreationIsCandidateEvent i m k (alpha + delta)) := by
    exact measurableSet_setOfPred.mpr
      ((measurable_of_countable
        (fun p : Site × Finset Site ↦ p.1 ∈ p.2)).comp
          (hsite.prodMk (hnear (alpha + delta))))
  have htheta : MeasurableSet[hnext.measurableSpace]
      {s | stoppedThetaSites (profiles i) (cStar i) s m k = ∅} :=
    measurableSet_eq_fun
      (measurable_stoppedThetaSites_at_next profiles hadapt cStar i m k hm hk)
      measurable_const
  have hcard : MeasurableSet[hnext.measurableSpace]
      {s | ((nearFavoriteSites i s m k kappaOne).card : ℝ) ≤ Real.log m ^ 2} :=
    measurableSet_le
      ((measurable_of_countable fun A : Finset Site ↦ (A.card : ℝ)).comp
        (hnear kappaOne)) measurable_const
  rw [prop47StageEvent]
  split_ifs with hlow
  · have heq : prefixPairingEvent m i (k + 1) ∩
        lowScaleStageEvent (profiles i) (cStar i) i m k alpha =
      prefixPairingEvent m i (k + 1) ∩
        (((distanceBinEvent m k alpha ∩
          nextCreationIsCandidateEvent i m k (alpha + delta)) ∩
          {s | stoppedThetaSites (profiles i) (cStar i) s m k = ∅}) ∩
          {s | ((nearFavoriteSites i s m k kappaOne).card : ℝ) ≤
            Real.log m ^ 2}) := by
      ext s
      constructor
      · rintro ⟨hp, ⟨⟨⟨⟨_ha, hd⟩, hc⟩, ht⟩, hh⟩⟩
        exact ⟨hp, ⟨⟨⟨hd, hc⟩, ht⟩, hh⟩⟩
      · rintro ⟨hp, ⟨⟨⟨hd, hc⟩, ht⟩, hh⟩⟩
        exact ⟨hp, ⟨⟨⟨⟨prefixPairingEvent_subset_directAvoidance
          m i k hm hk hp, hd⟩, hc⟩, ht⟩, hh⟩⟩
    rw [heq]
    exact hprefix.inter (((hdist.inter hcand).inter htheta).inter hcard)
  · have heq : prefixPairingEvent m i (k + 1) ∩
        (hlozDirectAvoidanceEvent m (k + 1) ∩ distanceBinEvent m k alpha) =
      prefixPairingEvent m i (k + 1) ∩ distanceBinEvent m k alpha := by
      ext s
      constructor
      · exact fun hs ↦ ⟨hs.1, hs.2.2⟩
      · exact fun hs ↦ ⟨hs.1,
          prefixPairingEvent_subset_directAvoidance m i k hm hk hs.1, hs.2⟩
    rw [heq]
    exact hprefix.inter hdist

theorem measurableSet_prop47History_at_threshold
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ) (m : ℕ) (i : Fin 6) (a : AlphaTriple)
    (n : ℕ) (hn : n ≤ 3) (hm : 0 < m) :
    MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m (n + 1)).measurableSpace]
      (prop47History profiles cStar m i a n) := by
  induction n with
  | zero =>
      simpa using measurableSet_prefixPairingEvent_at_threshold m i 1
  | succ n ih =>
      have hn3 : n < 3 := by omega
      let hprev := isStoppingTime_firstKSitesReachLevel m (n + 1)
      let hnext := isStoppingTime_firstKSitesReachLevel m (n + 2)
      have hmono : hprev.measurableSpace ≤ hnext.measurableSpace :=
        hprev.measurableSpace_mono hnext
          (fun s ↦ firstKSitesReachLevel_mono_k s m (by omega))
      have hhistory : MeasurableSet[hnext.measurableSpace]
          (prop47History profiles cStar m i a n) :=
        hmono _ (ih (by omega))
      let r : StageIndex := ⟨n, hn3⟩
      have hstage : MeasurableSet[hnext.measurableSpace]
          (prop47StageEvent profiles cStar i m r
            (alphaValue (tripleAlphaIndex a r))) := by
        convert measurableSet_prop47StageEvent_at_next
          profiles hadapt cStar i m r
            (alphaValue (tripleAlphaIndex a r)) hm using 1 <;>
          simp [hnext, r, stageNumber]
      rw [prop47History, screeningHistory_succ]
      simp only [hn3, dite_true]
      exact hhistory.inter hstage

theorem measurableSet_prop47History_stoppedFiber_iidHistory
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) (n : ℕ)
    (hm : 0 < m) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹'
          prop47History profiles cStar m i a r.1 ∩
        {ω | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk ω) = n}) := by
  apply Erdos1166.measurableSet_pathStoppedEvent_inter_fiber_iidHistory
    (isStoppingTime_firstKSitesReachLevel m (stageNumber r))
    (prop47History profiles cStar m i a r.1)
  convert measurableSet_prop47History_at_threshold
    profiles hadapt cStar
      m i a r.1 (by omega) hm using 1 <;>
    simp [stageNumber]

theorem measurableSet_canonicalProp47History_stoppedFiber_iidHistory
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) (n : ℕ)
    (hm : 0 < m) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹'
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
        {ω | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk ω) = n}) :=
  measurableSet_prop47History_stoppedFiber_iidHistory
    canonicalProfiles canonicalProfiles_oneStepAdapted canonicalCStar
      m i a r n hm

private theorem prop47History_subset_prefixPairingEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (n : ℕ) (hn : n ≤ 3) :
    prop47History profiles cStar m i a n ⊆
      prefixPairingEvent m i (n + 1) := by
  intro s hs
  cases n with
  | zero => exact hs
  | succ n =>
      have hn3 : n < 3 := by omega
      rw [prop47History, screeningHistory_succ] at hs
      simp only [hn3, dite_true] at hs
      simpa [prop47StageEvent, stageNumber] using hs.2.1

theorem prop47History_subset_thresholdFinite
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) :
    prop47History profiles cStar m i a r.1 ⊆
      {s | firstKSitesReachLevel m (stageNumber r) s ≠ ⊤} := by
  intro s hs
  have hprefix := prop47History_subset_prefixPairingEvent
    profiles cStar m i a r.1 (by omega) hs
  exact ne_top_of_lt hprefix.1

theorem walkFrom_incrementShiftAfter
    (omega : ℕ → Direction) (tau q : ℕ) :
    walkFrom 0 (incrementShiftAfter (fun _ ↦ tau) omega) q =
      simpleRandomWalk omega (tau + q) - simpleRandomWalk omega tau := by
  unfold walkFrom incrementShiftAfter simpleRandomWalk
  rw [Finset.sum_range_add]
  simp only [zero_add, add_sub_cancel_left]

private theorem siteDistance_zero_sub (x y : Site) :
    siteDistance 0 (y - x) = siteDistance x y := by
  unfold siteDistance siteSquaredDistance
  congr 1
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [Prod.fst_zero, Prod.fst_sub, Prod.snd_zero, Prod.snd_sub]
  congr 2 <;> congr 1 <;> ring

/-- A finite square comfortably contained in the Euclidean high-gap scale. -/
noncomputable def highEscapeRadius (m : ℕ) : ℕ :=
  Nat.ceil (Real.exp (((m : ℝ) ^ kappaTwo) / 2))

theorem exitBeforeReturnAtNextCreation_increment_subset
    (m k R : ℕ) (radius : ℝ) (hm : 0 < m) (hk : 0 < k)
    (hR : 3 * (R : ℝ) < radius) :
    simpleRandomWalk ⁻¹' exitBeforeReturnAtNextCreation m k radius ⊆
      incrementShiftAfter (fun omega ↦
        (firstKSitesReachLevel m k (simpleRandomWalk omega)).untopA) ⁻¹'
        exitBeforeReturnEvent (squareDisk R : Set Site) 0 := by
  intro omega homega
  let s := simpleRandomWalk omega
  let Tk := firstKSitesReachLevel m k s
  let Tnext := firstKSitesReachLevel m (k + 1) s
  have hTk : Tk ≠ ⊤ := homega.1
  have hTnext : Tnext ≠ ⊤ := homega.2.1
  let t := Tk.untopA
  let u := Tnext.untopA
  have htcoe : (t : WithTop ℕ) = Tk := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hTk]
    exact WithTop.coe_untop Tk hTk
  have hucoe : (u : WithTop ℕ) = Tnext := by
    dsimp only [u]
    rw [WithTop.untopA_eq_untop hTnext]
    exact WithTop.coe_untop Tnext hTnext
  have hstrict := firstKSitesReachLevel_strict_mono_k s m hk
    (Nat.lt_succ_self k) hTnext
  have htu : t < u := by
    exact_mod_cast htcoe.trans_lt (hstrict.trans_eq hucoe.symm)
  let tau : (ℕ → Direction) → ℕ := fun omega ↦
    (firstKSitesReachLevel m k (simpleRandomWalk omega)).untopA
  let eta := incrementShiftAfter tau omega
  have htstop : tau omega = t := rfl
  have hwalk (q : ℕ) : walkFrom 0 eta q = s (t + q) - s t := by
    change walkFrom 0 (incrementShiftAfter tau omega) q = _
    rw [show incrementShiftAfter tau omega =
        incrementShiftAfter (fun _ ↦ t) omega by
      funext j
      simp only [incrementShiftAfter, htstop]]
    exact walkFrom_incrementShiftAfter omega t q
  have hout : walkFrom 0 eta (u - t) ∉ squareDisk R := by
    intro hin
    have hzero : (0 : Site) ∈ squareDisk R := by simp [squareDisk]
    have hdist := siteDistance_le_three_mul_of_mem_squareDisk hzero hin
    have hend : walkFrom 0 eta (u - t) =
        levelCreationSite s m (k + 1) - levelCreationSite s m k := by
      rw [hwalk, Nat.add_sub_of_le htu.le]
      rfl
    rw [hend] at hdist
    have htranslate := siteDistance_zero_sub
      (levelCreationSite s m k) (levelCreationSite s m (k + 1))
    rw [htranslate] at hdist
    linarith [homega.2.2.2]
  refine ⟨?_, ⟨u - t, hout⟩⟩
  intro hreturn
  rcases Set.mem_iUnion.mp hreturn with ⟨q, hq⟩
  by_cases hqu : q + 1 ≤ u - t
  · have hpos : t < t + (q + 1) := by omega
    have hleu : t + (q + 1) ≤ u := by omega
    have havoid := homega.2.2.1 (t + (q + 1))
      (by
        have hcast : Tk < ((t + (q + 1) : ℕ) : WithTop ℕ) := by
          rw [← htcoe]
          exact_mod_cast hpos
        simpa [Tk, s] using hcast)
      (by
        have hcast : (((t + (q + 1) : ℕ) : WithTop ℕ)) ≤ Tnext := by
          rw [← hucoe]
          exact_mod_cast hleu
        simpa [Tnext, s] using hcast)
      k (by omega) (by omega)
    have hzero := hq.2.1
    rw [hwalk] at hzero
    have heq : s (t + (q + 1)) = s t := sub_eq_zero.mp hzero
    have hsite : levelCreationSite s m k = s t := rfl
    exact havoid (heq.trans hsite.symm)
  · have huq : u - t ≤ q + 1 := by omega
    exact hout (hq.1 (u - t) huq)

theorem measurableSet_eventuallyExitEvent (D : Set Site) (x : Site) :
    MeasurableSet (eventuallyExitEvent D x) := by
  have heq : eventuallyExitEvent D x = ⋃ n : ℕ, {omega |
      walkFrom x omega n ∉ D} := by
    ext omega
    simp [eventuallyExitEvent]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_setOfPred.mpr
    ((measurable_of_countable fun y : Site ↦ y ∈ D).comp
      ((measurable_walkFrom_iidHistory x le_rfl).mono
        (ProbabilityTheory.iidHistory_le n) le_rfl))).compl

theorem measurableSet_exitBeforeReturnEvent (D : Set Site) (x : Site) :
    MeasurableSet (exitBeforeReturnEvent D x) :=
  (measurableSet_returnBeforeExitEvent D x).compl.inter
    (measurableSet_eventuallyExitEvent D x)

theorem history_inter_highExit_le_mul
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (R : ℕ) (radius : ℝ) (hm : 0 < m)
    (hR : 3 * (R : ℝ) < radius) :
    simpleRandomWalkLaw
        (prop47History profiles cStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r) radius) ≤
      simpleRandomWalkLaw
          (prop47History profiles cStar m i a r.1) *
        incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) := by
  let history := prop47History profiles cStar m i a r.1
  let A : Set (ℕ → Direction) := simpleRandomWalk ⁻¹' history
  let tau : (ℕ → Direction) → ℕ := fun omega ↦
    (firstKSitesReachLevel m (stageNumber r)
      (simpleRandomWalk omega)).untopA
  let B := exitBeforeReturnEvent (squareDisk R : Set Site) 0
  change simpleRandomWalkLaw
      (history ∩ exitBeforeReturnAtNextCreation m (stageNumber r) radius) ≤
    simpleRandomWalkLaw history * incrementLaw B
  have hhistory : MeasurableSet history :=
    measurableSet_prop47History profiles cStar m i a r.1
  have hsource : MeasurableSet
      (exitBeforeReturnAtNextCreation m (stageNumber r) radius) :=
    measurableSet_exitBeforeReturnAtNextCreation m (stageNumber r) radius
  have hB : MeasurableSet B := measurableSet_exitBeforeReturnEvent _ _
  have hAfiber (n : ℕ) : MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | tau omega = n}) := by
    have hmeas := measurableSet_prop47History_stoppedFiber_iidHistory
      profiles hadapt cStar m i a r n hm
    have heq : A ∩ {omega | tau omega = n} =
        simpleRandomWalk ⁻¹' history ∩
          {omega | firstKSitesReachLevel m (stageNumber r)
            (simpleRandomWalk omega) = n} := by
      ext omega
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      refine and_congr_right fun hhist ↦ ?_
      have hfinite := prop47History_subset_thresholdFinite
        profiles cStar m i a r hhist
      let T := firstKSitesReachLevel m (stageNumber r)
        (simpleRandomWalk omega)
      have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop hfinite]
        exact WithTop.coe_untop T hfinite
      change T.untopA = n ↔ T = n
      constructor
      · intro h
        rw [← hcoe]
        exact_mod_cast h
      · intro h
        have := congrArg WithTop.untopA h
        simpa using this
    rw [heq]
    exact hmeas
  have hfactor : incrementLaw (A ∩ incrementShiftAfter tau ⁻¹' B) =
      incrementLaw A * incrementLaw B :=
    HLOZAppendixAExactExit.measure_inter_incrementShiftAfter_eq_mul
      tau A B
        (((isStoppingTime_firstKSitesReachLevel m (stageNumber r)).measurable'.untopA).comp
          measurable_simpleRandomWalk) hAfiber hB
  have hincl : simpleRandomWalk ⁻¹'
        (history ∩ exitBeforeReturnAtNextCreation m (stageNumber r) radius) ⊆
      A ∩ incrementShiftAfter tau ⁻¹' B := by
    intro omega homega
    exact ⟨homega.1,
      exitBeforeReturnAtNextCreation_increment_subset m (stageNumber r) R radius
        hm (by simp [stageNumber]) hR homega.2⟩
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk (hhistory.inter hsource),
    Measure.map_apply measurable_simpleRandomWalk hhistory]
  exact (measure_mono hincl).trans_eq hfactor

theorem canonicalHistory_inter_highExit_le_mul
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (R : ℕ) (radius : ℝ) (hm : 0 < m)
    (hR : 3 * (R : ℝ) < radius) :
    simpleRandomWalkLaw
        (prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r) radius) ≤
      simpleRandomWalkLaw
          (prop47History canonicalProfiles canonicalCStar m i a r.1) *
        incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) :=
  history_inter_highExit_le_mul canonicalProfiles
    canonicalProfiles_oneStepAdapted canonicalCStar
      m i a r R radius hm hR

theorem tendsto_highEscapeScale :
    Tendsto (fun m : ℕ ↦ Real.exp (((m : ℝ) ^ kappaTwo) / 2))
      atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact ((tendsto_rpow_atTop (by norm_num [kappaTwo] : 0 < kappaTwo)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num)

theorem eventually_highEscapeRadius_properties :
    ∀ᶠ m : ℕ in atTop,
      2 ≤ highEscapeRadius m ∧
        3 * (highEscapeRadius m : ℝ) <
          Real.exp ((m : ℝ) ^ kappaTwo) / 3 ∧
        ((m : ℝ) ^ kappaTwo) / 2 ≤
          Real.log (highEscapeRadius m : ℝ) := by
  have hlarge := tendsto_highEscapeScale.eventually (eventually_ge_atTop 10)
  filter_upwards [hlarge] with m hm
  let y := Real.exp (((m : ℝ) ^ kappaTwo) / 2)
  have hypos : 0 < y := Real.exp_pos _
  have hyceil : y ≤ (highEscapeRadius m : ℝ) := by
    exact Nat.le_ceil y
  have hyten : 10 ≤ y := by simpa only [y] using hm
  have hRtwo : 2 ≤ highEscapeRadius m := by
    have : (2 : ℝ) ≤ (highEscapeRadius m : ℝ) :=
      (by linarith)
    exact_mod_cast this
  have hceil : (highEscapeRadius m : ℝ) < y + 1 := by
    exact Nat.ceil_lt_add_one hypos.le
  have hexpsq : Real.exp ((m : ℝ) ^ kappaTwo) = y ^ 2 := by
    dsimp only [y]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hradius : 3 * (highEscapeRadius m : ℝ) <
      Real.exp ((m : ℝ) ^ kappaTwo) / 3 := by
    rw [hexpsq]
    nlinarith [sq_nonneg (y - 10)]
  have hlog : ((m : ℝ) ^ kappaTwo) / 2 ≤
      Real.log (highEscapeRadius m : ℝ) := by
    calc
      ((m : ℝ) ^ kappaTwo) / 2 = Real.log y := by
        dsimp only [y]
        rw [Real.log_exp]
      _ ≤ Real.log (highEscapeRadius m : ℝ) :=
        Real.log_le_log hypos hyceil
  exact ⟨hRtwo, hradius, hlog⟩

theorem eventually_highEscape_real_rate_le :
    ∀ᶠ m : ℕ in atTop,
      8 / Real.log (highEscapeRadius m : ℝ) ≤
        64 / (((m : ℝ) + 1) ^ kappa) := by
  have hpoly :=
    HLOZNearCriticalBridge.eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := (32 : ℝ)) (d := (64 : ℝ)) (p := kappa) (q := kappaTwo)
      (by norm_num) (by norm_num) (by norm_num [kappa, kappaTwo, delta])
  filter_upwards [eventually_highEscapeRadius_properties, hpoly,
    eventually_ge_atTop 1] with m hR hpoly hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpowpos : 0 < (m : ℝ) ^ kappaTwo :=
    Real.rpow_pos_of_pos hmpos _
  have hshiftpos : 0 < ((m : ℝ) + 1) ^ kappa :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlogpos : 0 < Real.log (highEscapeRadius m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < highEscapeRadius m by omega))
  have hfirst : 8 / Real.log (highEscapeRadius m : ℝ) ≤
      16 / ((m : ℝ) ^ kappaTwo) := by
    apply (div_le_div_iff₀ hlogpos hpowpos).2
    nlinarith [hR.2.2]
  have hkappa0 : 0 ≤ kappa := by norm_num [kappa_eq]
  have hkappa1 : kappa ≤ 1 := by norm_num [kappa_eq]
  have htwo : (2 : ℝ) ^ kappa ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hkappa1
    simpa only [Real.rpow_one] using h
  have hbase : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hshift : ((m : ℝ) + 1) ^ kappa ≤
      2 * (m : ℝ) ^ kappa := by
    calc
      ((m : ℝ) + 1) ^ kappa ≤ (2 * (m : ℝ)) ^ kappa :=
        Real.rpow_le_rpow (by positivity) hbase hkappa0
      _ = (2 : ℝ) ^ kappa * (m : ℝ) ^ kappa := by
        rw [Real.mul_rpow (by norm_num) hmpos.le]
      _ ≤ 2 * (m : ℝ) ^ kappa := by gcongr
  have hsecond : 16 / ((m : ℝ) ^ kappaTwo) ≤
      64 / (((m : ℝ) + 1) ^ kappa) := by
    apply (div_le_div_iff₀ hpowpos hshiftpos).2
    calc
      (16 : ℝ) * ((m : ℝ) + 1) ^ kappa ≤
          32 * (m : ℝ) ^ kappa := by nlinarith
      _ ≤ 64 * (m : ℝ) ^ kappaTwo := hpoly
  exact hfirst.trans hsecond

theorem ofReal_sourceStageRate_sixtyFour (m : ℕ) :
    ENNReal.ofReal (64 / (((m : ℝ) + 1) ^ kappa)) =
      sourceStageRate m 64 kappa := by
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  have hnum : ENNReal.ofReal (64 : ℝ) = (64 : ℝ≥0∞) := by norm_num
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [hnum, ← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
  simp only [sourceStageRate, div_eq_mul_inv]
  rw [ENNReal.rpow_neg]
  norm_num

theorem eventually_highEscape_increment_measure_le_sourceStageRate :
    ∀ᶠ m : ℕ in atTop,
      incrementLaw
          (exitBeforeReturnEvent (squareDisk (highEscapeRadius m) : Set Site) 0) ≤
        sourceStageRate m 64 kappa := by
  filter_upwards [eventually_highEscapeRadius_properties,
    eventually_highEscape_real_rate_le] with m hR hrate
  calc
    incrementLaw
        (exitBeforeReturnEvent (squareDisk (highEscapeRadius m) : Set Site) 0) ≤
        ENNReal.ofReal (8 / Real.log (highEscapeRadius m : ℝ)) :=
      measure_exitBeforeReturn_zero_le_ofReal_eight_div_log hR.1
    _ ≤ ENNReal.ofReal (64 / (((m : ℝ) + 1) ^ kappa)) :=
      ENNReal.ofReal_le_ofReal hrate
    _ = sourceStageRate m 64 kappa := ofReal_sourceStageRate_sixtyFour m

/-- Every one-step-adapted profile family has the literal source high-stage
escape estimate.  The natural prefactor `64` is explicit. -/
theorem prop47HighEscapeEstimate_of_oneStepAdapted
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ) :
    Prop47HighEscapeEstimate profiles cStar 64 := by
  filter_upwards [eventually_highEscapeRadius_properties,
    eventually_highEscape_increment_measure_le_sourceStageRate,
    eventually_ge_atTop 1] with m hR hmeasure hm
  intro i a r _hhigh
  calc
    simpleRandomWalkLaw
        (prop47History profiles cStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r)
            (Real.exp ((m : ℝ) ^ kappaTwo) / 3)) ≤
        simpleRandomWalkLaw
            (prop47History profiles cStar m i a r.1) *
          incrementLaw
            (exitBeforeReturnEvent
              (squareDisk (highEscapeRadius m) : Set Site) 0) :=
      history_inter_highExit_le_mul profiles hadapt cStar
        m i a r (highEscapeRadius m)
        (Real.exp ((m : ℝ) ^ kappaTwo) / 3) (by omega) hR.2.1
    _ ≤ simpleRandomWalkLaw
            (prop47History profiles cStar m i a r.1) *
          sourceStageRate m 64 kappa := by gcongr
    _ = sourceStageRate m 64 kappa *
          simpleRandomWalkLaw
            (prop47History profiles cStar m i a r.1) :=
      mul_comm _ _

/-- The auxiliary pairing-adapted family satisfies the high-stage estimate. -/
theorem canonical_prop47HighEscapeEstimate :
    Prop47HighEscapeEstimate canonicalProfiles canonicalCStar 64 :=
  prop47HighEscapeEstimate_of_oneStepAdapted canonicalProfiles
    canonicalProfiles_oneStepAdapted canonicalCStar

/-- The literal temporal-profile family satisfies the high-stage estimate. -/
theorem sourceCanonical_prop47HighEscapeEstimate :
    Prop47HighEscapeEstimate sourceCanonicalProfiles canonicalCStar 64 :=
  prop47HighEscapeEstimate_of_oneStepAdapted sourceCanonicalProfiles
    sourceCanonicalProfiles_oneStepAdapted canonicalCStar

/-- Any larger common stage coefficient inherits the canonical high escape
estimate.  This lets the final assembly choose its coefficient from the
low-distance estimates without reintroducing a high-stage premise. -/
theorem canonical_prop47HighEscapeEstimate_mono (stageCoeff : ℕ)
    (hcoeff : 64 ≤ stageCoeff) :
    Prop47HighEscapeEstimate canonicalProfiles canonicalCStar stageCoeff := by
  filter_upwards [canonical_prop47HighEscapeEstimate] with m hm
  intro i a r hhigh
  calc
    simpleRandomWalkLaw
        (prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r)
            (Real.exp ((m : ℝ) ^ kappaTwo) / 3)) ≤
      sourceStageRate m 64 kappa *
        simpleRandomWalkLaw
          (prop47History canonicalProfiles canonicalCStar m i a r.1) :=
      hm i a r hhigh
    _ ≤ sourceStageRate m stageCoeff kappa *
        simpleRandomWalkLaw
          (prop47History canonicalProfiles canonicalCStar m i a r.1) := by
      gcongr
      unfold sourceStageRate
      gcongr

theorem sourceCanonical_prop47HighEscapeEstimate_mono (stageCoeff : ℕ)
    (hcoeff : 64 ≤ stageCoeff) :
    Prop47HighEscapeEstimate sourceCanonicalProfiles canonicalCStar stageCoeff := by
  filter_upwards [sourceCanonical_prop47HighEscapeEstimate] with m hm
  intro i a r hhigh
  calc
    simpleRandomWalkLaw
        (prop47History sourceCanonicalProfiles canonicalCStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r)
            (Real.exp ((m : ℝ) ^ kappaTwo) / 3)) ≤
      sourceStageRate m 64 kappa *
        simpleRandomWalkLaw
          (prop47History sourceCanonicalProfiles canonicalCStar m i a r.1) :=
      hm i a r hhigh
    _ ≤ sourceStageRate m stageCoeff kappa *
        simpleRandomWalkLaw
          (prop47History sourceCanonicalProfiles canonicalCStar m i a r.1) := by
      gcongr
      unfold sourceStageRate
      gcongr

end Erdos1166.HLOZProp47HighEscape
