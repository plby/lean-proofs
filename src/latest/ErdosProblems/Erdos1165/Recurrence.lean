/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.Basic
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.FourierReturn
import ErdosProblems.Erdos1165.RenewalBound

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

/-! ## Returns and first returns on the increment space -/

/-- The event that the walk is at the origin at time `n`. -/
def returnAt (n : ℕ) : Set StepPath := {ω | trajectory ω n = (0, 0)}

/-- The event that `n` is the first strictly positive return time. -/
def firstReturnAt (n : ℕ) : Set StepPath :=
  {ω | 0 < n ∧ trajectory ω n = (0, 0) ∧
    ∀ j, 0 < j → j < n → trajectory ω j ≠ (0, 0)}

/-- The displacement in the `m` increments beginning at time `n` is zero. -/
def relativeReturnAt (n m : ℕ) : Set StepPath :=
  {ω | trajectory ω (n + m) - trajectory ω n = (0, 0)}

lemma returnAt_eq_stepPrefix_preimage (n : ℕ) :
    returnAt n = stepPrefix n ⁻¹' {u | markovBlockDisplacement u = (0, 0)} := by
  ext ω
  simp only [returnAt, mem_ofPred_eq, mem_preimage]
  rw [trajectory_eq_markovBlockDisplacement_stepPrefix]

lemma measurableSet_returnAt_filtration (n : ℕ) :
    MeasurableSet[incrementFiltration n] (returnAt n) := by
  rw [returnAt_eq_stepPrefix_preimage, incrementFiltration_apply]
  exact ⟨_, measurableSet_eq_fun (measurable_of_countable _) measurable_const, rfl⟩

lemma measurableSet_returnAt (n : ℕ) : MeasurableSet (returnAt n) :=
  incrementFiltration.le n _ (measurableSet_returnAt_filtration n)

lemma measurableSet_firstReturnAt_filtration (n : ℕ) :
    MeasurableSet[incrementFiltration n] (firstReturnAt n) := by
  by_cases hn : 0 < n
  · have hreturn : MeasurableSet[incrementFiltration n] (returnAt n) :=
      measurableSet_returnAt_filtration n
    have hbefore : MeasurableSet[incrementFiltration n]
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n), (returnAt j)ᶜ) := by
      exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        MeasurableSet.iInter fun hj ↦
          ((incrementFiltration.mono (Nat.le_of_lt hj)) _
            (measurableSet_returnAt_filtration j)).compl
    have heq : firstReturnAt n = returnAt n ∩
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n), (returnAt j)ᶜ) := by
      ext ω
      simp [firstReturnAt, returnAt, hn]
    rw [heq]
    exact hreturn.inter hbefore
  · have heq : firstReturnAt n = ∅ := by
      ext ω
      simp [firstReturnAt, hn]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma measurableSet_firstReturnAt (n : ℕ) : MeasurableSet (firstReturnAt n) :=
  incrementFiltration.le n _ (measurableSet_firstReturnAt_filtration n)

lemma firstReturnAt_subset_returnAt (n : ℕ) : firstReturnAt n ⊆ returnAt n := by
  intro ω hω
  exact hω.2.1

lemma firstReturnAt_pairwise_disjoint :
    Pairwise fun i j ↦ Disjoint (firstReturnAt i) (firstReturnAt j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro ω hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hj.2.2 i hi.1 hlt) hi.2.1
  · exact hij heq
  · exact (hi.2.2 j hj.1 hgt) hj.2.1

lemma firstReturnAt_exists_of_return {ω : StepPath} {n : ℕ} (hn : 0 < n)
    (hreturn : ω ∈ returnAt n) :
    ∃ k ∈ Finset.Icc 1 n, ω ∈ firstReturnAt k := by
  let k := Nat.find (show ∃ k, 0 < k ∧ trajectory ω k = (0, 0) from
    ⟨n, hn, hreturn⟩)
  have hk := Nat.find_spec (show ∃ k, 0 < k ∧ trajectory ω k = (0, 0) from
    ⟨n, hn, hreturn⟩)
  have hkn : k ≤ n := Nat.find_min' _ ⟨hn, hreturn⟩
  refine ⟨k, Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hk.1, hkn⟩,
    hk.1, hk.2, ?_⟩
  intro j hjpos hjlt hjzero
  exact (Nat.not_lt_of_ge (Nat.find_min'
    (show ∃ k, 0 < k ∧ trajectory ω k = (0, 0) from ⟨n, hn, hreturn⟩)
    ⟨hjpos, hjzero⟩)) hjlt

lemma returnAt_subset_firstReturn_relative_union {n : ℕ} (hn : 0 < n) :
    returnAt n ⊆ ⋃ k ∈ Finset.Icc 1 n, firstReturnAt k ∩ relativeReturnAt k (n - k) := by
  intro ω hω
  obtain ⟨k, hk, hkfirst⟩ := firstReturnAt_exists_of_return hn hω
  rw [mem_iUnion₂]
  refine ⟨k, hk, hkfirst, ?_⟩
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  change trajectory ω (k + (n - k)) - trajectory ω k = (0, 0)
  rw [Nat.add_sub_of_le hkn, hω, hkfirst.2.1]
  change (0 : Point) = 0
  rfl

lemma isMeasurableAtStopping_firstReturnAt_const (k : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ k) (firstReturnAt k) := by
  intro n
  by_cases hnk : n = k
  · subst n
    simpa using measurableSet_firstReturnAt_filtration k
  · have heq : firstReturnAt k ∩ {ω : StepPath | k = n} = ∅ := by
      ext ω
      simp [Ne.symm hnk]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma relativeReturnAt_eq_postStoppingBlock_preimage (n m : ℕ) :
    relativeReturnAt n m =
      postStoppingBlock (fun _ : StepPath ↦ n) m ⁻¹'
        {u | markovBlockDisplacement u = (0, 0)} := by
  ext ω
  simp only [relativeReturnAt, mem_ofPred_eq, mem_preimage]
  rw [show postStoppingBlock (fun _ : StepPath ↦ n) m ω = stepBlock n m ω from rfl]
  rw [show markovBlockDisplacement (stepBlock n m ω) =
      trajectory (shiftSteps n ω) m by
        exact (trajectory_eq_markovBlockDisplacement_stepPrefix (shiftSteps n ω) m).symm]
  rw [← trajectory_add_sub_trajectory]

lemma fairBlock_zero_displacement (m : ℕ) :
    fairBlock m {u | markovBlockDisplacement u = (0, 0)} = fairSteps (returnAt m) := by
  have hset : stepBlock 0 m ⁻¹' {u | markovBlockDisplacement u = (0, 0)} =
      returnAt m := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, returnAt]
    rw [show stepBlock 0 m ω = stepPrefix m ω by ext j; simp [stepBlock, stepPrefix]]
    rw [← trajectory_eq_markovBlockDisplacement_stepPrefix]
  rw [← fairSteps_map_stepBlock 0 m]
  rw [Measure.map_apply (measurable_stepBlock 0 m)
    (measurableSet_eq_fun (measurable_of_countable _) measurable_const)]
  rw [hset]

lemma measure_firstReturnAt_inter_relativeReturnAt (k m : ℕ) :
    fairSteps (firstReturnAt k ∩ relativeReturnAt k m) =
      fairSteps (firstReturnAt k) * fairSteps (returnAt m) := by
  rw [relativeReturnAt_eq_postStoppingBlock_preimage]
  rw [strongMarkov_stoppedEvent_set (isFiniteStoppingTime_const k)
    (isMeasurableAtStopping_firstReturnAt_const k) m
    {u | markovBlockDisplacement u = (0, 0)}]
  rw [fairBlock_zero_displacement]

lemma firstReturn_relative_subset_returnAt {n k : ℕ} (hk : k ≤ n) :
    firstReturnAt k ∩ relativeReturnAt k (n - k) ⊆ returnAt n := by
  intro ω hω
  change trajectory ω n = (0, 0)
  have hrelative : trajectory ω (k + (n - k)) - trajectory ω k = (0, 0) := hω.2
  rw [Nat.add_sub_of_le hk, hω.1.2.1] at hrelative
  change trajectory ω n - (0 : Point) = 0 at hrelative
  change trajectory ω n = (0 : Point)
  simpa using hrelative

lemma returnAt_eq_firstReturn_relative_union {n : ℕ} (hn : 0 < n) :
    returnAt n = ⋃ k ∈ Finset.Icc 1 n,
      firstReturnAt k ∩ relativeReturnAt k (n - k) := by
  apply Set.Subset.antisymm (returnAt_subset_firstReturn_relative_union hn)
  rw [iUnion_subset_iff]
  intro k
  rw [iUnion_subset_iff]
  intro hk
  exact firstReturn_relative_subset_returnAt (Finset.mem_Icc.mp hk).2

lemma measurableSet_relativeReturnAt (n m : ℕ) : MeasurableSet (relativeReturnAt n m) := by
  rw [relativeReturnAt_eq_postStoppingBlock_preimage]
  exact (measurable_postStoppingBlock (isFiniteStoppingTime_const n) m)
    (measurableSet_eq_fun (measurable_of_countable _) measurable_const)

lemma measurableSet_firstReturn_inter_relative (n k : ℕ) :
    MeasurableSet (firstReturnAt k ∩ relativeReturnAt k (n - k)) :=
  (measurableSet_firstReturnAt k).inter (measurableSet_relativeReturnAt k (n - k))

lemma firstReturn_relative_pairwiseDisjoint (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ)
      fun k ↦ firstReturnAt k ∩ relativeReturnAt k (n - k) := by
  intro i hi j hj hij
  exact (firstReturnAt_pairwise_disjoint hij).mono inter_subset_left inter_subset_left

lemma measure_returnAt_renewal {n : ℕ} (hn : 0 < n) :
    fairSteps (returnAt n) =
      ∑ k ∈ Finset.Icc 1 n,
        fairSteps (firstReturnAt k) * fairSteps (returnAt (n - k)) := by
  rw [returnAt_eq_firstReturn_relative_union hn]
  rw [measure_biUnion_finset (firstReturn_relative_pairwiseDisjoint n)
    fun k _ ↦ measurableSet_firstReturn_inter_relative n k]
  apply Finset.sum_congr rfl
  intro k hk
  exact measure_firstReturnAt_inter_relativeReturnAt k (n - k)

/-! ## The renewal inequality -/

/-- Real-valued return probabilities. -/
noncomputable def returnProbability (n : ℕ) : ℝ := (fairSteps (returnAt n)).toReal

/-- Real-valued first-return probabilities. -/
noncomputable def firstReturnProbability (n : ℕ) : ℝ :=
  (fairSteps (firstReturnAt n)).toReal

lemma returnProbability_nonneg (n : ℕ) : 0 ≤ returnProbability n :=
  ENNReal.toReal_nonneg

lemma firstReturnProbability_nonneg (n : ℕ) : 0 ≤ firstReturnProbability n :=
  ENNReal.toReal_nonneg

@[simp] lemma returnProbability_zero : returnProbability 0 = 1 := by
  have hset : returnAt 0 = Set.univ := by
    ext ω
    simp [returnAt]
  simp [returnProbability, hset]

@[simp] lemma firstReturnProbability_zero : firstReturnProbability 0 = 0 := by
  have hset : firstReturnAt 0 = ∅ := by
    ext ω
    simp [firstReturnAt]
  simp [firstReturnProbability, hset]

lemma fairSteps_returnAt_eq_simpleRandomWalk (n : ℕ) :
    fairSteps (returnAt n) = simpleRandomWalk {s | s n = (0, 0)} := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)]
  congr 1

lemma not_summable_returnProbability : ¬Summable returnProbability := by
  intro h
  apply not_summable_all_simpleRandomWalk_return_probabilities
  convert h using 1
  funext n
  rw [returnProbability, fairSteps_returnAt_eq_simpleRandomWalk]

lemma summable_firstReturnProbability : Summable firstReturnProbability := by
  exact summable_measure_toReal measurableSet_firstReturnAt firstReturnAt_pairwise_disjoint

lemma returnProbability_le_renewal_sum {n : ℕ} (hn : 0 < n) :
    returnProbability n ≤
      ∑ k ∈ Finset.Icc 1 n, firstReturnProbability k * returnProbability (n - k) := by
  have hmeasure : fairSteps (returnAt n) ≤
      ∑ k ∈ Finset.Icc 1 n,
        fairSteps (firstReturnAt k ∩ relativeReturnAt k (n - k)) :=
    (measure_mono (returnAt_subset_firstReturn_relative_union hn)).trans
      (measure_biUnion_finset_le (μ := fairSteps) (Finset.Icc 1 n)
        fun k ↦ firstReturnAt k ∩ relativeReturnAt k (n - k))
  calc
    returnProbability n = (fairSteps (returnAt n)).toReal := rfl
    _ ≤ (∑ k ∈ Finset.Icc 1 n,
        fairSteps (firstReturnAt k ∩ relativeReturnAt k (n - k))).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _
      · exact hmeasure
    _ = ∑ k ∈ Finset.Icc 1 n,
        firstReturnProbability k * returnProbability (n - k) := by
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [measure_firstReturnAt_inter_relativeReturnAt, ENNReal.toReal_mul]
        rfl
      · intro k hk
        exact measure_ne_top _ _

lemma returnProbability_le_renewal_range (n : ℕ) :
    returnProbability (n + 1) ≤
      ∑ k ∈ Finset.range (n + 1),
        firstReturnProbability (k + 1) * returnProbability (n - k) := by
  exact renewal_range_of_Icc firstReturnProbability returnProbability
    (fun m hm ↦ returnProbability_le_renewal_sum hm) n

lemma one_le_tsum_firstReturnProbability :
    1 ≤ ∑' n, firstReturnProbability n := by
  exact one_le_tsum_of_not_summable_renewal firstReturnProbability returnProbability
    firstReturnProbability_nonneg returnProbability_nonneg returnProbability_zero
    returnProbability_le_renewal_range summable_firstReturnProbability
    not_summable_returnProbability

lemma tsum_firstReturnProbability_le_one :
    (∑' n, firstReturnProbability n) ≤ 1 := by
  have hmeasure : (∑' n, fairSteps (firstReturnAt n)) ≤ 1 := by
    rw [← measure_iUnion firstReturnAt_pairwise_disjoint measurableSet_firstReturnAt]
    exact prob_le_one
  calc
    (∑' n, firstReturnProbability n) =
        (∑' n, fairSteps (firstReturnAt n)).toReal := by
      rw [ENNReal.tsum_toReal_eq fun n ↦ measure_ne_top fairSteps (firstReturnAt n)]
      rfl
    _ ≤ (1 : ℝ≥0∞).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.one_ne_top
      · exact hmeasure
    _ = 1 := by simp

theorem tsum_firstReturnProbability_eq_one :
    (∑' n, firstReturnProbability n) = 1 :=
  le_antisymm tsum_firstReturnProbability_le_one one_le_tsum_firstReturnProbability

/-! ## Probability-one recurrence -/

/-- The walk returns to the origin at some strictly positive time. -/
def positiveReturnEvent : Set StepPath :=
  {ω | ∃ n, 0 < n ∧ trajectory ω n = (0, 0)}

/-- The walk returns to the origin infinitely often. -/
def infiniteReturnEvent : Set StepPath :=
  {ω | ∃ᶠ n in atTop, trajectory ω n = (0, 0)}

/-- Time `m` is the final visit to the origin. -/
def lastReturnEvent (m : ℕ) : Set StepPath :=
  {ω | trajectory ω m = (0, 0) ∧
    ∀ k, 0 < k → trajectory ω (m + k) ≠ (0, 0)}

lemma positiveReturnEvent_eq_iUnion_firstReturnAt :
    positiveReturnEvent = ⋃ n, firstReturnAt n := by
  ext ω
  simp only [positiveReturnEvent, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨n, hn, hreturn⟩
    obtain ⟨k, hk, hkfirst⟩ :=
      firstReturnAt_exists_of_return hn (show ω ∈ returnAt n from hreturn)
    exact ⟨k, hkfirst⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1, hn.2.1⟩

lemma measurableSet_positiveReturnEvent : MeasurableSet positiveReturnEvent := by
  rw [positiveReturnEvent_eq_iUnion_firstReturnAt]
  exact MeasurableSet.iUnion measurableSet_firstReturnAt

theorem fairSteps_positiveReturnEvent : fairSteps positiveReturnEvent = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [positiveReturnEvent_eq_iUnion_firstReturnAt]
  rw [measure_iUnion firstReturnAt_pairwise_disjoint measurableSet_firstReturnAt]
  rw [ENNReal.tsum_toReal_eq fun n ↦ measure_ne_top fairSteps (firstReturnAt n)]
  exact tsum_firstReturnProbability_eq_one

lemma measurableSet_infiniteReturnEvent : MeasurableSet infiniteReturnEvent := by
  rw [infiniteReturnEvent, show
    {ω : StepPath | ∃ᶠ n in atTop, trajectory ω n = (0, 0)} =
      limsup (fun n ↦ returnAt n) atTop by
        ext ω
        change (∃ᶠ n in atTop, trajectory ω n = (0, 0)) ↔
          ω ∈ limsup (fun n ↦ returnAt n) atTop
        simpa only [returnAt, mem_ofPred_eq] using
          (mem_limsup_iff_frequently_mem
            (s := fun n ↦ returnAt n) (𝓕 := atTop) (a := ω)).symm]
  exact MeasurableSet.measurableSet_limsup measurableSet_returnAt

lemma not_infiniteReturnEvent_subset_iUnion_lastReturnEvent :
    infiniteReturnEventᶜ ⊆ ⋃ m, lastReturnEvent m := by
  intro ω hω
  have hnot : ¬ ∃ᶠ n in atTop, trajectory ω n = (0, 0) := by
    simpa [infiniteReturnEvent] using hω
  have hev : ∀ᶠ n in atTop, trajectory ω n ≠ (0, 0) :=
    (not_frequently).mp hnot
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hNpos : 0 < N := by
    by_contra h
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos h
    have hcontra := hN 0 (by simp [hNzero])
    exact hcontra (trajectory_zero ω)
  let R : Finset ℕ := (Finset.range N).filter fun n ↦ trajectory ω n = (0, 0)
  have hR : R.Nonempty := by
    refine ⟨0, ?_⟩
    simp [R, hNpos, trajectory_zero]
  let m : ℕ := R.max' hR
  have hmR : m ∈ R := Finset.max'_mem R hR
  have hmReturn : trajectory ω m = (0, 0) := (Finset.mem_filter.mp hmR).2
  refine mem_iUnion.mpr ⟨m, hmReturn, ?_⟩
  intro k hk hmkReturn
  by_cases hmkN : m + k < N
  · have hmkR : m + k ∈ R :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmkN, hmkReturn⟩
    have hle : m + k ≤ m := Finset.le_max' R (m + k) hmkR
    omega
  · exact hN (m + k) (Nat.le_of_not_gt hmkN) hmkReturn

lemma lastReturnEvent_subset_shift_noPositiveReturn (m : ℕ) :
    lastReturnEvent m ⊆ shiftSteps m ⁻¹' positiveReturnEventᶜ := by
  intro ω hω
  rw [mem_preimage, mem_compl_iff]
  intro htail
  obtain ⟨k, hk, hkzero⟩ := htail
  apply hω.2 k hk
  have hadd := trajectory_add_sub_trajectory ω m k
  rw [hω.1] at hadd
  change trajectory ω (m + k) - (0 : Point) =
    trajectory (shiftSteps m ω) k at hadd
  simpa only [sub_zero] using hadd.trans hkzero

theorem fairSteps_infinite_returns :
    ∀ᵐ ω ∂fairSteps, ∃ᶠ n in atTop, trajectory ω n = (0, 0) := by
  have hnoReturn : fairSteps positiveReturnEventᶜ = 0 := by
    rw [measure_compl measurableSet_positiveReturnEvent
      (measure_ne_top fairSteps positiveReturnEvent), fairSteps_positiveReturnEvent, measure_univ]
    norm_num
  have hlast : ∀ m, fairSteps (lastReturnEvent m) = 0 := by
    intro m
    apply measure_mono_null (lastReturnEvent_subset_shift_noPositiveReturn m)
    rw [← Measure.map_apply (measurable_shiftSteps m)
      measurableSet_positiveReturnEvent.compl, fairSteps_map_shiftSteps, hnoReturn]
  have hcompl : fairSteps infiniteReturnEventᶜ = 0 := by
    apply le_zero_iff.mp
    calc
      fairSteps infiniteReturnEventᶜ ≤ fairSteps (⋃ m, lastReturnEvent m) :=
        measure_mono not_infiniteReturnEvent_subset_iUnion_lastReturnEvent
      _ = 0 := measure_iUnion_null hlast
  rw [ae_iff]
  change fairSteps infiniteReturnEventᶜ = 0
  exact hcompl

/-! ## Divergence of the maximal local time -/

lemma localTime_eq_sum_indicator (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = ∑ k ∈ Finset.range (n + 1), if s k = x then 1 else 0 := by
  rw [localTime, localTimePrefix, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun k ↦ if s k = x then 1 else 0) (n + 1)

lemma localTime_succ (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s (n + 1) x = localTime s n x + if s (n + 1) = x then 1 else 0 := by
  calc
    localTime s (n + 1) x =
        ∑ k ∈ Finset.range (n + 2), if s k = x then 1 else 0 := by
      simpa [Nat.add_assoc] using localTime_eq_sum_indicator s (n + 1) x
    _ = (∑ k ∈ Finset.range (n + 1), if s k = x then 1 else 0) +
        if s (n + 1) = x then 1 else 0 := by
      exact Finset.sum_range_succ _ _
    _ = localTime s n x + if s (n + 1) = x then 1 else 0 := by
      rw [localTime_eq_sum_indicator]

lemma localTime_le_succ (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x ≤ localTime s (n + 1) x := by
  rw [localTime_succ]
  omega

lemma monotone_localTime (s : WalkPath) (x : Point) :
    Monotone fun n ↦ localTime s n x :=
  monotone_nat_of_le_succ fun n ↦ localTime_le_succ s n x

lemma localTime_eq_card_filter_range (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = ((Finset.range (n + 1)).filter (fun k ↦ s k = x)).card := by
  rw [localTime_eq_sum_indicator, Finset.card_filter]

lemma tendsto_localTime_atTop_of_frequently (s : WalkPath) (x : Point)
    (hrec : ∃ᶠ n in atTop, s n = x) :
    Tendsto (fun n ↦ localTime s n x) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hinf : Set.Infinite {n : ℕ | s n = x} :=
    Nat.frequently_atTop_iff_infinite.mp hrec
  obtain ⟨t, ht, htcard⟩ := hinf.exists_subset_card_eq b
  obtain ⟨N, htN⟩ := Finset.exists_nat_subset_range t
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [localTime_eq_card_filter_range, ← htcard]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter]
  exact ⟨Finset.range_mono (hn.trans (Nat.le_succ n)) (htN hk), ht hk⟩

lemma eventually_mem_visitedSites_of_frequently (s : WalkPath) (x : Point)
    (hrec : ∃ᶠ n in atTop, s n = x) :
    ∀ᶠ n in atTop, x ∈ visitedSites s n := by
  obtain ⟨k, hk⟩ := hrec.exists
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [visitedSites, mem_visitedPrefix_iff]
  exact ⟨⟨k, Nat.lt_succ_of_le hn⟩, hk⟩

lemma localTime_le_maxLocalTime (s : WalkPath) (n : ℕ) (x : Point)
    (hx : x ∈ visitedSites s n) :
    localTime s n x ≤ maxLocalTime s n :=
  localTimePrefix_le_maxLocalTimePrefix (pathPrefix s n) hx

lemma tendsto_maxLocalTime_atTop_of_frequently (s : WalkPath) (x : Point)
    (hrec : ∃ᶠ n in atTop, s n = x) :
    Tendsto (maxLocalTime s) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlocal := tendsto_atTop.mp (tendsto_localTime_atTop_of_frequently s x hrec) b
  filter_upwards [hlocal, eventually_mem_visitedSites_of_frequently s x hrec]
    with n hbn hxn
  exact hbn.trans (localTime_le_maxLocalTime s n x hxn)

lemma measurable_maxLocalTime (n : ℕ) :
    Measurable fun s : WalkPath ↦ maxLocalTime s n := by
  exact (measurable_of_countable
    (fun u : Fin (n + 1) → Point ↦ maxLocalTimePrefix u)).comp (measurable_pathPrefix n)

lemma measurableSet_tendsto_maxLocalTime :
    MeasurableSet {s : WalkPath | Tendsto (maxLocalTime s) atTop atTop} := by
  let E : Set WalkPath :=
    ⋂ b : ℕ, ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n},
      {s : WalkPath | b ≤ maxLocalTime s n}
  have hset : {s : WalkPath | Tendsto (maxLocalTime s) atTop atTop} = E := by
    ext s
    simp only [Set.mem_ofPred_eq, E, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hs b
      obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hs b)
      exact ⟨N, fun n ↦ hN n n.property⟩
    · intro hs
      rw [tendsto_atTop]
      intro b
      obtain ⟨N, hN⟩ := hs b
      exact eventually_atTop.mpr ⟨N, fun n hn ↦ hN ⟨n, hn⟩⟩
  rw [hset]
  exact MeasurableSet.iInter fun b ↦ MeasurableSet.iUnion fun N ↦
    MeasurableSet.iInter fun n ↦
      measurableSet_le measurable_const (measurable_maxLocalTime n)

/-- Planar simple random walk has maximal local time tending to infinity almost surely. -/
theorem simpleRandomWalk_maxLocalTime_tendsto :
    ∀ᵐ s ∂simpleRandomWalk, Tendsto (maxLocalTime s) atTop atTop := by
  rw [simpleRandomWalk, ae_map_iff measurable_trajectory.aemeasurable
    measurableSet_tendsto_maxLocalTime]
  filter_upwards [fairSteps_infinite_returns] with ω hω
  exact tendsto_maxLocalTime_atTop_of_frequently (trajectory ω) (0, 0) hω

/-- Alias exposing the recurrence bridge in the name used by the main HLOZ development. -/
theorem ae_maxLocalTime_tendsto_atTop :
    ∀ᵐ s ∂simpleRandomWalk, Tendsto (maxLocalTime s) atTop atTop :=
  simpleRandomWalk_maxLocalTime_tendsto

end Erdos1165
