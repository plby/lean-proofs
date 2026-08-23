import ErdosProblems.Erdos1166.Erdos1166HLOZExternalPairPath

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

namespace Erdos1166

open HLOZUrn

/-- Exact joint cylinder for a run-length list and a terminal-label list. -/
def pairRunsAndLabelsEqFrom
    (start : ℕ) (lengths : List ℕ) (labels : List IncrementPair) :
    Set (ℕ → Direction) :=
  firstPairRunsWithLabelsEqFrom start (List.zip lengths labels)

theorem pairRunsAndLabels_subset_terminalLabels
    (start : ℕ) (lengths : List ℕ) (labels : List IncrementPair)
    (hlen : lengths.length = labels.length) :
    pairRunsAndLabelsEqFrom start lengths labels ⊆
      firstPairTerminalLabelsEqFrom start labels := by
  induction labels generalizing start lengths with
  | nil =>
      have : lengths = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst lengths
      simp [pairRunsAndLabelsEqFrom, firstPairRunsWithLabelsEqFrom,
        firstPairTerminalLabelsEqFrom]
  | cons p labels ih =>
      cases lengths with
      | nil => simp at hlen
      | cons t lengths =>
          intro ω hω
          rw [pairRunsAndLabelsEqFrom, List.zip_cons_cons,
            firstPairRunsWithLabelsEqFrom] at hω
          rw [firstPairTerminalLabelsEqFrom]
          apply Set.mem_iUnion.mpr
          refine ⟨t, hω.1, ?_⟩
          exact ih (start := start + t + 1) (lengths := lengths)
            (by simpa using hlen) hω.2

theorem exists_pairRunsAndLabels_of_terminalLabels
    (start : ℕ) (labels : List IncrementPair) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairTerminalLabelsEqFrom start labels) :
    ∃ lengths : List ℕ, lengths.length = labels.length ∧
      ω ∈ pairRunsAndLabelsEqFrom start lengths labels := by
  induction labels generalizing start with
  | nil =>
      exact ⟨[], rfl, by simp [pairRunsAndLabelsEqFrom,
        firstPairRunsWithLabelsEqFrom]⟩
  | cons p labels ih =>
      rw [firstPairTerminalLabelsEqFrom] at hω
      rcases Set.mem_iUnion.mp hω with ⟨t, ht, htail⟩
      rcases ih (start := start + t + 1) htail with
        ⟨lengths, hlen, hruns⟩
      refine ⟨t :: lengths, by simp [hlen], ?_⟩
      exact ⟨ht, hruns⟩

theorem pairRunsAndLabels_unique
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    {lengths₁ lengths₂ : List ℕ}
    (hlen₁ : lengths₁.length = labels.length)
    (hlen₂ : lengths₂.length = labels.length)
    {ω : ℕ → Direction}
    (h₁ : ω ∈ pairRunsAndLabelsEqFrom start lengths₁ labels)
    (h₂ : ω ∈ pairRunsAndLabelsEqFrom start lengths₂ labels) :
    lengths₁ = lengths₂ := by
  induction labels generalizing start lengths₁ lengths₂ with
  | nil =>
      exact (List.eq_nil_of_length_eq_zero (by simpa using hlen₁)).trans
        (List.eq_nil_of_length_eq_zero (by simpa using hlen₂)).symm
  | cons p labels ih =>
      cases lengths₁ with
      | nil => simp at hlen₁
      | cons t ts =>
          cases lengths₂ with
          | nil => simp at hlen₂
          | cons u us =>
              rw [pairRunsAndLabelsEqFrom, List.zip_cons_cons,
                firstPairRunsWithLabelsEqFrom] at h₁ h₂
              have hp : p ≠ distinguishedIncrementPair :=
                hnondist p (by simp)
              have htu : t = u := by
                by_contra hne
                exact Set.disjoint_left.mp
                  (disjoint_distinguishedPairRunSegmentWithLabel start hp hne)
                    h₁.1 h₂.1
              subst u
              have htail : ts = us := ih
                (start := start + t + 1)
                (fun p hp ↦ hnondist p (by simp [hp]))
                (by simpa using hlen₁) (by simpa using hlen₂)
                h₁.2 h₂.2
              rw [htail]

/-- The finite vector of lazy-run counts associated with fixed successive
terminal labels.  Off the corresponding terminal-label atom it is assigned
an arbitrary default; conditioning removes that irrelevant part. -/
noncomputable def conditionalPairRunVector
    (start : ℕ) (labels : List IncrementPair) :
    (ℕ → Direction) → (Fin labels.length → ℕ) := by
  classical
  exact fun ω ↦
    if h : ∃ v : Fin labels.length → ℕ,
        ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn v) labels then
      Classical.choose h
    else 0

theorem exists_pairRunVector_of_terminalLabels
    (start : ℕ) (labels : List IncrementPair) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairTerminalLabelsEqFrom start labels) :
    ∃ v : Fin labels.length → ℕ,
      ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn v) labels := by
  rcases exists_pairRunsAndLabels_of_terminalLabels start labels hω with
    ⟨lengths, hlen, hruns⟩
  let v : Fin labels.length → ℕ := fun i ↦
    lengths.get (Fin.cast hlen.symm i)
  refine ⟨v, ?_⟩
  have hofFn : List.ofFn v = lengths := by
    apply List.ext_get
    · simp [v, hlen]
    · intro n h₁ h₂
      simp [v]
  simpa [hofFn] using hruns

theorem conditionalPairRunVector_eq_iff
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (v : Fin labels.length → ℕ) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairTerminalLabelsEqFrom start labels) :
    conditionalPairRunVector start labels ω = v ↔
      ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn v) labels := by
  classical
  have hex := exists_pairRunVector_of_terminalLabels start labels hω
  rw [conditionalPairRunVector, dif_pos hex]
  let chosen : Fin labels.length → ℕ := Classical.choose hex
  have hchosen : ω ∈ pairRunsAndLabelsEqFrom start
      (List.ofFn chosen) labels := Classical.choose_spec hex
  have huniq (w : Fin labels.length → ℕ)
      (hw : ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn w) labels) :
      chosen = w := by
    apply List.ofFn_injective
    exact pairRunsAndLabels_unique start labels hnondist
      (by simp) (by simp) hchosen hw
  change chosen = v ↔
    ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn v) labels
  constructor
  · intro h
    rwa [h] at hchosen
  · intro hv
    exact huniq v hv

theorem measurableSet_pairRunsAndLabelsEqFrom
    (start : ℕ) (lengths : List ℕ) (labels : List IncrementPair) :
    MeasurableSet (pairRunsAndLabelsEqFrom start lengths labels) := by
  unfold pairRunsAndLabelsEqFrom
  exact iidTail_le (2 * start) _
    (measurableSet_firstPairRunsWithLabelsEqFrom_iidTail start
      (List.zip lengths labels))

theorem measurableSet_externalPathAtom
    (start : ℕ) (labels : List IncrementPair) :
    MeasurableSet (firstPairExternalPathEqFrom start
      (externalPathFromLabels labels)) := by
  rw [firstPairExternalPathEqFrom_reconstructed]
  exact iidTail_le (2 * start) _
    (measurableSet_firstPairTerminalLabelsEqFrom_iidTail start labels)

theorem externalPathAtom_prob
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairExternalPathEqFrom start
      (externalPathFromLabels labels)) =
        ((15 : ENNReal)⁻¹) ^ labels.length := by
  rw [firstPairExternalPathEqFrom_reconstructed]
  exact firstPairTerminalLabelsEqFrom_prob start labels hnondist

theorem externalPathAtom_pos
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairExternalPathEqFrom start
      (externalPathFromLabels labels)) ≠ 0 := by
  rw [externalPathAtom_prob start labels hnondist]
  exact pow_ne_zero _ (by norm_num)

theorem externalPathAtom_inter_runVector_fiber
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (v : Fin labels.length → ℕ) :
    firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
        { ω | conditionalPairRunVector start labels ω = v } =
      pairRunsAndLabelsEqFrom start (List.ofFn v) labels := by
  rw [firstPairExternalPathEqFrom_reconstructed]
  ext ω
  constructor
  · rintro ⟨hlabel, hv⟩
    exact (conditionalPairRunVector_eq_iff start labels hnondist v hlabel).mp hv
  · intro hruns
    have hlabel : ω ∈ firstPairTerminalLabelsEqFrom start labels :=
      pairRunsAndLabels_subset_terminalLabels start (List.ofFn v) labels
        (by simp) hruns
    exact ⟨hlabel,
      (conditionalPairRunVector_eq_iff start labels hnondist v hlabel).mpr hruns⟩

theorem measurableSet_conditionalPairRunVector_fiber
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (v : Fin labels.length → ℕ) :
    MeasurableSet { ω | conditionalPairRunVector start labels ω = v } := by
  let A := firstPairTerminalLabelsEqFrom start labels
  let J := pairRunsAndLabelsEqFrom start (List.ofFn v) labels
  have hset : { ω | conditionalPairRunVector start labels ω = v } =
      if v = 0 then Aᶜ ∪ J else J := by
    ext ω
    by_cases hA : ω ∈ A
    · have hiff := conditionalPairRunVector_eq_iff start labels hnondist v hA
      by_cases hv : v = 0
      · simpa [hv, A, J, hA] using hiff
      · simpa [hv, A, J, hA] using hiff
    · have hnone : ¬ ∃ w : Fin labels.length → ℕ,
          ω ∈ pairRunsAndLabelsEqFrom start (List.ofFn w) labels := by
        rintro ⟨w, hw⟩
        apply hA
        exact pairRunsAndLabels_subset_terminalLabels start (List.ofFn w) labels
          (by simp) hw
      have hvalue : conditionalPairRunVector start labels ω = 0 := by
        rw [conditionalPairRunVector, dif_neg hnone]
      have hnotJ : ω ∉ J := by
        intro hJ
        exact hA (pairRunsAndLabels_subset_terminalLabels start (List.ofFn v) labels
          (by simp) hJ)
      by_cases hv : v = 0
      · subst v
        simp [hvalue, A, J, hA, hnotJ]
      · have hzero_ne : (0 : Fin labels.length → ℕ) ≠ v :=
          fun h ↦ hv h.symm
        simp [hvalue, J, hnotJ, hv, hzero_ne]
  rw [hset]
  split_ifs
  · exact (measurableSet_firstPairTerminalLabelsEqFrom_iidTail start labels
      |> iidTail_le (2 * start) _).compl.union
        (measurableSet_pairRunsAndLabelsEqFrom start (List.ofFn v) labels)
  · exact measurableSet_pairRunsAndLabelsEqFrom start (List.ofFn v) labels

theorem measurable_conditionalPairRunVector
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    Measurable (conditionalPairRunVector start labels) := by
  apply measurable_to_countable'
  exact measurableSet_conditionalPairRunVector_fiber start labels hnondist

theorem runMeasure_singleton_ennreal (t : ℕ) :
    runMeasure {t} = (15 : ENNReal) / 16 ^ (t + 1) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top runMeasure {t}) (by finiteness)).mp
  rw [← measureReal_def, runMeasure_real_singleton]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
  norm_num
  rw [div_pow, pow_succ]
  ring

theorem runVectorMeasure_singleton_ennreal
    (q : ℕ) (v : Fin q → ℕ) :
    runVectorMeasure q {v} =
      ∏ i, (15 : ENNReal) / 16 ^ (v i + 1) := by
  rw [runVectorMeasure_singleton]
  apply Finset.prod_congr rfl
  intro i hi
  exact runMeasure_singleton_ennreal (v i)

theorem pairRunsAndLabels_conditional_singleton
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (v : Fin labels.length → ℕ) :
    incrementLaw[
      { ω | conditionalPairRunVector start labels ω = v } |
      firstPairExternalPathEqFrom start (externalPathFromLabels labels)] =
        runVectorMeasure labels.length {v} := by
  let A := firstPairExternalPathEqFrom start (externalPathFromLabels labels)
  have hA : MeasurableSet A := measurableSet_externalPathAtom start labels
  rw [cond_apply hA]
  rw [externalPathAtom_inter_runVector_fiber start labels hnondist v]
  rw [mul_comm]
  change incrementLaw (pairRunsAndLabelsEqFrom start (List.ofFn v) labels) /
      incrementLaw A = _
  have hmapSnd : (List.zip (List.ofFn v) labels).map Prod.snd = labels :=
    List.map_snd_zip (by simp)
  have hnondistRuns : ∀ run ∈ List.zip (List.ofFn v) labels,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrun
    apply hnondist run.2
    rw [← hmapSnd]
    exact List.mem_map.mpr ⟨run, hrun, rfl⟩
  have hratio := firstPairRunLengths_conditional_on_externalPath
    start (List.zip (List.ofFn v) labels) hnondistRuns
  rw [hmapSnd] at hratio
  change incrementLaw (firstPairRunsWithLabelsEqFrom start
      (List.zip (List.ofFn v) labels)) /
        incrementLaw A = _ at hratio
  change incrementLaw (firstPairRunsWithLabelsEqFrom start
      (List.zip (List.ofFn v) labels)) /
        incrementLaw A = _
  rw [hratio, runVectorMeasure_singleton_ennreal]
  rw [← List.prod_ofFn]
  congr 1
  change (List.zip (List.ofFn v) labels).map
      ((fun t : ℕ ↦ (15 : ENNReal) / 16 ^ (t + 1)) ∘ Prod.fst) = _
  rw [← List.map_map, List.map_fst_zip (by simp)]
  rw [List.map_ofFn]
  congr 1

/-- Actual conditional law: on a positive fixed external-path atom, the
finite vector of lazy-run counts has the iid geometric `(15/16)` product
measure, hence the equality applies to every measurable vector event. -/
theorem conditionalPairRunVector_hasLaw
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    HasLaw (conditionalPairRunVector start labels)
      (runVectorMeasure labels.length)
      incrementLaw[|firstPairExternalPathEqFrom start
        (externalPathFromLabels labels)] := by
  constructor
  · exact (measurable_conditionalPairRunVector start labels hnondist).aemeasurable
  · apply Measure.ext_of_singleton
    intro v
    rw [Measure.map_apply
      (measurable_conditionalPairRunVector start labels hnondist)
      (measurableSet_singleton v)]
    exact pairRunsAndLabels_conditional_singleton start labels hnondist v

theorem conditionalExternalPath_isProbabilityMeasure
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    IsProbabilityMeasure
      incrementLaw[|firstPairExternalPathEqFrom start
        (externalPathFromLabels labels)] :=
  cond_isProbabilityMeasure (externalPathAtom_pos start labels hnondist)

/-! ### Restart at a random increment horizon -/

/-- The full sequence of increments viewed from a random increment horizon. -/
def incrementShiftAfter (τ : (ℕ → Direction) → ℕ)
    (ω : ℕ → Direction) (n : ℕ) : Direction :=
  ω (τ ω + n)

theorem measurable_incrementShiftAfter
    {τ : (ℕ → Direction) → ℕ} (hτ : Measurable τ) :
    Measurable (incrementShiftAfter τ) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro d
  change MeasurableSet { ω | incrementShiftAfter τ ω n = d }
  have heq : { ω | incrementShiftAfter τ ω n = d } =
      ⋃ k : ℕ, { ω | τ ω = k } ∩ { ω | ω (k + n) = d } := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      incrementShiftAfter]
    constructor
    · intro h
      exact ⟨τ ω, rfl, h⟩
    · rintro ⟨k, hk, hd⟩
      simpa [hk] using hd
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  have hcoord : MeasurableSet { ω : ℕ → Direction | ω (k + n) = d } := by
    change MeasurableSet ((fun ω : ℕ → Direction ↦ ω (k + n)) ⁻¹' {d})
    exact (measurable_pi_apply (k + n)) (measurableSet_singleton d)
  exact (hτ (measurableSet_singleton k)).inter hcoord

theorem measurableSet_pastEvent
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k })) :
    MeasurableSet A := by
  have hEq : A = ⋃ k : ℕ, A ∩ { ω | τ ω = k } := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨τ ω, h, rfl⟩, fun h ↦ h.choose_spec.1⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k ↦ iidHistory_le k _ (hA k)

/-- Measure-level IID restart: conditional on a positive past event, every
finite block beginning at the random horizon has the fresh product law. -/
theorem iidBlockAfter_hasLaw_cond
    (τ : (ℕ → Direction) → ℕ) (m : ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0) :
    HasLaw (iidBlockAfter (X := Direction) τ m)
      (Measure.infinitePi fun _ : Fin m ↦ directionLaw)
      incrementLaw[|A] := by
  have hAmeas : MeasurableSet A := measurableSet_pastEvent τ A hA
  have hblock : Measurable (iidBlockAfter (X := Direction) τ m) := by
    apply measurable_pi_lambda
    intro i
    change Measurable fun ω ↦ incrementShiftAfter τ ω (i : ℕ)
    exact (measurable_pi_apply (i : ℕ)).comp
      (measurable_incrementShiftAfter hτ)
  constructor
  · exact hblock.aemeasurable
  · ext B hB
    rw [Measure.map_apply hblock hB, cond_apply hAmeas]
    change (incrementLaw A)⁻¹ *
        (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
          (A ∩ iidBlockAfter (X := Direction) τ m ⁻¹' B) = _
    rw [measure_inter_iidBlockAfter_eq_mul directionLaw τ m A hA hB]
    change ((Measure.infinitePi fun _ : ℕ ↦ directionLaw) A)⁻¹ *
        ((Measure.infinitePi fun _ : ℕ ↦ directionLaw) A *
          (Measure.infinitePi fun _ : Fin m ↦ directionLaw) B) = _
    have hApos' : (Measure.infinitePi fun _ : ℕ ↦ directionLaw) A ≠ 0 := by
      simpa [incrementLaw] using hApos
    rw [← mul_assoc, ENNReal.inv_mul_cancel hApos'
      (measure_ne_top (Measure.infinitePi fun _ : ℕ ↦ directionLaw) A),
      one_mul]

/-- Strong restart for the entire iid increment sequence, obtained from the
finite-block restart theorem by the finite-cylinder characterization of
`Measure.infinitePi`. -/
theorem incrementShiftAfter_hasLaw_cond
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0) :
    HasLaw (incrementShiftAfter τ) incrementLaw incrementLaw[|A] := by
  have hshift : Measurable (incrementShiftAfter τ) :=
    measurable_incrementShiftAfter hτ
  constructor
  · exact hshift.aemeasurable
  · unfold incrementLaw
    apply Measure.eq_infinitePi
    intro s t ht
    let m := s.sup id + 1
    have himem (i : ℕ) (hi : i ∈ s) : i < m := by
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    let B : Set (Fin m → Direction) :=
      { b | ∀ i, ∀ hi : i ∈ s, b ⟨i, himem i hi⟩ ∈ t i }
    have hB : MeasurableSet B := by measurability
    have hshiftEvent : incrementShiftAfter τ ⁻¹' Set.pi s t =
        iidBlockAfter (X := Direction) τ m ⁻¹' B := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, B, Set.mem_ofPred_eq,
        incrementShiftAfter, iidBlockAfter]
      simp only [Finset.mem_coe]
    have hzeroEvent : iidBlock (X := Direction) 0 m ⁻¹' B = Set.pi s t := by
      ext ω
      simp only [Set.mem_preimage, B, Set.mem_ofPred_eq, Set.mem_pi,
        iidBlock, zero_add]
      simp only [Finset.mem_coe]
    have hblock := iidBlockAfter_hasLaw_cond τ m A hτ hA hApos
    rw [Measure.map_apply hshift
      (.pi s.countable_toSet fun i hi ↦ ht i)]
    rw [hshiftEvent]
    change incrementLaw[|A]
        (iidBlockAfter (X := Direction) τ m ⁻¹' B) = _
    calc
      incrementLaw[|A]
          (iidBlockAfter (X := Direction) τ m ⁻¹' B) =
          (Measure.infinitePi fun _ : Fin m ↦ directionLaw) B :=
        hblock.measure_eq hB
      (Measure.infinitePi fun _ : Fin m ↦ directionLaw) B =
          (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
            (iidBlock (X := Direction) 0 m ⁻¹' B) := by
        rw [← iidBlock_map directionLaw 0 m,
          Measure.map_apply (measurable_iidBlock 0 m) hB]
      _ = (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
          (Set.pi s t) := by rw [hzeroEvent]
      _ = ∏ i ∈ s, directionLaw (t i) :=
        Measure.infinitePi_pi (μ := fun _ : ℕ ↦ directionLaw)
          (fun i hi ↦ ht i)

/-- Conditioning commutes with a measurable random variable having a fixed
law: pull back the conditioning event and obtain the conditioned target law. -/
theorem HasLaw.cond_preimage
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : α → β} {P : Measure α} {μ : Measure β}
    (hX : HasLaw X μ P) (hXm : Measurable X) (C : Set β)
    (hC : MeasurableSet C) :
    HasLaw X μ[|C] P[|X ⁻¹' C] := by
  constructor
  · exact hXm.aemeasurable
  · unfold ProbabilityTheory.cond
    rw [Measure.map_smul, ← Measure.restrict_map hXm hC]
    rw [hX.map_eq]
    congr 1
    rw [← hX.map_eq, Measure.map_apply hXm hC]

/-- The future external-path atom used for the second conditioning has
strictly positive probability after restart. -/
theorem externalPathAtom_after_pos
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0)
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    incrementLaw[|A]
      (incrementShiftAfter τ ⁻¹'
        firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)) ≠ 0 := by
  have hshift := incrementShiftAfter_hasLaw_cond τ A hτ hA hApos
  have heq : incrementLaw[|A]
      (incrementShiftAfter τ ⁻¹'
        firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)) =
      incrementLaw
        (firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)) :=
    hshift.measure_eq (measurableSet_externalPathAtom 0 labels)
  rw [heq]
  exact externalPathAtom_pos 0 labels hnondist

/-- Stopping-horizon form of HLOZ Proposition 4.2.  After any random
increment horizon satisfying the IIDRestart past-fiber hypotheses, and on
any positive past event `A`, conditioning further on a fixed future external
path gives iid geometric `(15/16)` lazy-run counts. -/
theorem conditionalPairRunVector_hasLaw_after
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0)
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    HasLaw
      (fun ω ↦ conditionalPairRunVector 0 labels (incrementShiftAfter τ ω))
      (runVectorMeasure labels.length)
      (incrementLaw[|A])[|
        incrementShiftAfter τ ⁻¹'
          firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)] := by
  have hshift := incrementShiftAfter_hasLaw_cond τ A hτ hA hApos
  have hshiftCond := HasLaw.cond_preimage hshift
    (measurable_incrementShiftAfter hτ)
    (firstPairExternalPathEqFrom 0 (externalPathFromLabels labels))
    (measurableSet_externalPathAtom 0 labels)
  exact (conditionalPairRunVector_hasLaw 0 labels hnondist).fun_comp hshiftCond

/-- The usual stopping-time fiber condition itself implies ordinary
measurability of a natural-valued horizon. -/
theorem measurable_of_iidStoppingTime
    {τ : (ℕ → Direction) → ℕ}
    (hτ : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      { ω | τ ω = k }) :
    Measurable τ := by
  apply measurable_to_countable'
  intro k
  change MeasurableSet { ω | τ ω = k }
  exact iidHistory_le k _ (hτ k)

/-- Stopping-time specialization (and therefore, in particular, the
bounded-stopping-horizon specialization): conditioned on the fixed future
external/deleted-path atom, every measurable event of the complete finite
run vector has the iid geometric product law. -/
theorem conditionalPairRunVector_hasLaw_after_stoppingTime
    (τ : (ℕ → Direction) → ℕ)
    (hτ : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      { ω | τ ω = k })
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    HasLaw
      (fun ω ↦ conditionalPairRunVector 0 labels (incrementShiftAfter τ ω))
      (runVectorMeasure labels.length)
      incrementLaw[|
        incrementShiftAfter τ ⁻¹'
          firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)] := by
  have hτmeas : Measurable τ := measurable_of_iidStoppingTime hτ
  have hAfiber : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (Set.univ ∩ { ω | τ ω = k }) := by
    intro k
    simpa using hτ k
  simpa using conditionalPairRunVector_hasLaw_after τ Set.univ hτmeas
    hAfiber (by simp) labels hnondist

/-- The future external-path atom at a stopping horizon is supported with
positive probability, so the conditional measure in the preceding theorem
is a probability measure. -/
theorem externalPathAtom_after_stoppingTime_pos
    (τ : (ℕ → Direction) → ℕ)
    (hτ : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      { ω | τ ω = k })
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    incrementLaw
      (incrementShiftAfter τ ⁻¹'
        firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)) ≠ 0 := by
  have hτmeas : Measurable τ := measurable_of_iidStoppingTime hτ
  have hAfiber : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (Set.univ ∩ { ω | τ ω = k }) := by
    intro k
    simpa using hτ k
  simpa using externalPathAtom_after_pos τ Set.univ hτmeas hAfiber
    (by simp) labels hnondist

/-- A pair-index stopping time becomes an increment-index stopping time when
its horizon is doubled.  This is the form used when the external process is
sampled one adjacent increment pair at a time. -/
theorem iidStoppingTime_two_mul
    {σ : (ℕ → Direction) → ℕ}
    (hσ : ∀ k, MeasurableSet[iidHistory (X := Direction) (2 * k)]
      { ω | σ ω = k }) :
    ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      { ω | 2 * σ ω = n } := by
  intro n
  by_cases heven : ∃ k, n = 2 * k
  · rcases heven with ⟨k, rfl⟩
    convert hσ k using 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    omega
  · have hempty : { ω | 2 * σ ω = n } = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact heven ⟨σ ω, h.symm⟩
    rw [hempty]
    change @MeasurableSet (ℕ → Direction) (iidHistory (X := Direction) n) ∅
    exact @MeasurableSet.empty (ℕ → Direction) (iidHistory (X := Direction) n)

/-- Pair-horizon form of the stopped conditional law.  It applies in
particular to every bounded pair stopping time measurable from the external
pair history; no bound is needed by the proof. -/
theorem conditionalPairRunVector_hasLaw_after_pairStoppingTime
    (σ : (ℕ → Direction) → ℕ)
    (hσ : ∀ k, MeasurableSet[iidHistory (X := Direction) (2 * k)]
      { ω | σ ω = k })
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    HasLaw
      (fun ω ↦ conditionalPairRunVector 0 labels
        (incrementShiftAfter (fun ω ↦ 2 * σ ω) ω))
      (runVectorMeasure labels.length)
      incrementLaw[|
        incrementShiftAfter (fun ω ↦ 2 * σ ω) ⁻¹'
          firstPairExternalPathEqFrom 0 (externalPathFromLabels labels)] :=
  conditionalPairRunVector_hasLaw_after_stoppingTime
    (fun ω ↦ 2 * σ ω) (iidStoppingTime_two_mul hσ) labels hnondist

end Erdos1166
