/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZColumnBlockGrouping

/-!
# A fresh increment after an adaptive column terminal atom

A fixed column terminal label has a random length because every active
entry contains a geometric run.  Once the complete run vector is fixed,
however, its endpoint is deterministic and the corresponding cylinder uses
only increments strictly before twice that pair endpoint.  This file records
that stopped-past fact and applies the iid restart theorem.  It is the missing
bridge between the marginal column product law and the
`lazy-vector × next-direction` law used in (4.47).
-/

namespace Erdos1166.HLOZColumnTerminalRestart

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

open HLOZColumnPairRuns HLOZColumnBlockGrouping HLOZStoppedMapLaw
  HLOZProp42InverseLaw

/-! ## The random terminal pair endpoint -/

/-- Pair index immediately after a fixed selective run list. -/
def selectivePairRunsEnd : ℕ → List SelectivePairRun → ℕ
  | start, [] => start
  | start, (some t, _) :: runs =>
      selectivePairRunsEnd (start + t + 1) runs
  | start, (none, _) :: runs =>
      selectivePairRunsEnd (start + 1) runs

theorem selectivePairRunsEnd_start_le
    (start : ℕ) (runs : List SelectivePairRun) :
    start ≤ selectivePairRunsEnd start runs := by
  induction runs generalizing start with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot with
      | none =>
          simp only [selectivePairRunsEnd]
          exact (Nat.le_add_right start 1).trans (ih (start := start + 1))
      | some t =>
          simp only [selectivePairRunsEnd]
          exact (Nat.le_add_right start (t + 1)).trans
            (ih (start := start + t + 1))

/-- A fixed decoded run list is a cylinder strictly before its terminal pair
endpoint. -/
theorem measurableSet_selectivePairRunsEqFrom_iidHistory
    (start : ℕ) (runs : List SelectivePairRun) :
    MeasurableSet[iidHistory (X := Direction)
      (2 * selectivePairRunsEnd start runs)]
      (selectivePairRunsEqFrom start runs) := by
  induction runs generalizing start with
  | nil => simp [selectivePairRunsEqFrom, selectivePairRunsEnd]
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot with
      | none =>
          rw [selectivePairRunsEqFrom]
          have hend : 2 * (start + 1) ≤
              2 * selectivePairRunsEnd (start + 1) runs :=
            Nat.mul_le_mul_left 2
              (selectivePairRunsEnd_start_le (start + 1) runs)
          exact ((iidHistory_mono_local hend) _
            (measurableSet_incrementPair_eq_iidHistory start p)).inter
              (ih (start := start + 1))
      | some t =>
          rw [selectivePairRunsEqFrom]
          have hend : 2 * (start + t + 1) ≤
              2 * selectivePairRunsEnd (start + t + 1) runs :=
            Nat.mul_le_mul_left 2
              (selectivePairRunsEnd_start_le (start + t + 1) runs)
          exact ((iidHistory_mono_local hend) _
            (measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
              start t p)).inter (ih (start := start + t + 1))

theorem adjacentPairSwap_lt_evenCut {i n : ℕ} (hi : i < 2 * n) :
    adjacentPairSwap i < 2 * n := by
  rcases Nat.even_or_odd' i with ⟨r, rfl | rfl⟩
  · simp only [adjacentPairSwap_even]
    omega
  · simp only [adjacentPairSwap_odd]
    omega

/-- Swapping coordinates inside complete pairs preserves the sigma algebra
strictly before an even cutoff. -/
theorem measurable_swapAdjacentPairs_iidHistory_even (n : ℕ) :
    @Measurable (ℕ → Direction) (ℕ → Direction)
      (iidHistory (X := Direction) (2 * n))
      (iidHistory (X := Direction) (2 * n)) swapAdjacentPairs := by
  apply measurable_iff_comap_le.mpr
  simp only [iidHistory, MeasurableSpace.comap_iSup]
  refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
  rw [MeasurableSpace.comap_comp]
  have hfun : (fun omega : ℕ → Direction ↦ omega i) ∘
        swapAdjacentPairs =
      fun omega : ℕ → Direction ↦ omega (adjacentPairSwap i) := by
    rfl
  rw [hfun]
  exact le_iSup_of_le (adjacentPairSwap i)
    (le_iSup_of_le (adjacentPairSwap_lt_evenCut hi) le_rfl)

@[simp] theorem selectivePairRunsEnd_map_reverse
    (start : ℕ) (runs : List SelectivePairRun) :
    selectivePairRunsEnd start (runs.map reverseSelectivePairRun) =
      selectivePairRunsEnd start runs := by
  induction runs generalizing start with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot <;> simp [selectivePairRunsEnd, reverseSelectivePairRun, ih]

/-- The separately conditioned primed run list is also a cylinder before
the same complete-pair endpoint. -/
theorem measurableSet_primedSelectivePairRunsEqFrom_iidHistory
    (start : ℕ) (runs : List SelectivePairRun) :
    MeasurableSet[iidHistory (X := Direction)
      (2 * selectivePairRunsEnd start runs)]
      (primedSelectivePairRunsEqFrom start runs) := by
  rw [primedSelectivePairRunsEqFrom]
  have hruns := measurableSet_selectivePairRunsEqFrom_iidHistory start
    (runs.map reverseSelectivePairRun)
  rw [selectivePairRunsEnd_map_reverse] at hruns
  exact hruns.preimage
    (measurable_swapAdjacentPairs_iidHistory_even
      (selectivePairRunsEnd start runs))

/-! ## A generic terminal restriction -/

noncomputable def selectiveEncodedEndTime
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    (ℕ → Direction) → ℕ :=
  fun omega ↦ 2 * selectivePairRunsEnd start
    (e.encode (conditionalSelectiveRunVector e omega))

theorem measurable_selectiveEncodedEndTime
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    Measurable (selectiveEncodedEndTime e) := by
  exact (measurable_of_countable fun v : Fin e.q → ℕ ↦
    2 * selectivePairRunsEnd start (e.encode v)).comp
      (measurable_conditionalSelectiveRunVector e)

noncomputable def selectiveTerminalRestrictedAtom
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma) :
    Set (ℕ → Direction) :=
  selectiveTerminalLabelsEqFrom start specs ∩
    (fun omega ↦ f (conditionalSelectiveRunVector e omega)) ⁻¹' E

theorem selectiveTerminalRestrictedAtom_inter_vectorFiber
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (v : Fin e.q → ℕ) :
    selectiveTerminalRestrictedAtom e f E ∩
        (conditionalSelectiveRunVector e) ⁻¹' {v} =
      selectivePairRunsEqFrom start (e.encode v) ∩
        {omega | f v ∈ E} := by
  classical
  ext omega
  simp only [selectiveTerminalRestrictedAtom, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hterminal, hf⟩, hv⟩
    refine ⟨(conditionalSelectiveRunVector_eq_iff e v hterminal).mp hv, ?_⟩
    rw [← hv]
    exact hf
  · rintro ⟨hruns, hvE⟩
    have hboth := Set.ext_iff.mp
      (terminalAtom_inter_selectiveVector_fiber e v) omega
    have hpair := hboth.mpr hruns
    refine ⟨⟨hpair.1, ?_⟩, hpair.2⟩
    rw [hpair.2]
    exact hvE

theorem selectiveTerminalRestrictedAtom_past
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (selectiveTerminalRestrictedAtom e f E ∩
        {omega | selectiveEncodedEndTime e omega = n}) := by
  classical
  have heq : selectiveTerminalRestrictedAtom e f E ∩
        {omega | selectiveEncodedEndTime e omega = n} =
      ⋃ v : Fin e.q → ℕ,
        selectivePairRunsEqFrom start (e.encode v) ∩
          {omega | f v ∈ E ∧
            2 * selectivePairRunsEnd start (e.encode v) = n} := by
    ext omega
    constructor
    · rintro ⟨hA, hn⟩
      let v := conditionalSelectiveRunVector e omega
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hvE : f v ∈ E := hA.2
      have hvn : 2 * selectivePairRunsEnd start (e.encode v) = n := hn
      have hfiber : omega ∈ selectiveTerminalRestrictedAtom e f E ∩
          (conditionalSelectiveRunVector e) ⁻¹' {v} :=
        ⟨hA, rfl⟩
      rw [selectiveTerminalRestrictedAtom_inter_vectorFiber e f E v] at hfiber
      exact ⟨hfiber.1, hvE, hvn⟩
    · rw [Set.mem_iUnion]
      rintro ⟨v, hv⟩
      have hboth := Set.ext_iff.mp
        (terminalAtom_inter_selectiveVector_fiber e v) omega
      have hpair := hboth.mpr hv.1
      refine ⟨⟨hpair.1, ?_⟩, ?_⟩
      · change f (conditionalSelectiveRunVector e omega) ∈ E
        rw [hpair.2]
        exact hv.2.1
      · change 2 * selectivePairRunsEnd start
          (e.encode (conditionalSelectiveRunVector e omega)) = n
        rw [hpair.2]
        exact hv.2.2
  rw [heq]
  apply MeasurableSet.iUnion
  intro v
  by_cases hcond : f v ∈ E ∧
      2 * selectivePairRunsEnd start (e.encode v) = n
  · have hruns := measurableSet_selectivePairRunsEqFrom_iidHistory
      start (e.encode v)
    rw [hcond.2] at hruns
    have hset : {omega : ℕ → Direction | f v ∈ E ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = Set.univ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hcond
    rw [hset, Set.inter_univ]
    exact hruns
  · have hset : {omega : ℕ → Direction | f v ∈ E ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = ∅ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hcond
    rw [hset, Set.inter_empty]
    exact @MeasurableSet.empty (ℕ → Direction)
      (iidHistory (X := Direction) n)

theorem selectiveTerminalRestrictedStatisticFiber_past
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    {gamma beta : Type*}
    (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (g : (Fin e.q → ℕ) → beta) (b : beta) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((selectiveTerminalRestrictedAtom e f E ∩
          (fun omega ↦ g (conditionalSelectiveRunVector e omega)) ⁻¹' {b}) ∩
        {omega | selectiveEncodedEndTime e omega = n}) := by
  classical
  have heq :
      ((selectiveTerminalRestrictedAtom e f E ∩
          (fun omega ↦ g (conditionalSelectiveRunVector e omega)) ⁻¹' {b}) ∩
        {omega | selectiveEncodedEndTime e omega = n}) =
      ⋃ v : Fin e.q → ℕ,
        selectivePairRunsEqFrom start (e.encode v) ∩
          {omega | f v ∈ E ∧ g v = b ∧
            2 * selectivePairRunsEnd start (e.encode v) = n} := by
    ext omega
    constructor
    · rintro ⟨⟨hA, hgb⟩, hn⟩
      let v := conditionalSelectiveRunVector e omega
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hvE : f v ∈ E := hA.2
      have hvb : g v = b := hgb
      have hvn : 2 * selectivePairRunsEnd start (e.encode v) = n := hn
      have hfiber : omega ∈ selectiveTerminalRestrictedAtom e f E ∩
          (conditionalSelectiveRunVector e) ⁻¹' {v} := ⟨hA, rfl⟩
      rw [selectiveTerminalRestrictedAtom_inter_vectorFiber e f E v] at hfiber
      exact ⟨hfiber.1, hvE, hvb, hvn⟩
    · rw [Set.mem_iUnion]
      rintro ⟨v, hv⟩
      have hboth := Set.ext_iff.mp
        (terminalAtom_inter_selectiveVector_fiber e v) omega
      have hpair := hboth.mpr hv.1
      refine ⟨⟨⟨hpair.1, ?_⟩, ?_⟩, ?_⟩
      · change f (conditionalSelectiveRunVector e omega) ∈ E
        rw [hpair.2]
        exact hv.2.1
      · change g (conditionalSelectiveRunVector e omega) = b
        rw [hpair.2]
        exact hv.2.2.1
      · change 2 * selectivePairRunsEnd start
          (e.encode (conditionalSelectiveRunVector e omega)) = n
        rw [hpair.2]
        exact hv.2.2.2
  rw [heq]
  apply MeasurableSet.iUnion
  intro v
  by_cases hcond : f v ∈ E ∧ g v = b ∧
      2 * selectivePairRunsEnd start (e.encode v) = n
  · have hruns := measurableSet_selectivePairRunsEqFrom_iidHistory
      start (e.encode v)
    rw [hcond.2.2] at hruns
    have hset : {omega : ℕ → Direction | f v ∈ E ∧ g v = b ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = Set.univ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hcond
    rw [hset, Set.inter_univ]
    exact hruns
  · have hset : {omega : ℕ → Direction | f v ∈ E ∧ g v = b ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = ∅ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hcond
    rw [hset, Set.inter_empty]
    exact @MeasurableSet.empty (ℕ → Direction)
      (iidHistory (X := Direction) n)

/-- Generic iid restart after a forward adaptive terminal list. -/
theorem selectiveTerminal_hasLaw_prod_fresh
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    {gamma beta : Type*} [MeasurableSpace beta]
    [MeasurableSingletonClass beta] [Countable beta]
    (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (g : (Fin e.q → ℕ) → beta) (hg : Measurable g)
    (nu : Measure beta)
    (hLaw : HasLaw
      (fun omega ↦ g (conditionalSelectiveRunVector e omega)) nu
      incrementLaw[|selectiveTerminalRestrictedAtom e f E]) :
    HasLaw
      (fun omega ↦
        (g (conditionalSelectiveRunVector e omega),
          incrementShiftAfter (selectiveEncodedEndTime e) omega 0))
      (nu.prod directionLaw)
      incrementLaw[|selectiveTerminalRestrictedAtom e f E] := by
  apply hasLaw_prod_direction_after
    (selectiveEncodedEndTime e)
    (selectiveTerminalRestrictedAtom e f E)
    (fun omega ↦ g (conditionalSelectiveRunVector e omega)) nu
    (measurable_selectiveEncodedEndTime e)
  · exact selectiveTerminalRestrictedAtom_past e f E
  · exact hg.comp (measurable_conditionalSelectiveRunVector e)
  · exact selectiveTerminalRestrictedStatisticFiber_past e f E g
  · exact hLaw

/-! ## The independently conditioned primed terminal restriction -/

theorem conditionalPrimedSelectiveRunVector_eq_iff
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    (v : Fin e.q → ℕ) {omega : ℕ → Direction}
    (homega : omega ∈ primedSelectiveTerminalLabelsEqFrom start specs) :
    conditionalPrimedSelectiveRunVector e omega = v ↔
      omega ∈ primedSelectivePairRunsEqFrom start (e.encode v) := by
  change conditionalSelectiveRunVector e.toForward
      (swapAdjacentPairs omega) = v ↔
    swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
      ((e.encode v).map reverseSelectivePairRun)
  exact conditionalSelectiveRunVector_eq_iff e.toForward v homega

theorem primedTerminalAtom_inter_vectorFiber
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    (v : Fin e.q → ℕ) :
    primedSelectiveTerminalLabelsEqFrom start specs ∩
        (conditionalPrimedSelectiveRunVector e) ⁻¹' {v} =
      primedSelectivePairRunsEqFrom start (e.encode v) := by
  ext omega
  simp only [Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hterminal, hv⟩
    exact (conditionalPrimedSelectiveRunVector_eq_iff e v hterminal).mp hv
  · intro hruns
    have hterminal :
        omega ∈ primedSelectiveTerminalLabelsEqFrom start specs := by
      change swapAdjacentPairs omega ∈ selectiveTerminalLabelsEqFrom start
        (specs.map reverseSelectiveTerminalLabel)
      have ht := selectivePairRuns_subset_terminalLabels start
        ((e.encode v).map reverseSelectivePairRun) hruns
      rw [selectiveTerminalSpec_map_reverse, e.terminal_spec] at ht
      exact ht
    exact ⟨hterminal,
      (conditionalPrimedSelectiveRunVector_eq_iff e v hterminal).mpr hruns⟩

noncomputable def primedEncodedEndTime
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    (ℕ → Direction) → ℕ :=
  fun omega ↦ 2 * selectivePairRunsEnd start
    (e.encode (conditionalPrimedSelectiveRunVector e omega))

theorem measurable_primedEncodedEndTime
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    Measurable (primedEncodedEndTime e) := by
  exact (measurable_of_countable fun v : Fin e.q → ℕ ↦
    2 * selectivePairRunsEnd start (e.encode v)).comp
      (measurable_conditionalPrimedSelectiveRunVector e)

noncomputable def primedTerminalRestrictedAtom
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma) :
    Set (ℕ → Direction) :=
  primedSelectiveTerminalLabelsEqFrom start specs ∩
    (fun omega ↦ f (conditionalPrimedSelectiveRunVector e omega)) ⁻¹' E

theorem primedTerminalRestrictedAtom_inter_vectorFiber
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (v : Fin e.q → ℕ) :
    primedTerminalRestrictedAtom e f E ∩
        (conditionalPrimedSelectiveRunVector e) ⁻¹' {v} =
      primedSelectivePairRunsEqFrom start (e.encode v) ∩
        {omega | f v ∈ E} := by
  classical
  ext omega
  simp only [primedTerminalRestrictedAtom, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hterminal, hf⟩, hv⟩
    refine ⟨(conditionalPrimedSelectiveRunVector_eq_iff e v hterminal).mp hv,
      ?_⟩
    rw [← hv]
    exact hf
  · rintro ⟨hruns, hvE⟩
    have hboth := Set.ext_iff.mp
      (primedTerminalAtom_inter_vectorFiber e v) omega
    have hpair := hboth.mpr hruns
    refine ⟨⟨hpair.1, ?_⟩, hpair.2⟩
    rw [hpair.2]
    exact hvE

theorem primedTerminalRestrictedAtom_past
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    {gamma : Type*} (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (primedTerminalRestrictedAtom e f E ∩
        {omega | primedEncodedEndTime e omega = n}) := by
  classical
  have heq : primedTerminalRestrictedAtom e f E ∩
        {omega | primedEncodedEndTime e omega = n} =
      ⋃ v : Fin e.q → ℕ,
        primedSelectivePairRunsEqFrom start (e.encode v) ∩
          {omega | f v ∈ E ∧
            2 * selectivePairRunsEnd start (e.encode v) = n} := by
    ext omega
    constructor
    · rintro ⟨hA, hn⟩
      let v := conditionalPrimedSelectiveRunVector e omega
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hvE : f v ∈ E := hA.2
      have hvn : 2 * selectivePairRunsEnd start (e.encode v) = n := hn
      have hfiber : omega ∈ primedTerminalRestrictedAtom e f E ∩
          (conditionalPrimedSelectiveRunVector e) ⁻¹' {v} :=
        ⟨hA, rfl⟩
      rw [primedTerminalRestrictedAtom_inter_vectorFiber e f E v] at hfiber
      exact ⟨hfiber.1, hvE, hvn⟩
    · rw [Set.mem_iUnion]
      rintro ⟨v, hv⟩
      have hboth := Set.ext_iff.mp
        (primedTerminalAtom_inter_vectorFiber e v) omega
      have hpair := hboth.mpr hv.1
      refine ⟨⟨hpair.1, ?_⟩, ?_⟩
      · change f (conditionalPrimedSelectiveRunVector e omega) ∈ E
        rw [hpair.2]
        exact hv.2.1
      · change 2 * selectivePairRunsEnd start
          (e.encode (conditionalPrimedSelectiveRunVector e omega)) = n
        rw [hpair.2]
        exact hv.2.2
  rw [heq]
  apply MeasurableSet.iUnion
  intro v
  by_cases hcond : f v ∈ E ∧
      2 * selectivePairRunsEnd start (e.encode v) = n
  · have hruns := measurableSet_primedSelectivePairRunsEqFrom_iidHistory
      start (e.encode v)
    rw [hcond.2] at hruns
    have hset : {omega : ℕ → Direction | f v ∈ E ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = Set.univ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hcond
    rw [hset, Set.inter_univ]
    exact hruns
  · have hset : {omega : ℕ → Direction | f v ∈ E ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = ∅ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hcond
    rw [hset, Set.inter_empty]
    exact @MeasurableSet.empty (ℕ → Direction)
      (iidHistory (X := Direction) n)

theorem primedTerminalRestrictedStatisticFiber_past
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    {gamma beta : Type*}
    (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (g : (Fin e.q → ℕ) → beta) (b : beta) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((primedTerminalRestrictedAtom e f E ∩
          (fun omega ↦ g (conditionalPrimedSelectiveRunVector e omega)) ⁻¹' {b}) ∩
        {omega | primedEncodedEndTime e omega = n}) := by
  classical
  have heq :
      ((primedTerminalRestrictedAtom e f E ∩
          (fun omega ↦ g (conditionalPrimedSelectiveRunVector e omega)) ⁻¹' {b}) ∩
        {omega | primedEncodedEndTime e omega = n}) =
      ⋃ v : Fin e.q → ℕ,
        primedSelectivePairRunsEqFrom start (e.encode v) ∩
          {omega | f v ∈ E ∧ g v = b ∧
            2 * selectivePairRunsEnd start (e.encode v) = n} := by
    ext omega
    constructor
    · rintro ⟨⟨hA, hgb⟩, hn⟩
      let v := conditionalPrimedSelectiveRunVector e omega
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hvE : f v ∈ E := hA.2
      have hvb : g v = b := hgb
      have hvn : 2 * selectivePairRunsEnd start (e.encode v) = n := hn
      have hfiber : omega ∈ primedTerminalRestrictedAtom e f E ∩
          (conditionalPrimedSelectiveRunVector e) ⁻¹' {v} := ⟨hA, rfl⟩
      rw [primedTerminalRestrictedAtom_inter_vectorFiber e f E v] at hfiber
      exact ⟨hfiber.1, hvE, hvb, hvn⟩
    · rw [Set.mem_iUnion]
      rintro ⟨v, hv⟩
      have hboth := Set.ext_iff.mp
        (primedTerminalAtom_inter_vectorFiber e v) omega
      have hpair := hboth.mpr hv.1
      refine ⟨⟨⟨hpair.1, ?_⟩, ?_⟩, ?_⟩
      · change f (conditionalPrimedSelectiveRunVector e omega) ∈ E
        rw [hpair.2]
        exact hv.2.1
      · change g (conditionalPrimedSelectiveRunVector e omega) = b
        rw [hpair.2]
        exact hv.2.2.1
      · change 2 * selectivePairRunsEnd start
          (e.encode (conditionalPrimedSelectiveRunVector e omega)) = n
        rw [hpair.2]
        exact hv.2.2.2
  rw [heq]
  apply MeasurableSet.iUnion
  intro v
  by_cases hcond : f v ∈ E ∧ g v = b ∧
      2 * selectivePairRunsEnd start (e.encode v) = n
  · have hruns := measurableSet_primedSelectivePairRunsEqFrom_iidHistory
      start (e.encode v)
    rw [hcond.2.2] at hruns
    have hset : {omega : ℕ → Direction | f v ∈ E ∧ g v = b ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = Set.univ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hcond
    rw [hset, Set.inter_univ]
    exact hruns
  · have hset : {omega : ℕ → Direction | f v ∈ E ∧ g v = b ∧
        2 * selectivePairRunsEnd start (e.encode v) = n} = ∅ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact hcond
    rw [hset, Set.inter_empty]
    exact @MeasurableSet.empty (ℕ → Direction)
      (iidHistory (X := Direction) n)

/-- Generic iid restart for the separately conditioned primed terminal list.
The next direction is taken in the original (unswapped) increment sequence. -/
theorem primedTerminal_hasLaw_prod_fresh
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    {gamma beta : Type*} [MeasurableSpace beta]
    [MeasurableSingletonClass beta] [Countable beta]
    (f : (Fin e.q → ℕ) → gamma) (E : Set gamma)
    (g : (Fin e.q → ℕ) → beta) (hg : Measurable g)
    (nu : Measure beta)
    (hLaw : HasLaw
      (fun omega ↦ g (conditionalPrimedSelectiveRunVector e omega)) nu
      incrementLaw[|primedTerminalRestrictedAtom e f E]) :
    HasLaw
      (fun omega ↦
        (g (conditionalPrimedSelectiveRunVector e omega),
          incrementShiftAfter (primedEncodedEndTime e) omega 0))
      (nu.prod directionLaw)
      incrementLaw[|primedTerminalRestrictedAtom e f E] := by
  apply hasLaw_prod_direction_after
    (primedEncodedEndTime e)
    (primedTerminalRestrictedAtom e f E)
    (fun omega ↦ g (conditionalPrimedSelectiveRunVector e omega)) nu
    (measurable_primedEncodedEndTime e)
  · exact primedTerminalRestrictedAtom_past e f E
  · exact hg.comp (measurable_conditionalPrimedSelectiveRunVector e)
  · exact primedTerminalRestrictedStatisticFiber_past e f E g
  · exact hLaw

/-! ## Forward column winner atoms with the fresh direction retained -/

open HLOZProp47Prop45YColumns HLOZSourceInstantiation HLOZUrn
open HLOZProp48Truncated

@[simp] theorem forwardTerminalEncoding_q
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    h.encoding.q = selectiveActiveCount specs := by
  rfl

noncomputable def forwardIncrementTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    (ℕ → Direction) → ColumnRunBase h.baseAt → ℕ :=
  fun omega ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt
      (conditionalSelectiveRunVector h.encoding omega))

noncomputable def forwardTerminalMixedIncrementAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    Set (ℕ → Direction) :=
  selectiveTerminalRestrictedAtom h.encoding
    (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
    (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight)

noncomputable def forwardIncrementTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    (ℕ → Direction) →
      ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ :=
  fun omega ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
    (forwardIncrementTerminalBlockSums h omega)

@[simp] theorem forwardIncrementTerminalActiveFreeVector_apply
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (omega : ℕ → Direction) :
    forwardIncrementTerminalActiveFreeVector h creationSet activeBases omega =
      restrictColumnActiveFreeBase h.baseAt creationSet activeBases
        (columnBlockSums h.baseAt
          (columnBlockVector h.baseAt
            (conditionalSelectiveRunVector h.encoding omega))) := by
  rfl

theorem measurable_forwardIncrementTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (forwardIncrementTerminalActiveFreeVector h creationSet activeBases) :=
  (measurable_restrictColumnActiveFreeBase h.baseAt creationSet activeBases).comp
    ((measurable_columnBlockSums h.baseAt).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurable_conditionalSelectiveRunVector h.encoding)))

theorem forwardTerminalMixedIncrementAtom_preimage
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    simpleRandomWalk ⁻¹'
        forwardTerminalMixedPathAtom h level creationSet
          externalLeft externalRight =
      forwardTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight := by
  ext omega
  simp only [forwardTerminalMixedPathAtom,
    forwardTerminalMixedIncrementAtom, selectiveTerminalRestrictedAtom,
    Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hterminal, hblocks⟩
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp
        (preimage_selectiveTerminalPathAtom start specs) omega).mp hterminal
    · simpa only [forwardTerminalBlockSums,
        pathConditionalSelectiveRunVector_simpleRandomWalk] using hblocks
  · rintro ⟨hterminal, hblocks⟩
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp
        (preimage_selectiveTerminalPathAtom start specs) omega).mpr hterminal
    · simpa only [forwardTerminalBlockSums,
        pathConditionalSelectiveRunVector_simpleRandomWalk] using hblocks

theorem forwardTerminalMixedIncrementAtom_image
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    simpleRandomWalk ''
        forwardTerminalMixedIncrementAtom h level creationSet
          externalLeft externalRight =
      forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight := by
  apply Set.Subset.antisymm
  · rintro s ⟨omega, homega, rfl⟩
    exact (Set.ext_iff.mp
      (forwardTerminalMixedIncrementAtom_preimage h level creationSet
        externalLeft externalRight) omega).mpr homega
  · intro s hs
    rcases hs.1 with ⟨omega, homega, rfl⟩
    refine ⟨omega, ?_, rfl⟩
    apply (Set.ext_iff.mp
      (forwardTerminalMixedIncrementAtom_preimage h level creationSet
        externalLeft externalRight) omega).mp
    exact hs

theorem forwardIncrementTerminalActiveFree_truncated_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    HasLaw
      (forwardIncrementTerminalActiveFreeVector h creationSet activeBases)
      (sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases))
      incrementLaw[|forwardTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  let f := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  let R := restrictColumnActiveFreeBase h.baseAt creationSet activeBases
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  have hf : Measurable f :=
    (measurable_columnBlockSums h.baseAt).comp
      (measurable_columnBlockVector h.baseAt)
  have hfLaw : HasLaw f (columnBlockNegBinMeasure h.baseAt)
      (runVectorMeasure h.encoding.q) :=
    ⟨hf.aemeasurable, runVectorMeasure_map_columnBlockSums h.baseAt⟩
  have hbase := hfLaw.fun_comp
    (conditionalSelectiveRunVector_hasLaw h.encoding h.valid)
  have hE : MeasurableSet E :=
    measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight
  have hfcomp : Measurable
      (fun omega ↦ f (conditionalSelectiveRunVector h.encoding omega)) :=
    hf.comp (measurable_conditionalSelectiveRunVector h.encoding)
  have hcond := HasLaw.cond_preimage hbase hfcomp E hE
  rw [cond_cond_eq_cond_inter
    (measurableSet_selectiveTerminalLabelsEqFrom start specs)
    (hE.preimage hfcomp)] at hcond
  have hpos := columnMixedCoordinatePos_of_event_nonempty h.baseAt level
    creationSet externalLeft externalRight hEvent
  have hR : HasLaw R
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      ((columnBlockNegBinMeasure h.baseAt)[|E]) :=
    ⟨(measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).aemeasurable,
      columnBlockNegBinMeasure_cond_mixed_map_activeFree h.baseAt level
        creationSet activeBases externalLeft externalRight hpos⟩
  have hresult := hR.fun_comp hcond
  rw [sourceCappedProfileMeasure_eq_truncated _ _ _ hwinning] at hresult
  have hfun :
      (fun omega ↦
        restrictColumnActiveFreeBase h.baseAt creationSet activeBases
          (columnBlockSums h.baseAt
            (columnBlockVector h.baseAt
              (conditionalSelectiveRunVector h.encoding omega)))) =
        forwardIncrementTerminalActiveFreeVector h creationSet activeBases := by
    funext omega
    exact (forwardIncrementTerminalActiveFreeVector_apply h creationSet
      activeBases omega).symm
  rw [hfun] at hresult
  simpa only [forwardTerminalMixedIncrementAtom,
    selectiveTerminalRestrictedAtom, f, R, E, Function.comp_apply] using hresult

noncomputable def forwardTerminalNextDirection
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    (ℕ → Site) → Direction :=
  liftIncrementStatisticToPath fun omega ↦
    incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0

theorem measurable_forwardTerminalNextDirection
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    Measurable (forwardTerminalNextDirection h) := by
  apply measurable_liftIncrementStatisticToPath
  exact (measurable_pi_apply 0).comp
    (measurable_incrementShiftAfter
      (measurable_selectiveEncodedEndTime h.encoding))

/-- Exact forward column terminal law in the joint form required by (4.47).
The next direction is the first increment after the random terminal pair
endpoint and is proved fresh, rather than assumed. -/
theorem forwardTerminalActiveFree_prod_fresh_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    (simpleRandomWalkLaw.restrict
      (forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (fun s ↦
          (forwardTerminalActiveFreeVector h creationSet activeBases s,
            forwardTerminalNextDirection h s)) =
      simpleRandomWalkLaw
          (forwardTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw) := by
  let f := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  let g := fun v ↦ restrictColumnActiveFreeBase h.baseAt creationSet
    activeBases (f v)
  have hg : Measurable g :=
    (measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).comp
        ((measurable_columnBlockSums h.baseAt).comp
          (measurable_columnBlockVector h.baseAt))
  have hmarginal :=
    forwardIncrementTerminalActiveFree_truncated_hasLaw h level creationSet
      activeBases externalLeft externalRight hEvent hwinning
  have hgf :
      (fun omega ↦ g (conditionalSelectiveRunVector h.encoding omega)) =
        forwardIncrementTerminalActiveFreeVector h creationSet activeBases := by
    funext omega
    exact (forwardIncrementTerminalActiveFreeVector_apply h creationSet
      activeBases omega).symm
  have hfresh := selectiveTerminal_hasLaw_prod_fresh h.encoding f E g hg
    (sourceTruncatedProfileMeasure level
      (columnActiveFreeShape h.baseAt creationSet activeBases))
    (by
      rw [hgf]
      exact hmarginal)
  have hpath : HasLaw
      (fun s ↦
        (forwardTerminalActiveFreeVector h creationSet activeBases s,
          forwardTerminalNextDirection h s))
      ((sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
          directionLaw)
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
    rw [simpleRandomWalkLaw,
      ← forwardTerminalMixedIncrementAtom_image h level creationSet
        externalLeft externalRight]
    apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
      (measurableSet_pastEvent (selectiveEncodedEndTime h.encoding)
        (forwardTerminalMixedIncrementAtom h level creationSet
          externalLeft externalRight) (by
            exact selectiveTerminalRestrictedAtom_past h.encoding f E))
    · exact (measurable_forwardIncrementTerminalActiveFreeVector h creationSet
        activeBases).prodMk
          ((measurable_pi_apply 0).comp
            (measurable_incrementShiftAfter
              (measurable_selectiveEncodedEndTime h.encoding)))
    · intro omega _homega
      apply Prod.ext
      · change restrictColumnActiveFreeBase h.baseAt creationSet activeBases
            (forwardTerminalBlockSums h (simpleRandomWalk omega)) =
          forwardIncrementTerminalActiveFreeVector h creationSet activeBases omega
        rw [forwardIncrementTerminalActiveFreeVector_apply,
          forwardTerminalBlockSums,
          pathConditionalSelectiveRunVector_simpleRandomWalk]
      · simpa only [forwardTerminalNextDirection, Function.comp_apply] using
          (liftIncrementStatisticToPath_simpleRandomWalk
            (fun omega ↦
              incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0)
            omega)
    · have hpair :
          (fun omega ↦
            (g (conditionalSelectiveRunVector h.encoding omega),
              incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0)) =
          (fun omega ↦
            (forwardIncrementTerminalActiveFreeVector h creationSet activeBases omega,
              incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0)) := by
          funext omega
          exact Prod.ext (congrFun hgf omega) rfl
      rw [hpair] at hfresh
      exact hfresh
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_forwardTerminalMixedPathAtom h level creationSet
      externalLeft externalRight)
    ((measurable_forwardTerminalActiveFreeVector h creationSet
      activeBases).prodMk (measurable_forwardTerminalNextDirection h)) hpath

/-- Source weak-left winner specialization of the joint fresh-direction
law; only the concrete base-multiplicity identity remains. -/
theorem forwardTerminalLeftWinner_prod_fresh_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase h.baseAt))
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hleft : ∀ b,
      Fintype.card (ColumnRunIndex h.baseAt b) = externalLeft b) :
    (simpleRandomWalkLaw.restrict
      (forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (fun s ↦
          (forwardTerminalActiveFreeVector h creationSet
              (columnForwardLeftWinnerBases h.baseAt externalLeft
                externalRight candidateBases) s,
            forwardTerminalNextDirection h s)) =
      simpleRandomWalkLaw
          (forwardTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet
            (columnForwardLeftWinnerBases h.baseAt externalLeft
              externalRight candidateBases))).prod directionLaw) := by
  apply forwardTerminalActiveFree_prod_fresh_truncated_path_map_law
    h level creationSet
      (columnForwardLeftWinnerBases h.baseAt externalLeft externalRight
        candidateBases)
    externalLeft externalRight hEvent
  exact columnForwardLeftWinner_cap_eq_shape h.baseAt creationSet
    externalLeft externalRight candidateBases hleft

/-! ## The separately conditioned primed column winner atom -/

theorem preimage_primedSelectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    simpleRandomWalk ⁻¹' primedSelectiveTerminalPathAtom start specs =
      primedSelectiveTerminalLabelsEqFrom start specs :=
  simpleRandomWalk_injective.preimage_image _

theorem pathConditionalPrimedSelectiveRunVector_simpleRandomWalk
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    (omega : ℕ → Direction) :
    pathConditionalPrimedSelectiveRunVector e (simpleRandomWalk omega) =
      conditionalPrimedSelectiveRunVector e omega :=
  simpleRandomWalk_injective.extend_apply _ _ omega

noncomputable def primedIncrementTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    (ℕ → Direction) → ColumnRunBase h.baseAt → ℕ :=
  fun omega ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt
      (conditionalPrimedSelectiveRunVector h.encoding omega))

noncomputable def primedTerminalMixedIncrementAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    Set (ℕ → Direction) :=
  primedTerminalRestrictedAtom h.encoding
    (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
    (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight)

noncomputable def primedIncrementTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    (ℕ → Direction) →
      ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ :=
  fun omega ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
    (primedIncrementTerminalBlockSums h omega)

@[simp] theorem primedIncrementTerminalActiveFreeVector_apply
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (omega : ℕ → Direction) :
    primedIncrementTerminalActiveFreeVector h creationSet activeBases omega =
      restrictColumnActiveFreeBase h.baseAt creationSet activeBases
        (columnBlockSums h.baseAt
          (columnBlockVector h.baseAt
            (conditionalPrimedSelectiveRunVector h.encoding omega))) := by
  rfl

theorem measurable_primedIncrementTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (primedIncrementTerminalActiveFreeVector h creationSet activeBases) :=
  (measurable_restrictColumnActiveFreeBase h.baseAt creationSet activeBases).comp
    ((measurable_columnBlockSums h.baseAt).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurable_conditionalPrimedSelectiveRunVector h.encoding)))

theorem primedTerminalMixedIncrementAtom_preimage
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    simpleRandomWalk ⁻¹'
        primedTerminalMixedPathAtom h level creationSet
          externalLeft externalRight =
      primedTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight := by
  ext omega
  simp only [primedTerminalMixedPathAtom,
    primedTerminalMixedIncrementAtom, primedTerminalRestrictedAtom,
    Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hterminal, hblocks⟩
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp
        (preimage_primedSelectiveTerminalPathAtom start specs) omega).mp hterminal
    · simpa only [primedTerminalBlockSums,
        pathConditionalPrimedSelectiveRunVector_simpleRandomWalk] using hblocks
  · rintro ⟨hterminal, hblocks⟩
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp
        (preimage_primedSelectiveTerminalPathAtom start specs) omega).mpr hterminal
    · simpa only [primedTerminalBlockSums,
        pathConditionalPrimedSelectiveRunVector_simpleRandomWalk] using hblocks

theorem primedTerminalMixedIncrementAtom_image
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    simpleRandomWalk ''
        primedTerminalMixedIncrementAtom h level creationSet
          externalLeft externalRight =
      primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight := by
  apply Set.Subset.antisymm
  · rintro s ⟨omega, homega, rfl⟩
    exact (Set.ext_iff.mp
      (primedTerminalMixedIncrementAtom_preimage h level creationSet
        externalLeft externalRight) omega).mpr homega
  · intro s hs
    rcases hs.1 with ⟨omega, homega, rfl⟩
    refine ⟨omega, ?_, rfl⟩
    apply (Set.ext_iff.mp
      (primedTerminalMixedIncrementAtom_preimage h level creationSet
        externalLeft externalRight) omega).mp
    exact hs

theorem primedIncrementTerminalActiveFree_truncated_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    HasLaw
      (primedIncrementTerminalActiveFreeVector h creationSet activeBases)
      (sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases))
      incrementLaw[|primedTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  let f := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  let R := restrictColumnActiveFreeBase h.baseAt creationSet activeBases
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  have hf : Measurable f :=
    (measurable_columnBlockSums h.baseAt).comp
      (measurable_columnBlockVector h.baseAt)
  have hfLaw : HasLaw f (columnBlockNegBinMeasure h.baseAt)
      (runVectorMeasure h.encoding.q) :=
    ⟨hf.aemeasurable, runVectorMeasure_map_columnBlockSums h.baseAt⟩
  have hbase := hfLaw.fun_comp
    (conditionalPrimedSelectiveRunVector_hasLaw h.encoding h.valid)
  have hE : MeasurableSet E :=
    measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight
  have hfcomp : Measurable
      (fun omega ↦ f (conditionalPrimedSelectiveRunVector h.encoding omega)) :=
    hf.comp (measurable_conditionalPrimedSelectiveRunVector h.encoding)
  have hcond := HasLaw.cond_preimage hbase hfcomp E hE
  rw [cond_cond_eq_cond_inter
    (measurableSet_primedSelectiveTerminalLabelsEqFrom start specs)
    (hE.preimage hfcomp)] at hcond
  have hpos := columnMixedCoordinatePos_of_event_nonempty h.baseAt level
    creationSet externalLeft externalRight hEvent
  have hR : HasLaw R
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      ((columnBlockNegBinMeasure h.baseAt)[|E]) :=
    ⟨(measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).aemeasurable,
      columnBlockNegBinMeasure_cond_mixed_map_activeFree h.baseAt level
        creationSet activeBases externalLeft externalRight hpos⟩
  have hresult := hR.fun_comp hcond
  rw [sourceCappedProfileMeasure_eq_truncated _ _ _ hwinning] at hresult
  have hfun :
      (fun omega ↦
        restrictColumnActiveFreeBase h.baseAt creationSet activeBases
          (columnBlockSums h.baseAt
            (columnBlockVector h.baseAt
              (conditionalPrimedSelectiveRunVector h.encoding omega)))) =
        primedIncrementTerminalActiveFreeVector h creationSet activeBases := by
    funext omega
    exact (primedIncrementTerminalActiveFreeVector_apply h creationSet
      activeBases omega).symm
  rw [hfun] at hresult
  simpa only [primedTerminalMixedIncrementAtom,
    primedTerminalRestrictedAtom, f, R, E, Function.comp_apply] using hresult

noncomputable def primedTerminalNextDirection
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    (ℕ → Site) → Direction :=
  liftIncrementStatisticToPath fun omega ↦
    incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0

theorem measurable_primedTerminalNextDirection
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    Measurable (primedTerminalNextDirection h) := by
  apply measurable_liftIncrementStatisticToPath
  exact (measurable_pi_apply 0).comp
    (measurable_incrementShiftAfter
      (measurable_primedEncodedEndTime h.encoding))

/-- Exact primed/backward column terminal law with the first unswapped
direction following the random complete-pair endpoint retained. -/
theorem primedTerminalActiveFree_prod_fresh_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    (simpleRandomWalkLaw.restrict
      (primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (fun s ↦
          (primedTerminalActiveFreeVector h creationSet activeBases s,
            primedTerminalNextDirection h s)) =
      simpleRandomWalkLaw
          (primedTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw) := by
  let f := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  let g := fun v ↦ restrictColumnActiveFreeBase h.baseAt creationSet
    activeBases (f v)
  have hg : Measurable g :=
    (measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).comp
        ((measurable_columnBlockSums h.baseAt).comp
          (measurable_columnBlockVector h.baseAt))
  have hmarginal :=
    primedIncrementTerminalActiveFree_truncated_hasLaw h level creationSet
      activeBases externalLeft externalRight hEvent hwinning
  have hgf :
      (fun omega ↦ g (conditionalPrimedSelectiveRunVector h.encoding omega)) =
        primedIncrementTerminalActiveFreeVector h creationSet activeBases := by
    funext omega
    exact (primedIncrementTerminalActiveFreeVector_apply h creationSet
      activeBases omega).symm
  have hfresh := primedTerminal_hasLaw_prod_fresh h.encoding f E g hg
    (sourceTruncatedProfileMeasure level
      (columnActiveFreeShape h.baseAt creationSet activeBases))
    (by
      rw [hgf]
      exact hmarginal)
  have hpath : HasLaw
      (fun s ↦
        (primedTerminalActiveFreeVector h creationSet activeBases s,
          primedTerminalNextDirection h s))
      ((sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
          directionLaw)
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
    rw [simpleRandomWalkLaw,
      ← primedTerminalMixedIncrementAtom_image h level creationSet
        externalLeft externalRight]
    apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
      (measurableSet_pastEvent (primedEncodedEndTime h.encoding)
        (primedTerminalMixedIncrementAtom h level creationSet
          externalLeft externalRight) (by
            exact primedTerminalRestrictedAtom_past h.encoding f E))
    · exact (measurable_primedIncrementTerminalActiveFreeVector h creationSet
        activeBases).prodMk
          ((measurable_pi_apply 0).comp
            (measurable_incrementShiftAfter
              (measurable_primedEncodedEndTime h.encoding)))
    · intro omega _homega
      apply Prod.ext
      · change restrictColumnActiveFreeBase h.baseAt creationSet activeBases
            (primedTerminalBlockSums h (simpleRandomWalk omega)) =
          primedIncrementTerminalActiveFreeVector h creationSet activeBases omega
        rw [primedIncrementTerminalActiveFreeVector_apply,
          primedTerminalBlockSums,
          pathConditionalPrimedSelectiveRunVector_simpleRandomWalk]
      · simpa only [primedTerminalNextDirection, Function.comp_apply] using
          (liftIncrementStatisticToPath_simpleRandomWalk
            (fun omega ↦
              incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0)
            omega)
    · have hpair :
          (fun omega ↦
            (g (conditionalPrimedSelectiveRunVector h.encoding omega),
              incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0)) =
          (fun omega ↦
            (primedIncrementTerminalActiveFreeVector h creationSet activeBases omega,
              incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0)) := by
          funext omega
          exact Prod.ext (congrFun hgf omega) rfl
      rw [hpair] at hfresh
      exact hfresh
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_primedTerminalMixedPathAtom h level creationSet
      externalLeft externalRight)
    ((measurable_primedTerminalActiveFreeVector h creationSet
      activeBases).prodMk (measurable_primedTerminalNextDirection h)) hpath

/-- Source strict-right winner specialization on the independently
conditioned primed atom. -/
theorem primedTerminalStrictRightWinner_prod_fresh_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase h.baseAt))
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hright : ∀ b,
      Fintype.card (ColumnRunIndex h.baseAt b) = externalRight b) :
    (simpleRandomWalkLaw.restrict
      (primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (fun s ↦
          (primedTerminalActiveFreeVector h creationSet
              (columnPrimedStrictRightWinnerBases h.baseAt externalLeft
                externalRight candidateBases) s,
            primedTerminalNextDirection h s)) =
      simpleRandomWalkLaw
          (primedTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet
            (columnPrimedStrictRightWinnerBases h.baseAt externalLeft
              externalRight candidateBases))).prod directionLaw) := by
  apply primedTerminalActiveFree_prod_fresh_truncated_path_map_law
    h level creationSet
      (columnPrimedStrictRightWinnerBases h.baseAt externalLeft externalRight
        candidateBases)
    externalLeft externalRight hEvent
  exact columnPrimedStrictRightWinner_cap_eq_shape h.baseAt creationSet
    externalLeft externalRight candidateBases hright

end Erdos1166.HLOZColumnTerminalRestart
