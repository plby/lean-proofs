import ErdosProblems.Erdos1166.Erdos1166Core

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace Erdos1166

/-- The pair `(+e₁,-e₁)`, represented by its two direction labels. -/
def distinguishedIncrementPair : Fin 2 → Direction := ![0, 1]

@[simp] theorem distinguishedIncrementPair_zero :
    distinguishedIncrementPair 0 = 0 := rfl

@[simp] theorem distinguishedIncrementPair_one :
    distinguishedIncrementPair 1 = 1 := rfl

theorem distinguishedIncrementPair_steps :
    (directionStep (distinguishedIncrementPair 0),
      directionStep (distinguishedIncrementPair 1)) =
      ((1, 0), (-1, 0)) := by
  decide

/-- Pair the iid increments at indices `2r` and `2r+1`. -/
def incrementPair (r : ℕ) (ω : ℕ → Direction) : Fin 2 → Direction :=
  iidBlock (X := Direction) (2 * r) 2 ω

theorem measurable_incrementPair (r : ℕ) : Measurable (incrementPair r) := by
  exact measurable_iidBlock (2 * r) 2

theorem incrementPair_map (r : ℕ) :
    incrementLaw.map (incrementPair r) =
      Measure.infinitePi fun _ : Fin 2 ↦ directionLaw := by
  unfold incrementLaw incrementPair directionLaw
  exact iidBlock_map (PMF.uniformOfFintype Direction).toMeasure (2 * r) 2

theorem directionPair_product_singleton (p : Fin 2 → Direction) :
    (Measure.infinitePi fun _ : Fin 2 ↦ directionLaw) {p} =
      (16 : ENNReal)⁻¹ := by
  rw [Measure.infinitePi_singleton_of_fintype]
  simp [directionLaw]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- Every adjacent pair is uniform on the sixteen possible direction pairs. -/
theorem incrementPair_prob (r : ℕ) (p : Fin 2 → Direction) :
    incrementLaw {ω | incrementPair r ω = p} = (16 : ENNReal)⁻¹ := by
  calc
    incrementLaw {ω | incrementPair r ω = p} =
        (incrementLaw.map (incrementPair r)) {p} := by
      rw [Measure.map_apply (measurable_incrementPair r)
        (measurableSet_singleton p)]
      rfl
    _ = (Measure.infinitePi fun _ : Fin 2 ↦ directionLaw) {p} := by
      rw [incrementPair_map]
    _ = (16 : ENNReal)⁻¹ := directionPair_product_singleton p

theorem distinguishedIncrementPair_prob (r : ℕ) :
    incrementLaw {ω | incrementPair r ω = distinguishedIncrementPair} =
      (16 : ENNReal)⁻¹ :=
  incrementPair_prob r distinguishedIncrementPair

theorem directionPair_product_ne_distinguished :
    (Measure.infinitePi fun _ : Fin 2 ↦ directionLaw)
        {p | p ≠ distinguishedIncrementPair} = (15 : ENNReal) / 16 := by
  have hsingle : MeasurableSet ({distinguishedIncrementPair} :
      Set (Fin 2 → Direction)) := measurableSet_singleton _
  have heq : {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair} =
      ({distinguishedIncrementPair} : Set (Fin 2 → Direction))ᶜ := by
    ext p
    simp
  rw [heq, measure_compl hsingle]
  rw [measure_univ, directionPair_product_singleton]
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by norm_num) (by norm_num)]
    norm_num
  · exact measure_ne_top _ _

theorem incrementPair_ne_distinguished_prob (r : ℕ) :
    incrementLaw {ω | incrementPair r ω ≠ distinguishedIncrementPair} =
      (15 : ENNReal) / 16 := by
  calc
    incrementLaw {ω | incrementPair r ω ≠ distinguishedIncrementPair} =
        (incrementLaw.map (incrementPair r))
          {p | p ≠ distinguishedIncrementPair} := by
      rw [Measure.map_apply (measurable_incrementPair r) (by measurability)]
      rfl
    _ = (Measure.infinitePi fun _ : Fin 2 ↦ directionLaw)
          {p | p ≠ distinguishedIncrementPair} := by
      rw [incrementPair_map]
    _ = (15 : ENNReal) / 16 := directionPair_product_ne_distinguished

/-- The event that the first `t` pairs are all the distinguished backtrack. -/
def distinguishedPairPrefix (t : ℕ) : Set (ℕ → Direction) :=
  {ω | ∀ r < t, incrementPair r ω = distinguishedIncrementPair}

theorem measurable_incrementPair_iidHistory {r t : ℕ} (hrt : r < t) :
    Measurable[iidHistory (X := Direction) (2 * t)] (incrementPair r) := by
  let _ : MeasurableSpace (ℕ → Direction) :=
    iidHistory (X := Direction) (2 * t)
  apply measurable_pi_lambda
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (2 * r + (i : ℕ))
    (le_iSup_of_le (by omega : 2 * r + (i : ℕ) < 2 * t) le_rfl)

theorem measurableSet_distinguishedPairPrefix (t : ℕ) :
    MeasurableSet[iidHistory (X := Direction) (2 * t)]
      (distinguishedPairPrefix t) := by
  have heq : distinguishedPairPrefix t =
      ⋂ r : Fin t, {ω | incrementPair r ω = distinguishedIncrementPair} := by
    ext ω
    simp only [distinguishedPairPrefix, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h r
      exact h r r.isLt
    · intro h r hr
      exact h ⟨r, hr⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro r
  exact (measurable_incrementPair_iidHistory r.isLt)
    (measurableSet_singleton distinguishedIncrementPair)

theorem distinguishedPairPrefix_zero :
    distinguishedPairPrefix 0 = Set.univ := by
  ext ω
  simp [distinguishedPairPrefix]

theorem distinguishedPairPrefix_succ (t : ℕ) :
    distinguishedPairPrefix (t + 1) =
      distinguishedPairPrefix t ∩
        {ω | incrementPair t ω = distinguishedIncrementPair} := by
  ext ω
  simp only [distinguishedPairPrefix, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun r hr ↦ h r (by omega), h t (by omega)⟩
  · rintro ⟨hpre, ht⟩ r hr
    obtain hlt | rfl := Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hr)
    · exact hpre r hlt
    · exact ht

theorem distinguishedPairPrefix_prob (t : ℕ) :
    incrementLaw (distinguishedPairPrefix t) = ((16 : ENNReal)⁻¹) ^ t := by
  induction t with
  | zero =>
      rw [distinguishedPairPrefix_zero, measure_univ]
      simp
  | succ t ih =>
      rw [show t + 1 = t.succ by omega, distinguishedPairPrefix_succ]
      unfold incrementPair incrementLaw at *
      change (Measure.infinitePi fun _ : ℕ ↦
          (PMF.uniformOfFintype Direction).toMeasure)
        (distinguishedPairPrefix t ∩
          iidBlock (X := Direction) (2 * t) 2 ⁻¹'
            {distinguishedIncrementPair}) = (16 : ENNReal)⁻¹ ^ t.succ
      rw [measure_inter_iidBlock_eq_mul
        ((PMF.uniformOfFintype Direction).toMeasure) (2 * t) 2
        (measurableSet_distinguishedPairPrefix t)
        (measurableSet_singleton distinguishedIncrementPair)]
      rw [directionPair_product_singleton, ih]
      simp [pow_succ]

/-- Number of consecutive distinguished pairs before the first other pair. -/
noncomputable def distinguishedPairRunLength :
    (ℕ → Direction) → WithTop ℕ :=
  hittingAfter incrementPair
    {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair} 0

/-- Finite characterization of the geometric run length. -/
theorem distinguishedPairRunLength_eq_iff (ω : ℕ → Direction) (t : ℕ) :
    distinguishedPairRunLength ω = t ↔
      ω ∈ distinguishedPairPrefix t ∧
        incrementPair t ω ≠ distinguishedIncrementPair := by
  constructor
  · intro hrun
    have hfinite : distinguishedPairRunLength ω ≠ ⊤ := by simp [hrun]
    have hlast := hittingAfter_mem_set_of_ne_top
      (u := incrementPair)
      (s := {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
      (n := 0) (ω := ω) hfinite
    have hlast' : incrementPair t ω ≠ distinguishedIncrementPair := by
      change incrementPair (distinguishedPairRunLength ω).untopA ω ≠
        distinguishedIncrementPair at hlast
      have htime : (distinguishedPairRunLength ω).untopA = t := by
        rw [hrun]
        rfl
      rwa [htime] at hlast
    refine ⟨?_, hlast'⟩
    intro r hrt
    have hrlt : (r : WithTop ℕ) < distinguishedPairRunLength ω := by
      rw [hrun]
      exact_mod_cast hrt
    have hnot := notMem_of_lt_hittingAfter
      (u := incrementPair)
      (s := {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
      (n := 0) (ω := ω) hrlt (Nat.zero_le r)
    simpa using hnot
  · rintro ⟨hpre, hlast⟩
    have hle : distinguishedPairRunLength ω ≤ (t : WithTop ℕ) := by
      exact hittingAfter_le_of_mem
        (u := incrementPair)
        (s := {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
        (n := 0) (i := t) (ω := ω) (Nat.zero_le t) hlast
    apply le_antisymm hle
    by_contra hnotle
    have hlt : distinguishedPairRunLength ω < (t : WithTop ℕ) :=
      lt_of_not_ge hnotle
    have hfinite : distinguishedPairRunLength ω ≠ ⊤ := ne_top_of_lt hlt
    let j := (distinguishedPairRunLength ω).untopA
    have hjcoe : (j : WithTop ℕ) = distinguishedPairRunLength ω := by
      dsimp only [j]
      rw [WithTop.untopA_eq_untop hfinite]
      exact WithTop.coe_untop _ hfinite
    have hjt : j < t := by
      exact_mod_cast hjcoe.trans_lt hlt
    have hjdist : incrementPair j ω = distinguishedIncrementPair := hpre j hjt
    have hjnot := hittingAfter_mem_set_of_ne_top
      (u := incrementPair)
      (s := {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
      (n := 0) (ω := ω) hfinite
    have hjnot' : incrementPair j ω ≠ distinguishedIncrementPair := by
      simpa [distinguishedPairRunLength, j] using hjnot
    exact hjnot' hjdist

/-- Exact geometric law: the first non-distinguished pair occurs at `t`. -/
theorem distinguishedPairRunLength_prob (t : ℕ) :
    incrementLaw {ω | distinguishedPairRunLength ω = t} =
      (15 : ENNReal) / 16 ^ (t + 1) := by
  have hevent : {ω | distinguishedPairRunLength ω = t} =
      distinguishedPairPrefix t ∩
        iidBlock (X := Direction) (2 * t) 2 ⁻¹'
          {p | p ≠ distinguishedIncrementPair} := by
    ext ω
    simpa [incrementPair] using distinguishedPairRunLength_eq_iff ω t
  rw [hevent]
  unfold incrementLaw
  rw [measure_inter_iidBlock_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure) (2 * t) 2
    (measurableSet_distinguishedPairPrefix t) (by measurability)]
  rw [directionPair_product_ne_distinguished]
  have hprefix := distinguishedPairPrefix_prob t
  unfold incrementLaw at hprefix
  rw [hprefix]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num [inv_eq_one_div]
  rw [one_div, inv_pow, pow_succ]
  field_simp

/-! ### Joint law of successive pair runs -/

/-- The next `t` pairs beginning at pair index `start` are distinguished. -/
def distinguishedPairPrefixFrom (start t : ℕ) : Set (ℕ → Direction) :=
  {ω | ∀ r < t,
    incrementPair (start + r) ω = distinguishedIncrementPair}

theorem measurable_incrementPair_iidTail {start r : ℕ} (hsr : start ≤ r) :
    Measurable[iidTail (X := Direction) (2 * start)] (incrementPair r) := by
  let _ : MeasurableSpace (ℕ → Direction) :=
    iidTail (X := Direction) (2 * start)
  apply measurable_pi_lambda
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (2 * r + (i : ℕ))
    (le_iSup_of_le (by omega : 2 * start ≤ 2 * r + (i : ℕ)) le_rfl)

theorem iidHistory_mono_local {a b : ℕ} (hab : a ≤ b) :
    iidHistory (X := Direction) a ≤ iidHistory (X := Direction) b := by
  refine iSup_le fun i ↦ iSup_le fun hia ↦ ?_
  exact le_iSup_of_le i (le_iSup_of_le (hia.trans_le hab) le_rfl)

theorem iidTail_anti_local {a b : ℕ} (hab : a ≤ b) :
    iidTail (X := Direction) b ≤ iidTail (X := Direction) a := by
  refine iSup_le fun i ↦ iSup_le fun hbi ↦ ?_
  exact le_iSup_of_le i (le_iSup_of_le (hab.trans hbi) le_rfl)

theorem measurableSet_distinguishedPairPrefixFrom_iidHistory
    (start t : ℕ) :
    MeasurableSet[iidHistory (X := Direction) (2 * (start + t))]
      (distinguishedPairPrefixFrom start t) := by
  have heq : distinguishedPairPrefixFrom start t =
      ⋂ r : Fin t,
        {ω | incrementPair (start + r) ω = distinguishedIncrementPair} := by
    ext ω
    simp only [distinguishedPairPrefixFrom, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h r
      exact h r r.isLt
    · intro h r hr
      exact h ⟨r, hr⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro r
  exact (measurable_incrementPair_iidHistory
      (show start + (r : ℕ) < start + t by omega))
    (measurableSet_singleton distinguishedIncrementPair)

theorem measurableSet_distinguishedPairPrefixFrom_iidTail
    (start t : ℕ) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (distinguishedPairPrefixFrom start t) := by
  have heq : distinguishedPairPrefixFrom start t =
      ⋂ r : Fin t,
        {ω | incrementPair (start + r) ω = distinguishedIncrementPair} := by
    ext ω
    simp only [distinguishedPairPrefixFrom, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h r
      exact h r r.isLt
    · intro h r hr
      exact h ⟨r, hr⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro r
  exact (measurable_incrementPair_iidTail
      (show start ≤ start + (r : ℕ) by omega))
    (measurableSet_singleton distinguishedIncrementPair)

theorem distinguishedPairPrefixFrom_zero (start : ℕ) :
    distinguishedPairPrefixFrom start 0 = Set.univ := by
  ext ω
  simp [distinguishedPairPrefixFrom]

theorem distinguishedPairPrefixFrom_succ (start t : ℕ) :
    distinguishedPairPrefixFrom start (t + 1) =
      distinguishedPairPrefixFrom start t ∩
        {ω | incrementPair (start + t) ω = distinguishedIncrementPair} := by
  ext ω
  simp only [distinguishedPairPrefixFrom, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun r hr ↦ h r (by omega), h t (by omega)⟩
  · rintro ⟨hpre, ht⟩ r hr
    obtain hlt | rfl := Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hr)
    · exact hpre r hlt
    · exact ht

theorem distinguishedPairPrefixFrom_prob (start t : ℕ) :
    incrementLaw (distinguishedPairPrefixFrom start t) =
      ((16 : ENNReal)⁻¹) ^ t := by
  induction t with
  | zero =>
      rw [distinguishedPairPrefixFrom_zero, measure_univ]
      simp
  | succ t ih =>
      rw [show t + 1 = t.succ by omega,
        distinguishedPairPrefixFrom_succ]
      unfold incrementPair incrementLaw at *
      change (Measure.infinitePi fun _ : ℕ ↦
          (PMF.uniformOfFintype Direction).toMeasure)
        (distinguishedPairPrefixFrom start t ∩
          iidBlock (X := Direction) (2 * (start + t)) 2 ⁻¹'
            {distinguishedIncrementPair}) = (16 : ENNReal)⁻¹ ^ t.succ
      rw [measure_inter_iidBlock_eq_mul
        ((PMF.uniformOfFintype Direction).toMeasure) (2 * (start + t)) 2
        (measurableSet_distinguishedPairPrefixFrom_iidHistory start t)
        (measurableSet_singleton distinguishedIncrementPair)]
      rw [directionPair_product_singleton, ih]
      simp [pow_succ]

/-- A run of exactly `t` distinguished pairs, followed by a non-distinguished
pair, beginning at pair index `start`. -/
def distinguishedPairRunSegment (start t : ℕ) : Set (ℕ → Direction) :=
  distinguishedPairPrefixFrom start t ∩
    {ω | incrementPair (start + t) ω ≠ distinguishedIncrementPair}

theorem measurableSet_distinguishedPairRunSegment_iidHistory
    (start t : ℕ) :
    MeasurableSet[iidHistory (X := Direction) (2 * (start + t + 1))]
      (distinguishedPairRunSegment start t) := by
  change MeasurableSet[iidHistory (X := Direction) (2 * (start + t + 1))]
    (distinguishedPairPrefixFrom start t ∩
      incrementPair (start + t) ⁻¹'
        {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
  apply ((iidHistory_mono_local
    (show 2 * (start + t) ≤ 2 * (start + t + 1) by omega)) _
      (measurableSet_distinguishedPairPrefixFrom_iidHistory start t)).inter
  exact (measurable_incrementPair_iidHistory
      (show start + t < start + t + 1 by omega))
    (show MeasurableSet
      {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair} by measurability)

theorem measurableSet_distinguishedPairRunSegment_iidTail
    (start t : ℕ) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (distinguishedPairRunSegment start t) := by
  change MeasurableSet[iidTail (X := Direction) (2 * start)]
    (distinguishedPairPrefixFrom start t ∩
      incrementPair (start + t) ⁻¹'
        {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair})
  exact (measurableSet_distinguishedPairPrefixFrom_iidTail start t).inter
    ((measurable_incrementPair_iidTail
      (show start ≤ start + t by omega))
    (show MeasurableSet
      {p : Fin 2 → Direction | p ≠ distinguishedIncrementPair} by measurability))

theorem distinguishedPairRunSegment_prob (start t : ℕ) :
    incrementLaw (distinguishedPairRunSegment start t) =
      (15 : ENNReal) / 16 ^ (t + 1) := by
  change incrementLaw
    (distinguishedPairPrefixFrom start t ∩
      iidBlock (X := Direction) (2 * (start + t)) 2 ⁻¹'
        {p | p ≠ distinguishedIncrementPair}) = _
  unfold incrementLaw
  rw [measure_inter_iidBlock_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure) (2 * (start + t)) 2
    (measurableSet_distinguishedPairPrefixFrom_iidHistory start t)
    (by measurability)]
  rw [directionPair_product_ne_distinguished]
  have hprefix := distinguishedPairPrefixFrom_prob start t
  unfold incrementLaw at hprefix
  rw [hprefix]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num [inv_eq_one_div]
  rw [one_div, inv_pow, pow_succ]
  field_simp

/-- The cylinder event saying that the successive run lengths, beginning at
pair `start`, are exactly the entries of `lengths`. -/
def firstPairRunLengthsEqFrom :
    ℕ → List ℕ → Set (ℕ → Direction)
  | _, [] => Set.univ
  | start, t :: ts =>
      distinguishedPairRunSegment start t ∩
        firstPairRunLengthsEqFrom (start + t + 1) ts

theorem measurableSet_firstPairRunLengthsEqFrom_iidTail
    (start : ℕ) (lengths : List ℕ) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (firstPairRunLengthsEqFrom start lengths) := by
  induction lengths generalizing start with
  | nil => simp [firstPairRunLengthsEqFrom]
  | cons t ts ih =>
      rw [firstPairRunLengthsEqFrom]
      refine (measurableSet_distinguishedPairRunSegment_iidTail start t).inter ?_
      exact (iidTail_anti_local
        (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
          (ih (start := start + t + 1))

/-- Joint product law for any finite list of successive run lengths.  Thus
the run lengths are iid geometric with non-distinguished success probability
`15/16`. -/
theorem firstPairRunLengthsEqFrom_prob (start : ℕ) (lengths : List ℕ) :
    incrementLaw (firstPairRunLengthsEqFrom start lengths) =
      (lengths.map fun t ↦ (15 : ENNReal) / 16 ^ (t + 1)).prod := by
  induction lengths generalizing start with
  | nil =>
      rw [firstPairRunLengthsEqFrom, measure_univ]
      simp
  | cons t ts ih =>
      rw [firstPairRunLengthsEqFrom]
      have hInd : IndepSet
          (distinguishedPairRunSegment start t)
          (firstPairRunLengthsEqFrom (start + t + 1) ts)
          incrementLaw := by
        unfold incrementLaw
        exact (iidHistory_indep_iidTail
            ((PMF.uniformOfFintype Direction).toMeasure)
            (2 * (start + t + 1))).indepSet_of_measurableSet
          (measurableSet_distinguishedPairRunSegment_iidHistory start t)
          (measurableSet_firstPairRunLengthsEqFrom_iidTail
            (start + t + 1) ts)
      rw [hInd.measure_inter_eq_mul]
      rw [distinguishedPairRunSegment_prob, ih]
      simp

/-- Joint law for the first run lengths from pair zero. -/
theorem firstPairRunLengthsEq_prob (lengths : List ℕ) :
    incrementLaw (firstPairRunLengthsEqFrom 0 lengths) =
      (lengths.map fun t ↦ (15 : ENNReal) / 16 ^ (t + 1)).prod :=
  firstPairRunLengthsEqFrom_prob 0 lengths

abbrev IncrementPair := Fin 2 → Direction

/-- A run of `t` distinguished pairs whose terminal pair has the exact label
`p`, beginning at pair index `start`. -/
def distinguishedPairRunSegmentWithLabel
    (start t : ℕ) (p : IncrementPair) : Set (ℕ → Direction) :=
  distinguishedPairPrefixFrom start t ∩
    {ω | incrementPair (start + t) ω = p}

theorem measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
    (start t : ℕ) (p : IncrementPair) :
    MeasurableSet[iidHistory (X := Direction) (2 * (start + t + 1))]
      (distinguishedPairRunSegmentWithLabel start t p) := by
  change MeasurableSet[iidHistory (X := Direction) (2 * (start + t + 1))]
    (distinguishedPairPrefixFrom start t ∩
      incrementPair (start + t) ⁻¹' {p})
  apply ((iidHistory_mono_local
    (show 2 * (start + t) ≤ 2 * (start + t + 1) by omega)) _
      (measurableSet_distinguishedPairPrefixFrom_iidHistory start t)).inter
  exact (measurable_incrementPair_iidHistory
      (show start + t < start + t + 1 by omega))
    (measurableSet_singleton p)

theorem measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
    (start t : ℕ) (p : IncrementPair) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (distinguishedPairRunSegmentWithLabel start t p) := by
  change MeasurableSet[iidTail (X := Direction) (2 * start)]
    (distinguishedPairPrefixFrom start t ∩
      incrementPair (start + t) ⁻¹' {p})
  exact (measurableSet_distinguishedPairPrefixFrom_iidTail start t).inter
    ((measurable_incrementPair_iidTail
      (show start ≤ start + t by omega)) (measurableSet_singleton p))

theorem distinguishedPairRunSegmentWithLabel_prob
    (start t : ℕ) (p : IncrementPair) :
    incrementLaw (distinguishedPairRunSegmentWithLabel start t p) =
      ((16 : ENNReal)⁻¹) ^ (t + 1) := by
  change incrementLaw
    (distinguishedPairPrefixFrom start t ∩
      iidBlock (X := Direction) (2 * (start + t)) 2 ⁻¹' {p}) = _
  unfold incrementLaw
  rw [measure_inter_iidBlock_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure) (2 * (start + t)) 2
    (measurableSet_distinguishedPairPrefixFrom_iidHistory start t)
    (measurableSet_singleton p)]
  rw [directionPair_product_singleton]
  have hprefix := distinguishedPairPrefixFrom_prob start t
  unfold incrementLaw at hprefix
  rw [hprefix]
  simp [pow_succ]

/-- The exact joint cylinder for a finite list `(run length, terminal pair)`. -/
def firstPairRunsWithLabelsEqFrom :
    ℕ → List (ℕ × IncrementPair) → Set (ℕ → Direction)
  | _, [] => Set.univ
  | start, (t, p) :: runs =>
      distinguishedPairRunSegmentWithLabel start t p ∩
        firstPairRunsWithLabelsEqFrom (start + t + 1) runs

theorem measurableSet_firstPairRunsWithLabelsEqFrom_iidTail
    (start : ℕ) (runs : List (ℕ × IncrementPair)) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (firstPairRunsWithLabelsEqFrom start runs) := by
  induction runs generalizing start with
  | nil => simp [firstPairRunsWithLabelsEqFrom]
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      rw [firstPairRunsWithLabelsEqFrom]
      refine (measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
        start t p).inter ?_
      exact (iidTail_anti_local
        (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
          (ih (start := start + t + 1))

/-- Exact joint law of finitely many run lengths and terminal labels. -/
theorem firstPairRunsWithLabelsEqFrom_prob
    (start : ℕ) (runs : List (ℕ × IncrementPair)) :
    incrementLaw (firstPairRunsWithLabelsEqFrom start runs) =
      (runs.map fun run ↦ ((16 : ENNReal)⁻¹) ^ (run.1 + 1)).prod := by
  induction runs generalizing start with
  | nil =>
      rw [firstPairRunsWithLabelsEqFrom, measure_univ]
      simp
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      rw [firstPairRunsWithLabelsEqFrom]
      have hInd : IndepSet
          (distinguishedPairRunSegmentWithLabel start t p)
          (firstPairRunsWithLabelsEqFrom (start + t + 1) runs)
          incrementLaw := by
        unfold incrementLaw
        exact (iidHistory_indep_iidTail
            ((PMF.uniformOfFintype Direction).toMeasure)
            (2 * (start + t + 1))).indepSet_of_measurableSet
          (measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
            start t p)
          (measurableSet_firstPairRunsWithLabelsEqFrom_iidTail
            (start + t + 1) runs)
      rw [hInd.measure_inter_eq_mul]
      rw [distinguishedPairRunSegmentWithLabel_prob, ih]
      simp

private theorem inv_sixteen_pow_eq_geometric_mul_inv_fifteen (t : ℕ) :
    ((16 : ENNReal)⁻¹) ^ (t + 1) =
      ((15 : ENNReal) / 16 ^ (t + 1)) * (15 : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_mul, ENNReal.toReal_div]
  field_simp
  rw [one_div, inv_pow, inv_mul_cancel₀ (by positivity)]

/-- Factorization of the joint atom into the iid geometric run-length mass
and the uniform mass `1/15` of each fixed non-distinguished terminal label.
The label condition gives this the intended terminal-pair interpretation. -/
theorem firstPairRunsWithLabelsEqFrom_prob_factorized
    (start : ℕ) (runs : List (ℕ × IncrementPair))
    (hnondist : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairRunsWithLabelsEqFrom start runs) =
      (runs.map fun run ↦ (15 : ENNReal) / 16 ^ (run.1 + 1)).prod *
        ((15 : ENNReal)⁻¹) ^ runs.length := by
  rw [firstPairRunsWithLabelsEqFrom_prob]
  induction runs with
  | nil => simp
  | cons run runs ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [inv_sixteen_pow_eq_geometric_mul_inv_fifteen]
      rw [ih (fun r hr ↦ hnondist r (by simp [hr]))]
      rw [pow_succ]
      ring

/-- Finite-atom conditional statement: after dividing by the mass
`15^{-q}` of a fixed list of `q` non-distinguished terminal labels, the run
length vector has the iid geometric `(15/16)` product mass. -/
theorem firstPairRunLengths_conditional_mass_of_terminalLabels
    (start : ℕ) (runs : List (ℕ × IncrementPair))
    (hnondist : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairRunsWithLabelsEqFrom start runs) /
        (((15 : ENNReal)⁻¹) ^ runs.length) =
      (runs.map fun run ↦ (15 : ENNReal) / 16 ^ (run.1 + 1)).prod := by
  rw [firstPairRunsWithLabelsEqFrom_prob_factorized start runs hnondist]
  rw [ENNReal.mul_div_cancel_right]
  · exact pow_ne_zero _ (by norm_num)
  · exact ENNReal.pow_ne_top (by norm_num)

/-! ### Marginal law of the terminal labels -/

theorem disjoint_distinguishedPairRunSegmentWithLabel
    (start : ℕ) {p : IncrementPair}
    (hp : p ≠ distinguishedIncrementPair) {t u : ℕ} (htu : t ≠ u) :
    Disjoint (distinguishedPairRunSegmentWithLabel start t p)
      (distinguishedPairRunSegmentWithLabel start u p) := by
  rw [Set.disjoint_left]
  intro ω ht hu
  change ω ∈ distinguishedPairPrefixFrom start t ∩
    {ω | incrementPair (start + t) ω = p} at ht
  change ω ∈ distinguishedPairPrefixFrom start u ∩
    {ω | incrementPair (start + u) ω = p} at hu
  rcases lt_or_gt_of_ne htu with htu | hut
  · have hdist : incrementPair (start + t) ω = distinguishedIncrementPair :=
      hu.1 t htu
    exact hp (ht.2.symm.trans hdist)
  · have hdist : incrementPair (start + u) ω = distinguishedIncrementPair :=
      ht.1 u hut
    exact hp (hu.2.symm.trans hdist)

/-- Event that the successive non-distinguished terminal pairs have the
specified labels, with the intervening run lengths left unrestricted. -/
noncomputable def firstPairTerminalLabelsEqFrom :
    ℕ → List IncrementPair → Set (ℕ → Direction)
  | _, [] => Set.univ
  | start, p :: labels =>
      ⋃ t : ℕ, distinguishedPairRunSegmentWithLabel start t p ∩
        firstPairTerminalLabelsEqFrom (start + t + 1) labels

theorem measurableSet_firstPairTerminalLabelsEqFrom_iidTail
    (start : ℕ) (labels : List IncrementPair) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (firstPairTerminalLabelsEqFrom start labels) := by
  induction labels generalizing start with
  | nil => simp [firstPairTerminalLabelsEqFrom]
  | cons p labels ih =>
      rw [firstPairTerminalLabelsEqFrom]
      apply MeasurableSet.iUnion
      intro t
      refine (measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
        start t p).inter ?_
      exact (iidTail_anti_local
        (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
          (ih (start := start + t + 1))

private theorem tsum_inv_sixteen_pow_succ :
    (∑' t : ℕ, ((16 : ENNReal)⁻¹) ^ (t + 1)) =
      (15 : ENNReal)⁻¹ := by
  rw [ENNReal.tsum_geometric_add_one]
  have hfinite : (16 : ENNReal)⁻¹ * (1 - (16 : ENNReal)⁻¹)⁻¹ ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    apply (ENNReal.inv_ne_top).2
    exact (show 0 < 1 - (16 : ENNReal)⁻¹ by norm_num).ne'
  apply (ENNReal.toReal_eq_toReal_iff' hfinite (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_sub_of_le (by norm_num) (by norm_num)]
  norm_num

/-- The successive terminal labels are uniform on the fifteen
non-distinguished pairs. -/
theorem firstPairTerminalLabelsEqFrom_prob
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairTerminalLabelsEqFrom start labels) =
      ((15 : ENNReal)⁻¹) ^ labels.length := by
  induction labels generalizing start with
  | nil =>
      rw [firstPairTerminalLabelsEqFrom, measure_univ]
      simp
  | cons p labels ih =>
      have hp : p ≠ distinguishedIncrementPair :=
        hnondist p (by simp)
      have hlabels : ∀ q ∈ labels, q ≠ distinguishedIncrementPair := by
        intro q hq
        exact hnondist q (by simp [hq])
      rw [firstPairTerminalLabelsEqFrom]
      have hdisj : Pairwise fun t u : ℕ ↦ Disjoint
          (distinguishedPairRunSegmentWithLabel start t p ∩
            firstPairTerminalLabelsEqFrom (start + t + 1) labels)
          (distinguishedPairRunSegmentWithLabel start u p ∩
            firstPairTerminalLabelsEqFrom (start + u + 1) labels) := by
        intro t u htu
        exact (disjoint_distinguishedPairRunSegmentWithLabel start hp htu).mono
          Set.inter_subset_left Set.inter_subset_left
      have hmeas (t : ℕ) : MeasurableSet
          (distinguishedPairRunSegmentWithLabel start t p ∩
            firstPairTerminalLabelsEqFrom (start + t + 1) labels) := by
        exact iidTail_le (2 * start) _
          ((measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
            start t p).inter
            ((iidTail_anti_local
              (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
              (measurableSet_firstPairTerminalLabelsEqFrom_iidTail
                (start + t + 1) labels)))
      rw [measure_iUnion hdisj hmeas]
      have hpiece (t : ℕ) :
          incrementLaw
              (distinguishedPairRunSegmentWithLabel start t p ∩
                firstPairTerminalLabelsEqFrom (start + t + 1) labels) =
            ((16 : ENNReal)⁻¹) ^ (t + 1) *
              ((15 : ENNReal)⁻¹) ^ labels.length := by
        have hInd : IndepSet
            (distinguishedPairRunSegmentWithLabel start t p)
            (firstPairTerminalLabelsEqFrom (start + t + 1) labels)
            incrementLaw := by
          unfold incrementLaw
          exact (iidHistory_indep_iidTail
              ((PMF.uniformOfFintype Direction).toMeasure)
              (2 * (start + t + 1))).indepSet_of_measurableSet
            (measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
              start t p)
            (measurableSet_firstPairTerminalLabelsEqFrom_iidTail
              (start + t + 1) labels)
        rw [hInd.measure_inter_eq_mul]
        rw [distinguishedPairRunSegmentWithLabel_prob,
          ih (start := start + t + 1) hlabels]
      calc
        (∑' t : ℕ, incrementLaw
            (distinguishedPairRunSegmentWithLabel start t p ∩
              firstPairTerminalLabelsEqFrom (start + t + 1) labels)) =
            ∑' t : ℕ, ((16 : ENNReal)⁻¹) ^ (t + 1) *
              ((15 : ENNReal)⁻¹) ^ labels.length := by
                apply tsum_congr
                exact hpiece
        _ = (∑' t : ℕ, ((16 : ENNReal)⁻¹) ^ (t + 1)) *
              ((15 : ENNReal)⁻¹) ^ labels.length := ENNReal.tsum_mul_right
        _ = ((15 : ENNReal)⁻¹) ^ (p :: labels).length := by
          rw [tsum_inv_sixteen_pow_succ]
          simp [pow_succ, mul_comm]

/-- Literal conditional atom: divide the joint run-length/terminal-label
probability by the marginal probability of that fixed terminal-label list.
The result is the iid geometric `(15/16)` mass of the run lengths. -/
theorem firstPairRunLengths_conditional_on_terminalLabels
    (start : ℕ) (runs : List (ℕ × IncrementPair))
    (hnondist : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairRunsWithLabelsEqFrom start runs) /
        incrementLaw
          (firstPairTerminalLabelsEqFrom start (runs.map Prod.snd)) =
      (runs.map fun run ↦ (15 : ENNReal) / 16 ^ (run.1 + 1)).prod := by
  have hlabels : ∀ p ∈ runs.map Prod.snd,
      p ≠ distinguishedIncrementPair := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨run, hrun, rfl⟩
    exact hnondist run hrun
  rw [firstPairTerminalLabelsEqFrom_prob start (runs.map Prod.snd) hlabels]
  rw [List.length_map]
  exact firstPairRunLengths_conditional_mass_of_terminalLabels
    start runs hnondist


end Erdos1166
