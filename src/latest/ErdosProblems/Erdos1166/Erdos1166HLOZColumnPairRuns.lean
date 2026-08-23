/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZPairingProfiles
import ErdosProblems.Erdos1166.Erdos1166HLOZReconstruction
import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalPairRuns
import ErdosProblems.Erdos1166.Erdos1166HLOZSourceInstantiation
import ErdosProblems.Erdos1166.Erdos1166HLOZProp42InverseLaw

/-!
# Adaptive pair runs for the `Y` column deletion

The column deletion does not inspect every temporal pair: whether an
`(+e₁,-e₁)` run is removed is determined by the first-coordinate parity of
the current deleted-path endpoint.  On a *fixed* deleted pair path this is a
deterministic active/inactive mask.  This file proves the exact finite
conditional mass calculation for such a mask.

At an active entry, `some t` records `t` distinguished pairs followed by a
fixed non-distinguished terminal pair.  At an inactive entry, `none` records
one fixed pair without deleting it.  Thus active entries contribute the
geometric `(15/16)` mass, while inactive entries cancel completely when one
conditions on the fixed terminal path.  This is the probability core needed
by the separate `Y`-phase parser; no time-parity atom is used here.
-/

namespace Erdos1166.HLOZColumnPairRuns

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZReconstruction HLOZPairingProfiles HLOZSourceInstantiation
  HLOZPrimedStopped HLOZProp42InverseLaw

abbrev IncrementPair := Fin 2 → Direction

/-- One entry of an adaptively masked pair parser.  `some t` is an active
column endpoint with holding count `t`; `none` is an inactive endpoint. -/
abbrev SelectivePairRun := Option ℕ × IncrementPair

/-- The exact cylinder belonging to a fixed active/inactive run list. -/
def selectivePairRunsEqFrom :
    ℕ → List SelectivePairRun → Set (ℕ → Direction)
  | _, [] => Set.univ
  | start, (some t, p) :: runs =>
      distinguishedPairRunSegmentWithLabel start t p ∩
        selectivePairRunsEqFrom (start + t + 1) runs
  | start, (none, p) :: runs =>
      {ω | incrementPair start ω = p} ∩
        selectivePairRunsEqFrom (start + 1) runs

theorem measurableSet_incrementPair_eq_iidHistory
    (start : ℕ) (p : IncrementPair) :
    MeasurableSet[iidHistory (X := Direction) (2 * (start + 1))]
      {ω | incrementPair start ω = p} := by
  exact (measurable_incrementPair_iidHistory
      (show start < start + 1 by omega)) (measurableSet_singleton p)

theorem measurableSet_incrementPair_eq_iidTail
    (start : ℕ) (p : IncrementPair) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      {ω | incrementPair start ω = p} := by
  exact (measurable_incrementPair_iidTail (le_refl start))
    (measurableSet_singleton p)

theorem measurableSet_selectivePairRunsEqFrom_iidTail
    (start : ℕ) (runs : List SelectivePairRun) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (selectivePairRunsEqFrom start runs) := by
  induction runs generalizing start with
  | nil => simp [selectivePairRunsEqFrom]
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot with
      | none =>
          rw [selectivePairRunsEqFrom]
          exact (measurableSet_incrementPair_eq_iidTail start p).inter
            ((iidTail_anti_local
              (show 2 * start ≤ 2 * (start + 1) by omega)) _
              (ih (start := start + 1)))
      | some t =>
          rw [selectivePairRunsEqFrom]
          exact
            (measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
              start t p).inter
            ((iidTail_anti_local
              (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
              (ih (start := start + t + 1)))

/-- Raw joint mass of one selective run entry. -/
noncomputable def selectiveJointFactor : SelectivePairRun → ℝ≥0∞
  | (none, _) => (16 : ℝ≥0∞)⁻¹
  | (some t, _) => ((16 : ℝ≥0∞)⁻¹) ^ (t + 1)

theorem selectivePairRunsEqFrom_prob
    (start : ℕ) (runs : List SelectivePairRun) :
    incrementLaw (selectivePairRunsEqFrom start runs) =
      (runs.map selectiveJointFactor).prod := by
  induction runs generalizing start with
  | nil =>
      rw [selectivePairRunsEqFrom, measure_univ]
      simp
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot with
      | none =>
          rw [selectivePairRunsEqFrom]
          have hInd : IndepSet {ω | incrementPair start ω = p}
              (selectivePairRunsEqFrom (start + 1) runs) incrementLaw := by
            unfold incrementLaw
            exact (iidHistory_indep_iidTail
                ((PMF.uniformOfFintype Direction).toMeasure)
                (2 * (start + 1))).indepSet_of_measurableSet
              (measurableSet_incrementPair_eq_iidHistory start p)
              (measurableSet_selectivePairRunsEqFrom_iidTail
                (start + 1) runs)
          rw [hInd.measure_inter_eq_mul, incrementPair_prob,
            ih (start := start + 1)]
          rfl
      | some t =>
          rw [selectivePairRunsEqFrom]
          have hInd : IndepSet
              (distinguishedPairRunSegmentWithLabel start t p)
              (selectivePairRunsEqFrom (start + t + 1) runs)
              incrementLaw := by
            unfold incrementLaw
            exact (iidHistory_indep_iidTail
                ((PMF.uniformOfFintype Direction).toMeasure)
                (2 * (start + t + 1))).indepSet_of_measurableSet
              (measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
                start t p)
              (measurableSet_selectivePairRunsEqFrom_iidTail
                (start + t + 1) runs)
          rw [hInd.measure_inter_eq_mul,
            distinguishedPairRunSegmentWithLabel_prob,
            ih (start := start + t + 1)]
          rfl

/-- Forget the active run lengths but retain both the active mask and the
fixed terminal labels. -/
def selectiveTerminalSpec (runs : List SelectivePairRun) :
    List (Bool × IncrementPair) :=
  runs.map fun run ↦ (run.1.isSome, run.2)

/-- Event fixing a terminal pair path and its adaptive active mask, while
leaving every active holding count unrestricted. -/
noncomputable def selectiveTerminalLabelsEqFrom :
    ℕ → List (Bool × IncrementPair) → Set (ℕ → Direction)
  | _, [] => Set.univ
  | start, (true, p) :: specs =>
      ⋃ t : ℕ, distinguishedPairRunSegmentWithLabel start t p ∩
        selectiveTerminalLabelsEqFrom (start + t + 1) specs
  | start, (false, p) :: specs =>
      {ω | incrementPair start ω = p} ∩
        selectiveTerminalLabelsEqFrom (start + 1) specs

def SelectiveTerminalValid (specs : List (Bool × IncrementPair)) : Prop :=
  ∀ spec ∈ specs, spec.1 = true →
    spec.2 ≠ distinguishedIncrementPair

theorem measurableSet_selectiveTerminalLabelsEqFrom_iidTail
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    MeasurableSet[iidTail (X := Direction) (2 * start)]
      (selectiveTerminalLabelsEqFrom start specs) := by
  induction specs generalizing start with
  | nil => simp [selectiveTerminalLabelsEqFrom]
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active with
      | false =>
          rw [selectiveTerminalLabelsEqFrom]
          exact (measurableSet_incrementPair_eq_iidTail start p).inter
            ((iidTail_anti_local
              (show 2 * start ≤ 2 * (start + 1) by omega)) _
              (ih (start := start + 1)))
      | true =>
          rw [selectiveTerminalLabelsEqFrom]
          apply MeasurableSet.iUnion
          intro t
          exact
            (measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
              start t p).inter
            ((iidTail_anti_local
              (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
              (ih (start := start + t + 1)))

/-- Marginal mass of one fixed terminal label: `1/15` at active entries
and `1/16` at inactive entries. -/
noncomputable def selectiveTerminalFactor : Bool × IncrementPair → ℝ≥0∞
  | (true, _) => (15 : ℝ≥0∞)⁻¹
  | (false, _) => (16 : ℝ≥0∞)⁻¹

private theorem tsum_inv_sixteen_pow_succ :
    (∑' t : ℕ, ((16 : ℝ≥0∞)⁻¹) ^ (t + 1)) =
      (15 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.tsum_geometric_add_one]
  have hfinite : (16 : ℝ≥0∞)⁻¹ * (1 - (16 : ℝ≥0∞)⁻¹)⁻¹ ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    apply (ENNReal.inv_ne_top).2
    exact (show 0 < 1 - (16 : ℝ≥0∞)⁻¹ by norm_num).ne'
  apply (ENNReal.toReal_eq_toReal_iff' hfinite (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_sub_of_le (by norm_num) (by norm_num)]
  norm_num

theorem selectiveTerminalLabelsEqFrom_prob
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (hvalid : SelectiveTerminalValid specs) :
    incrementLaw (selectiveTerminalLabelsEqFrom start specs) =
      (specs.map selectiveTerminalFactor).prod := by
  induction specs generalizing start with
  | nil =>
      rw [selectiveTerminalLabelsEqFrom, measure_univ]
      simp
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      have htail : SelectiveTerminalValid specs := by
        intro s hs
        exact hvalid s (by simp [hs])
      cases active with
      | false =>
          rw [selectiveTerminalLabelsEqFrom]
          have hInd : IndepSet {ω | incrementPair start ω = p}
              (selectiveTerminalLabelsEqFrom (start + 1) specs)
              incrementLaw := by
            unfold incrementLaw
            exact (iidHistory_indep_iidTail
                ((PMF.uniformOfFintype Direction).toMeasure)
                (2 * (start + 1))).indepSet_of_measurableSet
              (measurableSet_incrementPair_eq_iidHistory start p)
              (measurableSet_selectiveTerminalLabelsEqFrom_iidTail
                (start + 1) specs)
          rw [hInd.measure_inter_eq_mul, incrementPair_prob,
            ih (start := start + 1) htail]
          rfl
      | true =>
          have hp : p ≠ distinguishedIncrementPair :=
            hvalid (true, p) (by simp) rfl
          rw [selectiveTerminalLabelsEqFrom]
          have hdisj : Pairwise fun t u : ℕ ↦ Disjoint
              (distinguishedPairRunSegmentWithLabel start t p ∩
                selectiveTerminalLabelsEqFrom (start + t + 1) specs)
              (distinguishedPairRunSegmentWithLabel start u p ∩
                selectiveTerminalLabelsEqFrom (start + u + 1) specs) := by
            intro t u htu
            exact (disjoint_distinguishedPairRunSegmentWithLabel
              start hp htu).mono Set.inter_subset_left Set.inter_subset_left
          have hmeas (t : ℕ) : MeasurableSet
              (distinguishedPairRunSegmentWithLabel start t p ∩
                selectiveTerminalLabelsEqFrom (start + t + 1) specs) :=
            iidTail_le (2 * start) _
              ((measurableSet_distinguishedPairRunSegmentWithLabel_iidTail
                start t p).inter
                ((iidTail_anti_local
                  (show 2 * start ≤ 2 * (start + t + 1) by omega)) _
                  (measurableSet_selectiveTerminalLabelsEqFrom_iidTail
                    (start + t + 1) specs)))
          rw [measure_iUnion hdisj hmeas]
          have hpiece (t : ℕ) :
              incrementLaw
                  (distinguishedPairRunSegmentWithLabel start t p ∩
                    selectiveTerminalLabelsEqFrom
                      (start + t + 1) specs) =
                ((16 : ℝ≥0∞)⁻¹) ^ (t + 1) *
                  (specs.map selectiveTerminalFactor).prod := by
            have hInd : IndepSet
                (distinguishedPairRunSegmentWithLabel start t p)
                (selectiveTerminalLabelsEqFrom (start + t + 1) specs)
                incrementLaw := by
              unfold incrementLaw
              exact (iidHistory_indep_iidTail
                  ((PMF.uniformOfFintype Direction).toMeasure)
                  (2 * (start + t + 1))).indepSet_of_measurableSet
                (measurableSet_distinguishedPairRunSegmentWithLabel_iidHistory
                  start t p)
                (measurableSet_selectiveTerminalLabelsEqFrom_iidTail
                  (start + t + 1) specs)
            rw [hInd.measure_inter_eq_mul,
              distinguishedPairRunSegmentWithLabel_prob,
              ih (start := start + t + 1) htail]
          calc
            (∑' t : ℕ, incrementLaw
                (distinguishedPairRunSegmentWithLabel start t p ∩
                  selectiveTerminalLabelsEqFrom
                    (start + t + 1) specs)) =
                ∑' t : ℕ, ((16 : ℝ≥0∞)⁻¹) ^ (t + 1) *
                  (specs.map selectiveTerminalFactor).prod := by
                    apply tsum_congr
                    exact hpiece
            _ = (∑' t : ℕ, ((16 : ℝ≥0∞)⁻¹) ^ (t + 1)) *
                  (specs.map selectiveTerminalFactor).prod :=
              ENNReal.tsum_mul_right
            _ = (List.map selectiveTerminalFactor
                  ((true, p) :: specs)).prod := by
              rw [tsum_inv_sixteen_pow_succ]
              rfl

/-- Product of the geometric factors belonging to the active entries.
Inactive entries contribute one. -/
noncomputable def selectiveRunFactor : SelectivePairRun → ℝ≥0∞
  | (none, _) => 1
  | (some t, _) => (15 : ℝ≥0∞) / 16 ^ (t + 1)

theorem selectiveJointFactor_eq_run_mul_terminal
    (run : SelectivePairRun) :
    selectiveJointFactor run = selectiveRunFactor run *
      selectiveTerminalFactor (run.1.isSome, run.2) := by
  rcases run with ⟨ot, p⟩
  cases ot with
  | none => simp [selectiveJointFactor, selectiveRunFactor,
      selectiveTerminalFactor]
  | some t =>
      simp only [selectiveJointFactor, selectiveRunFactor,
        selectiveTerminalFactor, Option.isSome_some]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
        (by finiteness)).mp
      simp only [ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_div]
      field_simp
      rw [one_div, inv_pow, inv_mul_cancel₀ (by positivity)]

theorem selectivePairRunsEqFrom_prob_factorized
    (start : ℕ) (runs : List SelectivePairRun) :
    incrementLaw (selectivePairRunsEqFrom start runs) =
      (runs.map selectiveRunFactor).prod *
        ((selectiveTerminalSpec runs).map selectiveTerminalFactor).prod := by
  rw [selectivePairRunsEqFrom_prob]
  induction runs with
  | nil => simp [selectiveTerminalSpec]
  | cons run runs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [selectiveJointFactor_eq_run_mul_terminal, ih]
      simp only [selectiveTerminalSpec, List.map_cons, List.prod_cons]
      ring

/-- The exact conditional atom calculation for a fixed adaptive mask. -/
theorem selectivePairRuns_conditional_mass
    (start : ℕ) (runs : List SelectivePairRun)
    (hvalid : SelectiveTerminalValid (selectiveTerminalSpec runs)) :
    incrementLaw (selectivePairRunsEqFrom start runs) /
        incrementLaw (selectiveTerminalLabelsEqFrom start
          (selectiveTerminalSpec runs)) =
      (runs.map selectiveRunFactor).prod := by
  rw [selectivePairRunsEqFrom_prob_factorized,
    selectiveTerminalLabelsEqFrom_prob _ _ hvalid]
  have hne_zero (specs : List (Bool × IncrementPair)) :
      (specs.map selectiveTerminalFactor).prod ≠ 0 := by
    induction specs with
    | nil => simp
    | cons spec specs ih =>
        rcases spec with ⟨active, p⟩
        cases active
        · simp only [List.map_cons, List.prod_cons, selectiveTerminalFactor]
          exact mul_ne_zero (by norm_num) ih
        · simp only [List.map_cons, List.prod_cons, selectiveTerminalFactor]
          exact mul_ne_zero (by norm_num) ih
  have hne_top (specs : List (Bool × IncrementPair)) :
      (specs.map selectiveTerminalFactor).prod ≠ ⊤ := by
    induction specs with
    | nil => simp
    | cons spec specs ih =>
        rcases spec with ⟨active, p⟩
        cases active
        · simp only [List.map_cons, List.prod_cons, selectiveTerminalFactor]
          exact ENNReal.mul_ne_top (by norm_num) ih
        · simp only [List.map_cons, List.prod_cons, selectiveTerminalFactor]
          exact ENNReal.mul_ne_top (by norm_num) ih
  rw [ENNReal.mul_div_cancel_right]
  · exact hne_zero _
  · exact hne_top _

theorem selectivePairRuns_subset_terminalLabels
    (start : ℕ) (runs : List SelectivePairRun) :
    selectivePairRunsEqFrom start runs ⊆
      selectiveTerminalLabelsEqFrom start (selectiveTerminalSpec runs) := by
  induction runs generalizing start with
  | nil => simp [selectivePairRunsEqFrom, selectiveTerminalLabelsEqFrom,
      selectiveTerminalSpec]
  | cons run runs ih =>
      rcases run with ⟨ot, p⟩
      cases ot with
      | none =>
          rintro ω ⟨hp, htail⟩
          exact ⟨hp, ih (start := start + 1) htail⟩
      | some t =>
          rintro ω ⟨hseg, htail⟩
          simp only [selectiveTerminalSpec, List.map_cons,
            Option.isSome_some, selectiveTerminalLabelsEqFrom]
          exact Set.mem_iUnion.mpr
            ⟨t, hseg, ih (start := start + t + 1) htail⟩

/-! ### From finite conditional masses to a joint vector law -/

/-- Deterministic finite parser data for one fixed adaptive terminal path.
The probability theorem below supplies its iid-geometric vector law.  Thus a
consumer need only construct the encoding, coverage, and uniqueness facts;
it must not assume the law separately. -/
structure SelectivePairVectorEncoding
    (start : ℕ) (specs : List (Bool × IncrementPair)) where
  q : ℕ
  encode : (Fin q → ℕ) → List SelectivePairRun
  terminal_spec : ∀ v, selectiveTerminalSpec (encode v) = specs
  run_factor : ∀ v,
    ((encode v).map selectiveRunFactor).prod =
      ∏ i, (15 : ℝ≥0∞) / 16 ^ (v i + 1)
  cover : ∀ ω ∈ selectiveTerminalLabelsEqFrom start specs,
    ∃ v, ω ∈ selectivePairRunsEqFrom start (encode v)
  unique : ∀ {ω v w},
    ω ∈ selectivePairRunsEqFrom start (encode v) →
    ω ∈ selectivePairRunsEqFrom start (encode w) → v = w

/-! ### The canonical finite parser

The encoding above is not an additional probabilistic hypothesis.  Once a
valid terminal specification is fixed, its active entries have one and only
one chronological vector of distinguished-pair run lengths.  The following
recursive construction supplies the encoding for every such specification. -/

/-- Number of active (deleted-run) entries in a selective terminal list. -/
@[simp] def selectiveActiveCount : List (Bool × IncrementPair) → ℕ
  | [] => 0
  | (false, _) :: specs => selectiveActiveCount specs
  | (true, _) :: specs => selectiveActiveCount specs + 1

/-- Put a run-length vector back into its chronological active positions.
The last vector coordinate is used for the head active entry; this makes the
tail definition exactly `Fin.init`. -/
def canonicalSelectiveRuns :
    (specs : List (Bool × IncrementPair)) →
      (Fin (selectiveActiveCount specs) → ℕ) → List SelectivePairRun
  | [], _ => []
  | (false, p) :: specs, v =>
      (none, p) :: canonicalSelectiveRuns specs v
  | (true, p) :: specs, v =>
      (some (v (Fin.last (selectiveActiveCount specs))), p) ::
        canonicalSelectiveRuns specs (Fin.init v)

@[simp] theorem canonicalSelectiveRuns_terminalSpec
    (specs : List (Bool × IncrementPair))
    (v : Fin (selectiveActiveCount specs) → ℕ) :
    selectiveTerminalSpec (canonicalSelectiveRuns specs v) = specs := by
  induction specs with
  | nil => rfl
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active with
      | false =>
          change Fin (selectiveActiveCount specs) → ℕ at v
          change (false, p) :: selectiveTerminalSpec
            (canonicalSelectiveRuns specs v) = (false, p) :: specs
          rw [ih]
      | true =>
          change Fin (selectiveActiveCount specs + 1) → ℕ at v
          change (true, p) :: selectiveTerminalSpec
            (canonicalSelectiveRuns specs (Fin.init v)) = (true, p) :: specs
          rw [ih]

@[simp] theorem canonicalSelectiveRuns_runFactor
    (specs : List (Bool × IncrementPair))
    (v : Fin (selectiveActiveCount specs) → ℕ) :
    ((canonicalSelectiveRuns specs v).map selectiveRunFactor).prod =
      ∏ i, (15 : ℝ≥0∞) / 16 ^ (v i + 1) := by
  induction specs with
  | nil =>
      change 1 = ∏ i : Fin 0, (15 : ℝ≥0∞) / 16 ^ (v i + 1)
      rw [Fin.prod_univ_zero]
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active with
      | false =>
          simp only [selectiveActiveCount, canonicalSelectiveRuns,
            List.map_cons, selectiveRunFactor, List.prod_cons, one_mul]
          exact ih v
      | true =>
          change Fin (selectiveActiveCount specs + 1) → ℕ at v
          simp only [canonicalSelectiveRuns]
          simp only [List.map_cons, List.prod_cons, selectiveRunFactor]
          rw [ih (Fin.init v)]
          change (15 : ℝ≥0∞) / 16 ^
              (v (Fin.last (selectiveActiveCount specs)) + 1) *
                (∏ i : Fin (selectiveActiveCount specs),
                  (15 : ℝ≥0∞) / 16 ^ (Fin.init v i + 1)) =
            ∏ i : Fin (selectiveActiveCount specs + 1),
              (15 : ℝ≥0∞) / 16 ^ (v i + 1)
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.init]
          ac_rfl

theorem canonicalSelectiveRuns_cover
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (ω : ℕ → Direction)
    (hω : ω ∈ selectiveTerminalLabelsEqFrom start specs) :
    ∃ v : Fin (selectiveActiveCount specs) → ℕ,
      ω ∈ selectivePairRunsEqFrom start (canonicalSelectiveRuns specs v) := by
  induction specs generalizing start with
  | nil =>
      exact ⟨fun i => Fin.elim0 i, by
        simpa [canonicalSelectiveRuns, selectivePairRunsEqFrom]⟩
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active with
      | false =>
          rw [selectiveTerminalLabelsEqFrom] at hω
          rcases hω with ⟨hp, htail⟩
          rcases ih (start := start + 1) htail with ⟨v, hv⟩
          exact ⟨v, by
            simpa [selectiveActiveCount, canonicalSelectiveRuns,
              selectivePairRunsEqFrom] using And.intro hp hv⟩
      | true =>
          rw [selectiveTerminalLabelsEqFrom] at hω
          rcases Set.mem_iUnion.mp hω with ⟨t, hseg, htail⟩
          rcases ih (start := start + t + 1) htail with ⟨v, hv⟩
          refine ⟨Fin.snoc v t, ?_⟩
          simpa [selectiveActiveCount, canonicalSelectiveRuns,
            selectivePairRunsEqFrom] using And.intro hseg hv

theorem canonicalSelectiveRuns_unique
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (hvalid : SelectiveTerminalValid specs) {ω : ℕ → Direction}
    {v w : Fin (selectiveActiveCount specs) → ℕ}
    (hv : ω ∈ selectivePairRunsEqFrom start (canonicalSelectiveRuns specs v))
    (hw : ω ∈ selectivePairRunsEqFrom start (canonicalSelectiveRuns specs w)) :
    v = w := by
  induction specs generalizing start with
  | nil =>
      funext i
      exact Fin.elim0 i
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      have htailValid : SelectiveTerminalValid specs := by
        intro spec hspec
        exact hvalid spec (by simp [hspec])
      cases active with
      | false =>
          simp only [selectiveActiveCount, canonicalSelectiveRuns,
            selectivePairRunsEqFrom] at hv hw
          exact ih (start := start + 1) htailValid hv.2 hw.2
      | true =>
          simp only [selectiveActiveCount, canonicalSelectiveRuns,
            selectivePairRunsEqFrom] at hv hw
          have hp : p ≠ distinguishedIncrementPair :=
            hvalid (true, p) (by simp) rfl
          have hlast : v (Fin.last (selectiveActiveCount specs)) =
              w (Fin.last (selectiveActiveCount specs)) := by
            by_contra hne
            exact Set.disjoint_left.mp
              (disjoint_distinguishedPairRunSegmentWithLabel start hp hne)
                hv.1 hw.1
          have hinit : Fin.init v = Fin.init w :=
            ih (start := start + v (Fin.last (selectiveActiveCount specs)) + 1)
              htailValid hv.2 (by simpa only [hlast] using hw.2)
          rw [← Fin.snoc_init_self v, ← Fin.snoc_init_self w,
            hinit, hlast]

/-- Every valid fixed selective terminal path has its canonical complete
run-vector encoding. -/
noncomputable def canonicalSelectivePairVectorEncoding
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (hvalid : SelectiveTerminalValid specs) :
    SelectivePairVectorEncoding start specs where
  q := selectiveActiveCount specs
  encode := canonicalSelectiveRuns specs
  terminal_spec := canonicalSelectiveRuns_terminalSpec specs
  run_factor := canonicalSelectiveRuns_runFactor specs
  cover := canonicalSelectiveRuns_cover start specs
  unique := canonicalSelectiveRuns_unique start specs hvalid

/-- The vector decoded by a deterministic selective parser.  Its default
off the terminal-path atom is irrelevant after conditioning. -/
noncomputable def conditionalSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    (ℕ → Direction) → (Fin e.q → ℕ) := by
  classical
  exact fun ω ↦
    if h : ∃ v, ω ∈ selectivePairRunsEqFrom start (e.encode v) then
      Classical.choose h
    else 0

theorem conditionalSelectiveRunVector_eq_iff
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (v : Fin e.q → ℕ) {ω : ℕ → Direction}
    (hω : ω ∈ selectiveTerminalLabelsEqFrom start specs) :
    conditionalSelectiveRunVector e ω = v ↔
      ω ∈ selectivePairRunsEqFrom start (e.encode v) := by
  classical
  have hex : ∃ w, ω ∈ selectivePairRunsEqFrom start (e.encode w) :=
    e.cover ω hω
  rw [conditionalSelectiveRunVector, dif_pos hex]
  let chosen : Fin e.q → ℕ := Classical.choose hex
  have hchosen : ω ∈ selectivePairRunsEqFrom start (e.encode chosen) :=
    Classical.choose_spec hex
  constructor
  · intro h
    have hcv : chosen = v := by simpa only [chosen] using h
    simpa only [hcv] using hchosen
  · intro hv
    exact e.unique hchosen hv

theorem terminalAtom_inter_selectiveVector_fiber
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (v : Fin e.q → ℕ) :
    selectiveTerminalLabelsEqFrom start specs ∩
        {ω | conditionalSelectiveRunVector e ω = v} =
      selectivePairRunsEqFrom start (e.encode v) := by
  ext ω
  constructor
  · rintro ⟨hA, hv⟩
    exact (conditionalSelectiveRunVector_eq_iff e v hA).mp hv
  · intro hruns
    have hA : ω ∈ selectiveTerminalLabelsEqFrom start specs := by
      rw [← e.terminal_spec v]
      exact selectivePairRuns_subset_terminalLabels start (e.encode v) hruns
    exact ⟨hA,
      (conditionalSelectiveRunVector_eq_iff e v hA).mpr hruns⟩

theorem measurableSet_conditionalSelectiveRunVector_fiber
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (v : Fin e.q → ℕ) :
    MeasurableSet {ω | conditionalSelectiveRunVector e ω = v} := by
  let A := selectiveTerminalLabelsEqFrom start specs
  let J := selectivePairRunsEqFrom start (e.encode v)
  have hset : {ω | conditionalSelectiveRunVector e ω = v} =
      if v = 0 then Aᶜ ∪ J else J := by
    ext ω
    by_cases hA : ω ∈ A
    · have hiff := conditionalSelectiveRunVector_eq_iff e v hA
      by_cases hv : v = 0
      · simpa [hv, A, J, hA] using hiff
      · simpa [hv, A, J, hA] using hiff
    · have hnone : ¬ ∃ w,
          ω ∈ selectivePairRunsEqFrom start (e.encode w) := by
        rintro ⟨w, hw⟩
        apply hA
        change ω ∈ selectiveTerminalLabelsEqFrom start specs
        rw [← e.terminal_spec w]
        exact selectivePairRuns_subset_terminalLabels start (e.encode w) hw
      have hvalue : conditionalSelectiveRunVector e ω = 0 := by
        rw [conditionalSelectiveRunVector, dif_neg hnone]
      have hnotJ : ω ∉ J := by
        intro hJ
        exact hA (by
          change ω ∈ selectiveTerminalLabelsEqFrom start specs
          rw [← e.terminal_spec v]
          exact selectivePairRuns_subset_terminalLabels start (e.encode v) hJ)
      by_cases hv : v = 0
      · subst v
        simp [hvalue, A, J, hA, hnotJ]
      · have hzero_ne : (0 : Fin e.q → ℕ) ≠ v := fun h ↦ hv h.symm
        simp [hvalue, J, hnotJ, hv, hzero_ne]
  rw [hset]
  split_ifs
  · exact (measurableSet_selectiveTerminalLabelsEqFrom_iidTail start specs
      |> iidTail_le (2 * start) _).compl.union
        (measurableSet_selectivePairRunsEqFrom_iidTail start (e.encode v)
          |> iidTail_le (2 * start) _)
  · exact measurableSet_selectivePairRunsEqFrom_iidTail start (e.encode v)
      |> iidTail_le (2 * start) _

theorem measurable_conditionalSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    Measurable (conditionalSelectiveRunVector e) := by
  apply measurable_to_countable'
  exact measurableSet_conditionalSelectiveRunVector_fiber e

theorem selectivePairVector_conditional_singleton
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (hvalid : SelectiveTerminalValid specs) (v : Fin e.q → ℕ) :
    incrementLaw[|selectiveTerminalLabelsEqFrom start specs]
        {ω | conditionalSelectiveRunVector e ω = v} =
      HLOZUrn.runVectorMeasure e.q {v} := by
  let A := selectiveTerminalLabelsEqFrom start specs
  have hA : MeasurableSet A :=
    measurableSet_selectiveTerminalLabelsEqFrom_iidTail start specs
      |> iidTail_le (2 * start) _
  rw [cond_apply hA]
  rw [terminalAtom_inter_selectiveVector_fiber e v]
  rw [mul_comm]
  change incrementLaw (selectivePairRunsEqFrom start (e.encode v)) /
      incrementLaw A = _
  have hvalid' : SelectiveTerminalValid
      (selectiveTerminalSpec (e.encode v)) := by
    simpa only [e.terminal_spec v] using hvalid
  have hratio :=
    selectivePairRuns_conditional_mass start (e.encode v) hvalid'
  rw [e.terminal_spec v] at hratio
  rw [show incrementLaw (selectivePairRunsEqFrom start (e.encode v)) /
      incrementLaw A = ((e.encode v).map selectiveRunFactor).prod by
    simpa only [A] using hratio]
  rw [e.run_factor v, runVectorMeasure_singleton_ennreal]

theorem conditionalSelectiveRunVector_hasLaw
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (hvalid : SelectiveTerminalValid specs) :
    HasLaw (conditionalSelectiveRunVector e)
      (HLOZUrn.runVectorMeasure e.q)
      incrementLaw[|selectiveTerminalLabelsEqFrom start specs] := by
  constructor
  · exact (measurable_conditionalSelectiveRunVector e).aemeasurable
  · apply Measure.ext_of_singleton
    intro v
    rw [Measure.map_apply (measurable_conditionalSelectiveRunVector e)
      (measurableSet_singleton v)]
    exact selectivePairVector_conditional_singleton e hvalid v

/-! ### Transfer to the canonical path space -/

def selectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    Set (ℕ → Site) :=
  simpleRandomWalk '' selectiveTerminalLabelsEqFrom start specs

theorem measurableSet_selectiveTerminalLabelsEqFrom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    MeasurableSet (selectiveTerminalLabelsEqFrom start specs) :=
  iidTail_le (2 * start) _
    (measurableSet_selectiveTerminalLabelsEqFrom_iidTail start specs)

theorem measurableSet_selectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    MeasurableSet (selectiveTerminalPathAtom start specs) :=
  measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_selectiveTerminalLabelsEqFrom start specs)

theorem preimage_selectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    simpleRandomWalk ⁻¹' selectiveTerminalPathAtom start specs =
      selectiveTerminalLabelsEqFrom start specs :=
  simpleRandomWalk_injective.preimage_image _

noncomputable def pathConditionalSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    (ℕ → Site) → (Fin e.q → ℕ) :=
  Function.extend simpleRandomWalk (conditionalSelectiveRunVector e) 0

theorem measurable_pathConditionalSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs) :
    Measurable (pathConditionalSelectiveRunVector e) := by
  apply measurableEmbedding_simpleRandomWalk.measurable_extend
  · exact measurable_conditionalSelectiveRunVector e
  · exact measurable_const

theorem pathConditionalSelectiveRunVector_simpleRandomWalk
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (ω : ℕ → Direction) :
    pathConditionalSelectiveRunVector e (simpleRandomWalk ω) =
      conditionalSelectiveRunVector e ω :=
  simpleRandomWalk_injective.extend_apply _ _ ω

/-- Path-space joint iid-geometric law for a deterministic adaptive column
parser.  This is the direct constructor consumed by the Proposition-4.5
column clock interface. -/
theorem pathConditionalSelectiveRunVector_hasLaw
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start specs)
    (hvalid : SelectiveTerminalValid specs) :
    HasLaw (pathConditionalSelectiveRunVector e)
      (HLOZUrn.runVectorMeasure e.q)
      simpleRandomWalkLaw[|selectiveTerminalPathAtom start specs] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_selectiveTerminalLabelsEqFrom start specs)
  · exact measurable_conditionalSelectiveRunVector e
  · intro ω _
    exact pathConditionalSelectiveRunVector_simpleRandomWalk e ω
  · exact conditionalSelectiveRunVector_hasLaw e hvalid

/-! ### The deterministic `Y` active mask -/

/-- Along a fixed retained pair path, mark exactly those pair starts whose
first coordinate is even.  Inserted `(+e₁,-e₁)` loops return to the same
base, so this mask is independent of all holding counts. -/
def yForwardTerminalSpec :
    Site → List IncrementPair → List (Bool × IncrementPair)
  | _, [] => []
  | a, p :: labels =>
      (decide (Even a.1), p) ::
        yForwardTerminalSpec (pairEndpoint a p) labels

@[simp] theorem yForwardTerminalSpec_length
    (a : Site) (labels : List IncrementPair) :
    (yForwardTerminalSpec a labels).length = labels.length := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      simp only [yForwardTerminalSpec, List.length_cons]
      rw [ih]

theorem yForwardTerminalSpec_head_active_iff
    (a : Site) (p : IncrementPair) (labels : List IncrementPair) :
    (yForwardTerminalSpec a (p :: labels)).head?.map Prod.fst =
      some true ↔ Even a.1 := by
  simp [yForwardTerminalSpec]

/-! ### The backward/primed column phase

The primed deletion removes the reversed pair `(-e₁,+e₁)` at the
opposite (odd-column) endpoint.  Adjacent-pair reversal preserves the iid
increment law and turns this pair into the forward distinguished pair.  We
use that symmetry only to prove the phase's law: its conditioning atom,
encoding, and decoder remain distinct from the forward phase. -/

def reverseSelectivePairRun (run : SelectivePairRun) : SelectivePairRun :=
  (run.1, reverseIncrementPair run.2)

def reverseSelectiveTerminalLabel
    (spec : Bool × IncrementPair) : Bool × IncrementPair :=
  (spec.1, reverseIncrementPair spec.2)

@[simp] theorem reverseSelectivePairRun_involutive (run : SelectivePairRun) :
    reverseSelectivePairRun (reverseSelectivePairRun run) = run := by
  rcases run with ⟨ot, p⟩
  simp [reverseSelectivePairRun]

@[simp] theorem reverseSelectiveTerminalLabel_involutive
    (spec : Bool × IncrementPair) :
    reverseSelectiveTerminalLabel (reverseSelectiveTerminalLabel spec) = spec := by
  rcases spec with ⟨active, p⟩
  simp [reverseSelectiveTerminalLabel]

theorem swapAdjacentPairs_involutive : Function.Involutive swapAdjacentPairs := by
  intro omega
  funext n
  change omega (adjacentPairSwap (adjacentPairSwap n)) = omega n
  rw [adjacentPairSwap_involutive]

theorem incrementPair_swapAdjacentPairs
    (omega : ℕ → Direction) (r : ℕ) :
    incrementPair r (swapAdjacentPairs omega) =
      reverseIncrementPair (incrementPair r omega) := by
  funext i
  fin_cases i
  · simp [incrementPair, iidBlock, swapAdjacentPairs, reverseIncrementPair,
      adjacentPairSwap_even, adjacentPairSwap_odd]
  · simp [incrementPair, iidBlock, swapAdjacentPairs, reverseIncrementPair,
      adjacentPairSwap_even, adjacentPairSwap_odd]

/-- Backward selective run event.  Pair reversal changes every terminal
label and changes the repeated pair from `(-e₁,+e₁)` to
`(+e₁,-e₁)`. -/
def primedSelectivePairRunsEqFrom
    (start : ℕ) (runs : List SelectivePairRun) : Set (ℕ → Direction) :=
  swapAdjacentPairs ⁻¹'
    selectivePairRunsEqFrom start (runs.map reverseSelectivePairRun)

/-- Backward terminal-label atom, conditioned independently of the forward
column atom. -/
def primedSelectiveTerminalLabelsEqFrom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    Set (ℕ → Direction) :=
  swapAdjacentPairs ⁻¹'
    selectiveTerminalLabelsEqFrom start
      (specs.map reverseSelectiveTerminalLabel)

def PrimedSelectiveTerminalValid
    (specs : List (Bool × IncrementPair)) : Prop :=
  ∀ spec ∈ specs, spec.1 = true →
    spec.2 ≠ primedDistinguishedIncrementPair

theorem reverse_specs_valid {specs : List (Bool × IncrementPair)}
    (h : PrimedSelectiveTerminalValid specs) :
    SelectiveTerminalValid (specs.map reverseSelectiveTerminalLabel) := by
  intro spec hspec hactive
  simp only [List.mem_map] at hspec
  rcases hspec with ⟨orig, horig, rfl⟩
  intro heq
  apply h orig horig hactive
  have hrev := congrArg reverseIncrementPair heq
  simpa [reverseSelectiveTerminalLabel] using hrev

theorem measurableSet_primedSelectiveTerminalLabelsEqFrom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    MeasurableSet (primedSelectiveTerminalLabelsEqFrom start specs) := by
  exact (measurableSet_selectiveTerminalLabelsEqFrom start
    (specs.map reverseSelectiveTerminalLabel)).preimage
      measurable_swapAdjacentPairs

/-- Deterministic finite parser data for the primed column phase. -/
structure PrimedSelectivePairVectorEncoding
    (start : ℕ) (specs : List (Bool × IncrementPair)) where
  q : ℕ
  encode : (Fin q → ℕ) → List SelectivePairRun
  terminal_spec : ∀ v, selectiveTerminalSpec (encode v) = specs
  run_factor : ∀ v,
    ((encode v).map selectiveRunFactor).prod =
      ∏ i, (15 : ℝ≥0∞) / 16 ^ (v i + 1)
  cover : ∀ ω ∈ primedSelectiveTerminalLabelsEqFrom start specs,
    ∃ v, ω ∈ primedSelectivePairRunsEqFrom start (encode v)
  unique : ∀ {ω v w},
    ω ∈ primedSelectivePairRunsEqFrom start (encode v) →
    ω ∈ primedSelectivePairRunsEqFrom start (encode w) → v = w

theorem selectiveTerminalSpec_map_reverse (runs : List SelectivePairRun) :
    selectiveTerminalSpec (runs.map reverseSelectivePairRun) =
      (selectiveTerminalSpec runs).map reverseSelectiveTerminalLabel := by
  induction runs with
  | nil => rfl
  | cons run runs _ =>
      rcases run with ⟨ot, p⟩
      simp [selectiveTerminalSpec, reverseSelectivePairRun,
        reverseSelectiveTerminalLabel]

theorem runFactor_map_reverse (runs : List SelectivePairRun) :
    ((runs.map reverseSelectivePairRun).map selectiveRunFactor).prod =
      (runs.map selectiveRunFactor).prod := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      change selectiveRunFactor (reverseSelectivePairRun run) *
          ((runs.map reverseSelectivePairRun).map selectiveRunFactor).prod =
        selectiveRunFactor run * (runs.map selectiveRunFactor).prod
      rw [ih]
      rcases run with ⟨ot, p⟩
      cases ot <;> rfl

/-- Conjugate a forward encoding of the reversed terminal labels into the
independently conditioned backward/primed encoding. -/
noncomputable def SelectivePairVectorEncoding.toPrimed
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : SelectivePairVectorEncoding start
      (specs.map reverseSelectiveTerminalLabel)) :
    PrimedSelectivePairVectorEncoding start specs where
  q := e.q
  encode := fun v ↦ (e.encode v).map reverseSelectivePairRun
  terminal_spec := by
    intro v
    rw [selectiveTerminalSpec_map_reverse, e.terminal_spec, List.map_map]
    have hfun : reverseSelectiveTerminalLabel ∘
        reverseSelectiveTerminalLabel = id := by
      funext spec
      exact reverseSelectiveTerminalLabel_involutive spec
    rw [hfun, List.map_id]
  run_factor := by
    intro v
    rw [runFactor_map_reverse, e.run_factor]
  cover := by
    intro omega homega
    rcases e.cover (swapAdjacentPairs omega) homega with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
      (((e.encode v).map reverseSelectivePairRun).map reverseSelectivePairRun)
    rw [List.map_map]
    have hfun : reverseSelectivePairRun ∘ reverseSelectivePairRun = id := by
      funext run
      exact reverseSelectivePairRun_involutive run
    rw [hfun, List.map_id]
    exact hv
  unique := by
    intro omega v w hv hw
    apply e.unique
    · change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
        (((e.encode v).map reverseSelectivePairRun).map reverseSelectivePairRun) at hv
      rw [List.map_map] at hv
      have hfun : reverseSelectivePairRun ∘ reverseSelectivePairRun = id := by
        funext run
        exact reverseSelectivePairRun_involutive run
      rw [hfun, List.map_id] at hv
      exact hv
    · change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
        (((e.encode w).map reverseSelectivePairRun).map reverseSelectivePairRun) at hw
      rw [List.map_map] at hw
      have hfun : reverseSelectivePairRun ∘ reverseSelectivePairRun = id := by
        funext run
        exact reverseSelectivePairRun_involutive run
      rw [hfun, List.map_id] at hw
      exact hw

/-- Every valid primed terminal specification likewise has a canonical
run-vector encoding; no law or parser witness remains to be supplied. -/
noncomputable def canonicalPrimedSelectivePairVectorEncoding
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (hvalid : PrimedSelectiveTerminalValid specs) :
    PrimedSelectivePairVectorEncoding start specs :=
  (canonicalSelectivePairVectorEncoding start
    (specs.map reverseSelectiveTerminalLabel) (reverse_specs_valid hvalid)).toPrimed

/-- Conjugate a primed encoding by adjacent-pair reversal. -/
noncomputable def PrimedSelectivePairVectorEncoding.toForward
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    SelectivePairVectorEncoding start
      (specs.map reverseSelectiveTerminalLabel) where
  q := e.q
  encode := fun v ↦ (e.encode v).map reverseSelectivePairRun
  terminal_spec := by
    intro v
    rw [selectiveTerminalSpec_map_reverse, e.terminal_spec]
  run_factor := by
    intro v
    rw [runFactor_map_reverse, e.run_factor]
  cover := by
    intro eta heta
    let omega := swapAdjacentPairs eta
    have homega : omega ∈ primedSelectiveTerminalLabelsEqFrom start specs := by
      change swapAdjacentPairs omega ∈
        selectiveTerminalLabelsEqFrom start
          (specs.map reverseSelectiveTerminalLabel)
      simpa only [omega, swapAdjacentPairs_involutive eta] using heta
    rcases e.cover omega homega with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
      ((e.encode v).map reverseSelectivePairRun) at hv
    simpa only [omega, swapAdjacentPairs_involutive eta] using hv
  unique := by
    intro eta v w hv hw
    let omega := swapAdjacentPairs eta
    apply e.unique (ω := omega)
    · change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
        ((e.encode v).map reverseSelectivePairRun)
      simpa only [omega, swapAdjacentPairs_involutive eta] using hv
    · change swapAdjacentPairs omega ∈ selectivePairRunsEqFrom start
        ((e.encode w).map reverseSelectivePairRun)
      simpa only [omega, swapAdjacentPairs_involutive eta] using hw

noncomputable def conditionalPrimedSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    (ℕ → Direction) → (Fin e.q → ℕ) :=
  fun omega ↦ conditionalSelectiveRunVector e.toForward
    (swapAdjacentPairs omega)

/-- The complete joint geometric law on the independently conditioned
primed column atom. -/
theorem conditionalPrimedSelectiveRunVector_hasLaw
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    (hvalid : PrimedSelectiveTerminalValid specs) :
    HasLaw (conditionalPrimedSelectiveRunVector e)
      (HLOZUrn.runVectorMeasure e.q)
      incrementLaw[|primedSelectiveTerminalLabelsEqFrom start specs] := by
  have hswap := HasLaw.cond_preimage swapAdjacentPairs_hasLaw
    measurable_swapAdjacentPairs
    (selectiveTerminalLabelsEqFrom start
      (specs.map reverseSelectiveTerminalLabel))
    (measurableSet_selectiveTerminalLabelsEqFrom start
      (specs.map reverseSelectiveTerminalLabel))
  exact (conditionalSelectiveRunVector_hasLaw e.toForward
    (reverse_specs_valid hvalid)).fun_comp hswap

def primedSelectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    Set (ℕ → Site) :=
  simpleRandomWalk '' primedSelectiveTerminalLabelsEqFrom start specs

noncomputable def pathConditionalPrimedSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    (ℕ → Site) → (Fin e.q → ℕ) :=
  Function.extend simpleRandomWalk (conditionalPrimedSelectiveRunVector e) 0

theorem measurable_conditionalPrimedSelectiveRunVector
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs) :
    Measurable (conditionalPrimedSelectiveRunVector e) :=
  (measurable_conditionalSelectiveRunVector e.toForward).comp
    measurable_swapAdjacentPairs

/-- Path-space primed column parser law. -/
theorem pathConditionalPrimedSelectiveRunVector_hasLaw
    {start : ℕ} {specs : List (Bool × IncrementPair)}
    (e : PrimedSelectivePairVectorEncoding start specs)
    (hvalid : PrimedSelectiveTerminalValid specs) :
    HasLaw (pathConditionalPrimedSelectiveRunVector e)
      (HLOZUrn.runVectorMeasure e.q)
      simpleRandomWalkLaw[|primedSelectiveTerminalPathAtom start specs] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_primedSelectiveTerminalLabelsEqFrom start specs)
  · exact measurable_conditionalPrimedSelectiveRunVector e
  · intro omega _
    exact simpleRandomWalk_injective.extend_apply _ _ omega
  · exact conditionalPrimedSelectiveRunVector_hasLaw e hvalid

/-- The active mask for the primed phase of the same column tiling. -/
def yPrimedTerminalSpec :
    Site → List IncrementPair → List (Bool × IncrementPair)
  | _, [] => []
  | a, p :: labels =>
      (decide (Odd a.1), p) ::
        yPrimedTerminalSpec (pairEndpoint a p) labels

@[simp] theorem yPrimedTerminalSpec_length
    (a : Site) (labels : List IncrementPair) :
    (yPrimedTerminalSpec a labels).length = labels.length := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      simp only [yPrimedTerminalSpec, List.length_cons]
      rw [ih]

theorem yPrimedTerminalSpec_head_active_iff
    (a : Site) (p : IncrementPair) (labels : List IncrementPair) :
    (yPrimedTerminalSpec a (p :: labels)).head?.map Prod.fst =
      some true ↔ Odd a.1 := by
  simp [yPrimedTerminalSpec]

end Erdos1166.HLOZColumnPairRuns
