/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Proposition6Final
import ErdosProblems.Erdos285.Proposition7
import ErdosProblems.Erdos285.Proposition4

/-!
# Exact representations of smooth rational targets

This file exposes the target-generic content of the already formalized
Erdős--285 approximation-and-correction construction.  The fixed lower
endpoint `149 / 200` leaves a uniform positive residual for every target in
`[1/3,1)`.  Martin's prime-power descent makes that residual fifth-root
smooth, and Proposition 7 represents it exactly below the ambient cutoff.
-/

open Filter Finset Real
open scoped Topology

namespace Erdos305.SmoothInterval

noncomputable section

attribute [local instance] Classical.propDecidable

private def alpha : ℝ := 149 / 200

private lemma alpha_pos : 0 < alpha := by
  norm_num [alpha]

private lemma alpha_le_one : alpha ≤ 1 := by
  norm_num [alpha]

private lemma alpha_lt_three_fourths : alpha < (3 : ℝ) / 4 := by
  norm_num [alpha]

private lemma exp_neg_third_lt_alpha :
    Real.exp (-((1 : ℝ) / 3)) < alpha := by
  have he : (27 : ℝ) / 20 < Real.exp ((1 : ℝ) / 3) := by
    have h := Real.exp_bound (x := (1 : ℝ) / 3) (n := 3)
      (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, abs_sub_le_iff] at h ⊢
    linarith
  rw [Real.exp_neg, div_eq_mul_inv]
  have hi := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 27 / 20) he
  norm_num [alpha] at hi ⊢
  exact hi.trans (by norm_num)

private lemma quarter_lt_neg_log_alpha :
    (1 / 4 : ℝ) < -Real.log alpha := by
  rw [lt_neg, Real.log_lt_iff_lt_exp alpha_pos]
  have h := Real.add_one_lt_exp (x := -(1 : ℝ) / 4) (by norm_num)
  norm_num [alpha] at h ⊢
  linarith

private lemma neg_log_alpha_lt_three_tenths :
    -Real.log alpha < (3 / 10 : ℝ) := by
  rw [neg_lt, Real.lt_log_iff_exp_lt alpha_pos]
  have he : (1349 : ℝ) / 1000 < Real.exp ((3 : ℝ) / 10) := by
    have h := Real.exp_bound (x := (3 : ℝ) / 10) (n := 4)
      (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, abs_sub_le_iff] at h ⊢
    linarith
  rw [Real.exp_neg, div_eq_mul_inv]
  have hi := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 1349 / 1000) he
  norm_num [alpha] at hi ⊢
  exact hi.trans (by norm_num)

/-- The concrete Lemma 12 removal descent is uniform in the target rational,
provided the target denominator is smooth at the main cutoff. -/
theorem eventually_concreteRemovalDescent :
    ∀ᶠ x : ℕ in atTop, ∀ (r : ℚ) (a : ℝ),
      UnitFractions.is_smooth (Erdos285.proposition6MainCutoff x) r.den →
      0 ≤ a → a < (3 : ℝ) / 4 →
      Nonempty (Erdos285.RemovalDescentOutcome
        (Erdos285.initialSmoothBlock a x (Erdos285.proposition6MainCutoff x)) x
        (Erdos285.approximationCorrectionScale x)
        (Erdos285.initialResidualApproximationState r a x
          (Erdos285.proposition6MainCutoff x))) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Erdos285.eventually_lemma12StepData_threeFourths,
    eventually_ge_atTop 1, hlogTop.eventually_ge_atTop 1]
      with x hstepData hx hlog
  intro r a hr ha haXi
  let z := Erdos285.proposition6MainCutoff x
  let y := Erdos285.approximationCorrectionScale x
  let Q := ⌊z⌋₊
  let start := Erdos285.initialResidualApproximationState r a x z
  have hz : 0 ≤ z := by
    dsimp [z, Erdos285.proposition6MainCutoff]
    positivity
  have hbound : start.primePowerMeasure ≤ Q := by
    exact Erdos285.initialResidualApproximationState_measure_le_floor hr
  have hQz : (Q : ℝ) ≤ z := Nat.floor_le hz
  have hxi : (⌊a * (x : ℝ)⌋₊ : ℝ) < ((3 : ℝ) / 4) * x := by
    have hfloor : (⌊a * (x : ℝ)⌋₊ : ℝ) ≤ a * x :=
      Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg x))
    have hxR : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    exact hfloor.trans_lt (mul_lt_mul_of_pos_right haXi hxR)
  have hdata : ∀ s : Erdos285.ResidualApproximationState r, s.Coherent →
      Erdos285.AvailableBelow (Erdos285.initialSmoothBlock a x z) s →
      s.primePowerMeasure ≤ Q → y < s.primePowerMeasure →
      Erdos285.Lemma12StepData ((3 : ℝ) / 4) x s := by
    intro s _ _ hsQ hys
    apply hstepData s
    constructor
    · have hrootLt : (x : ℝ) ^ ((5 : ℝ)⁻¹) <
          ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) := by
        simpa using Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
      have hsucc : ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 ≤
          s.primePowerMeasure := by
        change y + 1 ≤ s.primePowerMeasure
        omega
      have hsuccR : ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) ≤
          (s.primePowerMeasure : ℝ) := by exact_mod_cast hsucc
      simpa only [show ((5 : ℝ)⁻¹) = (1 : ℝ) / 5 by norm_num] using
        hrootLt.le.trans hsuccR
    · have hqQ : (s.primePowerMeasure : ℝ) ≤ Q := by exact_mod_cast hsQ
      calc
        (s.primePowerMeasure : ℝ) ≤ z := hqQ.trans hQz
        _ = (x : ℝ) * Real.log x ^ (-30 : ℝ) := by
          dsimp [z, Erdos285.proposition6MainCutoff]
          rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
            Real.rpow_neg (zero_lt_one.trans_le hlog).le,
            show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          ring
  exact ⟨Erdos285.lemma12RemovalDescent a ((3 : ℝ) / 4) z
    (Erdos285.initialSmoothBlock a x z) x y Q start rfl
    (by exact Finset.Subset.rfl)
    (by intro n hn _; exact hn) hbound hQz hxi hdata⟩

/-- Uniform approximation certificates for every smooth target in
`[1/3,1)`.  The requested cardinality is the cardinality of the full initial
block; the five-prime reservoir replaces every term removed by the descent. -/
theorem eventually_approximationCertificate :
    ∀ᶠ x : ℕ in atTop, ∀ r : ℚ,
      (1 / 3 : ℝ) ≤ (r : ℝ) → (r : ℝ) < 1 →
      UnitFractions.is_smooth (Erdos285.proposition6MainCutoff x) r.den →
      Nonempty (Erdos285.ApproximationCertificate r x
        (Erdos285.initialBlockAt alpha x).card) := by
  have hrec := Erdos285.initialBlockAt_recSum_tendsto alpha alpha_pos alpha_le_one
  have hrecBounds : ∀ᶠ x : ℕ in atTop,
      (1 / 4 : ℝ) <
          (UnitFractions.rec_sum (Erdos285.initialBlockAt alpha x) : ℝ) ∧
        (UnitFractions.rec_sum (Erdos285.initialBlockAt alpha x) : ℝ) < 3 / 10 :=
    hrec.eventually (Ioo_mem_nhds quarter_lt_neg_log_alpha
      neg_log_alpha_lt_three_tenths)
  have hratio := (Erdos285.proposition6BudgetRatio_tendsto_zero alpha alpha_pos).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := hlogTop.inv_tendsto_atTop.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  filter_upwards [eventually_concreteRemovalDescent,
    Erdos285.eventually_totalEliminationBudget_mainCutoff_le,
    Erdos285.eventually_two_budget_le_smoothReservoir alpha alpha_pos alpha_le_one,
    hrecBounds, hratio, hinv, eventually_ge_atTop 3]
      with x hdescent hbudget hreservoir hrecB hratioB hinvB hx
  intro r hrLower hrUpper hrsmooth
  have hxpos : 0 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hinvpos : 0 < (Real.log (x : ℝ))⁻¹ := inv_pos.mpr hlogpos
  have hExpLe : Real.exp (-(r : ℝ)) ≤ alpha := by
    have hneg : -(r : ℝ) ≤ -((1 : ℝ) / 3) := neg_le_neg hrLower
    exact (Real.exp_le_exp.mpr hneg).trans exp_neg_third_lt_alpha.le
  obtain ⟨out⟩ := hdescent r alpha hrsmooth alpha_pos.le alpha_lt_three_fourths
  have hmeasure :
      (Erdos285.initialResidualApproximationState r alpha x
        (Erdos285.proposition6MainCutoff x)).primePowerMeasure ≤
          Erdos285.mainCutoffNat x := by
    rw [Erdos285.mainCutoffNat_eq]
    exact Erdos285.initialResidualApproximationState_measure_le_floor hrsmooth
  have hbudget' : Erdos285.totalEliminationBudget x
      (Erdos285.initialResidualApproximationState r alpha x
        (Erdos285.proposition6MainCutoff x)).primePowerMeasure ≤
          Erdos285.proposition6DeletionBudget x :=
    (Erdos285.totalEliminationBudget_mono x hmeasure).trans hbudget
  have hcapacity :
      (Erdos285.initialBlockAt alpha x).card -
            (Erdos285.initialBlockAt alpha x).card +
          Erdos285.totalEliminationBudget x
            (Erdos285.initialResidualApproximationState r alpha x
              (Erdos285.proposition6MainCutoff x)).primePowerMeasure ≤
        (Erdos285.smoothReservoir
          (Erdos285.proposition6ReservoirScale alpha x)).card := by
    simp only [Nat.sub_self, zero_add]
    exact hbudget'.trans ((Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)).trans hreservoir)
  have hyRoot :
      (Erdos285.approximationCorrectionScale x : ℝ) ≤
        (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have hresLower : (1 / 30 : ℝ) <
      (Erdos285.initialResidual r alpha x
        (Erdos285.proposition6MainCutoff x) : ℝ) := by
    rw [Erdos285.initialResidual]
    push_cast
    change (1 / 30 : ℝ) < (r : ℝ) -
      (UnitFractions.rec_sum (Erdos285.initialBlockAt alpha x) : ℝ)
    linarith [hrecB.2]
  have hresUpper :
      (Erdos285.initialResidual r alpha x
        (Erdos285.proposition6MainCutoff x) : ℝ) < 3 / 4 := by
    rw [Erdos285.initialResidual]
    push_cast
    change (r : ℝ) -
      (UnitFractions.rec_sum (Erdos285.initialBlockAt alpha x) : ℝ) < 3 / 4
    linarith [hrecB.1]
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos alpha_pos (by exact_mod_cast hxpos)
  have hbudgetRatio :
      (Erdos285.proposition6DeletionBudget x : ℝ) / (alpha * x) < 1 / 100 := by
    simpa [Erdos285.proposition6BudgetRatio] using hratioB
  have hbudgetR :
      (Erdos285.totalEliminationBudget x
        (Erdos285.initialResidualApproximationState r alpha x
          (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℝ) ≤
        Erdos285.proposition6DeletionBudget x := by
    exact_mod_cast hbudget'
  have hlowerNeeded :
      (Real.log (x : ℝ))⁻¹ +
          (((Erdos285.initialBlockAt alpha x).card -
              (Erdos285.initialBlockAt alpha x).card +
              Erdos285.totalEliminationBudget x
                (Erdos285.initialResidualApproximationState r alpha x
                  (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℕ) : ℝ) /
            (alpha * x / 2) <
        (Erdos285.initialResidual r alpha x
          (Erdos285.proposition6MainCutoff x) : ℝ) := by
    simp only [Nat.sub_self, zero_add]
    have hquot :
        (Erdos285.totalEliminationBudget x
          (Erdos285.initialResidualApproximationState r alpha x
            (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℝ) /
            (alpha * x / 2) ≤
          2 * ((Erdos285.proposition6DeletionBudget x : ℝ) / (alpha * x)) := by
      calc
        _ ≤ (Erdos285.proposition6DeletionBudget x : ℝ) / (alpha * x / 2) :=
          div_le_div_of_nonneg_right hbudgetR (by positivity)
        _ = 2 * ((Erdos285.proposition6DeletionBudget x : ℝ) / (alpha * x)) := by
          field_simp [halphaX.ne']
    have hquotSmall :
        (Erdos285.totalEliminationBudget x
          (Erdos285.initialResidualApproximationState r alpha x
            (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℝ) /
            (alpha * x / 2) < 1 / 50 := by
      exact hquot.trans_lt (by nlinarith [hbudgetRatio])
    calc
      _ < (1 / 100 : ℝ) + 1 / 50 := add_lt_add hinvB hquotSmall
      _ < 1 / 30 := by norm_num
      _ < _ := hresLower
  have hupperNeeded :
      (Erdos285.initialResidual r alpha x
          (Erdos285.proposition6MainCutoff x) : ℝ) +
          (Erdos285.totalEliminationBudget x
            (Erdos285.initialResidualApproximationState r alpha x
              (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℝ) /
            (alpha * x) < 1 := by
    have hquot := div_le_div_of_nonneg_right hbudgetR halphaX.le
    have hquotSmall :
        (Erdos285.totalEliminationBudget x
          (Erdos285.initialResidualApproximationState r alpha x
            (Erdos285.proposition6MainCutoff x)).primePowerMeasure : ℝ) /
            (alpha * x) < 1 / 100 := hquot.trans_lt hbudgetRatio
    nlinarith [hresUpper]
  simpa only [Erdos285.initialBlockAt] using
    (Erdos285.exists_approximationCertificate_of_removalDescent
      alpha_pos alpha_le_one alpha_pos le_rfl hExpLe hxpos out le_rfl hcapacity
      hyRoot hinvpos hlowerNeeded hupperNeeded)

private lemma approximationCertificate_residual_lower_one_sixth
    {r : ℚ} {x R : ℕ} (C : Erdos285.ApproximationCertificate r x R)
    (hy : 32 ≤ Erdos285.Proposition4.fifthRootFloor x) :
    (1 / 6 : ℝ) *
        (Real.log (Erdos285.Proposition4.fifthRootFloor x : ℝ))⁻¹ <
      (C.residual : ℝ) := by
  have hcast : (C.residual : ℝ) =
      (C.numerator : ℝ) / (C.denominator : ℝ) := by
    simp [Erdos285.ApproximationCertificate.residual]
  rw [hcast]
  exact (Erdos285.Proposition4.one_sixth_mul_inv_log_fifthRoot_lt_inv_log_cutoff
    hy).trans C.residual_lower

/-- Every target in `[1/3,1)` whose denominator is smooth at
`N / log(N)^30` has an exact distinct-unit-fraction representation with all
denominators at most `N`. -/
theorem eventually_smooth_target_representation :
    ∀ᶠ x : ℕ in atTop, ∀ r : ℚ,
      (1 / 3 : ℝ) ≤ (r : ℝ) → (r : ℝ) < 1 →
      UnitFractions.is_smooth (Erdos285.proposition6MainCutoff x) r.den →
      ∃ E : Finset ℕ,
        UnitFractions.rec_sum E = r ∧ 0 ∉ E ∧ ∀ n ∈ E, n ≤ x := by
  have hyTop : Tendsto Erdos285.Proposition4.fifthRootFloor atTop atTop :=
    Erdos285.Proposition4.fifthRootFloor_tendsto_atTop
      (C := (1 : ℝ)) (by norm_num)
      Erdos285.Proposition4.identity_cutoff_ratio_tendsto
  have hprop7 := hyTop.eventually
    (Erdos285.Proposition7.eventually_proposition7
      (c := (1 / 6 : ℝ)) (by norm_num))
  filter_upwards [eventually_approximationCertificate, hprop7,
    hyTop.eventually (eventually_ge_atTop 32),
    Erdos285.Proposition4.eventually_cutoffs_separated
      (C := (1 : ℝ)) (by norm_num)
      Erdos285.Proposition4.identity_cutoff_ratio_tendsto,
    Erdos285.Proposition4.eventually_correctionCutoff_le
      (C := (1 : ℝ)) (by norm_num)
      Erdos285.Proposition4.identity_cutoff_ratio_tendsto]
      with x hcert hprop hy hsep hcorrLe
  intro r hrLower hrUpper hrsmooth
  obtain ⟨C⟩ := hcert r hrLower hrUpper hrsmooth
  have hry : Erdos285.PrimePowers.largestPrimePowerPart C.residual.den ≤
      Erdos285.Proposition4.fifthRootFloor x :=
    Erdos285.Proposition4.approximationCertificate_residual_largestPart_le C
  have hrLow : (1 / 6 : ℝ) /
      Real.log (Erdos285.Proposition4.fifthRootFloor x : ℝ) <
        (C.residual : ℝ) := by
    simpa [div_eq_mul_inv] using
      approximationCertificate_residual_lower_one_sixth C hy
  have hrUp : (C.residual : ℝ) < 1 := by
    exact_mod_cast Erdos285.Proposition4.approximationCertificate_residual_lt_one C
  obtain ⟨correction, _, hcorrSum, hcorrZero, hcorrUpper⟩ :=
    hprop C.residual hry hrLow hrUp
  have hlargeLower : ∀ n ∈ C.denominators,
      Erdos285.Proposition4.largeLowerCutoff x ≤ n := by
    intro n hn
    have hfloor :
        (Erdos285.Proposition4.largeLowerCutoff x : ℝ) ≤
          Real.exp (-1) * (x : ℝ) / 2 := by
      exact Nat.floor_le (by positivity)
    have hexp : Real.exp (-1) ≤ Real.exp (-(r : ℝ)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hrUpper.le)
    have hscale : Real.exp (-1) * (x : ℝ) / 2 ≤
        Real.exp (-(r : ℝ)) * (x : ℝ) / 2 := by
      gcongr
    exact_mod_cast hfloor.trans (hscale.trans (C.interval n hn).1)
  have hcorrCutoff : ∀ n ∈ correction,
      n ≤ Erdos285.correctionCutoff
        (Erdos285.Proposition4.fifthRootFloor x) := by
    intro n hn
    simpa only [Erdos285.correctionCutoff] using hcorrUpper n hn
  have hdisjoint : Disjoint C.denominators correction := by
    rw [Finset.disjoint_left]
    intro n hnC hnCorr
    exact (not_lt_of_ge (hlargeLower n hnC))
      ((hcorrCutoff n hnCorr).trans_lt hsep)
  refine ⟨C.denominators ∪ correction, ?_, ?_, ?_⟩
  · rw [UnitFractions.rec_sum_disjoint hdisjoint, hcorrSum]
    simpa [Erdos285.ApproximationCertificate.residual] using C.sum_add_residual
  · simp only [Finset.mem_union, not_or]
    exact ⟨C.zero_not_mem, hcorrZero⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hnC | hnCorr
    · exact_mod_cast (C.interval n hnC).2
    · exact (hcorrCutoff n hnCorr).trans hcorrLe

end

end Erdos305.SmoothInterval
