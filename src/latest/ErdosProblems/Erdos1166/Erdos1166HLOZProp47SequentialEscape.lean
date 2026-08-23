import ErdosProblems.Erdos1166.Erdos1166HLOZProp47HighEscape
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47LowStageConnector

namespace Erdos1166.HLOZProp47LowEscape

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open HLOZFoundation KilledGreen HLOZAppendixAExactExit
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp47SourceAssembly HLOZProp47Canonical
open HLOZProp47HighEscape HLOZProp47LowStageConnector
open HLOZPairing.ScreeningBridge

def prependDirection (d : Direction) (eta : ℕ → Direction) : ℕ → Direction
  | 0 => d
  | n + 1 => eta n

theorem measurable_prependDirection (d : Direction) :
    Measurable (prependDirection d) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

theorem prependDirection_shift_one (omega : ℕ → Direction) :
    prependDirection (omega 0)
        (incrementShiftAfter (fun _ : ℕ → Direction ↦ 1) omega) = omega := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [prependDirection, incrementShiftAfter]
      congr 1 <;> omega

theorem prependDirection_shift_succ
    (tau : (ℕ → Direction) → ℕ) (omega : ℕ → Direction) :
    prependDirection (incrementShiftAfter tau omega 0)
        (incrementShiftAfter (fun eta ↦ tau eta + 1) omega) =
      incrementShiftAfter tau omega := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [prependDirection, incrementShiftAfter]
      congr 1 <;> omega

def tailSection (B : Set (ℕ → Direction)) (d : Direction) :
    Set (ℕ → Direction) :=
  prependDirection d ⁻¹' B

theorem measurableSet_tailSection {B : Set (ℕ → Direction)}
    (hB : MeasurableSet B) (d : Direction) :
    MeasurableSet (tailSection B d) :=
  hB.preimage (measurable_prependDirection d)

theorem tailSection_measure_le_four_mul
    (B : Set (ℕ → Direction)) (hB : MeasurableSet B) (d : Direction) :
    incrementLaw (tailSection B d) ≤ 4 * incrementLaw B := by
  let atom : Set (ℕ → Direction) := {omega | omega 0 = d}
  have hatomFiber (k : ℕ) : MeasurableSet[iidHistory (X := Direction) k]
      (atom ∩ {omega | (fun _ : ℕ → Direction ↦ 1) omega = k}) := by
    by_cases hk : k = 1
    · subst k
      simpa [atom] using KilledGreen.measurableSet_firstDirection_iidHistory d
    · have heq : atom ∩
          {omega | (fun _ : ℕ → Direction ↦ 1) omega = k} = ∅ := by
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        intro h
        exact hk h.2.symm
      rw [heq]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) k)
  have hfactor := measure_inter_incrementShiftAfter_eq_mul
    (fun _ : ℕ → Direction ↦ 1) atom (tailSection B d)
      measurable_const hatomFiber (measurableSet_tailSection hB d)
  have heq : atom ∩
        incrementShiftAfter (fun _ : ℕ → Direction ↦ 1) ⁻¹'
          tailSection B d = atom ∩ B := by
    ext omega
    constructor
    · rintro ⟨hd, htail⟩
      refine ⟨hd, ?_⟩
      change prependDirection d
        (incrementShiftAfter (fun _ : ℕ → Direction ↦ 1) omega) ∈ B at htail
      rw [show d = omega 0 by exact hd.symm, prependDirection_shift_one] at htail
      exact htail
    · rintro ⟨hd, homega⟩
      refine ⟨hd, ?_⟩
      change prependDirection d
        (incrementShiftAfter (fun _ : ℕ → Direction ↦ 1) omega) ∈ B
      rw [show d = omega 0 by exact hd.symm, prependDirection_shift_one]
      exact homega
  rw [heq, increment_direction_prob] at hfactor
  calc
    incrementLaw (tailSection B d) =
        4 * ((4 : ℝ≥0∞)⁻¹ * incrementLaw (tailSection B d)) := by
      rw [← mul_assoc]
      rw [ENNReal.mul_inv_cancel] <;> norm_num
    _ = 4 * incrementLaw (atom ∩ B) := by rw [← hfactor]
    _ ≤ 4 * incrementLaw B :=
      (by simpa only [mul_comm] using
        mul_le_mul_left (measure_mono inter_subset_right) 4)

theorem measure_inter_shift_le_four_mul
    (tau : (ℕ → Direction) → ℕ) (A B : Set (ℕ → Direction))
    (htau : Measurable tau)
    (hA : ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | tau omega + 1 = n}))
    (hB : MeasurableSet B) :
    incrementLaw (A ∩ incrementShiftAfter tau ⁻¹' B) ≤
      4 * incrementLaw B * incrementLaw A := by
  let sigma : (ℕ → Direction) → ℕ := fun omega ↦ tau omega + 1
  let atom : Direction → Set (ℕ → Direction) := fun d ↦
    A ∩ {omega | incrementShiftAfter tau omega 0 = d}
  have hsigma : Measurable sigma := htau.add measurable_const
  have hatomFiber (d : Direction) (n : ℕ) :
      MeasurableSet[iidHistory (X := Direction) n]
        (atom d ∩ {omega | sigma omega = n}) := by
    by_cases hn : n = 0
    · subst n
      have heq : atom d ∩ {omega | sigma omega = 0} = ∅ := by
        ext omega
        simp [sigma]
      rw [heq]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) 0)
    · have heq : atom d ∩ {omega | sigma omega = n} =
          (A ∩ {omega | tau omega + 1 = n}) ∩
            {omega | omega (n - 1) = d} := by
        ext omega
        simp only [atom, sigma, Set.mem_inter_iff, Set.mem_setOf_eq,
          incrementShiftAfter]
        constructor
        · rintro ⟨⟨hAomega, hd⟩, hs⟩
          refine ⟨⟨hAomega, hs⟩, ?_⟩
          simpa [show tau omega = n - 1 by omega] using hd
        · rintro ⟨⟨hAomega, hs⟩, hd⟩
          refine ⟨⟨hAomega, ?_⟩, hs⟩
          simpa [show tau omega = n - 1 by omega] using hd
      rw [heq]
      apply (hA n).inter
      let _ : MeasurableSpace (ℕ → Direction) := iidHistory (X := Direction) n
      apply measurableSet_eq_fun _ measurable_const
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le (n - 1) (le_iSup_of_le (by omega) le_rfl)
  have hatomMeas (d : Direction) : MeasurableSet (atom d) :=
    measurableSet_pastEvent sigma (atom d) (hatomFiber d)
  have hfactor (d : Direction) :
      incrementLaw (atom d ∩ incrementShiftAfter sigma ⁻¹' tailSection B d) =
        incrementLaw (atom d) * incrementLaw (tailSection B d) :=
    measure_inter_incrementShiftAfter_eq_mul sigma (atom d) (tailSection B d)
      hsigma (hatomFiber d) (measurableSet_tailSection hB d)
  have hevent : A ∩ incrementShiftAfter tau ⁻¹' B =
      ⋃ d : Direction,
        atom d ∩ incrementShiftAfter sigma ⁻¹' tailSection B d := by
    ext omega
    constructor
    · rintro ⟨hAomega, hfuture⟩
      let d := incrementShiftAfter tau omega 0
      refine Set.mem_iUnion_of_mem d ⟨⟨hAomega, rfl⟩, ?_⟩
      change prependDirection d (incrementShiftAfter sigma omega) ∈ B
      rw [prependDirection_shift_succ]
      exact hfuture
    · rintro h
      rcases Set.mem_iUnion.mp h with ⟨d, ⟨⟨hAomega, hd⟩, htail⟩⟩
      refine ⟨hAomega, ?_⟩
      change prependDirection d (incrementShiftAfter sigma omega) ∈ B at htail
      rw [show d = incrementShiftAfter tau omega 0 by exact hd.symm,
        prependDirection_shift_succ] at htail
      exact htail
  have hatomDisjoint : Pairwise fun d e ↦ Disjoint (atom d) (atom e) := by
    intro d e hde
    rw [Set.disjoint_left]
    intro omega hd he
    exact hde (hd.2.symm.trans he.2)
  have hatomUnion : (⋃ d : Direction, atom d) = A := by
    ext omega
    simp [atom]
  calc
    incrementLaw (A ∩ incrementShiftAfter tau ⁻¹' B) =
        incrementLaw (⋃ d : Direction,
          atom d ∩ incrementShiftAfter sigma ⁻¹' tailSection B d) := by rw [hevent]
    _ ≤ ∑' d : Direction,
        incrementLaw (atom d ∩ incrementShiftAfter sigma ⁻¹' tailSection B d) :=
      measure_iUnion_le _
    _ = ∑' d : Direction,
        incrementLaw (atom d) * incrementLaw (tailSection B d) := by
      apply tsum_congr
      exact hfactor
    _ ≤ ∑' d : Direction,
        incrementLaw (atom d) * (4 * incrementLaw B) := by
      apply ENNReal.tsum_le_tsum
      intro d
      gcongr
      exact tailSection_measure_le_four_mul B hB d
    _ = (∑' d : Direction, incrementLaw (atom d)) * (4 * incrementLaw B) := by
      rw [ENNReal.tsum_mul_right]
    _ = incrementLaw A * (4 * incrementLaw B) := by
      rw [← measure_iUnion hatomDisjoint hatomMeas, hatomUnion]
    _ = 4 * incrementLaw B * incrementLaw A := by ring

theorem sequentialScreen_stoppedFiber
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) (n : ℕ)
    (hm : 0 < m) :
    let k := stageNumber r
    let tau : (ℕ → Direction) → ℕ := fun omega ↦
      (firstKSitesReachLevel m k (simpleRandomWalk omega)).untopA
    let screen := prop47SequentialScreenEvent profiles cStar
      m i a r
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' screen ∩ {omega | tau omega + 1 = n}) := by
  dsimp only
  let k := stageNumber r
  let hT := isStoppingTime_firstKSitesReachLevel m k
  let hsucc := hT.add_const' 1
  let history := prop47History profiles cStar m i a r.1
  let lowScreen := lowScaleScreenEvent (profiles i) (cStar i)
    i m k (alphaValue (tripleAlphaIndex a r) + delta)
  let screen := prop47SequentialScreenEvent profiles cStar
    m i a r
  have hTsucc : hT.measurableSpace ≤ hsucc.measurableSpace :=
    hT.measurableSpace_mono hsucc (fun s ↦ le_add_right (le_refl _))
  have hhistory : MeasurableSet[hT.measurableSpace] history := by
    convert measurableSet_prop47History_at_threshold profiles
      hadapt cStar m i a r.1 (by omega) hm
      using 1 <;> simp [hT, k, stageNumber]
  have hlow : MeasurableSet[hsucc.measurableSpace] lowScreen := by
    exact measurableSet_lowScaleScreenEvent_at_succ profiles
      hadapt cStar i m k
        (alphaValue (tripleAlphaIndex a r) + delta)
  have hscreen : MeasurableSet[hsucc.measurableSpace] screen := by
    change MeasurableSet[hsucc.measurableSpace] (history ∩ lowScreen)
    exact (hT.measurableSpace_mono hsucc
      (fun s ↦ le_add_right (le_refl _)) history hhistory).inter hlow
  have hmeas := Erdos1166.measurableSet_pathStoppedEvent_inter_fiber_iidHistory
    hsucc screen hscreen n
  have heq : simpleRandomWalk ⁻¹' screen ∩
        {omega | (firstKSitesReachLevel m k
          (simpleRandomWalk omega)).untopA + 1 = n} =
      simpleRandomWalk ⁻¹' screen ∩
        {omega | firstKSitesReachLevel m k (simpleRandomWalk omega) + 1 = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    refine and_congr_right fun hscreenOmega ↦ ?_
    have hhistoryOmega : simpleRandomWalk omega ∈ history := hscreenOmega.1
    have hfinite := prop47History_subset_thresholdFinite
      profiles cStar m i a r hhistoryOmega
    let T := firstKSitesReachLevel m k (simpleRandomWalk omega)
    have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
      rw [WithTop.untopA_eq_untop hfinite]
      exact WithTop.coe_untop T hfinite
    change T.untopA + 1 = n ↔ T + 1 = n
    rw [← hcoe]
    exact_mod_cast Iff.rfl
  rw [heq]
  change MeasurableSet[iidHistory (X := Direction) n]
    (simpleRandomWalk ⁻¹' screen ∩
      {omega | firstKSitesReachLevel m k (simpleRandomWalk omega) +
        ((1 : ℕ) : WithTop ℕ) = (n : WithTop ℕ)})
  exact hmeas

theorem canonicalSequentialScreen_stoppedFiber
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) (n : ℕ)
    (hm : 0 < m) :
    let k := stageNumber r
    let tau : (ℕ → Direction) → ℕ := fun omega ↦
      (firstKSitesReachLevel m k (simpleRandomWalk omega)).untopA
    let screen := prop47SequentialScreenEvent canonicalProfiles canonicalCStar
      m i a r
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' screen ∩ {omega | tau omega + 1 = n}) :=
  sequentialScreen_stoppedFiber canonicalProfiles
    canonicalProfiles_oneStepAdapted canonicalCStar m i a r n hm

theorem sequentialExitScreen_le_four_escape_mul
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles)
    (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (R : ℕ) (hm : 0 < m)
    (hR : 3 * (R : ℝ) <
      distanceBinLower m (alphaValue (tripleAlphaIndex a r))) :
    simpleRandomWalkLaw
        (prop47SequentialExitScreenEvent profiles cStar
          m i a r) ≤
      4 * incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) *
        simpleRandomWalkLaw
          (prop47SequentialScreenEvent profiles cStar
            m i a r) := by
  let k := stageNumber r
  let tau : (ℕ → Direction) → ℕ := fun omega ↦
    (firstKSitesReachLevel m k (simpleRandomWalk omega)).untopA
  let screen := prop47SequentialScreenEvent profiles cStar
    m i a r
  let source := prop47SequentialExitScreenEvent profiles cStar
    m i a r
  let B := exitBeforeReturnEvent (squareDisk R : Set Site) 0
  have htau : Measurable tau :=
    ((isStoppingTime_firstKSitesReachLevel m k).measurable'.untopA).comp
      measurable_simpleRandomWalk
  have hAfiber (n : ℕ) : MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' screen ∩ {omega | tau omega + 1 = n}) := by
    exact sequentialScreen_stoppedFiber profiles hadapt cStar m i a r n hm
  have hB : MeasurableSet B := measurableSet_exitBeforeReturnEvent _ _
  have hincl : simpleRandomWalk ⁻¹' source ⊆
      simpleRandomWalk ⁻¹' screen ∩ incrementShiftAfter tau ⁻¹' B := by
    intro omega homega
    refine ⟨⟨homega.1, homega.2.2⟩, ?_⟩
    exact exitBeforeReturnAtNextCreation_increment_subset m k R
      (distanceBinLower m (alphaValue (tripleAlphaIndex a r))) hm
        (by simp [k, stageNumber]) hR homega.2.1
  have hbound := measure_inter_shift_le_four_mul tau
    (simpleRandomWalk ⁻¹' screen) B htau hAfiber hB
  have hscreenGlobal : MeasurableSet screen :=
    (measurableSet_prop47History profiles cStar m i a r.1).inter
      (measurableSet_lowScaleScreenEvent (profiles i)
        (cStar i) i m k
          (alphaValue (tripleAlphaIndex a r) + delta))
  have hsourceGlobal : MeasurableSet source := by
    exact (measurableSet_prop47History profiles cStar
      m i a r.1).inter
        ((measurableSet_exitBeforeReturnAtNextCreation m k
          (distanceBinLower m (alphaValue (tripleAlphaIndex a r)))).inter
        (measurableSet_lowScaleScreenEvent (profiles i)
          (cStar i) i m k
            (alphaValue (tripleAlphaIndex a r) + delta)))
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk hsourceGlobal,
    Measure.map_apply measurable_simpleRandomWalk hscreenGlobal]
  exact (measure_mono hincl).trans hbound

theorem canonicalSequentialExitScreen_le_four_escape_mul
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (R : ℕ) (hm : 0 < m)
    (hR : 3 * (R : ℝ) <
      distanceBinLower m (alphaValue (tripleAlphaIndex a r))) :
    simpleRandomWalkLaw
        (prop47SequentialExitScreenEvent canonicalProfiles canonicalCStar
          m i a r) ≤
      4 * incrementLaw (exitBeforeReturnEvent (squareDisk R : Set Site) 0) *
        simpleRandomWalkLaw
          (prop47SequentialScreenEvent canonicalProfiles canonicalCStar
            m i a r) :=
  sequentialExitScreen_le_four_escape_mul canonicalProfiles
    canonicalProfiles_oneStepAdapted canonicalCStar m i a r R hm hR

noncomputable def lowEscapeRadius (m : ℕ) (e : ℝ) : ℕ :=
  Nat.ceil (Real.exp (((m : ℝ) ^ e) / 2))

theorem tendsto_lowEscapeScale {e : ℝ} (he : 0 < e) :
    Tendsto (fun m : ℕ ↦ Real.exp (((m : ℝ) ^ e) / 2)) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact ((tendsto_rpow_atTop he).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num)

theorem eventually_lowEscapeRadius_properties {e : ℝ} (he : 0 < e) :
    ∀ᶠ m : ℕ in atTop,
      2 ≤ lowEscapeRadius m e ∧
        3 * (lowEscapeRadius m e : ℝ) < Real.exp ((m : ℝ) ^ e) / 3 ∧
        ((m : ℝ) ^ e) / 2 ≤ Real.log (lowEscapeRadius m e : ℝ) := by
  have hlarge := (tendsto_lowEscapeScale he).eventually (eventually_ge_atTop 10)
  filter_upwards [hlarge] with m hm
  let y := Real.exp (((m : ℝ) ^ e) / 2)
  have hypos : 0 < y := Real.exp_pos _
  have hyceil : y ≤ (lowEscapeRadius m e : ℝ) := Nat.le_ceil y
  have hyten : 10 ≤ y := by simpa only [y] using hm
  have hRtwo : 2 ≤ lowEscapeRadius m e := by
    have : (2 : ℝ) ≤ (lowEscapeRadius m e : ℝ) := by linarith
    exact_mod_cast this
  have hceil : (lowEscapeRadius m e : ℝ) < y + 1 :=
    Nat.ceil_lt_add_one hypos.le
  have hexpsq : Real.exp ((m : ℝ) ^ e) = y ^ 2 := by
    dsimp only [y]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hradius : 3 * (lowEscapeRadius m e : ℝ) <
      Real.exp ((m : ℝ) ^ e) / 3 := by
    rw [hexpsq]
    nlinarith [sq_nonneg (y - 10)]
  have hlog : ((m : ℝ) ^ e) / 2 ≤
      Real.log (lowEscapeRadius m e : ℝ) := by
    calc
      ((m : ℝ) ^ e) / 2 = Real.log y := by
        dsimp only [y]
        rw [Real.log_exp]
      _ ≤ Real.log (lowEscapeRadius m e : ℝ) :=
        Real.log_le_log hypos hyceil
  exact ⟨hRtwo, hradius, hlog⟩

theorem ofReal_sourceLowEscapeRate_oneTwentyEight
    (m : ℕ) (alpha : ℝ) :
    ENNReal.ofReal (128 /
      (((m : ℝ) + 1) ^ (alpha - delta))) =
      sourceLowEscapeRate m 128 alpha := by
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  have hnum : ENNReal.ofReal (128 : ℝ) = (128 : ℝ≥0∞) := by norm_num
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [hnum, ← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
  simp only [sourceLowEscapeRate, div_eq_mul_inv]
  rw [ENNReal.rpow_neg]
  norm_num

theorem eventually_four_escape_measure_le_sourceLowEscapeRate
    {alpha : ℝ} (he : 0 < alpha - delta) (halpha : alpha ≤ kappaTwo) :
    ∀ᶠ m : ℕ in atTop,
      4 * incrementLaw
          (exitBeforeReturnEvent
            (squareDisk (lowEscapeRadius m (alpha - delta)) : Set Site) 0) ≤
        sourceLowEscapeRate m 128 alpha := by
  filter_upwards [eventually_lowEscapeRadius_properties he,
    eventually_ge_atTop 1] with m hR hm
  let e := alpha - delta
  have he0 : 0 ≤ e := he.le
  have he1 : e ≤ 1 := by
    dsimp only [e]
    linarith [halpha, kappaTwo_between_one_third_and_kappaOne.2,
      kappaOne_between_one_third_and_seven_twentieths.2, delta_pos]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpowpos : 0 < (m : ℝ) ^ e := Real.rpow_pos_of_pos hmpos _
  have hshiftpos : 0 < ((m : ℝ) + 1) ^ e :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlogpos : 0 < Real.log (lowEscapeRadius m e : ℝ) :=
    Real.log_pos (by
      have : 1 < lowEscapeRadius m (alpha - delta) := by omega
      simpa only [e] using (show (1 : ℝ) < lowEscapeRadius m (alpha - delta) by
        exact_mod_cast this))
  have hfirst : 32 / Real.log (lowEscapeRadius m e : ℝ) ≤
      64 / ((m : ℝ) ^ e) := by
    apply (div_le_div_iff₀ hlogpos hpowpos).2
    nlinarith [hR.2.2]
  have htwo : (2 : ℝ) ^ e ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) he1
    simpa only [Real.rpow_one] using h
  have hbase : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hshift : ((m : ℝ) + 1) ^ e ≤ 2 * (m : ℝ) ^ e := by
    calc
      ((m : ℝ) + 1) ^ e ≤ (2 * (m : ℝ)) ^ e :=
        Real.rpow_le_rpow (by positivity) hbase he0
      _ = (2 : ℝ) ^ e * (m : ℝ) ^ e := by
        rw [Real.mul_rpow (by norm_num) hmpos.le]
      _ ≤ 2 * (m : ℝ) ^ e := by gcongr
  have hsecond : 64 / ((m : ℝ) ^ e) ≤
      128 / (((m : ℝ) + 1) ^ e) := by
    apply (div_le_div_iff₀ hpowpos hshiftpos).2
    nlinarith
  have hreal := hfirst.trans hsecond
  calc
    4 * incrementLaw
        (exitBeforeReturnEvent (squareDisk (lowEscapeRadius m e) : Set Site) 0) ≤
        4 * ENNReal.ofReal (8 / Real.log (lowEscapeRadius m e : ℝ)) := by
      gcongr
      exact measure_exitBeforeReturn_zero_le_ofReal_eight_div_log hR.1
    _ = ENNReal.ofReal (32 / Real.log (lowEscapeRadius m e : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hlogpos,
        ENNReal.ofReal_div_of_pos hlogpos]
      simp only [ENNReal.ofReal_ofNat]
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
      norm_num
    _ ≤ ENNReal.ofReal (128 / (((m : ℝ) + 1) ^ e)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = sourceLowEscapeRate m 128 alpha := by
      exact ofReal_sourceLowEscapeRate_oneTwentyEight m alpha

/-- The low-stage source escape factor in (4.37), for any one-step-adapted
profile family, with the explicit harmless constant coming from the one-step
terminal-pair exposure and the finite Green escape estimate. -/
theorem prop47SequentialEscapeEstimate_of_oneStepAdapted
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ) :
    Prop47SequentialEscapeEstimate profiles cStar 128 := by
  rw [Prop47SequentialEscapeEstimate, Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro a
  rw [Filter.eventually_all]
  intro r
  let alpha := alphaValue (tripleAlphaIndex a r)
  by_cases halpha : alpha ≤ kappaTwo
  · by_cases he : 0 < alpha - delta
    · filter_upwards [eventually_lowEscapeRadius_properties he,
        eventually_four_escape_measure_le_sourceLowEscapeRate he halpha,
        eventually_ge_atTop 1] with m hR hrate hm
      intro _halpha
      have hmpos : 0 < m := by omega
      have hradius :
          3 * (lowEscapeRadius m (alpha - delta) : ℝ) <
            distanceBinLower m alpha := by
        simpa only [distanceBinLower] using hR.2.1
      calc
        simpleRandomWalkLaw
            (prop47SequentialExitScreenEvent profiles cStar
              m i a r) ≤
            4 * incrementLaw
                (exitBeforeReturnEvent
                  (squareDisk (lowEscapeRadius m (alpha - delta)) : Set Site) 0) *
              simpleRandomWalkLaw
                (prop47SequentialScreenEvent profiles cStar
                  m i a r) :=
          sequentialExitScreen_le_four_escape_mul profiles hadapt cStar m i a r
            (lowEscapeRadius m (alpha - delta)) hmpos hradius
        _ ≤ sourceLowEscapeRate m 128 alpha *
              simpleRandomWalkLaw
                (prop47SequentialScreenEvent profiles cStar
                  m i a r) := by
          gcongr
    · exact Eventually.of_forall fun m _halpha ↦ by
        have hexp : 0 ≤ -(alpha - delta) := by linarith
        have hpow : 1 ≤
            ((m : ℝ≥0∞) + 1) ^ (-(alpha - delta)) := by
          by_cases hz : -(alpha - delta) = 0
          · simp [hz]
          · exact ENNReal.one_le_rpow (by simp) (lt_of_le_of_ne hexp (Ne.symm hz))
        have hrate : 1 ≤ sourceLowEscapeRate m 128 alpha := by
          rw [sourceLowEscapeRate]
          calc
            1 ≤ (128 : ℝ≥0∞) := by norm_num
            _ = (128 : ℝ≥0∞) * 1 := by simp
            _ ≤ (128 : ℝ≥0∞) *
                ((m : ℝ≥0∞) + 1) ^ (-(alpha - delta)) := by gcongr
        calc
          simpleRandomWalkLaw
              (prop47SequentialExitScreenEvent profiles cStar
                m i a r) ≤
              simpleRandomWalkLaw
                (prop47SequentialScreenEvent profiles cStar
                  m i a r) := by
            apply measure_mono
            rintro s ⟨hhistory, ⟨_hexit, hscreen⟩⟩
            exact ⟨hhistory, hscreen⟩
          _ = 1 * simpleRandomWalkLaw
                (prop47SequentialScreenEvent profiles cStar
                  m i a r) := by simp
          _ ≤ sourceLowEscapeRate m 128 alpha *
                simpleRandomWalkLaw
                  (prop47SequentialScreenEvent profiles cStar
                    m i a r) := by gcongr
  · exact Eventually.of_forall fun _m h ↦ (halpha h).elim

theorem canonical_prop47SequentialEscapeEstimate :
    Prop47SequentialEscapeEstimate canonicalProfiles canonicalCStar 128 :=
  prop47SequentialEscapeEstimate_of_oneStepAdapted canonicalProfiles
    canonicalProfiles_oneStepAdapted canonicalCStar

theorem sourceCanonical_prop47SequentialEscapeEstimate :
    Prop47SequentialEscapeEstimate sourceCanonicalProfiles canonicalCStar 128 :=
  prop47SequentialEscapeEstimate_of_oneStepAdapted sourceCanonicalProfiles
    sourceCanonicalProfiles_oneStepAdapted canonicalCStar

end Erdos1166.HLOZProp47LowEscape
