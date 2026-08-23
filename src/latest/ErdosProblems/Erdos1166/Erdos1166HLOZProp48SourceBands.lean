import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411Recursion
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma412Windows
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411
import ErdosProblems.Erdos1166.Erdos1166HLOZBandRatios

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval Topology

namespace Erdos1166.HLOZProp48SourceBands

open HLOZLemma411Recursion
open HLOZLemma412Windows
open HLOZBandRatios
open HLOZLemma411
open HLOZProp47Parameters

def categoryActive (y : Fin 3) : ℝ := if y = 2 then 0 else 1

def categoryScore (C : ℝ) (y : Fin 3) : ℝ :=
  if y = 0 then 1 else if y = 1 then -2 * C else 0

def categoryActiveCount {ι : Type*} [Fintype ι] (z : ι → Fin 3) : ℕ :=
  (Finset.univ.filter fun x ↦ z x ≠ 2).card

def categoryScoreSum {ι : Type*} [Fintype ι] (C : ℝ) (z : ι → Fin 3) : ℝ :=
  ∑ x, categoryScore C (z x)

def categoryImbalanceEvent {ι : Type*} [Fintype ι] (C : ℝ) (h : ℕ) :
    Set (ι → Fin 3) :=
  {z | h ≤ categoryActiveCount z ∧ 0 < categoryScoreSum C z}

lemma sum_categoryActive_eq_activeCount {ι : Type*} [Fintype ι]
    (z : ι → Fin 3) :
    ∑ x, categoryActive (z x) = categoryActiveCount z := by
  classical
  unfold categoryActiveCount
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hx : z x = 2 <;> simp [categoryActive, hx]

lemma coordinate_tilt_sum_le_one
    (ν : Measure (Fin 3)) [IsProbabilityMeasure ν]
    (C : ℝ) (hC : 1 ≤ C)
    (hq : 0 < ν.real {1}) (hpq : ν.real {0} ≤ C * ν.real {1}) :
    ∑ y, ν.real {y} * Real.exp
        (imbalanceRate C * categoryActive y + imbalanceTilt C * categoryScore C y) ≤ 1 := by
  let p := ν.real {0}
  let q := ν.real {1}
  let θ := Erdos1166.HLOZUrn.adjacentUrnParameter p q measureReal_nonneg hq
  have hθ : (θ : ℝ) ≤ C / (C + 1) :=
    Erdos1166.HLOZUrn.adjacentUrnParameter_le measureReal_nonneg hq
      (zero_le_one.trans hC) hpq
  have hbase := binomial_imbalance_base_le_exp θ hC hθ
  have hpqpos : 0 < p + q := by dsimp [p, q]; positivity
  have hpair :
      p * Real.exp (imbalanceTilt C) +
          q * Real.exp (-2 * C * imbalanceTilt C) ≤
        (p + q) * Real.exp (-imbalanceRate C) := by
    have hm := mul_le_mul_of_nonneg_left hbase hpqpos.le
    dsimp [θ] at hm
    calc
      p * Real.exp (imbalanceTilt C) +
          q * Real.exp (-2 * C * imbalanceTilt C) =
          (p + q) * (p / (p + q) * Real.exp (imbalanceTilt C) +
            (1 - p / (p + q)) * Real.exp (-2 * C * imbalanceTilt C)) := by
        field_simp [ne_of_gt hpqpos]
        <;> ring
      _ ≤ (p + q) * Real.exp (-imbalanceRate C) := hm
  have hpairTilt :
      p * Real.exp (imbalanceRate C + imbalanceTilt C) +
          q * Real.exp (imbalanceRate C - 2 * C * imbalanceTilt C) ≤ p + q := by
    have hexpPos := Real.exp_pos (imbalanceRate C)
    have hm := mul_le_mul_of_nonneg_left hpair hexpPos.le
    calc
      p * Real.exp (imbalanceRate C + imbalanceTilt C) +
          q * Real.exp (imbalanceRate C - 2 * C * imbalanceTilt C) =
          Real.exp (imbalanceRate C) *
            (p * Real.exp (imbalanceTilt C) +
              q * Real.exp (-2 * C * imbalanceTilt C)) := by
        rw [Real.exp_add, show imbalanceRate C - 2 * C * imbalanceTilt C =
          imbalanceRate C + (-2 * C * imbalanceTilt C) by ring,
          Real.exp_add]
        ring
      _ ≤ Real.exp (imbalanceRate C) *
          ((p + q) * Real.exp (-imbalanceRate C)) := hm
      _ = p + q := by
        rw [show Real.exp (imbalanceRate C) * ((p + q) *
          Real.exp (-imbalanceRate C)) =
            (p + q) * (Real.exp (imbalanceRate C) *
              Real.exp (-imbalanceRate C)) by ring,
          ← Real.exp_add]
        simp
  have htotal : ν.real {0} + ν.real {1} + ν.real {2} = 1 := by
    have hsum := sum_measureReal_singleton (μ := ν) (Finset.univ : Finset (Fin 3))
    have huniv : ν.real (Set.univ : Set (Fin 3)) = 1 := by
      rw [measureReal_def, measure_univ]
      norm_num
    calc
      ν.real {0} + ν.real {1} + ν.real {2} =
          ∑ y : Fin 3, ν.real {y} := by rw [Fin.sum_univ_three]
      _ = ν.real (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := hsum
      _ = ν.real (Set.univ : Set (Fin 3)) := by
        congr 1
        ext y
        simp
      _ = 1 := huniv
  calc
    ∑ y, ν.real {y} * Real.exp
        (imbalanceRate C * categoryActive y + imbalanceTilt C * categoryScore C y) =
        ν.real {0} * Real.exp (imbalanceRate C + imbalanceTilt C) +
          ν.real {1} * Real.exp (imbalanceRate C - 2 * C * imbalanceTilt C) +
          ν.real {2} := by
      simp [Fin.sum_univ_three, categoryActive, categoryScore]
      <;> ring
      <;> simp
    _ ≤ 1 := by
      dsimp [p, q] at hpairTilt
      nlinarith

lemma pi_measureReal_singleton {ι : Type*} [Fintype ι]
    (ν : ι → Measure (Fin 3)) [∀ x, IsProbabilityMeasure (ν x)]
    (z : ι → Fin 3) :
    (Measure.pi ν).real {z} = ∏ x, (ν x).real {z x} := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def]

theorem categorical_product_imbalance_real_le
    {ι : Type*} [Fintype ι]
    (ν : ι → Measure (Fin 3)) [∀ x, IsProbabilityMeasure (ν x)]
    (C : ℝ) (h : ℕ) (hC : 1 ≤ C)
    (hq : ∀ x, 0 < (ν x).real {1})
    (hpq : ∀ x, (ν x).real {0} ≤ C * (ν x).real {1}) :
    (Measure.pi ν).real (categoryImbalanceEvent C h) ≤
      Real.exp (-imbalanceRate C * h) := by
  classical
  let bad : Finset (ι → Fin 3) :=
    Finset.univ.filter fun z ↦ h ≤ categoryActiveCount z ∧ 0 < categoryScoreSum C z
  have hbad : (↑bad : Set (ι → Fin 3)) = categoryImbalanceEvent C h := by
    ext z
    simp [bad, categoryImbalanceEvent]
  rw [← hbad, ← sum_measureReal_singleton]
  calc
    ∑ z ∈ bad, (Measure.pi ν).real {z} ≤
        Real.exp (-imbalanceRate C * h) *
          ∑ z ∈ bad, (Measure.pi ν).real {z} *
            Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
              imbalanceTilt C * categoryScore C (z x))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hzbad := (Finset.mem_filter.mp hz).2
      have hactive : (h : ℝ) ≤ ∑ x, categoryActive (z x) := by
        rw [sum_categoryActive_eq_activeCount]
        exact_mod_cast hzbad.1
      have hrate := imbalanceRate_pos hC
      have htilt : 0 ≤ imbalanceTilt C := by unfold imbalanceTilt; positivity
      have hscore : 0 < categoryScoreSum C z := hzbad.2
      have hexponent : 0 ≤
          -imbalanceRate C * h +
            ∑ x, (imbalanceRate C * categoryActive (z x) +
              imbalanceTilt C * categoryScore C (z x)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        dsimp [categoryScoreSum] at hscore
        nlinarith
      have hone : 1 ≤ Real.exp (-imbalanceRate C * h) *
          Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
            imbalanceTilt C * categoryScore C (z x))) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hexponent
      calc
        (Measure.pi ν).real {z} = (Measure.pi ν).real {z} * 1 := (mul_one _).symm
        _ ≤ (Measure.pi ν).real {z} *
            (Real.exp (-imbalanceRate C * h) *
              Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
                imbalanceTilt C * categoryScore C (z x)))) :=
          mul_le_mul_of_nonneg_left hone measureReal_nonneg
        _ = Real.exp (-imbalanceRate C * h) *
            ((Measure.pi ν).real {z} *
              Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
                imbalanceTilt C * categoryScore C (z x)))) := by ring
    _ ≤ Real.exp (-imbalanceRate C * h) *
          ∑ z : ι → Fin 3, (Measure.pi ν).real {z} *
            Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
              imbalanceTilt C * categoryScore C (z x))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _hz _hnot
      positivity
    _ = Real.exp (-imbalanceRate C * h) *
          ∏ x, ∑ y : Fin 3, (ν x).real {y} * Real.exp
            (imbalanceRate C * categoryActive y + imbalanceTilt C * categoryScore C y) := by
      congr 1
      rw [Finset.prod_univ_sum]
      apply Finset.sum_congr
      · ext z
        simp
      intro z _hz
      rw [pi_measureReal_singleton, Real.exp_sum, Finset.prod_mul_distrib]
    _ ≤ Real.exp (-imbalanceRate C * h) * 1 := by
      gcongr
      exact Finset.prod_le_one (fun x _ ↦ by positivity)
        (fun x _ ↦ coordinate_tilt_sum_le_one (ν x) C hC (hq x) (hpq x))
    _ = Real.exp (-imbalanceRate C * h) := mul_one _

def categoryWindowedImbalanceEvent {ι : Type*} [Fintype ι]
    (valid : ι → Prop) (C : ℝ) (h : ℕ) : Set (ι → Fin 3) :=
  {z | (∀ x, ¬valid x → z x = 2) ∧
    h ≤ categoryActiveCount z ∧ 0 < categoryScoreSum C z}

noncomputable def windowedTiltWeight {ι : Type*}
    (valid : ι → Prop) [DecidablePred valid]
    (C : ℝ) (x : ι) (y : Fin 3) : ℝ :=
  if valid x then
    Real.exp (imbalanceRate C * categoryActive y +
      imbalanceTilt C * categoryScore C y)
  else if y = 2 then 1 else 0

/-- Variant allowing profiles outside the source mean window.  The event
requires those invalid coordinates to be inactive; only valid coordinates
need the adjacent-band comparison. -/
theorem categorical_product_windowed_imbalance_real_le
    {ι : Type*} [Fintype ι] (valid : ι → Prop) [DecidablePred valid]
    (ν : ι → Measure (Fin 3)) [∀ x, IsProbabilityMeasure (ν x)]
    (C : ℝ) (h : ℕ) (hC : 1 ≤ C)
    (hq : ∀ x, valid x → 0 < (ν x).real {1})
    (hpq : ∀ x, valid x → (ν x).real {0} ≤ C * (ν x).real {1}) :
    (Measure.pi ν).real (categoryWindowedImbalanceEvent valid C h) ≤
      Real.exp (-imbalanceRate C * h) := by
  classical
  let bad : Finset (ι → Fin 3) := Finset.univ.filter fun z ↦
    (∀ x, ¬valid x → z x = 2) ∧
      h ≤ categoryActiveCount z ∧ 0 < categoryScoreSum C z
  have hbad : (↑bad : Set (ι → Fin 3)) =
      categoryWindowedImbalanceEvent valid C h := by
    ext z
    simp [bad, categoryWindowedImbalanceEvent]
  rw [← hbad, ← sum_measureReal_singleton]
  calc
    ∑ z ∈ bad, (Measure.pi ν).real {z} ≤
        Real.exp (-imbalanceRate C * h) *
          ∑ z ∈ bad, ∏ x,
            (ν x).real {z x} * windowedTiltWeight valid C x (z x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hzbad := (Finset.mem_filter.mp hz).2
      have hactive : (h : ℝ) ≤ ∑ x, categoryActive (z x) := by
        rw [sum_categoryActive_eq_activeCount]
        exact_mod_cast hzbad.2.1
      have hrate := imbalanceRate_pos hC
      have htilt : 0 ≤ imbalanceTilt C := by unfold imbalanceTilt; positivity
      have hscore : 0 < categoryScoreSum C z := hzbad.2.2
      have hexponent : 0 ≤ -imbalanceRate C * h +
          ∑ x, (imbalanceRate C * categoryActive (z x) +
            imbalanceTilt C * categoryScore C (z x)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        dsimp [categoryScoreSum] at hscore
        nlinarith
      have hone : 1 ≤ Real.exp (-imbalanceRate C * h) *
          Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
            imbalanceTilt C * categoryScore C (z x))) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hexponent
      have hweight : ∏ x, windowedTiltWeight valid C x (z x) =
          Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
            imbalanceTilt C * categoryScore C (z x))) := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro x _hx
        by_cases hx : valid x
        · simp [windowedTiltWeight, hx]
        · have hzx := hzbad.1 x hx
          simp [windowedTiltWeight, hx, hzx, categoryActive, categoryScore]
      calc
        (Measure.pi ν).real {z} = ∏ x, (ν x).real {z x} :=
          pi_measureReal_singleton ν z
        _ = (∏ x, (ν x).real {z x}) * 1 := (mul_one _).symm
        _ ≤ (∏ x, (ν x).real {z x}) *
            (Real.exp (-imbalanceRate C * h) *
              Real.exp (∑ x, (imbalanceRate C * categoryActive (z x) +
                imbalanceTilt C * categoryScore C (z x)))) :=
          mul_le_mul_of_nonneg_left hone (Finset.prod_nonneg fun x _ ↦ measureReal_nonneg)
        _ = Real.exp (-imbalanceRate C * h) *
            ∏ x, ((ν x).real {z x} * windowedTiltWeight valid C x (z x)) := by
          rw [Finset.prod_mul_distrib, hweight]
          ring
    _ ≤ Real.exp (-imbalanceRate C * h) *
          ∑ z : ι → Fin 3, ∏ x,
            ((ν x).real {z x} * windowedTiltWeight valid C x (z x)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _hz _hnot
      exact Finset.prod_nonneg fun x _ ↦
        mul_nonneg measureReal_nonneg (by
          unfold windowedTiltWeight
          split_ifs <;> positivity)
    _ = Real.exp (-imbalanceRate C * h) *
          ∏ x, ∑ y : Fin 3,
            ((ν x).real {y} * windowedTiltWeight valid C x y) := by
      congr 1
      rw [Finset.prod_univ_sum]
      apply Finset.sum_congr
      · ext z
        simp
      intro z _hz
      rfl
    _ ≤ Real.exp (-imbalanceRate C * h) * 1 := by
      gcongr
      apply Finset.prod_le_one
      · intro x _hx
        exact Finset.sum_nonneg fun y _hy ↦
          mul_nonneg measureReal_nonneg (by
            unfold windowedTiltWeight
            split_ifs <;> positivity)
      · intro x _hx
        by_cases hx : valid x
        · simpa [windowedTiltWeight, hx] using
            coordinate_tilt_sum_le_one (ν x) C hC (hq x hx) (hpq x hx)
        · calc
            ∑ y : Fin 3, (ν x).real {y} * windowedTiltWeight valid C x y =
                (ν x).real {2} := by
              rw [Fin.sum_univ_three]
              simp [windowedTiltWeight, hx]
            _ ≤ 1 := measureReal_le_one
    _ = Real.exp (-imbalanceRate C * h) := mul_one _

/-! ### Concrete source windows -/

noncomputable def sourceCurrentLazyBand (m ℓ i : ℕ) : Finset ℕ :=
  Finset.Ico (sourceIntervalLower m ℓ - i) (sourceIntervalUpper m ℓ - i)

noncomputable def sourcePreviousLazyBand (m ℓ i : ℕ) : Finset ℕ :=
  Finset.Ico (sourceIntervalUpper m ℓ - i) (sourcePreviousUpper m ℓ - i)

/-- Category `0` is the current source band `I_ℓ`, category `1` is the
adjacent band immediately above it, and category `2` contains all other
lazy local-time values. -/
noncomputable def sourceBandCategory (m ℓ i k : ℕ) : Fin 3 :=
  if k ∈ sourceCurrentLazyBand m ℓ i then 0
  else if k ∈ sourcePreviousLazyBand m ℓ i then 1 else 2

noncomputable def sourceCategoryMeasure (m ℓ i : ℕ) : Measure (Fin 3) :=
  (Erdos1166.HLOZUrn.negBinMeasure i).map (sourceBandCategory m ℓ i)

instance (m ℓ i : ℕ) : IsProbabilityMeasure (sourceCategoryMeasure m ℓ i) := by
  unfold sourceCategoryMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma sourceCellWidth_pos (m : ℕ) (hm : 1 ≤ m) : 0 < sourceCellWidth m := by
  unfold sourceCellWidth
  rw [Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _

lemma negBinMass_pos (i k : ℕ) (hi : 1 ≤ i) :
    0 < Erdos1166.HLOZUrn.negBinMass i k := by
  unfold Erdos1166.HLOZUrn.negBinMass
  have hc : 0 < Nat.choose (i + k - 1) k := Nat.choose_pos (by omega)
  positivity

/-- Both adjacent total-local-time bands lie in the same lazy
negative-binomial mean window. -/
lemma source_adjacent_interval_arithmetic (c m ℓ i j : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hj : sourceIntervalLower m ℓ ≤ j ∧ j < sourcePreviousUpper m ℓ) :
    i ≤ j ∧ Erdos1166.HLOZUrn.InNegBinMeanBand i
      (sourceMeanBandRadius c m) (j - i) := by
  rcases hindex with ⟨hℓ, hindex⟩
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindex
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindex
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  refine ⟨hiLower.trans hj.1, ?_⟩
  unfold Erdos1166.HLOZUrn.InNegBinMeanBand
  unfold InSourceExternalWindow at hiwin
  unfold sourceMeanBandRadius
  omega

/-- Shifting one cell upward compares the two corresponding source-window
masses with the concrete constant `exp (1280(c+1))`. -/
lemma source_shifted_negBinMass_le (c m ℓ i k : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (hk : k ∈ sourceCurrentLazyBand m ℓ i) :
    Erdos1166.HLOZUrn.negBinMass i k ≤
      Real.exp (sourceComparisonExponent c) *
        Erdos1166.HLOZUrn.negBinMass i (k + sourceCellWidth m) := by
  rcases hindex with ⟨hℓ, hindexBound⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindexBound
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindexBound
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hgrowthCopy := hgrowth
  rcases hgrowthCopy with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  have hkIco := Finset.mem_Ico.mp hk
  have hj : sourceIntervalLower m ℓ ≤ i + k ∧
      i + k + sourceCellWidth m < sourcePreviousUpper m ℓ := by
    unfold sourceCurrentLazyBand at hkIco
    omega
  have hband₁ := (source_adjacent_interval_arithmetic c m ℓ i (i + k)
    ⟨hℓ, hindexBound⟩ hgrowth hiwin ⟨hj.1, by omega⟩).2
  have hband₂ := (source_adjacent_interval_arithmetic c m ℓ i
    (i + k + sourceCellWidth m) ⟨hℓ, hindexBound⟩ hgrowth hiwin
      ⟨by omega, hj.2⟩).2
  have hki : i + k - i = k := by omega
  have hkiShift : i + k + sourceCellWidth m - i = k + sourceCellWidth m := by omega
  rw [hki] at hband₁
  rw [hkiShift] at hband₂
  have hmi : m ≤ 4 * i := by
    unfold InSourceExternalWindow at hiwin
    omega
  have hi : 1 ≤ i := by omega
  have hscaleM : 320 * (c + 1) * m ≤ sourceComparisonExponent c * i := by
    have hmul := Nat.mul_le_mul_left (320 * (c + 1)) hmi
    convert hmul using 1 <;> simp [sourceComparisonExponent] <;> ring
  have hscale : 32 * sourceCellWidth m * (sourceMeanBandRadius c m + 1) ≤
      sourceComparisonExponent c * i := hsourceScale.trans hscaleM
  have hpow := negBinBandFactor_pow_le_exp_nat i (sourceMeanBandRadius c m)
    (sourceCellWidth m) (sourceComparisonExponent c) hi hscale
  have hpow' : Erdos1166.HLOZUrn.negBinBandFactor i
      (sourceMeanBandRadius c m) ^ (k + sourceCellWidth m - k) ≤
        Real.exp (sourceComparisonExponent c) := by
    simpa using hpow
  exact (Erdos1166.HLOZUrn.negBinMass_reverse_pow i
    (sourceMeanBandRadius c m) k (k + sourceCellWidth m) hi (by omega)
      hband₁ hband₂).trans
    (mul_le_mul_of_nonneg_right hpow'
      (Erdos1166.HLOZUrn.negBinMass_nonneg i (k + sourceCellWidth m)))

/-- The pointwise shifted comparison sums to the required comparison of the
two adjacent source-band masses. -/
theorem source_lazyBand_mass_le (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    ∑ k ∈ sourceCurrentLazyBand m ℓ i,
        Erdos1166.HLOZUrn.negBinMass i k ≤
      Real.exp (sourceComparisonExponent c) *
        ∑ k ∈ sourcePreviousLazyBand m ℓ i,
          Erdos1166.HLOZUrn.negBinMass i k := by
  rcases hindex with ⟨hℓ, hindexBound⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindexBound
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hgrowthCopy := hgrowth
  rcases hgrowthCopy with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindexBound
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  calc
    ∑ k ∈ sourceCurrentLazyBand m ℓ i,
        Erdos1166.HLOZUrn.negBinMass i k ≤
        ∑ k ∈ sourceCurrentLazyBand m ℓ i,
          Real.exp (sourceComparisonExponent c) *
            Erdos1166.HLOZUrn.negBinMass i (k + sourceCellWidth m) := by
      apply Finset.sum_le_sum
      intro k hk
      exact source_shifted_negBinMass_le c m ℓ i k
        ⟨hℓ, hindexBound⟩ hgrowth hiwin hk
    _ = Real.exp (sourceComparisonExponent c) *
        ∑ k ∈ sourcePreviousLazyBand m ℓ i,
          Erdos1166.HLOZUrn.negBinMass i k := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij (fun k _hk ↦ k + sourceCellWidth m)
      · intro k hk
        have hkIco := Finset.mem_Ico.mp hk
        apply Finset.mem_Ico.mpr
        unfold sourceCurrentLazyBand at hkIco
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        omega
      · intro r hr
        have hrIco := Finset.mem_Ico.mp hr
        refine ⟨r - sourceCellWidth m, ?_, by omega⟩
        apply Finset.mem_Ico.mpr
        unfold sourcePreviousLazyBand at hrIco
        omega
      · intro k hk
        rfl

lemma sourcePreviousLazyBand_nonempty (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    (sourcePreviousLazyBand m ℓ i).Nonempty := by
  rcases hindex with ⟨hℓ, hindexBound⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindexBound
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  have hgrowthCopy := hgrowth
  rcases hgrowthCopy with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindexBound
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  have hiLower : i ≤ sourceIntervalLower m ℓ := by
    unfold InSourceExternalWindow at hiwin
    omega
  refine ⟨sourceIntervalUpper m ℓ - i, ?_⟩
  apply Finset.mem_Ico.mpr
  constructor
  · rfl
  have hwidth := sourceCellWidth_pos m hm
  omega

/-- Every external profile lying in a valid adjacent-window regime is
positive.  This is the support fact needed for the negative-binomial law:
under the source growth and interval hypotheses, the external window sits a
definite distance away from profile zero. -/
lemma sourceExternalWindow_profile_pos (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) : 0 < i := by
  rcases hindex with ⟨hℓ, hindexBound⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    have hle : ℓ ≤ 2 * ℓ := by omega
    exact (Nat.mul_le_mul_right (sourceCellWidth m) hle).trans hindexBound
  obtain ⟨hupper, hprev⟩ := sourceInterval_endpoint_relations m ℓ hℓ hfit
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hsourceScale⟩
  have hindex' : 2 * (ℓ * sourceCellWidth m) ≤ m := by
    calc
      2 * (ℓ * sourceCellWidth m) = 2 * ℓ * sourceCellWidth m := by ring
      _ ≤ m := hindexBound
  have hhalf : m ≤ 2 * sourceIntervalLower m ℓ := by
    unfold sourceIntervalLower
    omega
  have hclose : 30 * sourceCellWidth m + 16 * sourceDeviationWidth c m ≤
      sourceIntervalLower m ℓ := by omega
  unfold InSourceExternalWindow at hiwin
  omega

lemma sourcePreviousLazyBand_mass_pos (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    0 < ∑ k ∈ sourcePreviousLazyBand m ℓ i,
      Erdos1166.HLOZUrn.negBinMass i k := by
  have hi : 1 ≤ i :=
    sourceExternalWindow_profile_pos c m ℓ i hindex hgrowth hiwin
  exact Finset.sum_pos (fun k _hk ↦ negBinMass_pos i k hi)
    (sourcePreviousLazyBand_nonempty c m ℓ i hindex hgrowth hiwin)

lemma sourceBandCategory_zero_preimage (m ℓ i : ℕ) :
    sourceBandCategory m ℓ i ⁻¹' ({0} : Set (Fin 3)) =
      (↑(sourceCurrentLazyBand m ℓ i) : Set ℕ) := by
  ext k
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · intro hk
    by_contra hkCurrent
    simp [sourceBandCategory, hkCurrent] at hk
    by_cases hkPrevious : k ∈ sourcePreviousLazyBand m ℓ i <;>
      simp [hkPrevious] at hk
  · intro hk
    simp [sourceBandCategory, hk]

lemma sourceBandCategory_one_preimage (m ℓ i : ℕ) :
    sourceBandCategory m ℓ i ⁻¹' ({1} : Set (Fin 3)) =
      (↑(sourcePreviousLazyBand m ℓ i) : Set ℕ) := by
  ext k
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe,
    sourceBandCategory]
  have hdisjoint : ¬(k ∈ sourceCurrentLazyBand m ℓ i ∧
      k ∈ sourcePreviousLazyBand m ℓ i) := by
    intro hk
    have hk₀ := Finset.mem_Ico.mp hk.1
    have hk₁ := Finset.mem_Ico.mp hk.2
    unfold sourceCurrentLazyBand at hk₀
    unfold sourcePreviousLazyBand at hk₁
    omega
  by_cases hk₀ : k ∈ sourceCurrentLazyBand m ℓ i
  · have hk₁ : k ∉ sourcePreviousLazyBand m ℓ i := by
      intro hk₁
      exact hdisjoint ⟨hk₀, hk₁⟩
    simp [hk₀, hk₁]
  · simp [hk₀]

lemma sourceCategoryMeasure_real_zero (m ℓ i : ℕ) :
    (sourceCategoryMeasure m ℓ i).real {0} =
      ∑ k ∈ sourceCurrentLazyBand m ℓ i,
        Erdos1166.HLOZUrn.negBinMass i k := by
  rw [measureReal_def, sourceCategoryMeasure,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton 0),
    sourceBandCategory_zero_preimage, ← measureReal_def,
    ← sum_measureReal_singleton]
  apply Finset.sum_congr rfl
  intro k _hk
  exact Erdos1166.HLOZUrn.negBinMeasure_real_singleton i k

lemma sourceCategoryMeasure_real_one (m ℓ i : ℕ) :
    (sourceCategoryMeasure m ℓ i).real {1} =
      ∑ k ∈ sourcePreviousLazyBand m ℓ i,
        Erdos1166.HLOZUrn.negBinMass i k := by
  rw [measureReal_def, sourceCategoryMeasure,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton 1),
    sourceBandCategory_one_preimage, ← measureReal_def,
    ← sum_measureReal_singleton]
  apply Finset.sum_congr rfl
  intro k _hk
  exact Erdos1166.HLOZUrn.negBinMeasure_real_singleton i k

theorem sourceCategoryMeasure_mass_comparable (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    (sourceCategoryMeasure m ℓ i).real {0} ≤
      Real.exp (sourceComparisonExponent c) *
        (sourceCategoryMeasure m ℓ i).real {1} := by
  rw [sourceCategoryMeasure_real_zero, sourceCategoryMeasure_real_one]
  exact source_lazyBand_mass_le c m ℓ i hindex hgrowth hiwin

lemma sourceCategoryMeasure_one_pos (c m ℓ i : ℕ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    0 < (sourceCategoryMeasure m ℓ i).real {1} := by
  rw [sourceCategoryMeasure_real_one]
  exact sourcePreviousLazyBand_mass_pos c m ℓ i hindex hgrowth hiwin

/-! ### Fixed external profile events -/

def categoryUpperCount {ι : Type*} [Fintype ι] (z : ι → Fin 3) : ℕ :=
  (Finset.univ.filter fun x ↦ z x = 0).card

def categoryLowerCount {ι : Type*} [Fintype ι] (z : ι → Fin 3) : ℕ :=
  (Finset.univ.filter fun x ↦ z x = 1).card

lemma categoryActiveCount_eq_add {ι : Type*} [Fintype ι]
    (z : ι → Fin 3) :
    categoryActiveCount z = categoryUpperCount z + categoryLowerCount z := by
  classical
  unfold categoryActiveCount categoryUpperCount categoryLowerCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    generalize hy : z x = y
    fin_cases y <;> simp [hy]
  · apply Finset.disjoint_left.mpr
    intro x hx₀ hx₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₀ hx₁
    omega

lemma categoryScoreSum_eq_sub {ι : Type*} [Fintype ι]
    (C : ℝ) (z : ι → Fin 3) :
    categoryScoreSum C z =
      categoryUpperCount z - 2 * C * categoryLowerCount z := by
  classical
  unfold categoryScoreSum categoryUpperCount categoryLowerCount
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  generalize hy : z x = y
  fin_cases y <;> simp [categoryScore]

noncomputable def sourceProfileCategory {ι : Type*}
    (m ℓ : ℕ) (profile lazy : ι → ℕ) : ι → Fin 3 :=
  fun x ↦ sourceBandCategory m ℓ (profile x) (lazy x)

def sourceProfileBelowMEvent {ι : Type*}
    (m : ℕ) (profile : ι → ℕ) : Set (ι → ℕ) :=
  {lazy | ∀ x, profile x + lazy x < m}

noncomputable def sourceProfileBandCount {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (profile lazy : ι → ℕ) : ℕ :=
  categoryUpperCount (sourceProfileCategory m ℓ profile lazy)

/-- A band count cannot exceed the number of available coordinates. -/
lemma sourceProfileBandCount_le_card {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (profile lazy : ι → ℕ) :
    sourceProfileBandCount m ℓ profile lazy ≤ Fintype.card ι := by
  classical
  unfold sourceProfileBandCount categoryUpperCount
  simpa only [Finset.card_univ] using
    (Finset.card_filter_le (Finset.univ : Finset ι)
      (fun x ↦ sourceProfileCategory m ℓ profile lazy x = 0))

noncomputable def sourceProfileBandOverflow {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (profile : ι → ℕ) (ρ : ℝ) : Set (ι → ℕ) :=
  {lazy | ρ < sourceProfileBandCount m ℓ profile lazy}

noncomputable def sourceProfileQEvent {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (profile : ι → ℕ) (ρ : ℝ) : Set (ι → ℕ) :=
  sourceProfileBelowMEvent m profile ∩ sourceProfileBandOverflow m ℓ profile ρ

/-- The exact profile-window failure denoted by `Θ` in the one-step
argument: an active adjacent-band coordinate has external local time outside
the Lemma 4.12 mean window. -/
noncomputable def sourceProfileThetaBad {ι : Type*} [Fintype ι]
    (c m ℓ : ℕ) (profile : ι → ℕ) : Set (ι → ℕ) :=
  {lazy | ∃ x, sourceBandCategory m ℓ (profile x) (lazy x) ≠ 2 ∧
    ¬ InSourceExternalWindow c m ℓ (profile x)}

lemma sourceProfileCategory_outside_eq_two
    {ι : Type*} [Fintype ι] {c m ℓ : ℕ} {profile lazy : ι → ℕ}
    (hgood : lazy ∉ sourceProfileThetaBad c m ℓ profile) :
    ∀ x, ¬ InSourceExternalWindow c m ℓ (profile x) →
      sourceProfileCategory m ℓ profile lazy x = 2 := by
  intro x hx
  by_contra hne
  exact hgood ⟨x, hne, hx⟩

lemma sourceProfileBandCount_eq_upperCount
    {ι : Type*} [Fintype ι] (m ℓ : ℕ) (profile lazy : ι → ℕ) :
    sourceProfileBandCount m ℓ profile lazy =
      categoryUpperCount (sourceProfileCategory m ℓ profile lazy) := rfl

lemma sourceProfile_previousBandCount_eq_lowerCount
    {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (hfit : ℓ * sourceCellWidth m ≤ m)
    (profile lazy : ι → ℕ) :
    sourceProfileBandCount m (ℓ - 1) profile lazy =
      categoryLowerCount (sourceProfileCategory m ℓ profile lazy) := by
  classical
  unfold sourceProfileBandCount categoryUpperCount categoryLowerCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold sourceProfileCategory sourceBandCategory sourceCurrentLazyBand
    sourcePreviousLazyBand
  have hlower : sourceIntervalLower m (ℓ - 1) = sourceIntervalUpper m ℓ := by
    unfold sourceIntervalLower sourceIntervalUpper
    omega
  have hupper : sourceIntervalUpper m (ℓ - 1) = sourcePreviousUpper m ℓ := by
    have hmul : (ℓ - 1 - 1) * sourceCellWidth m + sourceCellWidth m =
        (ℓ - 1) * sourceCellWidth m := by
      have hc : ℓ - 1 - 1 + 1 = ℓ - 1 := by omega
      simpa [Nat.add_mul] using
        congrArg (fun n : ℕ ↦ n * sourceCellWidth m) hc
    unfold sourceIntervalUpper sourcePreviousUpper
    rw [← hmul]
    omega
  have hbands : sourceCurrentLazyBand m (ℓ - 1) (profile x) =
      sourcePreviousLazyBand m ℓ (profile x) := by
    unfold sourceCurrentLazyBand sourcePreviousLazyBand
    rw [hlower, hupper]
  have hzero : sourceBandCategory m (ℓ - 1) (profile x) (lazy x) = 0 ↔
      lazy x ∈ sourceCurrentLazyBand m (ℓ - 1) (profile x) := by
    change lazy x ∈ sourceBandCategory m (ℓ - 1) (profile x) ⁻¹' ({0} : Set (Fin 3)) ↔ _
    rw [sourceBandCategory_zero_preimage]
    rfl
  have hone : sourceBandCategory m ℓ (profile x) (lazy x) = 1 ↔
      lazy x ∈ sourcePreviousLazyBand m ℓ (profile x) := by
    change lazy x ∈ sourceBandCategory m ℓ (profile x) ⁻¹' ({1} : Set (Fin 3)) ↔ _
    rw [sourceBandCategory_one_preimage]
    rfl
  change sourceBandCategory m (ℓ - 1) (profile x) (lazy x) = 0 ↔
    sourceBandCategory m ℓ (profile x) (lazy x) = 1
  rw [hzero, hbands, hone]

lemma sourceProfile_first_previous_empty_of_below
    {ι : Type*} [Fintype ι] {m : ℕ} {profile lazy : ι → ℕ}
    (hbelow : lazy ∈ sourceProfileBelowMEvent m profile) :
    categoryLowerCount (sourceProfileCategory m 1 profile lazy) = 0 := by
  classical
  unfold categoryLowerCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _hx hxone
  have hprev : lazy x ∈ sourcePreviousLazyBand m 1 (profile x) := by
    have hnotcurrent : lazy x ∉ sourceCurrentLazyBand m 1 (profile x) := by
      intro hcur
      simp [sourceProfileCategory, sourceBandCategory, hcur] at hxone
    simpa [sourceProfileCategory, sourceBandCategory, hnotcurrent] using hxone
  have hp := Finset.mem_Ico.mp hprev
  have htotal : m ≤ profile x + lazy x := by
    unfold sourcePreviousLazyBand sourceIntervalUpper at hp
    omega
  exact (Nat.not_le_of_lt (hbelow x)) htotal

noncomputable def sourceProfileImbalanceEvent {ι : Type*} [Fintype ι]
    (c m ℓ : ℕ) (profile : ι → ℕ) (ρ : ℝ) : Set (ι → ℕ) :=
  sourceProfileCategory m ℓ profile ⁻¹'
    categoryWindowedImbalanceEvent
      (fun x ↦ InSourceExternalWindow c m ℓ (profile x))
      (Real.exp (sourceAdjacentComparisonExponent c)) (Nat.ceil ρ)

/-- Mapping the exact external-profile product law coordinatewise produces
the product of the three-category source-band laws.  The equality `hProduct`
is the finite conditional-product theorem that must ultimately be supplied
by the stopped-walk construction. -/
theorem sourceProfileCategory_map_eq_pi
    {ι : Type*} [Fintype ι] (m ℓ : ℕ) (profile : ι → ℕ)
    (μ : Measure (ι → ℕ))
    (hProduct : μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x))) :
    μ.map (sourceProfileCategory m ℓ profile) =
      Measure.pi (fun x ↦ sourceCategoryMeasure m ℓ (profile x)) := by
  rw [hProduct]
  exact Measure.pi_map_pi fun x ↦
    (measurable_of_countable (sourceBandCategory m ℓ (profile x))).aemeasurable

lemma sourceCategoryMeasure_mass_comparable_adjacent
    (c m ℓ i : ℕ) (hindex : SourceIntervalIndex m ℓ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    (sourceCategoryMeasure m ℓ i).real {0} ≤
      Real.exp (sourceAdjacentComparisonExponent c) *
        (sourceCategoryMeasure m ℓ i).real {1} := by
  have hsmall := sourceCategoryMeasure_mass_comparable c m ℓ i
    hindex hgrowth hiwin
  have hexp : Real.exp (sourceComparisonExponent c) ≤
      Real.exp (sourceAdjacentComparisonExponent c) := by
    apply Real.exp_le_exp.mpr
    rw [show (sourceAdjacentComparisonExponent c : ℝ) =
      2 * sourceComparisonExponent c by
        norm_num [sourceAdjacentComparisonExponent]]
    have hnonneg : (0 : ℝ) ≤ sourceComparisonExponent c := by positivity
    linarith
  calc
    (sourceCategoryMeasure m ℓ i).real {0} ≤
        Real.exp (sourceComparisonExponent c) *
          (sourceCategoryMeasure m ℓ i).real {1} := hsmall
    _ ≤ Real.exp (sourceAdjacentComparisonExponent c) *
          (sourceCategoryMeasure m ℓ i).real {1} := by gcongr

/-- The event-level adjacent-band estimate in (4.48), conditional on one
fixed finite external profile.  No conditional-binomial-law premise is
used: it follows from the exact product law by the finite product Chernoff
calculation above. -/
theorem sourceProfileImbalance_real_le
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (μ : Measure (ι → ℕ))
    (hProduct : μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x)))
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (ρ : ℝ) :
    μ.real (sourceProfileImbalanceEvent c m ℓ profile ρ) ≤
      Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) *
        Nat.ceil ρ) := by
  classical
  let C := Real.exp (sourceAdjacentComparisonExponent c)
  have hC : 1 ≤ C := Real.one_le_exp (by positivity)
  have hmap := sourceProfileCategory_map_eq_pi m ℓ profile μ hProduct
  rw [measureReal_def, sourceProfileImbalanceEvent,
    ← Measure.map_apply (measurable_of_countable _)
      MeasurableSet.of_discrete, hmap, ← measureReal_def]
  apply categorical_product_windowed_imbalance_real_le
    (fun x ↦ InSourceExternalWindow c m ℓ (profile x))
    (fun x ↦ sourceCategoryMeasure m ℓ (profile x)) C (Nat.ceil ρ) hC
  · intro x hx
    exact sourceCategoryMeasure_one_pos c m ℓ (profile x) hindex hgrowth hx
  · intro x hx
    exact sourceCategoryMeasure_mass_comparable_adjacent c m ℓ (profile x)
      hindex hgrowth hx

/-- Deterministic source cover behind the first-level estimate (4.47).
The artificial band above `I₁` is empty on the below-`m` event. -/
theorem sourceProfile_base_cover
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    sourceProfileQEvent m 1 profile ρ ⊆
      sourceProfileThetaBad c m 1 profile ∪
        sourceProfileImbalanceEvent c m 1 profile ρ := by
  intro lazy hlazy
  by_cases htheta : lazy ∈ sourceProfileThetaBad c m 1 profile
  · exact Or.inl htheta
  · right
    refine ⟨sourceProfileCategory_outside_eq_two htheta, ?_, ?_⟩
    · rw [categoryActiveCount_eq_add]
      have hover : ρ <
          (sourceProfileBandCount m 1 profile lazy : ℝ) := hlazy.2
      have hceil : Nat.ceil ρ ≤ sourceProfileBandCount m 1 profile lazy :=
        Nat.ceil_le.mpr hover.le
      simpa [sourceProfileBandCount] using
        hceil.trans (Nat.le_add_right _ _)
    · rw [categoryScoreSum_eq_sub,
        ← sourceProfileBandCount_eq_upperCount]
      have hlower := sourceProfile_first_previous_empty_of_below hlazy.1
      rw [hlower]
      push_cast
      have hover := hlazy.2
      dsimp [sourceProfileBandOverflow] at hover
      nlinarith

/-- Deterministic cover behind one transition in (4.48). -/
theorem sourceProfile_one_step_cover
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (hℓ : 2 ≤ ℓ) (hfit : ℓ * sourceCellWidth m ≤ m)
    {ρprev ρcur : ℝ} (hρcur : 0 ≤ ρcur)
    (hgrow : 2 * Real.exp (sourceAdjacentComparisonExponent c) * ρprev ≤ ρcur) :
    sourceProfileQEvent m ℓ profile ρcur ⊆
      sourceProfileQEvent m (ℓ - 1) profile ρprev ∪
        sourceProfileThetaBad c m ℓ profile ∪
          sourceProfileImbalanceEvent c m ℓ profile ρcur := by
  intro lazy hlazy
  by_cases hprev : lazy ∈ sourceProfileQEvent m (ℓ - 1) profile ρprev
  · exact Or.inl (Or.inl hprev)
  by_cases htheta : lazy ∈ sourceProfileThetaBad c m ℓ profile
  · exact Or.inl (Or.inr htheta)
  · right
    have hprevCount : (sourceProfileBandCount m (ℓ - 1) profile lazy : ℝ) ≤
        ρprev := by
      have hnotOverflow : lazy ∉ sourceProfileBandOverflow m (ℓ - 1) profile ρprev := by
        intro hover
        exact hprev ⟨hlazy.1, hover⟩
      exact le_of_not_gt hnotOverflow
    have hpreviousEq := sourceProfile_previousBandCount_eq_lowerCount
      m ℓ hℓ hfit profile lazy
    refine ⟨sourceProfileCategory_outside_eq_two htheta, ?_, ?_⟩
    · rw [categoryActiveCount_eq_add]
      have hover : ρcur <
          (sourceProfileBandCount m ℓ profile lazy : ℝ) := hlazy.2
      have hceil : Nat.ceil ρcur ≤ sourceProfileBandCount m ℓ profile lazy :=
        Nat.ceil_le.mpr hover.le
      simpa [sourceProfileBandCount] using
        hceil.trans (Nat.le_add_right _ _)
    · rw [categoryScoreSum_eq_sub,
        ← sourceProfileBandCount_eq_upperCount, ← hpreviousEq]
      have hover := hlazy.2
      dsimp [sourceProfileBandOverflow] at hover
      have hC0 : 0 ≤ Real.exp (sourceAdjacentComparisonExponent c) :=
        (Real.exp_pos _).le
      nlinarith

lemma sourceProfileImbalance_real_le_threshold
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (μ : Measure (ι → ℕ))
    (hProduct : μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x)))
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (ρ : ℝ) :
    μ.real (sourceProfileImbalanceEvent c m ℓ profile ρ) ≤
      Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρ) := by
  have htail := sourceProfileImbalance_real_le c m ℓ profile μ hProduct
    hindex hgrowth ρ
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hrate : 0 < imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) :=
    imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hceil : ρ ≤ (Nat.ceil ρ : ℝ) := Nat.le_ceil ρ
  nlinarith

/-- Exact one-step probability recursion (4.48) for one fixed finite
external profile.  Its only probabilistic inputs are `hProduct`, the exact
conditional product law, and `hTheta`, the source `Θ` estimate. -/
theorem sourceProfile_one_step_recursion
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (μ : Measure (ι → ℕ))
    (hProduct : μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x)))
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hℓ : 2 ≤ ℓ) {ρprev ρcur cTheta a : ℝ}
    (hρcur : 0 ≤ ρcur)
    (hgrow : 2 * Real.exp (sourceAdjacentComparisonExponent c) * ρprev ≤ ρcur)
    (hTheta : μ.real (sourceProfileThetaBad c m ℓ profile) ≤
      Real.exp (-cTheta * (m : ℝ) ^ a)) :
    μ.real (sourceProfileQEvent m ℓ profile ρcur) ≤
      μ.real (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
  letI : IsProbabilityMeasure μ := ⟨by rw [hProduct, measure_univ]⟩
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    calc
      ℓ * sourceCellWidth m ≤ 2 * ℓ * sourceCellWidth m := by
        exact Nat.mul_le_mul_right (sourceCellWidth m) (by omega)
      _ ≤ m := hindex.2
  have hcover := sourceProfile_one_step_cover c m ℓ profile hℓ
    hfit hρcur hgrow
  have himbalance := sourceProfileImbalance_real_le_threshold c m ℓ profile μ
    hProduct hindex hgrowth ρcur
  calc
    μ.real (sourceProfileQEvent m ℓ profile ρcur) ≤
        μ.real ((sourceProfileQEvent m (ℓ - 1) profile ρprev ∪
          sourceProfileThetaBad c m ℓ profile) ∪
          sourceProfileImbalanceEvent c m ℓ profile ρcur) :=
      measureReal_mono hcover
    _ ≤ (μ.real (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        μ.real (sourceProfileThetaBad c m ℓ profile)) +
        μ.real (sourceProfileImbalanceEvent c m ℓ profile ρcur) := by
      exact (measureReal_union_le _ _).trans
        (add_le_add (measureReal_union_le _ _) (le_refl _))
    _ ≤ μ.real (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-cTheta * (m : ℝ) ^ a) +
        Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) := by
      gcongr
    _ = μ.real (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by ring

theorem sourceProfile_base_recursion
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    (μ : Measure (ι → ℕ))
    (hProduct : μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x)))
    (hindex : SourceIntervalIndex m 1) (hgrowth : SourceWindowGrowth c m)
    {ρ cTheta a : ℝ} (hρ : 0 ≤ ρ)
    (hTheta : μ.real (sourceProfileThetaBad c m 1 profile) ≤
      Real.exp (-cTheta * (m : ℝ) ^ a)) :
    μ.real (sourceProfileQEvent m 1 profile ρ) ≤
      Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρ) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
  letI : IsProbabilityMeasure μ := ⟨by rw [hProduct, measure_univ]⟩
  have hcover := sourceProfile_base_cover c m profile hρ
  have himbalance := sourceProfileImbalance_real_le_threshold c m 1 profile μ
    hProduct hindex hgrowth ρ
  calc
    μ.real (sourceProfileQEvent m 1 profile ρ) ≤
        μ.real (sourceProfileThetaBad c m 1 profile ∪
          sourceProfileImbalanceEvent c m 1 profile ρ) := measureReal_mono hcover
    _ ≤ μ.real (sourceProfileThetaBad c m 1 profile) +
        μ.real (sourceProfileImbalanceEvent c m 1 profile ρ) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-cTheta * (m : ℝ) ^ a) +
        Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρ) := by
      gcongr
    _ = Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρ) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := add_comm _ _

lemma geometricThreshold_succ (rho R : ℝ) {l : ℕ} (hl : 1 ≤ l) :
    geometricThreshold rho R (l + 1) = R * geometricThreshold rho R l := by
  unfold geometricThreshold
  have hsub : l - 1 + 1 = l := Nat.sub_add_cancel hl
  rw [show l + 1 - 1 = l by omega]
  calc
    rho * R ^ l = rho * R ^ (l - 1 + 1) := by rw [hsub]
    _ = R * (rho * R ^ (l - 1)) := by rw [pow_succ]; ring

/-- The two base errors from the first source cell are absorbed into the
single logarithmic-square error required by Lemma 4.11. -/
lemma eventually_sourceProfile_base_absorb
    {r cTheta a : ℝ} (hr : 0 < r) (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ (qbase rho : ℝ),
      Real.log (m : ℝ) ^ 2 ≤ rho →
      qbase ≤ Real.exp (-r * rho) +
        Real.exp (-cTheta * (m : ℝ) ^ a) →
      qbase ≤ Real.exp (-(r / 2) * Real.log (m : ℝ) ^ 2) := by
  have hstretch := eventually_const_mul_log_sq_le_rpow hr hcTheta ha
  have habsorb := eventually_three_rpow_mul_exp_neg_log_sq_le hr
    (show (0 : ℝ) ≤ 0 by norm_num)
  filter_upwards [hstretch, habsorb] with m hstretch habsorb qbase rho hrho hq
  have hfirst : Real.exp (-r * rho) ≤
      Real.exp (-r * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsecond : Real.exp (-cTheta * (m : ℝ) ^ a) ≤
      Real.exp (-r * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    qbase ≤ Real.exp (-r * rho) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := hq
    _ ≤ 2 * Real.exp (-r * Real.log (m : ℝ) ^ 2) := by nlinarith
    _ ≤ 3 * (m : ℝ) ^ (0 : ℝ) *
        Real.exp (-r * Real.log (m : ℝ) ^ 2) := by
      rw [Real.rpow_zero]
      have he : 0 < Real.exp (-r * Real.log (m : ℝ) ^ 2) := Real.exp_pos _
      nlinarith
    _ ≤ Real.exp (-(r / 2) * Real.log (m : ℝ) ^ 2) := habsorb

/-- Source-window form of Proposition 4.8 for one fixed finite external
profile.  The number of cells is exactly
`floor (m^(alpha-kappaOne)) + 1`, their width is the corrected
`ceil (m^(17/50))`, and the recursion ratio is the concrete BandRatios
constant `2 exp(sourceAdjacentComparisonExponent c)`.

The only unresolved probabilistic facts in this theorem are exactly:
* `hProduct`, the conditional product law of the lazy runs after fixing the
  external profile; and
* `hTheta`, the per-level bad-profile estimate.
-/
theorem eventually_sourceProfile_prop48_band_bound
    {ι : Type*} [Fintype ι] (c : ℕ) {cTheta a : ℝ}
    (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ (alpha : ℝ) (profile : ι → ℕ)
      (μ : Measure (ι → ℕ)),
      kappaOne ≤ alpha → alpha ≤ (4 : ℝ) / 5 →
      μ = Measure.pi (fun x ↦ Erdos1166.HLOZUrn.negBinMeasure (profile x)) →
      (∀ l, 1 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
        μ.real (sourceProfileThetaBad c m l profile) ≤
          Real.exp (-cTheta * (m : ℝ) ^ a)) →
      μ.real (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha))) ≤
        Real.exp (-(imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) / 4) *
            Real.log (m : ℝ) ^ 2) := by
  let r := imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))
  let R := sourceLemma411GrowthFactor c
  have hr : 0 < r := imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hR : 1 ≤ R := sourceLemma411GrowthFactor_one_le c
  have hbase := eventually_sourceProfile_base_absorb hr hcTheta ha
  have hassembly := eventually_hloz_lemma_4_11_assembly
    (show 0 < r / 2 by positivity) hcTheta ha
      (show (0 : ℝ) ≤ 1 by norm_num) hR
  filter_upwards [eventually_sourceWindowGrowth c, eventually_sourceIntervalIndex,
    hbase, hassembly, eventually_ge_atTop 1] with
      m hgrowth hindices hbaseM hassemblyM hm alpha profile μ halpha hAlpha hProduct hTheta
  let L := sourceAlphaIntervalCount m alpha
  let rho := Real.log (m : ℝ) ^ 2
  let q : ℕ → ℝ := fun l ↦ μ.real
    (sourceProfileQEvent m l profile (geometricThreshold rho R l))
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hLcut : L ≤ sourceIntervalCutoff m :=
    sourceAlphaIntervalCount_le_cutoff m hm hAlpha
  have hLindex : SourceIntervalIndex m L := hindices L hL hLcut
  have hwidth : 0 < sourceCellWidth m := sourceCellWidth_pos m hm
  have hLm : L ≤ m := by
    calc
      L ≤ L * sourceCellWidth m := Nat.le_mul_of_pos_right L hwidth
      _ ≤ 2 * L * sourceCellWidth m := by
        simpa only [mul_assoc] using
          (Nat.le_mul_of_pos_left (L * sourceCellWidth m) (by omega : 0 < 2))
      _ ≤ m := hLindex.2
  have hlevels : ((((L - 1) + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 : ℝ)) := by
    rw [Nat.sub_add_cancel hL, Real.rpow_one]
    exact_mod_cast hLm
  have hrho : Real.log (m : ℝ) ^ 2 ≤ rho := le_rfl
  have hrho0 : 0 ≤ rho := sq_nonneg _
  have hbaseRaw : q 1 ≤ Real.exp (-r * rho) +
      Real.exp (-cTheta * (m : ℝ) ^ a) := by
    dsimp [q]
    rw [geometricThreshold_one]
    exact sourceProfile_base_recursion c m profile μ hProduct
      (hindices 1 (by omega) (hL.trans hLcut)) hgrowth hrho0 (hTheta 1 (by omega) hL)
  have hqone : q 1 ≤ Real.exp (-(r / 2) * Real.log (m : ℝ) ^ 2) :=
    hbaseM (q 1) rho hrho hbaseRaw
  have hstep : ∀ k < L - 1,
      q (k + 2) ≤ q (k + 1) +
        Real.exp (-(r / 2) * geometricThreshold rho R (k + 2)) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
    intro k hk
    have hlevel : k + 2 ≤ L := by omega
    have hlevelCut : k + 2 ≤ sourceIntervalCutoff m := hlevel.trans hLcut
    have hindex := hindices (k + 2) (by omega) hlevelCut
    have hthreshold : geometricThreshold rho R (k + 2) =
        2 * Real.exp (sourceAdjacentComparisonExponent c) *
          geometricThreshold rho R (k + 1) := by
      rw [geometricThreshold_succ rho R (show 1 ≤ k + 1 by omega)]
      rfl
    have hrec := sourceProfile_one_step_recursion c m (k + 2) profile μ
      hProduct hindex hgrowth (by omega)
      (hrho0.trans (geometricThreshold_le rho R hrho0 hR (by omega)))
      (le_of_eq hthreshold.symm)
      (hTheta (k + 2) (by omega) hlevel)
    have hweaken : Real.exp (-r * geometricThreshold rho R (k + 2)) ≤
        Real.exp (-(r / 2) * geometricThreshold rho R (k + 2)) := by
      apply Real.exp_le_exp.mpr
      have ht0 := geometricThreshold_le rho R hrho0 hR
        (show 1 ≤ k + 2 by omega)
      nlinarith
    dsimp [q] at hrec ⊢
    exact hrec.trans (by gcongr)
  have hfinal := hassemblyM q (L - 1) rho hrho hlevels hqone hstep
  rw [show r / 2 / 2 = r / 4 by ring] at hfinal
  simpa only [q, L, R, r, rho, Nat.sub_add_cancel hL] using hfinal

/-! ### Full-grid versus `Lambda₀` bookkeeping -/

/-- The two source grids are genuinely different finite objects: the
Proposition 4.7 distance grid has 960 points, whereas the near-favourite
`Lambda₀` grid used by Lemma 4.10 has 324. -/
theorem fullGrid_and_lambdaZero_card :
    alphaGrid.card = 960 ∧ screeningAlphaGrid.card = 324 := by
  simp

/-- Every member of the 324-point `Lambda₀` grid lies in the low branch. -/
theorem lambdaZero_is_low_branch (j : ScreeningAlphaIndex) :
    screeningAlphaValue j ≤ kappaTwo :=
  screeningAlphaValue_le_kappaTwo j

/-- Every source exponent covered by Proposition 4.8 is strictly on the
high side of the `kappaTwo` split. -/
lemma kappaTwo_lt_of_kappaOne_le {alpha : ℝ} (h : kappaOne ≤ alpha) :
    kappaTwo < alpha := kappaTwo_between_one_third_and_kappaOne.2.trans_le h

/-- The full 960-point distance grid is split at `kappaTwo`.  The low side
is the separate 324-point `Lambda₀`/Lemma 4.10 regime; the source-window
bound above is used only in the high branch. -/
theorem fullAlphaGrid_kappaTwo_split (j : AlphaIndex) :
    alphaValue j ≤ kappaTwo ∨ kappaTwo < alphaValue j :=
  le_or_gt (alphaValue j) kappaTwo

end Erdos1166.HLOZProp48SourceBands
