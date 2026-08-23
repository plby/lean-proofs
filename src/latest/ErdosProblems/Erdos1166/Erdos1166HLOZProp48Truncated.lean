import ErdosProblems.Erdos1166.Erdos1166HLOZProp48SourceBands

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval Topology

namespace Erdos1166.HLOZProp48Truncated

open HLOZProp48SourceBands
open HLOZLemma411Recursion HLOZLemma412Windows HLOZBandRatios HLOZLemma411
open HLOZProp47Parameters

/-- Proposition 4.3's coordinatewise cap (4.8), after the external profile
has been fixed and the even member of the domino is the winning member. -/
def sourceBelowSet (m i : ℕ) : Set ℕ := {lazy | i + lazy < m}

lemma measurableSet_sourceBelowSet (m i : ℕ) :
    MeasurableSet (sourceBelowSet m i) := MeasurableSet.of_discrete

lemma negBinMeasure_sourceBelowSet_ne_zero (m i : ℕ) (hi : i < m) :
    Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i) ≠ 0 := by
  have hzeroMem : (0 : ℕ) ∈ sourceBelowSet m i := by
    simpa [sourceBelowSet] using hi
  have hmono : Erdos1166.HLOZUrn.negBinMeasure i ({0} : Set ℕ) ≤
      Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i) := by
    apply measure_mono
    simpa only [Set.singleton_subset_iff]
  intro h
  rw [h] at hmono
  have hsingleton : Erdos1166.HLOZUrn.negBinMeasure i ({0} : Set ℕ) = 0 :=
    nonpos_iff_eq_zero.mp hmono
  have hreal : (Erdos1166.HLOZUrn.negBinMeasure i).real ({0} : Set ℕ) = 0 := by
    rw [measureReal_def, hsingleton]
    simp
  rw [Erdos1166.HLOZUrn.negBinMeasure_real_singleton] at hreal
  unfold Erdos1166.HLOZUrn.negBinMass at hreal
  simp at hreal

/-- The exact one-coordinate law from Proposition 4.3: negative binomial
lazy total, conditioned by the below-`m` constraint. -/
noncomputable def sourceTruncatedNegBinMeasure (m i : ℕ) : Measure ℕ :=
  (Erdos1166.HLOZUrn.negBinMeasure i)[|sourceBelowSet m i]

/-- Singleton mass of the below-`m` truncated negative-binomial law. -/
lemma sourceTruncatedNegBinMeasure_real_singleton
    (m i k : ℕ) (hi : i < m) (hk : k ∈ sourceBelowSet m i) :
    (sourceTruncatedNegBinMeasure m i).real {k} =
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal⁻¹ *
        Erdos1166.HLOZUrn.negBinMass i k := by
  rw [measureReal_def, sourceTruncatedNegBinMeasure,
    cond_apply (measurableSet_sourceBelowSet m i)]
  have hinter : sourceBelowSet m i ∩ ({k} : Set ℕ) = {k} := by
    exact Set.inter_eq_right.mpr (by simpa only [Set.singleton_subset_iff])
  rw [hinter, ENNReal.toReal_mul, ENNReal.toReal_inv]
  congr 1
  exact Erdos1166.HLOZUrn.negBinMeasure_real_singleton i k

/-- A singleton outside the below-`m` support has zero mass under the
truncated negative-binomial law.  This is the complementary case to
`sourceTruncatedNegBinMeasure_real_singleton` and lets source-facing
likelihood comparisons be stated for the explicit, unnormalized
negative-binomial mass. -/
lemma sourceTruncatedNegBinMeasure_real_singleton_eq_zero_of_not_mem
    (m i k : ℕ) (hk : k ∉ sourceBelowSet m i) :
    (sourceTruncatedNegBinMeasure m i).real {k} = 0 := by
  rw [measureReal_def, sourceTruncatedNegBinMeasure,
    cond_apply (measurableSet_sourceBelowSet m i)]
  have hinter : sourceBelowSet m i ∩ ({k} : Set ℕ) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, rfl⟩
    exact hk hx
  rw [hinter, measure_empty]
  simp

/-- A negative-binomial atom is positive on its exact support.  For a
positive shape every natural lazy total is supported; at shape zero the
only supported total is zero. -/
lemma negBinMass_pos_of_support (i k : ℕ) (hk : i = 0 → k = 0) :
    0 < Erdos1166.HLOZUrn.negBinMass i k := by
  by_cases hi : i = 0
  · subst i
    have : k = 0 := hk rfl
    subst k
    norm_num [Erdos1166.HLOZUrn.negBinMass]
  · exact HLOZProp48SourceBands.negBinMass_pos i k (by omega)

/-- Every supported atom of the below-`m` truncated law has nonzero mass. -/
lemma sourceTruncatedNegBinMeasure_singleton_ne_zero
    (m i k : ℕ) (hi : i < m) (hkBelow : k ∈ sourceBelowSet m i)
    (hkSupport : i = 0 → k = 0) :
    sourceTruncatedNegBinMeasure m i ({k} : Set ℕ) ≠ 0 := by
  have hcap : 0 <
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal := by
    exact ENNReal.toReal_pos
      (negBinMeasure_sourceBelowSet_ne_zero m i hi) (measure_ne_top _ _)
  have hreal : 0 < (sourceTruncatedNegBinMeasure m i).real {k} := by
    rw [sourceTruncatedNegBinMeasure_real_singleton m i k hi hkBelow]
    have hmass := negBinMass_pos_of_support i k hkSupport
    positivity
  intro hzero
  have : (sourceTruncatedNegBinMeasure m i).real ({k} : Set ℕ) = 0 := by
    rw [measureReal_def, hzero]
    simp
  linarith

/-- A deterministic supported witness inside a set proves that its
below-`m` truncated negative-binomial mass is nonzero. -/
lemma sourceTruncatedNegBinMeasure_ne_zero_of_support_mem
    (m i k : ℕ) (A : Set ℕ) (hi : i < m) (hkA : k ∈ A)
    (hkBelow : k ∈ sourceBelowSet m i) (hkSupport : i = 0 → k = 0) :
    sourceTruncatedNegBinMeasure m i A ≠ 0 := by
  have hmono : sourceTruncatedNegBinMeasure m i ({k} : Set ℕ) ≤
      sourceTruncatedNegBinMeasure m i A := by
    apply measure_mono
    simpa only [Set.singleton_subset_iff]
  intro hzero
  rw [hzero] at hmono
  have hsingleton : sourceTruncatedNegBinMeasure m i ({k} : Set ℕ) = 0 :=
    nonpos_iff_eq_zero.mp hmono
  exact sourceTruncatedNegBinMeasure_singleton_ne_zero
    m i k hi hkBelow hkSupport hsingleton

noncomputable def sourceTruncatedCategoryMeasure (m ℓ i : ℕ) : Measure (Fin 3) :=
  (sourceTruncatedNegBinMeasure m i).map (sourceBandCategory m ℓ i)

lemma sourceCurrentLazyBand_subset_below (m ℓ i : ℕ) {k : ℕ}
    (hk : k ∈ sourceCurrentLazyBand m ℓ i) : k ∈ sourceBelowSet m i := by
  rw [sourceCurrentLazyBand, Finset.mem_Ico] at hk
  unfold sourceIntervalUpper at hk
  simp only [sourceBelowSet, Set.mem_ofPred_eq]
  omega

lemma sourcePreviousLazyBand_subset_below (m ℓ i : ℕ) (hℓ : 2 ≤ ℓ) {k : ℕ}
    (hk : k ∈ sourcePreviousLazyBand m ℓ i) : k ∈ sourceBelowSet m i := by
  rw [sourcePreviousLazyBand, Finset.mem_Ico] at hk
  have hik' : k + i < sourcePreviousUpper m ℓ :=
    Nat.lt_sub_iff_add_lt.mp hk.2
  have hik : i + k < sourcePreviousUpper m ℓ := by omega
  have hmul : sourceCellWidth m ≤ (ℓ - 1) * sourceCellWidth m := by
    have : 1 ≤ ℓ - 1 := by omega
    simpa using Nat.mul_le_mul_right (sourceCellWidth m) this
  have hupper : sourcePreviousUpper m ℓ ≤ m := by
    unfold sourcePreviousUpper
    omega
  simp only [sourceBelowSet, Set.mem_ofPred_eq]
  exact hik.trans_le hupper

/-- HLOZ Lemma 4.12's adjacent-window comparison survives the common
below-`m` conditioning normalizer pointwise. -/
theorem sourceTruncatedNegBinMeasure_adjacent_singleton_le
    (c m ℓ i a b : ℕ) (hi : i < m) (hℓ : 2 ≤ ℓ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i)
    (ha : a ∈ sourceCurrentLazyBand m ℓ i)
    (hb : b ∈ sourcePreviousLazyBand m ℓ i) :
    (sourceTruncatedNegBinMeasure m i).real {a} ≤
      Real.exp (sourceAdjacentComparisonExponent c) *
        (sourceTruncatedNegBinMeasure m i).real {b} := by
  have haBelow : a ∈ sourceBelowSet m i :=
    sourceCurrentLazyBand_subset_below m ℓ i ha
  have hbBelow : b ∈ sourceBelowSet m i :=
    sourcePreviousLazyBand_subset_below m ℓ i hℓ hb
  have haIco := Finset.mem_Ico.mp ha
  have hbIco := Finset.mem_Ico.mp hb
  have hja : sourceIntervalLower m ℓ ≤ i + a ∧
      i + a < sourcePreviousUpper m ℓ := by
    unfold sourceCurrentLazyBand at haIco
    omega
  have hjb : sourceIntervalLower m ℓ ≤ i + b ∧
      i + b < sourcePreviousUpper m ℓ := by
    unfold sourcePreviousLazyBand at hbIco
    omega
  have hraw := barNegBinMass_compare_adjacentUnion
    c m ℓ i (i + a) (i + b) hindex hgrowth hiwin hja hjb
  have hraw' : Erdos1166.HLOZUrn.negBinMass i a ≤
      Real.exp (sourceAdjacentComparisonExponent c) *
        Erdos1166.HLOZUrn.negBinMass i b := by
    simpa [barNegBinMass] using hraw
  rw [sourceTruncatedNegBinMeasure_real_singleton m i a hi haBelow,
    sourceTruncatedNegBinMeasure_real_singleton m i b hi hbBelow]
  have hnorm : 0 ≤
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal⁻¹ := by
    positivity
  calc
    _ ≤
        (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal⁻¹ *
          (Real.exp (sourceAdjacentComparisonExponent c) *
            Erdos1166.HLOZUrn.negBinMass i b) :=
      mul_le_mul_of_nonneg_left hraw' hnorm
    _ = _ := by ring

lemma sourceBandCategory_zero_subset_below (m ℓ i : ℕ) {k : ℕ}
    (hk : sourceBandCategory m ℓ i k = 0) : k ∈ sourceBelowSet m i := by
  apply sourceCurrentLazyBand_subset_below m ℓ i
  have hk' : k ∈ sourceBandCategory m ℓ i ⁻¹' ({0} : Set (Fin 3)) := by
    simpa using hk
  rw [sourceBandCategory_zero_preimage] at hk'
  exact hk'

lemma sourceBandCategory_one_subset_below (m ℓ i : ℕ) (hℓ : 2 ≤ ℓ) {k : ℕ}
    (hk : sourceBandCategory m ℓ i k = 1) : k ∈ sourceBelowSet m i := by
  apply sourcePreviousLazyBand_subset_below m ℓ i hℓ
  have hk' : k ∈ sourceBandCategory m ℓ i ⁻¹' ({1} : Set (Fin 3)) := by
    simpa using hk
  rw [sourceBandCategory_one_preimage] at hk'
  exact hk'

lemma sourceTruncatedCategoryMeasure_real_singleton
    (m ℓ i : ℕ) (_hi : i < m) (y : Fin 3)
    (hy : ∀ k, sourceBandCategory m ℓ i k = y → k ∈ sourceBelowSet m i) :
    (sourceTruncatedCategoryMeasure m ℓ i).real {y} =
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal⁻¹ *
        (sourceCategoryMeasure m ℓ i).real {y} := by
  rw [measureReal_def, sourceTruncatedCategoryMeasure,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y),
    sourceTruncatedNegBinMeasure,
    cond_apply (measurableSet_sourceBelowSet m i)]
  have hinter : sourceBelowSet m i ∩
      sourceBandCategory m ℓ i ⁻¹' ({y} : Set (Fin 3)) =
        sourceBandCategory m ℓ i ⁻¹' ({y} : Set (Fin 3)) := by
    apply Set.inter_eq_right.mpr
    intro k hk
    exact hy k (by simpa using hk)
  rw [hinter, ENNReal.toReal_mul, ENNReal.toReal_inv]
  congr 1
  rw [sourceCategoryMeasure, measureReal_def,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y)]

lemma sourceTruncatedCategoryMeasure_one_pos
    (c m ℓ i : ℕ) (hi : i < m) (hℓ : 2 ≤ ℓ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    0 < (sourceTruncatedCategoryMeasure m ℓ i).real {1} := by
  rw [sourceTruncatedCategoryMeasure_real_singleton m ℓ i hi 1
    (fun k hk ↦ sourceBandCategory_one_subset_below m ℓ i hℓ hk)]
  have hraw := sourceCategoryMeasure_one_pos c m ℓ i hindex hgrowth hiwin
  have hcap : 0 <
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal := by
    exact ENNReal.toReal_pos
      (negBinMeasure_sourceBelowSet_ne_zero m i hi) (measure_ne_top _ _)
  positivity

lemma sourceTruncatedCategoryMeasure_mass_comparable_adjacent
    (c m ℓ i : ℕ) (hi : i < m) (hℓ : 2 ≤ ℓ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hiwin : InSourceExternalWindow c m ℓ i) :
    (sourceTruncatedCategoryMeasure m ℓ i).real {0} ≤
      Real.exp (sourceAdjacentComparisonExponent c) *
        (sourceTruncatedCategoryMeasure m ℓ i).real {1} := by
  rw [sourceTruncatedCategoryMeasure_real_singleton m ℓ i hi 0
      (fun k hk ↦ sourceBandCategory_zero_subset_below m ℓ i hk),
    sourceTruncatedCategoryMeasure_real_singleton m ℓ i hi 1
      (fun k hk ↦ sourceBandCategory_one_subset_below m ℓ i hℓ hk)]
  have hraw := sourceCategoryMeasure_mass_comparable_adjacent
    c m ℓ i hindex hgrowth hiwin
  have hscale : 0 ≤
      (Erdos1166.HLOZUrn.negBinMeasure i (sourceBelowSet m i)).toReal⁻¹ := by
    positivity
  nlinarith

noncomputable def sourceTruncatedProfileMeasure {ι : Type*} [Fintype ι]
    (m : ℕ) (profile : ι → ℕ) : Measure (ι → ℕ) :=
  Measure.pi fun x ↦ sourceTruncatedNegBinMeasure m (profile x)

noncomputable def sourceTruncatedProfileCategoryMeasure {ι : Type*} [Fintype ι]
    (m ℓ : ℕ) (profile : ι → ℕ) : ι → Measure (Fin 3) :=
  fun x ↦ sourceTruncatedCategoryMeasure m ℓ (profile x)

theorem sourceTruncatedProfileCategory_map_eq_pi
    {ι : Type*} [Fintype ι] (m ℓ : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m) :
    (sourceTruncatedProfileMeasure m profile).map
        (sourceProfileCategory m ℓ profile) =
      Measure.pi (sourceTruncatedProfileCategoryMeasure m ℓ profile) := by
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI (x : ι) : IsProbabilityMeasure
      ((sourceTruncatedNegBinMeasure m (profile x)).map
        (sourceBandCategory m ℓ (profile x))) :=
    Measure.isProbabilityMeasure_map
      (measurable_of_countable (sourceBandCategory m ℓ (profile x))).aemeasurable
  unfold sourceTruncatedProfileMeasure sourceTruncatedProfileCategoryMeasure
    sourceProfileCategory sourceTruncatedCategoryMeasure
  exact Measure.pi_map_pi fun x ↦
    (measurable_of_countable (sourceBandCategory m ℓ (profile x))).aemeasurable

/-- Corrected source form of (4.48): the law is the coordinatewise
Proposition 4.3 truncation, not the raw negative-binomial product. -/
theorem sourceTruncatedProfileImbalance_real_le
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m) (hℓ : 2 ≤ ℓ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (ρ : ℝ) :
    (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileImbalanceEvent c m ℓ profile ρ) ≤
      Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) *
        Nat.ceil ρ) := by
  classical
  let C := Real.exp (sourceAdjacentComparisonExponent c)
  have hC : 1 ≤ C := Real.one_le_exp (by positivity)
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedProfileCategoryMeasure m ℓ profile x) := by
    unfold sourceTruncatedProfileCategoryMeasure sourceTruncatedCategoryMeasure
    exact Measure.isProbabilityMeasure_map
      (measurable_of_countable (sourceBandCategory m ℓ (profile x))).aemeasurable
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  have hmap := sourceTruncatedProfileCategory_map_eq_pi m ℓ profile hprofile
  rw [measureReal_def, sourceProfileImbalanceEvent,
    ← Measure.map_apply (measurable_of_countable _)
      MeasurableSet.of_discrete, hmap, ← measureReal_def]
  apply categorical_product_windowed_imbalance_real_le
    (fun x ↦ InSourceExternalWindow c m ℓ (profile x))
    (sourceTruncatedProfileCategoryMeasure m ℓ profile)
      C (Nat.ceil ρ) hC
  · intro x hx
    exact sourceTruncatedCategoryMeasure_one_pos c m ℓ (profile x)
      (hprofile x) hℓ hindex hgrowth hx
  · intro x hx
    exact sourceTruncatedCategoryMeasure_mass_comparable_adjacent c m ℓ
      (profile x) (hprofile x) hℓ hindex hgrowth hx

lemma sourceTruncatedProfileImbalance_real_le_threshold
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m) (hℓ : 2 ≤ ℓ)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (ρ : ℝ) :
    (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileImbalanceEvent c m ℓ profile ρ) ≤
      Real.exp (-imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c)) * ρ) := by
  have htail := sourceTruncatedProfileImbalance_real_le c m ℓ profile
    hprofile hℓ hindex hgrowth ρ
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hrate : 0 < imbalanceRate
      (Real.exp (sourceAdjacentComparisonExponent c)) :=
    imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hceil : ρ ≤ (Nat.ceil ρ : ℝ) := Nat.le_ceil ρ
  nlinarith

lemma sourceTruncatedProfile_below_ae
    {ι : Type*} [Fintype ι] (m : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m) :
    (sourceTruncatedProfileMeasure m profile)
      (sourceProfileBelowMEvent m profile) = 1 := by
  classical
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  have hevent : sourceProfileBelowMEvent m profile =
      Set.univ.pi (fun x ↦ sourceBelowSet m (profile x)) := by
    ext lazy
    simp [sourceProfileBelowMEvent, sourceBelowSet]
  rw [sourceTruncatedProfileMeasure, hevent, Measure.pi_pi]
  apply Finset.prod_eq_one
  intro x _hx
  unfold sourceTruncatedNegBinMeasure
  exact cond_apply_self
    (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
    (measure_ne_top _ _)

/-- Exact one-step recursion under Proposition 4.3's truncated product.
This is the event-level content of source equation (4.48). -/
theorem sourceTruncatedProfile_one_step_recursion
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hℓ : 2 ≤ ℓ) {ρprev ρcur cTheta a : ℝ}
    (hρcur : 0 ≤ ρcur)
    (hgrow : 2 * Real.exp (sourceAdjacentComparisonExponent c) * ρprev ≤ ρcur)
    (hTheta : (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileThetaBad c m ℓ profile) ≤
      Real.exp (-cTheta * (m : ℝ) ^ a)) :
    (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileQEvent m ℓ profile ρcur) ≤
      (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
  classical
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  have hfit : ℓ * sourceCellWidth m ≤ m := by
    calc
      ℓ * sourceCellWidth m ≤ 2 * ℓ * sourceCellWidth m := by
        exact Nat.mul_le_mul_right (sourceCellWidth m) (by omega)
      _ ≤ m := hindex.2
  have hcover := sourceProfile_one_step_cover c m ℓ profile hℓ
    hfit hρcur hgrow
  have himbalance := sourceTruncatedProfileImbalance_real_le_threshold
    c m ℓ profile hprofile hℓ hindex hgrowth ρcur
  calc
    (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileQEvent m ℓ profile ρcur) ≤
      (sourceTruncatedProfileMeasure m profile).real
        ((sourceProfileQEvent m (ℓ - 1) profile ρprev ∪
          sourceProfileThetaBad c m ℓ profile) ∪
          sourceProfileImbalanceEvent c m ℓ profile ρcur) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ((sourceTruncatedProfileMeasure m profile).real
          (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileThetaBad c m ℓ profile)) +
        (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileImbalanceEvent c m ℓ profile ρcur) := by
      exact (measureReal_union_le _ _).trans
        (add_le_add (measureReal_union_le _ _) (le_refl _))
    _ ≤ (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-cTheta * (m : ℝ) ^ a) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) := by
      gcongr
    _ = (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileQEvent m (ℓ - 1) profile ρprev) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * ρcur) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by ring

/-! ### Source-exact fixed-path signature

Proposition 4.3 truncates by the larger external local time of the two
members of a domino, while the negative-binomial shape and the source band
are attached to the selected member.  These are kept as two profiles here.
On the `V²` side used in (4.48), the selected member is the larger one, so
`capProfile = profile`. -/

noncomputable def sourceCappedProfileMeasure {ι : Type*} [Fintype ι]
    (m : ℕ) (profile capProfile : ι → ℕ) : Measure (ι → ℕ) :=
  Measure.pi fun x ↦
    (Erdos1166.HLOZUrn.negBinMeasure (profile x))[|
      sourceBelowSet m (capProfile x)]

lemma sourceCappedProfileMeasure_eq_truncated
    {ι : Type*} [Fintype ι] (m : ℕ) (profile capProfile : ι → ℕ)
    (hwinning : ∀ x, capProfile x = profile x) :
    sourceCappedProfileMeasure m profile capProfile =
      sourceTruncatedProfileMeasure m profile := by
  unfold sourceCappedProfileMeasure sourceTruncatedProfileMeasure
  congr 1
  funext x
  rw [hwinning x]
  rfl

/-- Equation (4.48) with the literal Proposition 4.3 fixed-path law as its
input.  `hwinning` records that the index type consists of the winning
members `V²`; it is exactly what identifies the shape profile with the cap
profile on the active adjacent-band union. -/
theorem sourceCappedProfile_one_step_recursion
    {ι : Type*} [Fintype ι] (c m ℓ : ℕ)
    (profile capProfile : ι → ℕ) (mu : Measure (ι → ℕ))
    (hprofile : ∀ x, profile x < m)
    (hwinning : ∀ x, capProfile x = profile x)
    (hProposition43 : mu = sourceCappedProfileMeasure m profile capProfile)
    (hindex : SourceIntervalIndex m ℓ) (hgrowth : SourceWindowGrowth c m)
    (hℓ : 2 ≤ ℓ) {rhoPrev rhoCur cTheta a : ℝ}
    (hRhoCur : 0 ≤ rhoCur)
    (hRhoGrowth :
      2 * Real.exp (sourceAdjacentComparisonExponent c) * rhoPrev ≤ rhoCur)
    (hTheta : mu.real (sourceProfileThetaBad c m ℓ profile) ≤
      Real.exp (-cTheta * (m : ℝ) ^ a)) :
    mu.real (sourceProfileQEvent m ℓ profile rhoCur) ≤
      mu.real (sourceProfileQEvent m (ℓ - 1) profile rhoPrev) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * rhoCur) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
  have hmeasure : mu = sourceTruncatedProfileMeasure m profile :=
    hProposition43.trans
      (sourceCappedProfileMeasure_eq_truncated m profile capProfile hwinning)
  rw [hmeasure] at hTheta ⊢
  exact sourceTruncatedProfile_one_step_recursion c m ℓ profile hprofile
    hindex hgrowth hℓ hRhoCur hRhoGrowth hTheta

/-- Proposition 4.8's high-band recursion after conditioning on one fixed
external path and on `D_m^k`.  The first-level estimate is deliberately a
separate hypothesis: source equation (4.47) uses the forced step `Psi` and
cannot be obtained from the below-`m` truncated law by the artificial
above-`m` band argument. -/
theorem eventually_sourceCappedProfile_prop48_band_bound
    {ι : Type*} [Fintype ι] (c : ℕ) {cBase cTheta a : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ (alpha : ℝ) (profile capProfile : ι → ℕ)
      (mu : Measure (ι → ℕ)),
      kappaOne ≤ alpha → alpha ≤ (4 : ℝ) / 5 →
      (∀ x, profile x < m) →
      (∀ x, capProfile x = profile x) →
      mu = sourceCappedProfileMeasure m profile capProfile →
      mu.real (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2) →
      (∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
        mu.real (sourceProfileThetaBad c m l profile) ≤
          Real.exp (-cTheta * (m : ℝ) ^ a)) →
      mu.real (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha))) ≤
        Real.exp (-(min cBase
          (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
            Real.log (m : ℝ) ^ 2) := by
  let r := imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))
  let cAssembly := min cBase r
  let R := sourceLemma411GrowthFactor c
  have hr : 0 < r := imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hcAssembly : 0 < cAssembly := lt_min hcBase hr
  have hR : 1 ≤ R := sourceLemma411GrowthFactor_one_le c
  have hassembly := eventually_hloz_lemma_4_11_assembly
    hcAssembly hcTheta ha (show (0 : ℝ) ≤ 1 by norm_num) hR
  filter_upwards [eventually_sourceWindowGrowth c, eventually_sourceIntervalIndex,
    hassembly, eventually_ge_atTop 1] with
      m hgrowth hindices hassemblyM hm alpha profile capProfile mu
        halpha hAlpha hprofile hwinning hLaw hEquation447 hTheta
  let L := sourceAlphaIntervalCount m alpha
  let rho := Real.log (m : ℝ) ^ 2
  let q : ℕ → ℝ := fun l ↦ mu.real
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
  have hqone : q 1 ≤ Real.exp (-cAssembly * Real.log (m : ℝ) ^ 2) := by
    rw [show q 1 = mu.real
      (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) by
        simp [q, rho, geometricThreshold_one]]
    exact hEquation447.trans (Real.exp_le_exp.mpr (by
      have hcLe : cAssembly ≤ cBase := min_le_left _ _
      nlinarith [sq_nonneg (Real.log (m : ℝ))]))
  have hstep : ∀ k < L - 1,
      q (k + 2) ≤ q (k + 1) +
        Real.exp (-cAssembly * geometricThreshold rho R (k + 2)) +
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
    have hrec := sourceCappedProfile_one_step_recursion c m (k + 2)
      profile capProfile mu hprofile hwinning hLaw hindex hgrowth (by omega)
      (hrho0.trans (geometricThreshold_le rho R hrho0 hR (by omega)))
      (le_of_eq hthreshold.symm)
      (hTheta (k + 2) (by omega) hlevel)
    have hweaken : Real.exp (-r * geometricThreshold rho R (k + 2)) ≤
        Real.exp (-cAssembly * geometricThreshold rho R (k + 2)) := by
      apply Real.exp_le_exp.mpr
      have ht0 := geometricThreshold_le rho R hrho0 hR
        (show 1 ≤ k + 2 by omega)
      have hcLe : cAssembly ≤ r := min_le_right _ _
      nlinarith
    dsimp [q, r] at hrec ⊢
    exact hrec.trans (by gcongr)
  have hfinal := hassemblyM q (L - 1) rho hrho hlevels hqone hstep
  simpa only [q, L, R, cAssembly, rho, r, Nat.sub_add_cancel hL] using hfinal

end Erdos1166.HLOZProp48Truncated
