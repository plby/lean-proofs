/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Fiber
import Util.MaynardTao.Concentration
import ErdosProblems.Erdos6.GenericOuterCollision

/-!
# Continuous off-face cutoffs for the variable candidate

The arithmetic fiber endpoint is a little shorter than the limiting face.
A narrow continuous cutoff absorbs that endpoint loss while retaining the
concentration lower bound on a slightly smaller good region.
-/

namespace MaynardTao

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

def variableOuterCutoff (q0 q1 s : ℝ) : ℝ :=
  min 1 (max 0 ((q1 - s) / (q1 - q0)))

theorem continuous_variableOuterCutoff (q0 q1 : ℝ) :
    Continuous (variableOuterCutoff q0 q1) := by
  unfold variableOuterCutoff
  fun_prop

theorem variableOuterCutoff_nonneg (q0 q1 s : ℝ) :
    0 ≤ variableOuterCutoff q0 q1 s := by
  unfold variableOuterCutoff
  exact le_min (by norm_num) (le_max_left _ _)

theorem variableOuterCutoff_le_one (q0 q1 s : ℝ) :
    variableOuterCutoff q0 q1 s ≤ 1 := by
  unfold variableOuterCutoff
  exact min_le_left _ _

theorem variableOuterCutoff_eq_one {q0 q1 s : ℝ}
    (hq : q0 < q1) (hs : s ≤ q0) :
    variableOuterCutoff q0 q1 s = 1 := by
  unfold variableOuterCutoff
  have hden : 0 < q1 - q0 := sub_pos.mpr hq
  have h : 1 ≤ (q1 - s) / (q1 - q0) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [max_eq_right ((by norm_num : (0 : ℝ) ≤ 1).trans h),
    min_eq_left h]

theorem variableOuterCutoff_eq_zero {q0 q1 s : ℝ}
    (hq : q0 < q1) (hs : q1 ≤ s) :
    variableOuterCutoff q0 q1 s = 0 := by
  unfold variableOuterCutoff
  have hd : 0 ≤ q1 - q0 := (sub_pos.mpr hq).le
  have h : (q1 - s) / (q1 - q0) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd
  rw [max_eq_left h]
  norm_num

def tupleVariableOuterDensity (K : ℕ) (A : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∏ i, inverseAffineProfile (A * (K : ℝ)) (t i) ^ 2

def tupleVariableOuterSquaredIntegrand (K : ℕ) (A q0 q1 : ℝ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  variableOuterCutoff q0 q1
      (Erdos4.VariableMaynard.coordinateSum t) ^ 2 *
    tupleVariableOuterDensity K A t

theorem continuous_tupleVariableOuterDensity_of_pos
    {K : ℕ} (hK : 0 < K) {A : ℝ} (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    Continuous (tupleVariableOuterDensity K A : (ι → ℝ) → ℝ) := by
  unfold tupleVariableOuterDensity
  apply continuous_finsetProd
  intro i hi
  exact ((continuous_inverseAffineProfile
    (mul_pos hA (by exact_mod_cast hK))).comp (continuous_apply i)).pow 2

theorem continuous_tupleVariableOuterSquaredIntegrand
    {K : ℕ} (hK : 0 < K) {A : ℝ} (hA : 0 < A)
    (q0 q1 : ℝ) (ι : Type*) [Fintype ι] :
    Continuous
      (tupleVariableOuterSquaredIntegrand K A q0 q1 :
        (ι → ℝ) → ℝ) := by
  unfold tupleVariableOuterSquaredIntegrand
  have hsum : Continuous (fun t : ι → ℝ =>
      Erdos4.VariableMaynard.coordinateSum t) := by
    unfold Erdos4.VariableMaynard.coordinateSum
    fun_prop
  exact ((continuous_variableOuterCutoff q0 q1).comp hsum).pow 2 |>.mul
      (continuous_tupleVariableOuterDensity_of_pos hK hA ι)

theorem tupleVariableOuterDensity_bounds
    {K : ℕ} (hK : 0 < K) {A : ℝ} (hA : 0 < A)
    {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 ≤ tupleVariableOuterDensity K A t ∧
      tupleVariableOuterDensity K A t ≤ 1 := by
  have hlam : 0 < A * (K : ℝ) := mul_pos hA (by exact_mod_cast hK)
  unfold tupleVariableOuterDensity
  constructor
  · exact Finset.prod_nonneg fun i hi =>
      sq_nonneg (inverseAffineProfile (A * (K : ℝ)) (t i))
  · calc
      ∏ i : ι, inverseAffineProfile (A * (K : ℝ)) (t i) ^ 2 ≤
          ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sq_nonneg _
        · intro i hi
          exact pow_le_one₀
            (inverseAffineProfile_nonneg hlam (ht i (Set.mem_univ i)).1)
            (inverseAffineProfile_le_one hlam (ht i (Set.mem_univ i)).1)
      _ = 1 := Finset.prod_const_one

theorem tupleVariableOuterSquaredIntegrand_bounds
    {K : ℕ} (hK : 0 < K) {A : ℝ} (hA : 0 < A)
    (q0 q1 : ℝ) {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 ≤ tupleVariableOuterSquaredIntegrand K A q0 q1 t ∧
      tupleVariableOuterSquaredIntegrand K A q0 q1 t ≤ 1 := by
  have hd := tupleVariableOuterDensity_bounds hK hA t ht
  have hc0 := variableOuterCutoff_nonneg q0 q1
    (Erdos4.VariableMaynard.coordinateSum t)
  have hc1 := variableOuterCutoff_le_one q0 q1
    (Erdos4.VariableMaynard.coordinateSum t)
  unfold tupleVariableOuterSquaredIntegrand
  constructor
  · exact mul_nonneg (sq_nonneg _) hd.1
  · exact (mul_le_mul (pow_le_one₀ hc0 hc1) hd.2 hd.1
      (by norm_num)).trans_eq (by ring)

theorem tupleVariableOuterDensity_eq_productDensity_of_mem_cube
    {K : ℕ} {A : ℝ} {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    tupleVariableOuterDensity K A t =
      Erdos4.VariableMaynard.productDensity K A t := by
  unfold tupleVariableOuterDensity Erdos4.VariableMaynard.productDensity
    Erdos4.VariableMaynard.squareDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [inverseAffineProfile_eq_factor (hx := (ht i (Set.mem_univ i)).1)]

theorem tupleVariableOuterSquaredIntegrand_eq_productDensity_of_mem_good
    {K : ℕ} {A q0 q1 : ℝ} {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (hq : q0 < q1) (ht : t ∈ variableGoodRegion q0 ι) :
    tupleVariableOuterSquaredIntegrand K A q0 q1 t =
      Erdos4.VariableMaynard.productDensity K A t := by
  unfold tupleVariableOuterSquaredIntegrand
  rw [variableOuterCutoff_eq_one hq ht.2,
    tupleVariableOuterDensity_eq_productDensity_of_mem_cube ht.1]
  ring

theorem integral_tupleVariableOuterSquaredIntegrand_gt_goodMass
    {K : ℕ} (hK : 0 < K) {A q0 q1 γ : ℝ} (hA : 0 < A)
    (hq : q0 < q1) (hq1 : q1 ≤ 1) {J : Finset ℕ}
    (hgood : γ * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card J <
      ∫ t : J → ℝ in variableGoodRegion q0 J,
        Erdos4.VariableMaynard.productDensity K A t) :
    γ * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card J <
      ∫ t : J → ℝ in BoundedGaps.Maynard.finiteSimplexOf J,
        tupleVariableOuterSquaredIntegrand K A q0 q1 t := by
  have hgoodSubset :
      variableGoodRegion q0 J ⊆
        BoundedGaps.Maynard.finiteSimplexOf J := by
    intro t ht
    constructor
    · exact ht.1
    · change Erdos4.VariableMaynard.coordinateSum t ≤ 1
      exact ht.2.trans (hq.le.trans hq1)
  have hfullInt : IntegrableOn
      (tupleVariableOuterSquaredIntegrand K A q0 q1 : (J → ℝ) → ℝ)
      (BoundedGaps.Maynard.finiteSimplexOf J) :=
    (continuous_tupleVariableOuterSquaredIntegrand hK hA q0 q1 J).continuousOn.integrableOn_compact
      (BoundedGaps.Maynard.isCompact_finiteSimplexOf J)
  have hmono :
      (∫ t : J → ℝ in variableGoodRegion q0 J,
        tupleVariableOuterSquaredIntegrand K A q0 q1 t) ≤
      ∫ t : J → ℝ in BoundedGaps.Maynard.finiteSimplexOf J,
        tupleVariableOuterSquaredIntegrand K A q0 q1 t := by
    apply setIntegral_mono_set hfullInt
    · exact (ae_restrict_mem
        (BoundedGaps.Maynard.isCompact_finiteSimplexOf J).measurableSet).mono
          (fun t ht =>
            (tupleVariableOuterSquaredIntegrand_bounds hK hA q0 q1 t ht.1).1)
    · exact Filter.Eventually.of_forall hgoodSubset
  calc
    γ * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card J <
        ∫ t : J → ℝ in variableGoodRegion q0 J,
          Erdos4.VariableMaynard.productDensity K A t := hgood
    _ = ∫ t : J → ℝ in variableGoodRegion q0 J,
          tupleVariableOuterSquaredIntegrand K A q0 q1 t := by
      apply setIntegral_congr_fun (variableGoodRegion_measurable q0 J)
      intro t ht
      exact (tupleVariableOuterSquaredIntegrand_eq_productDensity_of_mem_good
        hq ht).symm
    _ ≤ _ := hmono

end

end MaynardTao
