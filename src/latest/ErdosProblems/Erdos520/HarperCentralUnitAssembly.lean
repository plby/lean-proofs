import ErdosProblems.Erdos520.HarperDyadicEnergyAssembly
import ErdosProblems.Erdos520.HarperParsevalTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# The complete central unit interval

The dyadic-band decomposition starts at `[-1/2,1/2]`.  The two remaining
half-unit pieces are exactly the central comparison band with scale parameter
zero.  This file joins those three pieces and transfers their common moment
bound to each of the two shell-zero intervals used by Parseval.
-/

/-- The outer half-unit piece on either side of the origin.  The endpoint
convention makes every point satisfy `1/2 < |t| ≤ 1`. -/
noncomputable def harperOuterCentralBand
    (positive : Bool) : Set ℝ :=
  if positive then Ioc (1 / 2 : ℝ) 1
  else Ico (-1 : ℝ) (-(1 / 2 : ℝ))

/-- The symmetric unit interval containing both shell-zero Parseval pieces. -/
def harperCentralUnitSet : Set ℝ := Icc (-1) 1

theorem measurableSet_harperOuterCentralBand (positive : Bool) :
    MeasurableSet (harperOuterCentralBand positive) := by
  cases positive <;> simp [harperOuterCentralBand]

theorem harperOuterCentralBand_finite (positive : Bool) :
    volume (harperOuterCentralBand positive) ≠ ∞ := by
  cases positive <;>
    simp [harperOuterCentralBand, Real.volume_Ioc, Real.volume_Ico]

theorem measurableSet_harperCentralUnitSet :
    MeasurableSet harperCentralUnitSet := measurableSet_Icc

theorem harperCentralUnitSet_finite :
    volume harperCentralUnitSet ≠ ∞ := by
  simp [harperCentralUnitSet, Real.volume_Icc]

theorem abs_bounds_of_mem_harperOuterCentralBand
    (positive : Bool) {t : ℝ}
    (ht : t ∈ harperOuterCentralBand positive) :
    (1 / 2 : ℝ) < |t| ∧ |t| ≤ 1 := by
  cases positive with
  | false =>
      simp only [harperOuterCentralBand, Bool.false_eq_true, if_false,
        Set.mem_Ico] at ht
      have htneg : t < 0 := ht.2.trans (by norm_num)
      rw [abs_of_neg htneg]
      constructor <;> linarith
  | true =>
      simp only [harperOuterCentralBand, if_true, Set.mem_Ioc] at ht
      have htpos : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans ht.1
      rwa [abs_of_pos htpos]

theorem disjoint_harperOuterCentralBand_false_core :
    Disjoint (harperOuterCentralBand false) (harperDyadicCore 0) := by
  rw [Set.disjoint_left]
  intro t htOuter htCore
  simp only [harperOuterCentralBand, Bool.false_eq_true, if_false,
    Set.mem_Ico] at htOuter
  simp only [harperDyadicCore, Set.mem_Icc, harperDyadicRadius] at htCore
  norm_num at htCore
  linarith

theorem disjoint_harperOuterCentralBand_false_union_core_true :
    Disjoint
      (harperOuterCentralBand false ∪ harperDyadicCore 0)
      (harperOuterCentralBand true) := by
  rw [Set.disjoint_left]
  intro t htLeft htRight
  rcases htLeft with htOuter | htCore
  · simp only [harperOuterCentralBand, Bool.false_eq_true, if_false,
      if_true, Set.mem_Ico, Set.mem_Ioc] at htOuter htRight
    linarith
  · simp only [harperDyadicCore, Set.mem_Icc, harperDyadicRadius] at htCore
    simp only [harperOuterCentralBand, if_true, Set.mem_Ioc] at htRight
    norm_num at htCore
    linarith

theorem harperCentralUnitSet_split :
    harperCentralUnitSet =
      (harperOuterCentralBand false ∪ harperDyadicCore 0) ∪
        harperOuterCentralBand true := by
  ext t
  simp only [harperCentralUnitSet, harperOuterCentralBand,
    Bool.false_eq_true, if_false, if_true, harperDyadicCore,
    harperDyadicRadius, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc,
    Set.mem_union]
  norm_num
  constructor
  · intro ht
    by_cases hleft : t < -(1 / 2 : ℝ)
    · exact Or.inl (Or.inl ⟨ht.1, hleft⟩)
    by_cases hright : t ≤ (1 / 2 : ℝ)
    · exact Or.inl (Or.inr ⟨by linarith, hright⟩)
    · exact Or.inr ⟨by linarith, ht.2⟩
  · rintro ((ht | ht) | ht)
    · exact ⟨ht.1, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, ht.2⟩

theorem harperEulerSetEnergy_centralUnit_split
    (y : ℕ) (omega : Omega) :
    harperEulerSetEnergy y harperCentralUnitSet omega =
      harperEulerSetEnergy y (harperOuterCentralBand false) omega +
        harperEulerSetEnergy y (harperDyadicCore 0) omega +
          harperEulerSetEnergy y (harperOuterCentralBand true) omega := by
  have hfalse : IntegrableOn
      (fun t : ℝ ↦ harperEulerDensity y omega t)
      (harperOuterCentralBand false) := by
    have hIcc : IntegrableOn
        (fun t : ℝ ↦ harperEulerDensity y omega t) (Icc (-1) 1) :=
      (continuous_harperEulerDensity_vertical y omega).continuousOn
        |>.integrableOn_compact isCompact_Icc
    exact hIcc.mono_set (by
      intro t ht
      simp only [harperOuterCentralBand, Bool.false_eq_true, if_false,
        Set.mem_Ico] at ht
      exact ⟨ht.1, by linarith [ht.2]⟩)
  have hcore :=
    integrableOn_harperEulerDensity_harperDyadicCore y omega 0
  have htrue : IntegrableOn
      (fun t : ℝ ↦ harperEulerDensity y omega t)
      (harperOuterCentralBand true) := by
    have hIcc : IntegrableOn
        (fun t : ℝ ↦ harperEulerDensity y omega t) (Icc (-1) 1) :=
      (continuous_harperEulerDensity_vertical y omega).continuousOn
        |>.integrableOn_compact isCompact_Icc
    exact hIcc.mono_set (by
      intro t ht
      simp only [harperOuterCentralBand, if_true, Set.mem_Ioc] at ht
      exact ⟨by linarith [ht.1], ht.2⟩)
  unfold harperEulerSetEnergy at ⊢
  rw [harperCentralUnitSet_split,
    setIntegral_union
      disjoint_harperOuterCentralBand_false_union_core_true
      (measurableSet_harperOuterCentralBand true)
      (hfalse.union hcore) htrue,
    setIntegral_union disjoint_harperOuterCentralBand_false_core
      (measurableSet_harperDyadicCore 0) hfalse hcore]
  ring

/-- The Parseval local energy is definitionally the arbitrary-set energy on
its unit interval. -/
theorem harperEulerLocalEnergy_eq_setEnergy
    (y : ℕ) (positive : Bool) (shell : ℕ) (omega : Omega) :
    harperEulerLocalEnergy y positive shell omega =
      harperEulerSetEnergy y
        (harperEulerUnitInterval positive shell) omega := by
  rfl

theorem harperEulerUnitInterval_zero_subset_centralUnit
    (positive : Bool) :
    harperEulerUnitInterval positive 0 ⊆ harperCentralUnitSet := by
  intro t ht
  cases positive with
  | false =>
      simp only [harperEulerUnitInterval, Bool.false_eq_true, if_false,
        Set.mem_Ioc] at ht
      simp only [harperCentralUnitSet, Set.mem_Icc]
      norm_num at ht ⊢
      exact ⟨by linarith, by linarith⟩
  | true =>
      simp only [harperEulerUnitInterval, if_true, Set.mem_Ico] at ht
      simp only [harperCentralUnitSet, Set.mem_Icc]
      norm_num at ht ⊢
      exact ⟨by linarith, by linarith⟩

/-- Each signed shell-zero local energy is pointwise dominated by the
complete symmetric central unit energy. -/
theorem harperEulerLocalEnergy_zero_le_centralUnit
    {y : ℕ} (hy : 1 < y) (positive : Bool) (omega : Omega) :
    harperEulerLocalEnergy y positive 0 omega ≤
      harperEulerSetEnergy y harperCentralUnitSet omega := by
  rw [harperEulerLocalEnergy_eq_setEnergy]
  unfold harperEulerSetEnergy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  apply (div_le_div_iff_of_pos_right hlog).2
  apply setIntegral_mono_set
    ((continuous_harperEulerDensity_vertical y omega).continuousOn
      |>.integrableOn_compact isCompact_Icc)
  · exact Filter.Eventually.of_forall fun t ↦
      harperEulerDensity_nonneg y omega t
  · exact Filter.Eventually.of_forall fun t ht ↦
      harperEulerUnitInterval_zero_subset_centralUnit positive ht

private theorem integrable_harperEulerSetEnergy_twoThird
    {y : ℕ} (hy : 1 < y) {I : Set ℝ}
    (hI : MeasurableSet I) (hIfinite : volume I ≠ ∞) :
    Integrable (fun omega ↦
      harperEulerSetEnergy y I omega ^ harperTwoThird) μ := by
  apply integrable_rpow_of_integrable_nonneg
    (integrable_harperEulerSetEnergy y hI hIfinite)
  · exact harperEulerSetEnergy_nonneg hy hI
  · norm_num [harperTwoThird]
  · norm_num [harperTwoThird]

/-- Fractional-moment assembly of the two outer scale-zero bands and the
already-decomposed inner core. -/
theorem integral_harperEulerSetEnergy_centralUnit_twoThird_le
    {y : ℕ} (hy : 2 ≤ y)
    {outerBudget : Bool → ℝ} {coreBudget : ℝ}
    (houter : ∀ positive,
      (∫ omega,
        harperEulerSetEnergy y (harperOuterCentralBand positive) omega ^
          harperTwoThird ∂μ) ≤ outerBudget positive)
    (hcore :
      (∫ omega,
        harperEulerSetEnergy y (harperDyadicCore 0) omega ^
          harperTwoThird ∂μ) ≤ coreBudget) :
    (∫ omega,
      harperEulerSetEnergy y harperCentralUnitSet omega ^
        harperTwoThird ∂μ) ≤
      outerBudget false + coreBudget + outerBudget true := by
  have hy1 : 1 < y := by omega
  have hnonnegOuter : ∀ positive omega,
      0 ≤ harperEulerSetEnergy y
        (harperOuterCentralBand positive) omega :=
    fun positive ↦ harperEulerSetEnergy_nonneg hy1
      (measurableSet_harperOuterCentralBand positive)
  have hnonnegCore : ∀ omega,
      0 ≤ harperEulerSetEnergy y (harperDyadicCore 0) omega :=
    harperEulerSetEnergy_nonneg hy1 (measurableSet_harperDyadicCore 0)
  have hpointwise (omega : Omega) :
      harperEulerSetEnergy y harperCentralUnitSet omega ^ harperTwoThird ≤
        harperEulerSetEnergy y (harperOuterCentralBand false) omega ^
            harperTwoThird +
          harperEulerSetEnergy y (harperDyadicCore 0) omega ^
            harperTwoThird +
          harperEulerSetEnergy y (harperOuterCentralBand true) omega ^
            harperTwoThird := by
    rw [harperEulerSetEnergy_centralUnit_split]
    have hfirst := Real.rpow_add_le_add_rpow (p := harperTwoThird)
      (hnonnegOuter false omega) (hnonnegCore omega)
      (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
    have hsecond := Real.rpow_add_le_add_rpow (p := harperTwoThird)
      (add_nonneg (hnonnegOuter false omega) (hnonnegCore omega))
      (hnonnegOuter true omega)
      (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
    exact hsecond.trans (add_le_add hfirst (le_refl
      (harperEulerSetEnergy y (harperOuterCentralBand true) omega ^
        harperTwoThird)))
  have hcentralInt := integrable_harperEulerSetEnergy_twoThird hy1
    measurableSet_harperCentralUnitSet harperCentralUnitSet_finite
  have hfalseInt := integrable_harperEulerSetEnergy_twoThird hy1
    (measurableSet_harperOuterCentralBand false)
    (harperOuterCentralBand_finite false)
  have hcoreInt := integrable_harperEulerSetEnergy_twoThird hy1
    (measurableSet_harperDyadicCore 0) (harperDyadicCore_finite 0)
  have htrueInt := integrable_harperEulerSetEnergy_twoThird hy1
    (measurableSet_harperOuterCentralBand true)
    (harperOuterCentralBand_finite true)
  calc
    (∫ omega,
        harperEulerSetEnergy y harperCentralUnitSet omega ^
          harperTwoThird ∂μ) ≤
        ∫ omega,
          (harperEulerSetEnergy y (harperOuterCentralBand false) omega ^
              harperTwoThird +
            harperEulerSetEnergy y (harperDyadicCore 0) omega ^
              harperTwoThird) +
            harperEulerSetEnergy y (harperOuterCentralBand true) omega ^
              harperTwoThird ∂μ :=
      integral_mono hcentralInt ((hfalseInt.add hcoreInt).add htrueInt)
        hpointwise
    _ = (∫ omega,
          (harperEulerSetEnergy y (harperOuterCentralBand false) omega ^
              harperTwoThird +
            harperEulerSetEnergy y (harperDyadicCore 0) omega ^
              harperTwoThird) ∂μ) +
        ∫ omega,
          harperEulerSetEnergy y (harperOuterCentralBand true) omega ^
            harperTwoThird ∂μ := by
      exact integral_add (hfalseInt.add hcoreInt) htrueInt
    _ = ((∫ omega,
          harperEulerSetEnergy y (harperOuterCentralBand false) omega ^
            harperTwoThird ∂μ) +
        ∫ omega,
          harperEulerSetEnergy y (harperDyadicCore 0) omega ^
            harperTwoThird ∂μ) +
        ∫ omega,
          harperEulerSetEnergy y (harperOuterCentralBand true) omega ^
            harperTwoThird ∂μ := by
      rw [integral_add hfalseInt hcoreInt]
    _ ≤ outerBudget false + coreBudget + outerBudget true :=
      add_le_add (add_le_add (houter false) hcore) (houter true)

/-- A bound for the complete central unit interval immediately supplies the
same bound for either Parseval shell-zero interval. -/
theorem integral_harperEulerLocalEnergy_zero_twoThird_le_of_centralUnit
    {y : ℕ} (hy : 2 ≤ y) {B : ℝ}
    (hcentral :
      (∫ omega,
        harperEulerSetEnergy y harperCentralUnitSet omega ^
          harperTwoThird ∂μ) ≤ B) (positive : Bool) :
    (∫ omega,
      harperEulerLocalEnergy y positive 0 omega ^ harperTwoThird ∂μ) ≤
      B := by
  have hy1 : 1 < y := by omega
  have hlocalInt := integrable_harperEulerLocalEnergy_twoThird hy1 positive 0
  have hcentralInt := integrable_harperEulerSetEnergy_twoThird hy1
    measurableSet_harperCentralUnitSet harperCentralUnitSet_finite
  calc
    (∫ omega,
        harperEulerLocalEnergy y positive 0 omega ^ harperTwoThird ∂μ) ≤
        ∫ omega,
          harperEulerSetEnergy y harperCentralUnitSet omega ^
            harperTwoThird ∂μ := by
      apply integral_mono hlocalInt hcentralInt
      intro omega
      exact Real.rpow_le_rpow
        (harperEulerLocalEnergy_nonneg hy1 positive 0 omega)
        (harperEulerLocalEnergy_zero_le_centralUnit hy1 positive omega)
        (by norm_num [harperTwoThird])
    _ ≤ B := hcentral

end Problem520
end Erdos

#print axioms Erdos.Problem520.harperEulerSetEnergy_centralUnit_split
#print axioms Erdos.Problem520.integral_harperEulerSetEnergy_centralUnit_twoThird_le
#print axioms Erdos.Problem520.integral_harperEulerLocalEnergy_zero_twoThird_le_of_centralUnit
