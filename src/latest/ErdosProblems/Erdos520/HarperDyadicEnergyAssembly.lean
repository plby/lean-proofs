import ErdosProblems.Erdos520.HarperDyadicBands

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Euler-energy assembly over the dyadic central bands

The interval conventions in `HarperDyadicBands` make the pieces genuinely
disjoint.  This file turns the set decomposition into an exact finite
decomposition of the Euler-product energy, ready for separate small-height
and tilted-barrier estimates.
-/

theorem integrableOn_harperEulerDensity_harperSignedDyadicBand
    (y : Nat) (omega : Omega) (positive : Bool) (d : Nat) :
    IntegrableOn (fun t : Real => harperEulerDensity y omega t)
      (harperSignedDyadicBand positive d) := by
  have hcont := continuous_harperEulerDensity_vertical y omega
  cases positive with
  | false =>
      exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ico_subset_Icc_self
  | true =>
      exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self

theorem integrableOn_harperEulerDensity_harperDyadicCore
    (y : Nat) (omega : Omega) (m : Nat) :
    IntegrableOn (fun t : Real => harperEulerDensity y omega t)
      (harperDyadicCore m) := by
  exact (continuous_harperEulerDensity_vertical y omega).continuousOn
    |>.integrableOn_compact isCompact_Icc

theorem disjoint_harperNegativeDyadicBand_harperDyadicCore_succ
    (d : Nat) :
    Disjoint (harperSignedDyadicBand false d)
      (harperDyadicCore (d + 1)) := by
  rw [Set.disjoint_left]
  intro t htBand htCore
  simp only [harperSignedDyadicBand, Bool.false_eq_true, if_false,
    Set.mem_Ico] at htBand
  simp only [harperDyadicCore, Set.mem_Icc] at htCore
  rw [harperDyadicRadius_succ] at htBand htCore
  linarith

theorem disjoint_harperNegativeBand_union_core_harperPositiveBand
    (d : Nat) :
    Disjoint
      (harperSignedDyadicBand false d ∪ harperDyadicCore (d + 1))
      (harperSignedDyadicBand true d) := by
  rw [Set.disjoint_left]
  intro t htLeft htPos
  rcases htLeft with htNeg | htCore
  · simp only [harperSignedDyadicBand, Bool.false_eq_true, if_false,
      Set.mem_Ico] at htNeg
    simp only [harperSignedDyadicBand, if_true, Set.mem_Ioc] at htPos
    rw [harperDyadicRadius_succ] at htNeg htPos
    linarith
  · simp only [harperDyadicCore, Set.mem_Icc] at htCore
    simp only [harperSignedDyadicBand, if_true, Set.mem_Ioc] at htPos
    rw [harperDyadicRadius_succ] at htCore htPos
    linarith

/-- One exact refinement step for the actual normalized Euler energy. -/
theorem harperEulerSetEnergy_dyadicCore_split
    (y d : Nat) (omega : Omega) :
    harperEulerSetEnergy y (harperDyadicCore d) omega =
      harperEulerSetEnergy y (harperSignedDyadicBand false d) omega +
        harperEulerSetEnergy y (harperDyadicCore (d + 1)) omega +
          harperEulerSetEnergy y
            (harperSignedDyadicBand true d) omega := by
  have hneg :=
    integrableOn_harperEulerDensity_harperSignedDyadicBand
      y omega false d
  have hcore := integrableOn_harperEulerDensity_harperDyadicCore
    y omega (d + 1)
  have hpos :=
    integrableOn_harperEulerDensity_harperSignedDyadicBand
      y omega true d
  unfold harperEulerSetEnergy
  rw [harperDyadicCore_split d,
    setIntegral_union
      (disjoint_harperNegativeBand_union_core_harperPositiveBand d)
      (measurableSet_harperSignedDyadicBand true d)
      (hneg.union hcore) hpos,
    setIntegral_union
      (disjoint_harperNegativeDyadicBand_harperDyadicCore_succ d)
      (measurableSet_harperDyadicCore (d + 1)) hneg hcore]
  ring

/-- Exact finite decomposition at any stopping depth. -/
theorem harperEulerSetEnergy_dyadic_decomposition
    (y m : Nat) (omega : Omega) :
    harperEulerSetEnergy y (harperDyadicCore 0) omega =
      harperEulerSetEnergy y (harperDyadicCore m) omega +
        ∑ d ∈ Finset.range m,
          (harperEulerSetEnergy y
              (harperSignedDyadicBand false d) omega +
            harperEulerSetEnergy y
              (harperSignedDyadicBand true d) omega) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        harperEulerSetEnergy y (harperDyadicCore 0) omega =
            harperEulerSetEnergy y (harperDyadicCore m) omega +
              ∑ d ∈ Finset.range m,
                (harperEulerSetEnergy y
                    (harperSignedDyadicBand false d) omega +
                  harperEulerSetEnergy y
                    (harperSignedDyadicBand true d) omega) := ih
        _ = (harperEulerSetEnergy y
                (harperSignedDyadicBand false m) omega +
              harperEulerSetEnergy y (harperDyadicCore (m + 1)) omega +
              harperEulerSetEnergy y
                (harperSignedDyadicBand true m) omega) +
              ∑ d ∈ Finset.range m,
                (harperEulerSetEnergy y
                    (harperSignedDyadicBand false d) omega +
                  harperEulerSetEnergy y
                    (harperSignedDyadicBand true d) omega) := by
          rw [harperEulerSetEnergy_dyadicCore_split]
        _ = harperEulerSetEnergy y (harperDyadicCore (m + 1)) omega +
              ∑ d ∈ Finset.range (m + 1),
                (harperEulerSetEnergy y
                    (harperSignedDyadicBand false d) omega +
                  harperEulerSetEnergy y
                    (harperSignedDyadicBand true d) omega) := by
          rw [Finset.sum_range_succ]
          ring

/-! ## Fractional-moment assembly -/

/-- Jensen disposes of the final binary-logarithmic core with a bound
stronger than the target square-root saving. -/
theorem integral_harperEulerSetEnergy_clogCore_twoThird_le
    {y n : Nat} (hy : 2 ≤ y) (hn : 1 ≤ n) :
    (∫ omega,
      harperEulerSetEnergy y (harperDyadicCore (Nat.clog 2 n)) omega ^
        harperTwoThird ∂μ) ≤
      (harperExplicitMertensConstant / (n : Real)) ^
        harperTwoThird := by
  have hJ := integral_harperEulerSetEnergy_twoThird_le hy
    (measurableSet_harperDyadicCore (Nat.clog 2 n))
    (harperDyadicCore_finite (Nat.clog 2 n))
  have hvolume := volume_real_harperDyadicCore_clog_le_inv hn
  have hbase :
      harperExplicitMertensConstant *
          volume.real (harperDyadicCore (Nat.clog 2 n)) ≤
        harperExplicitMertensConstant / (n : Real) := by
    calc
      harperExplicitMertensConstant *
          volume.real (harperDyadicCore (Nat.clog 2 n)) ≤
          harperExplicitMertensConstant * (1 / (n : Real)) :=
        mul_le_mul_of_nonneg_left hvolume
          harperExplicitMertensConstant_pos.le
      _ = harperExplicitMertensConstant / (n : Real) := by ring
  exact hJ.trans (Real.rpow_le_rpow
    (mul_nonneg harperExplicitMertensConstant_pos.le measureReal_nonneg)
    hbase (by norm_num [harperTwoThird]))

/-- The exact dyadic decomposition passes to the `2/3` moment with no
cardinality loss: subadditivity is applied before integration. -/
theorem integral_harperEulerSetEnergy_core_zero_twoThird_le
    {y m : Nat} (hy : 2 ≤ y)
    {coreBudget : Real} {bandBudget : Bool → Nat → Real}
    (hcore :
      (∫ omega,
        harperEulerSetEnergy y (harperDyadicCore m) omega ^
          harperTwoThird ∂μ) ≤ coreBudget)
    (hband : ∀ positive d, d < m →
      (∫ omega,
        harperEulerSetEnergy y (harperSignedDyadicBand positive d) omega ^
          harperTwoThird ∂μ) ≤ bandBudget positive d) :
    (∫ omega,
      harperEulerSetEnergy y (harperDyadicCore 0) omega ^
        harperTwoThird ∂μ) ≤
      coreBudget + ∑ d ∈ Finset.range m,
        (bandBudget false d + bandBudget true d) := by
  have hy1 : 1 < y := by omega
  let core : Omega → Real := fun omega =>
    harperEulerSetEnergy y (harperDyadicCore m) omega
  let pair : Nat → Omega → Real := fun d omega =>
    harperEulerSetEnergy y (harperSignedDyadicBand false d) omega +
      harperEulerSetEnergy y (harperSignedDyadicBand true d) omega
  have hcoreNonneg : ∀ omega, 0 ≤ core omega := fun omega =>
    harperEulerSetEnergy_nonneg hy1
      (measurableSet_harperDyadicCore m) omega
  have hbandNonneg : ∀ positive d omega,
      0 ≤ harperEulerSetEnergy y
        (harperSignedDyadicBand positive d) omega :=
    fun positive d omega => harperEulerSetEnergy_nonneg hy1
      (measurableSet_harperSignedDyadicBand positive d) omega
  have hpairNonneg : ∀ d omega, 0 ≤ pair d omega := fun d omega =>
    add_nonneg (hbandNonneg false d omega) (hbandNonneg true d omega)
  have hpointwise (omega : Omega) :
      harperEulerSetEnergy y (harperDyadicCore 0) omega ^
          harperTwoThird ≤
        core omega ^ harperTwoThird +
          ∑ d ∈ Finset.range m, pair d omega ^ harperTwoThird := by
    rw [harperEulerSetEnergy_dyadic_decomposition y m omega]
    refine (Real.rpow_add_le_add_rpow
      (hcoreNonneg omega)
      (Finset.sum_nonneg fun d hd => hpairNonneg d omega)
      (by norm_num [harperTwoThird])
      (by norm_num [harperTwoThird])).trans ?_
    exact add_le_add (le_refl _)
      (finset_sum_rpow_twoThird_le (Finset.range m)
        (fun d => pair d omega)
        (fun d hd => hpairNonneg d omega))
  have hcoreInt : Integrable (fun omega => core omega ^ harperTwoThird) μ := by
    apply integrable_rpow_of_integrable_nonneg
      (integrable_harperEulerSetEnergy y
        (measurableSet_harperDyadicCore m)
        (harperDyadicCore_finite m)) hcoreNonneg
    · norm_num [harperTwoThird]
    · norm_num [harperTwoThird]
  have hpairInt : ∀ d, d ∈ Finset.range m →
      Integrable (fun omega => pair d omega ^ harperTwoThird) μ := by
    intro d hd
    have hneg := integrable_harperEulerSetEnergy y
      (measurableSet_harperSignedDyadicBand false d)
      (harperSignedDyadicBand_finite false d)
    have hpos := integrable_harperEulerSetEnergy y
      (measurableSet_harperSignedDyadicBand true d)
      (harperSignedDyadicBand_finite true d)
    apply integrable_rpow_of_integrable_nonneg (hneg.add hpos)
      (hpairNonneg d)
    · norm_num [harperTwoThird]
    · norm_num [harperTwoThird]
  have hrightInt : Integrable (fun omega =>
      core omega ^ harperTwoThird +
        ∑ d ∈ Finset.range m, pair d omega ^ harperTwoThird) μ :=
    hcoreInt.add (integrable_finset_sum (Finset.range m) hpairInt)
  calc
    (∫ omega,
        harperEulerSetEnergy y (harperDyadicCore 0) omega ^
          harperTwoThird ∂μ) ≤
        ∫ omega, (core omega ^ harperTwoThird +
          ∑ d ∈ Finset.range m, pair d omega ^ harperTwoThird) ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all μ fun omega => Real.rpow_nonneg
          (harperEulerSetEnergy_nonneg hy1
            (measurableSet_harperDyadicCore 0) omega) _
      · exact hrightInt
      · exact ae_of_all μ hpointwise
    _ = (∫ omega, core omega ^ harperTwoThird ∂μ) +
        ∑ d ∈ Finset.range m,
          ∫ omega, pair d omega ^ harperTwoThird ∂μ := by
      rw [integral_add hcoreInt
        (integrable_finset_sum (Finset.range m) hpairInt),
        integral_finset_sum (Finset.range m) hpairInt]
    _ ≤ coreBudget + ∑ d ∈ Finset.range m,
        (bandBudget false d + bandBudget true d) := by
      apply add_le_add hcore
      apply Finset.sum_le_sum
      intro d hd
      have hpairPow (omega : Omega) :
          pair d omega ^ harperTwoThird ≤
            harperEulerSetEnergy y
                (harperSignedDyadicBand false d) omega ^ harperTwoThird +
              harperEulerSetEnergy y
                (harperSignedDyadicBand true d) omega ^ harperTwoThird := by
        exact Real.rpow_add_le_add_rpow
          (hbandNonneg false d omega) (hbandNonneg true d omega)
          (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
      have hnegInt : Integrable (fun omega =>
          harperEulerSetEnergy y
            (harperSignedDyadicBand false d) omega ^ harperTwoThird) μ := by
        apply integrable_rpow_of_integrable_nonneg
          (integrable_harperEulerSetEnergy y
            (measurableSet_harperSignedDyadicBand false d)
            (harperSignedDyadicBand_finite false d))
          (hbandNonneg false d)
        · norm_num [harperTwoThird]
        · norm_num [harperTwoThird]
      have hposInt : Integrable (fun omega =>
          harperEulerSetEnergy y
            (harperSignedDyadicBand true d) omega ^ harperTwoThird) μ := by
        apply integrable_rpow_of_integrable_nonneg
          (integrable_harperEulerSetEnergy y
            (measurableSet_harperSignedDyadicBand true d)
            (harperSignedDyadicBand_finite true d))
          (hbandNonneg true d)
        · norm_num [harperTwoThird]
        · norm_num [harperTwoThird]
      calc
        (∫ omega, pair d omega ^ harperTwoThird ∂μ) ≤
            (∫ omega,
              harperEulerSetEnergy y
                (harperSignedDyadicBand false d) omega ^ harperTwoThird +
              harperEulerSetEnergy y
                (harperSignedDyadicBand true d) omega ^ harperTwoThird ∂μ) :=
          integral_mono (hpairInt d hd) (hnegInt.add hposInt) hpairPow
        _ = (∫ omega,
              harperEulerSetEnergy y
                (harperSignedDyadicBand false d) omega ^ harperTwoThird ∂μ) +
            ∫ omega,
              harperEulerSetEnergy y
                (harperSignedDyadicBand true d) omega ^ harperTwoThird ∂μ := by
          rw [integral_add hnegInt hposInt]
        _ ≤ bandBudget false d + bandBudget true d :=
          add_le_add (hband false d (Finset.mem_range.mp hd))
            (hband true d (Finset.mem_range.mp hd))

end Problem520
end Erdos
