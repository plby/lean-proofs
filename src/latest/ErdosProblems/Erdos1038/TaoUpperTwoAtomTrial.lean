import ErdosProblems.Erdos1038.UpperReduction
import ErdosProblems.Erdos1038.OneCutElementary
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The two-atom trial in Tao's sharp upper argument

The first parameter range in Tao's proof uses the trial measure
`δ₀ + C δ_M`.  Its logarithmic potential between the two atoms is a convex
function, so strict negativity at the endpoints of an interval implies
strict negativity throughout.  This file proves that reduction and the
exact ratio conditions on `C`.
-/

open Set

namespace Erdos1038

noncomputable section

def taoTwoAtomTrialPotential (M C t : ℝ) : ℝ :=
  -Real.log t - C * Real.log (M - t)

def taoUpperEdge : ℝ := 2 * Real.sqrt 2

def taoCaseOneCeiling : ℝ := 2203 / 1250

lemma seven_fifths_lt_sqrt_two : (7 / 5 : ℝ) < Real.sqrt 2 := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

lemma taoTwoAtomTrialPotential_eq_log_reciprocals
    {M C t : ℝ} :
    taoTwoAtomTrialPotential M C t =
      Real.log (1 / t) + C * Real.log (1 / (M - t)) := by
  simp only [taoTwoAtomTrialPotential, one_div, Real.log_inv]
  ring

theorem taoTwoAtomTrialPotential_convexOn_Icc
    {M C l r : ℝ} (hl : 0 < l)
    (hrM : r < M) (hC : 0 ≤ C) :
    ConvexOn ℝ (Icc l r) (taoTwoAtomTrialPotential M C) := by
  refine ⟨convex_Icc l r, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : x ∈ Ioi (0 : ℝ) := hl.trans_le hx.1
  have hy0 : y ∈ Ioi (0 : ℝ) := hl.trans_le hy.1
  have hMx0 : M - x ∈ Ioi (0 : ℝ) := by
    exact sub_pos.mpr (hx.2.trans_lt hrM)
  have hMy0 : M - y ∈ Ioi (0 : ℝ) := by
    exact sub_pos.mpr (hy.2.trans_lt hrM)
  have hlogFirst := strictConcaveOn_log_Ioi.concaveOn.2
    hx0 hy0 ha hb hab
  have hlogSecond := strictConcaveOn_log_Ioi.concaveOn.2
    hMx0 hMy0 ha hb hab
  simp only [smul_eq_mul] at hlogFirst hlogSecond ⊢
  have hcombo :
      a * (M - x) + b * (M - y) =
        M - (a * x + b * y) := by
    calc
      a * (M - x) + b * (M - y) =
          (a + b) * M - (a * x + b * y) := by ring
      _ = M - (a * x + b * y) := by rw [hab]; ring
  rw [hcombo] at hlogSecond
  have hfirst :
      -Real.log (a * x + b * y) ≤
        a * (-Real.log x) + b * (-Real.log y) := by
    linarith
  have hsecond :
      -Real.log (M - (a * x + b * y)) ≤
        a * (-Real.log (M - x)) + b * (-Real.log (M - y)) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hsecond hC
  unfold taoTwoAtomTrialPotential
  linarith

theorem taoTwoAtomTrialPotential_le_endpoint_max
    {M C l r t : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hrM : r < M) (hC : 0 ≤ C) (ht : t ∈ Icc l r) :
    taoTwoAtomTrialPotential M C t ≤
      max (taoTwoAtomTrialPotential M C l)
        (taoTwoAtomTrialPotential M C r) := by
  exact (taoTwoAtomTrialPotential_convexOn_Icc hl hrM hC).le_max_of_mem_Icc
    ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ ht

theorem taoTwoAtomTrialPotential_neg_on_Icc_of_endpoints
    {M C l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hrM : r < M) (hC : 0 ≤ C)
    (hleft : taoTwoAtomTrialPotential M C l < 0)
    (hright : taoTwoAtomTrialPotential M C r < 0) :
    ∀ t ∈ Icc l r, taoTwoAtomTrialPotential M C t < 0 := by
  intro t ht
  exact (taoTwoAtomTrialPotential_le_endpoint_max
    hl hlr hrM hC ht).trans_lt (max_lt hleft hright)

lemma taoTwoAtomTrialPotential_left_neg_of_ratio
    {M C l : ℝ} (hMl : 1 < M - l)
    (hC : -Real.log l / Real.log (M - l) < C) :
    taoTwoAtomTrialPotential M C l < 0 := by
  have hlog : 0 < Real.log (M - l) := Real.log_pos hMl
  have hmul := (div_lt_iff₀ hlog).1 hC
  unfold taoTwoAtomTrialPotential
  nlinarith

lemma taoTwoAtomTrialPotential_right_neg_of_ratio
    {M C r : ℝ} (hMr0 : 0 < M - r)
    (hMr1 : M - r < 1)
    (hC : C < Real.log r / (-Real.log (M - r))) :
    taoTwoAtomTrialPotential M C r < 0 := by
  have hlogNeg : Real.log (M - r) < 0 := Real.log_neg hMr0 hMr1
  have hden : 0 < -Real.log (M - r) := neg_pos.mpr hlogNeg
  have hmul := (lt_div_iff₀ hden).1 hC
  unfold taoTwoAtomTrialPotential
  nlinarith

/-- Exact analytic reduction for Tao's first trial-measure range. -/
theorem taoTwoAtomTrialPotential_neg_on_Icc_of_ratio_bounds
    {M C l r : ℝ} (hl : 0 < l)
    (hlr : l ≤ r) (hrM : r < M)
    (hMl : 1 < M - l) (hMr1 : M - r < 1) (hC0 : 0 ≤ C)
    (hClower : -Real.log l / Real.log (M - l) < C)
    (hCupper : C < Real.log r / (-Real.log (M - r))) :
    ∀ t ∈ Icc l r, taoTwoAtomTrialPotential M C t < 0 := by
  have hMr0 : 0 < M - r := sub_pos.mpr hrM
  apply taoTwoAtomTrialPotential_neg_on_Icc_of_endpoints
    hl hlr hrM hC0
  · exact taoTwoAtomTrialPotential_left_neg_of_ratio hMl hClower
  · exact taoTwoAtomTrialPotential_right_neg_of_ratio hMr0 hMr1 hCupper

lemma tao_case_one_interval_geometry {t0 : ℝ}
    (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling) :
    0 < t0 - 1 ∧ t0 - 1 ≤ t0 + 1 ∧
      t0 + 1 < taoUpperEdge ∧
      1 < taoUpperEdge - (t0 - 1) ∧
      taoUpperEdge - (t0 + 1) < 1 ∧
      t0 - 1 < 1 := by
  have hsqrtLtTwo : Real.sqrt 2 < 2 := by
    nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]
  unfold taoUpperEdge taoCaseOneCeiling at *
  constructor
  · linarith [one_lt_sqrt_two]
  constructor
  · linarith
  constructor
  · linarith [seven_fifths_lt_sqrt_two]
  constructor
  · linarith [eleven_eighths_lt_sqrt_two]
  constructor
  · linarith [hsqrtLtTwo]
  · norm_num at ht0Upper ⊢
    linarith

/-- Tao's first parameter range, reduced to the one explicit ratio comparison (2.4). -/
theorem exists_tao_case_one_twoAtomTrial
    {t0 : ℝ} (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling)
    (hratio :
      -Real.log (t0 - 1) /
          Real.log (taoUpperEdge - (t0 - 1)) <
        Real.log (t0 + 1) /
          (-Real.log (taoUpperEdge - (t0 + 1)))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc (t0 - 1) (t0 + 1),
        taoTwoAtomTrialPotential taoUpperEdge C t < 0 := by
  rcases tao_case_one_interval_geometry ht0Lower ht0Upper with
    ⟨hl, hlr, hrM, hMl, hMr1, hl1⟩
  let lower := -Real.log (t0 - 1) /
    Real.log (taoUpperEdge - (t0 - 1))
  let upper := Real.log (t0 + 1) /
    (-Real.log (taoUpperEdge - (t0 + 1)))
  let C := (lower + upper) / 2
  have hlowerUpper : lower < upper := by
    simpa [lower, upper] using! hratio
  have hlogl : Real.log (t0 - 1) < 0 := Real.log_neg hl hl1
  have hden : 0 < Real.log (taoUpperEdge - (t0 - 1)) :=
    Real.log_pos hMl
  have hlower : 0 < lower := by
    unfold lower
    exact div_pos (neg_pos.mpr hlogl) hden
  have hlowerC : lower < C := by
    dsimp [C]
    linarith [hlowerUpper]
  have hCupper : C < upper := by
    dsimp [C]
    linarith [hlowerUpper]
  refine ⟨C, hlower.le.trans hlowerC.le, ?_⟩
  apply taoTwoAtomTrialPotential_neg_on_Icc_of_ratio_bounds
    hl hlr hrM hMl hMr1 (hlower.le.trans hlowerC.le)
  · simpa [lower] using! hlowerC
  · simpa [upper] using! hCupper

end

end Erdos1038
