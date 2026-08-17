/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.Phase
import ErdosProblems.Erdos175.VanDerCorput
import ErdosProblems.Erdos175.ReciprocalDerivatives
import ErdosProblems.Erdos175.KusminLandau

/-!
# Explicit reciprocal exponential sums

This file supplies the integer-interval formulation of the reciprocal
exponential sums in Granville--Ramaré, Proposition 8.1.
-/

namespace Erdos175

open scoped BigOperators
open Finset

noncomputable section

/-- The unweighted reciprocal exponential sum over `A < n ≤ B`. -/
def reciprocalExpSum (x : ℝ) (A B : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc A B, e (x / n)

/-- Reciprocal exponential sum with the real endpoints used in the
analytic statement: the integer summation condition is exactly
`A < n ∧ n ≤ B`.  The hypotheses of Proposition 8.1 have `0 < A`, so the
natural floors lose no information at the lower endpoint. -/
def reciprocalExpSumReal (x A B : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, e (x / n)

lemma reciprocalExpSumReal_eq (x : ℝ) (A B : ℕ) :
    reciprocalExpSumReal x A B = reciprocalExpSum x A B := by
  simp [reciprocalExpSumReal, reciprocalExpSum]

/-- The same sum, normalized to a range starting at zero. -/
def reciprocalExpRange (x : ℝ) (C N : ℕ) : ℂ :=
  ∑ j ∈ range N, e (x / (C + j))

lemma reciprocalExpSum_eq_range (x : ℝ) (A B : ℕ) (hAB : A ≤ B) :
    reciprocalExpSum x A B = reciprocalExpRange x (A + 1) (B - A) := by
  classical
  rw [reciprocalExpSum, reciprocalExpRange]
  apply Finset.sum_bij (fun n _ ↦ n - (A + 1))
  · intro n hn
    simp only [mem_Ioc] at hn
    simp only [mem_range]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [mem_Ioc] at hn₁ hn₂
    omega
  · intro j hj
    simp only [mem_range] at hj
    refine ⟨A + 1 + j, ?_, ?_⟩
    · simp only [mem_Ioc]
      omega
    · omega
  · intro n hn
    simp only [mem_Ioc] at hn
    have hind : A + 1 + (n - (A + 1)) = n := by omega
    have hind' : (n : ℝ) = (A + 1 : ℕ) + (n - (A + 1) : ℕ) := by
      exact_mod_cast hind.symm
    rw [hind']

lemma norm_reciprocalExpRange_le (x : ℝ) (C N : ℕ) :
    ‖reciprocalExpRange x C N‖ ≤ N := by
  rw [reciprocalExpRange]
  calc
    ‖∑ j ∈ range N, e (x / (C + j))‖ ≤
        ∑ j ∈ range N, ‖e (x / (C + j))‖ := norm_sum_le _ _
    _ = N := by simp

lemma norm_reciprocalExpSum_le (x : ℝ) (A B : ℕ) :
    ‖reciprocalExpSum x A B‖ ≤ ((B - A : ℕ) : ℝ) := by
  by_cases hAB : A ≤ B
  · rw [reciprocalExpSum_eq_range x A B hAB]
    exact norm_reciprocalExpRange_le x (A + 1) (B - A)
  · have hempty : Ioc A B = ∅ := by
      exact Ioc_eq_empty (by omega)
    simp [reciprocalExpSum, hempty]

/-- Reversing the sign of a real phase conjugates a reciprocal range sum,
so its norm is unchanged. -/
lemma norm_reciprocalExpRange_neg (x : ℝ) (C N : ℕ) :
    ‖reciprocalExpRange (-x) C N‖ = ‖reciprocalExpRange x C N‖ := by
  rw [reciprocalExpRange, reciprocalExpRange, ← Complex.norm_conj]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [conj_e]
  congr 1
  ring

/-- Sign invariance for a reciprocal sum over an arbitrary natural
half-open/closed interval. -/
lemma norm_reciprocalExpSum_neg (x : ℝ) (A B : ℕ) :
    ‖reciprocalExpSum (-x) A B‖ = ‖reciprocalExpSum x A B‖ := by
  rw [reciprocalExpSum, reciprocalExpSum, ← Complex.norm_conj]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [conj_e]
  congr 1
  ring

/-- A positive shift is represented by `h + 1`; this convention avoids a
zero shift in finite Weyl differencing while keeping every index natural. -/
def positivePhaseDifference (f : ℕ → ℝ) (h n : ℕ) : ℝ :=
  f (n + h + 1) - f n

/-- Two successive positive phase differences. -/
def positivePhaseDifference₂ (f : ℕ → ℝ) (h₁ h₂ n : ℕ) : ℝ :=
  positivePhaseDifference (positivePhaseDifference f h₂) h₁ n

/-- The multiplicative correlation corresponding to a positive shift. -/
def positiveCorrelation (z : ℕ → ℂ) (h n : ℕ) : ℂ :=
  z (n + h + 1) * (starRingEnd ℂ) (z n)

/-- Two successive positive correlations. -/
def positiveCorrelation₂ (z : ℕ → ℂ) (h₁ h₂ n : ℕ) : ℂ :=
  positiveCorrelation (positiveCorrelation z h₂) h₁ n

lemma positiveCorrelation_e (f : ℕ → ℝ) (h n : ℕ) :
    positiveCorrelation (fun j ↦ e (f j)) h n =
      e (positivePhaseDifference f h n) := by
  simp only [positiveCorrelation, positivePhaseDifference]
  exact (e_sub _ _).symm

lemma positiveCorrelation₂_e (f : ℕ → ℝ) (h₁ h₂ n : ℕ) :
    positiveCorrelation₂ (fun j ↦ e (f j)) h₁ h₂ n =
      e (positivePhaseDifference₂ f h₁ h₂ n) := by
  simp only [positiveCorrelation₂, positivePhaseDifference₂]
  rw [show positiveCorrelation (fun j ↦ e (f j)) h₂ =
      fun j ↦ e (positivePhaseDifference f h₂ j) by
    funext j
    exact positiveCorrelation_e f h₂ j]
  exact positiveCorrelation_e (positivePhaseDifference f h₂) h₁ n

lemma positivePhaseDifference₂_apply (f : ℕ → ℝ) (h₁ h₂ n : ℕ) :
    positivePhaseDifference₂ f h₁ h₂ n =
      (f (n + h₁ + 1 + h₂ + 1) - f (n + h₁ + 1)) -
        (f (n + h₂ + 1) - f n) := by
  simp only [positivePhaseDifference₂, positivePhaseDifference]

/-- Exact algebraic form of a twice-differenced reciprocal phase. -/
lemma positivePhaseDifference₂_reciprocal
    (x : ℝ) (C h₁ h₂ n : ℕ) (hC : 0 < C) :
    positivePhaseDifference₂
        (fun j ↦ reciprocalPhase x (C + j)) h₁ h₂ n =
      x * (h₁ + 1) * (h₂ + 1) *
          (2 * (C + n) + (h₁ + 1) + (h₂ + 1)) /
        ((C + n) * (C + n + (h₁ + 1)) *
          (C + n + (h₂ + 1)) *
            (C + n + (h₁ + 1) + (h₂ + 1))) := by
  rw [positivePhaseDifference₂_apply]
  simp only [reciprocalPhase]
  have h0 : (C + n : ℝ) ≠ 0 := by positivity
  have h1 : (C + n + (h₁ + 1) : ℝ) ≠ 0 := by positivity
  have h2 : (C + n + (h₂ + 1) : ℝ) ≠ 0 := by positivity
  have h12 : (C + n + (h₁ + 1) + (h₂ + 1) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [h0, h1, h2, h12]
  ring

/-! ## Mean-value bounds for shifted differences -/

/-- A real forward difference with an arbitrary positive real shift. -/
def realShiftDifference (f : ℝ → ℝ) (h t : ℝ) : ℝ :=
  f (t + h) - f t

/-- Two successive real forward differences. -/
def realShiftDifference₂ (f : ℝ → ℝ) (h₁ h₂ t : ℝ) : ℝ :=
  realShiftDifference (realShiftDifference f h₂) h₁ t

/-- Three successive real forward differences. -/
def realShiftDifference₃ (f : ℝ → ℝ) (h₁ h₂ h₃ t : ℝ) : ℝ :=
  realShiftDifference (realShiftDifference₂ f h₂ h₃) h₁ t

lemma hasDerivAt_realShiftDifference
    {f f' : ℝ → ℝ} {h t : ℝ}
    (h₁ : HasDerivAt f (f' (t + h)) (t + h))
    (h₀ : HasDerivAt f (f' t) t) :
    HasDerivAt (realShiftDifference f h)
      (realShiftDifference f' h t) t := by
  have hinner : HasDerivAt (fun u : ℝ ↦ u + h) 1 t :=
    (hasDerivAt_id t).add_const h
  have hc := h₁.comp t hinner
  have hc' : HasDerivAt (fun u : ℝ ↦ f (u + h)) (f' (t + h)) t := by
    convert hc using 1
    all_goals first | rfl | simp
  change HasDerivAt (fun u : ℝ ↦ f (u + h) - f u)
    (f' (t + h) - f' t) t
  exact hc'.sub h₀

lemma hasDerivAt_realShiftDifference₂
    {f f' : ℝ → ℝ} {h₁ h₂ t : ℝ}
    (hf : ∀ u ∈ Set.Icc t (t + h₁ + h₂), HasDerivAt f (f' u) u)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) :
    HasDerivAt (realShiftDifference₂ f h₁ h₂)
      (realShiftDifference₂ f' h₁ h₂ t) t := by
  apply hasDerivAt_realShiftDifference
  · apply hasDerivAt_realShiftDifference
    · apply hf
      constructor <;> linarith
    · apply hf
      constructor <;> linarith
  · apply hasDerivAt_realShiftDifference
    · apply hf
      constructor <;> linarith
    · apply hf
      constructor <;> linarith

/-- A closed-interval mean-value estimate with explicit lower and upper
derivative bounds.  Keeping this lemma division-free is convenient for the
iterated shifted differences below. -/
lemma image_sub_bounds_of_hasDerivAt
    {f f' : ℝ → ℝ} {a b m M : ℝ} (hab : a < b)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (f' u) u)
    (hbound : ∀ u ∈ Set.Ioo a b, m ≤ f' u ∧ f' u ≤ M) :
    m * (b - a) ≤ f b - f a ∧
      f b - f a ≤ M * (b - a) := by
  have hcont : ContinuousOn f (Set.Icc a b) :=
    continuousOn_of_forall_continuousAt fun u hu ↦ (hf u hu).continuousAt
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont
      (fun u hu ↦ hf u (Set.Ioo_subset_Icc_self hu))
  have hba : 0 < b - a := sub_pos.mpr hab
  have hcBound := hbound c hc
  constructor
  · apply (le_div_iff₀ hba).mp
    simpa [hslope] using hcBound.1
  · apply (div_le_iff₀ hba).mp
    simpa [hslope] using hcBound.2

/-- Two applications of the mean-value estimate.  This is the
division-free two-shift form used while descending through the derivatives
in the Weyl process. -/
lemma realShiftDifference₂_bounds
    {f f' f'' : ℝ → ℝ} {t h₁ h₂ m M : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hf : ∀ u ∈ Set.Icc t (t + h₁ + h₂), HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ Set.Icc t (t + h₁ + h₂), HasDerivAt f' (f'' u) u)
    (hbound : ∀ u ∈ Set.Ioo t (t + h₁ + h₂), m ≤ f'' u ∧ f'' u ≤ M) :
    m * h₂ * h₁ ≤ realShiftDifference₂ f h₁ h₂ t ∧
      realShiftDifference₂ f h₁ h₂ t ≤ M * h₂ * h₁ := by
  let g : ℝ → ℝ := realShiftDifference f h₂
  let g' : ℝ → ℝ := realShiftDifference f' h₂
  have hg (u : ℝ) (hu : u ∈ Set.Icc t (t + h₁)) :
      HasDerivAt g (g' u) u := by
    rcases hu with ⟨hu0, hu1⟩
    apply hasDerivAt_realShiftDifference
    · apply hf
      constructor <;> linarith
    · apply hf
      constructor <;> linarith
  have hg'bound (u : ℝ) (hu : u ∈ Set.Ioo t (t + h₁)) :
      m * h₂ ≤ g' u ∧ g' u ≤ M * h₂ := by
    have hsegment (v : ℝ) (hv : v ∈ Set.Icc u (u + h₂)) :
        HasDerivAt f' (f'' v) v := by
      apply hf'
      constructor <;> rcases hu with ⟨hu0, hu1⟩ <;>
        rcases hv with ⟨hv0, hv1⟩ <;> linarith
    have hb (v : ℝ) (hv : v ∈ Set.Ioo u (u + h₂)) :
        m ≤ f'' v ∧ f'' v ≤ M := by
      apply hbound
      rcases hu with ⟨hu0, hu1⟩
      rcases hv with ⟨hv0, hv1⟩
      constructor <;> linarith
    simpa only [g', realShiftDifference, add_sub_cancel_left] using
      image_sub_bounds_of_hasDerivAt (show u < u + h₂ by linarith) hsegment hb
  have hout := image_sub_bounds_of_hasDerivAt
    (f := g) (f' := g') (m := m * h₂) (M := M * h₂)
    (show t < t + h₁ by linarith) hg hg'bound
  simpa only [g, realShiftDifference₂, realShiftDifference,
    add_sub_cancel_left] using hout

/-- Three applications of the mean-value estimate.  In the reciprocal
application `f'''(u)=6x/u^4`; this lemma therefore supplies both derivative
bounds needed by the final Kusmin--Landau sum. -/
lemma realShiftDifference₃_bounds
    {f f' f'' f''' : ℝ → ℝ} {t h₁ h₂ h₃ m M : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃)
    (hf : ∀ u ∈ Set.Icc t (t + h₁ + h₂ + h₃), HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ Set.Icc t (t + h₁ + h₂ + h₃), HasDerivAt f' (f'' u) u)
    (hf'' : ∀ u ∈ Set.Icc t (t + h₁ + h₂ + h₃), HasDerivAt f'' (f''' u) u)
    (hbound : ∀ u ∈ Set.Ioo t (t + h₁ + h₂ + h₃),
      m ≤ f''' u ∧ f''' u ≤ M) :
    m * h₃ * h₂ * h₁ ≤ realShiftDifference₃ f h₁ h₂ h₃ t ∧
      realShiftDifference₃ f h₁ h₂ h₃ t ≤ M * h₃ * h₂ * h₁ := by
  let g : ℝ → ℝ := realShiftDifference₂ f h₂ h₃
  let g' : ℝ → ℝ := realShiftDifference₂ f' h₂ h₃
  have hg (u : ℝ) (hu : u ∈ Set.Icc t (t + h₁)) :
      HasDerivAt g (g' u) u := by
    rcases hu with ⟨hu0, hu1⟩
    apply hasDerivAt_realShiftDifference₂
    · intro v hv
      apply hf
      rcases hv with ⟨hv0, hv1⟩
      constructor <;> linarith
    · exact hh₂.le
    · exact hh₃.le
  have hg'bound (u : ℝ) (hu : u ∈ Set.Ioo t (t + h₁)) :
      m * h₃ * h₂ ≤ g' u ∧ g' u ≤ M * h₃ * h₂ := by
    rcases hu with ⟨hu0, hu1⟩
    apply realShiftDifference₂_bounds hh₂ hh₃
    · intro v hv
      apply hf'
      rcases hv with ⟨hv0, hv1⟩
      constructor <;> linarith
    · intro v hv
      apply hf''
      rcases hv with ⟨hv0, hv1⟩
      constructor <;> linarith
    · intro v hv
      apply hbound
      rcases hv with ⟨hv0, hv1⟩
      constructor <;> linarith
  have hout := image_sub_bounds_of_hasDerivAt
    (f := g) (f' := g') (m := m * h₃ * h₂) (M := M * h₃ * h₂)
    (show t < t + h₁ by linarith) hg hg'bound
  simpa only [g, realShiftDifference₃, realShiftDifference,
    add_sub_cancel_left] using hout

end

end Erdos175
