/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileRow
import ErdosProblems.Erdos1165.AnnularLiteralNestedProfileTailUpper

/-!
# Corrected recursive profile-tail upper

This is the aggregate analytic endpoint for the erased-parent recursion.
The fixed-chain row from `AnnularRecursiveProfileRow` is summed over the
usual weak-composition chains.  The result is the canonical `exp 1` times
the exact transition-segment product, now for the genuinely recursive
physical factorization in which every child interval appears once.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveProfileTailUpper

open AnnularIntegratedProfileKernel AnnularLiteralNestedProfileTailUpper
open AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileRow AnnularRecursiveProfileShape
open AppendixFirstMoment AppendixPairMoment PathInsertion ProfileGapChain
open ProfileListExponent ProfileSmallBall ProfileWeightUpper ThickPoint

noncomputable section

private theorem profileSegmentValues_entries_two_le
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    ∀ a ∈ profileSegmentValues m start, 2 ≤ a := by
  rw [profileSegmentValues, List.forall_mem_ofFn_iff]
  intro i
  have hiSum : start + i.1 ≤ n := by
    have hcancel : start + (n + 1 - start) = n + 1 :=
      Nat.add_sub_of_le (by omega)
    omega
  let j : Fin (n - 1) := ⟨start + i.1 - 2, by omega⟩
  have hscale : scaleIndex j = start + i.1 := by
    change (start + i.1 - 2) + 2 = start + i.1
    exact Nat.sub_add_cancel (by omega)
  rw [← hscale, profileAtScale_scaleIndex]
  exact constrainedProfile_all_entries_two_le hdelta hm (m j) (by
    simp [profileList])

private theorem profileSegmentValues_entries_le_three_mul_sq
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    ∀ a ∈ profileSegmentValues m start, a ≤ 3 * n ^ 2 := by
  rw [profileSegmentValues, List.forall_mem_ofFn_iff]
  intro i
  have hiSum : start + i.1 ≤ n := by
    have hcancel : start + (n + 1 - start) = n + 1 :=
      Nat.add_sub_of_le (by omega)
    omega
  let j : Fin (n - 1) := ⟨start + i.1 - 2, by omega⟩
  have hscale : scaleIndex j = start + i.1 := by
    change (start + i.1 - 2) + 2 = start + i.1
    exact Nat.sub_add_cancel (by omega)
  rw [← hscale, profileAtScale_scaleIndex]
  exact constrainedProfile_entry_le_three_mul_n_sq hdelta hm j

private theorem radialWordLength_profileSegmentValues_le_six_mul_cube
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    radialWordLength (profileSegmentValues m start) ≤ 6 * n ^ 3 := by
  have hsum := List.sum_le_card_nsmul
    (profileSegmentValues m start) (3 * n ^ 2)
    (profileSegmentValues_entries_le_three_mul_sq hstart hstartn hm hdelta)
  have hlength : (profileSegmentValues m start).length ≤ n := by
    rw [profileSegmentValues_length]
    omega
  have hsum' : (profileSegmentValues m start).sum ≤
      (profileSegmentValues m start).length * (3 * n ^ 2) := by
    simpa [nsmul_eq_mul] using hsum
  calc
    radialWordLength (profileSegmentValues m start) ≤
        2 * (profileSegmentValues m start).sum :=
      radialWordLength_le_two_mul_sum _
    _ ≤ 2 * ((profileSegmentValues m start).length * (3 * n ^ 2)) :=
      Nat.mul_le_mul_left 2 hsum'
    _ ≤ 2 * (n * (3 * n ^ 2)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (3 * n ^ 2) hlength)
    _ = 6 * n ^ 3 := by ring

theorem one_add_inv_pow_six_profileSegmentValues_le_exp_one
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hn : 2 ≤ n) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    (1 + 1 / (n : ℝ) ^ 6) ^
        radialWordLength (profileSegmentValues m start) ≤ Real.exp 1 := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlengthNat :=
    radialWordLength_profileSegmentValues_le_six_mul_cube
      hstart hstartn hm hdelta
  have hlength : (radialWordLength (profileSegmentValues m start) : ℝ) ≤
      6 * (n : ℝ) ^ 3 := by
    exact_mod_cast hlengthNat
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (6 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hp : (2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hnTwo 3
    norm_num at hp ⊢
    linarith
  have hcost :
      (radialWordLength (profileSegmentValues m start) : ℝ) *
          (1 / (n : ℝ) ^ 6) ≤ 1 := by
    have hpow : (n : ℝ) ^ 6 = (n : ℝ) ^ 3 * (n : ℝ) ^ 3 := by ring
    have hbound :
        (radialWordLength (profileSegmentValues m start) : ℝ) ≤
          (n : ℝ) ^ 6 := by
      rw [hpow]
      exact hlength.trans
        (mul_le_mul_of_nonneg_right hcube (pow_nonneg (by positivity) 3))
    calc
      (radialWordLength (profileSegmentValues m start) : ℝ) *
            (1 / (n : ℝ) ^ 6) =
          (radialWordLength (profileSegmentValues m start) : ℝ) /
            (n : ℝ) ^ 6 := by ring
      _ ≤ 1 := (div_le_one (pow_pos hnPos 6)).2 hbound
  exact (pow_one_add_le_exp_nat_mul (by positivity)
      (radialWordLength (profileSegmentValues m start))).trans
    (Real.exp_le_exp.mpr hcost)

/-- The recursive distortion actually uses only half of the canonical
`exp 1` budget once the ambient scale is at least three. -/
theorem one_add_inv_pow_six_profileSegmentValues_le_exp_half
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hn : 3 ≤ n) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    (1 + 1 / (n : ℝ) ^ 6) ^
        radialWordLength (profileSegmentValues m start) ≤
      Real.exp (1 / 2 : ℝ) := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlengthNat :=
    radialWordLength_profileSegmentValues_le_six_mul_cube
      hstart hstartn hm hdelta
  have hlength : (radialWordLength (profileSegmentValues m start) : ℝ) ≤
      6 * (n : ℝ) ^ 3 := by
    exact_mod_cast hlengthNat
  have hnThree : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (12 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hp : (3 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hnThree 3
    norm_num at hp ⊢
    linarith
  have hcube0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcube hcube0
  have hhalfBound :
      (radialWordLength (profileSegmentValues m start) : ℝ) ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ 6 := by
    have hpow : (n : ℝ) ^ 6 = (n : ℝ) ^ 3 * (n : ℝ) ^ 3 := by ring
    rw [hpow]
    exact hlength.trans (by linarith)
  have hcost :
      (radialWordLength (profileSegmentValues m start) : ℝ) *
          (1 / (n : ℝ) ^ 6) ≤ (1 / 2 : ℝ) := by
    calc
      (radialWordLength (profileSegmentValues m start) : ℝ) *
            (1 / (n : ℝ) ^ 6) =
          (radialWordLength (profileSegmentValues m start) : ℝ) /
            (n : ℝ) ^ 6 := by ring
      _ ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ (pow_pos hnPos 6)).2 hhalfBound
  exact (pow_one_add_le_exp_nat_mul (by positivity)
      (radialWordLength (profileSegmentValues m start))).trans
    (Real.exp_le_exp.mpr hcost)

/-- The purely numerical sum of all refinement-chain reference costs uses
only half of the canonical exponential budget.  This is the endpoint-free
part of the recursive row estimate and can therefore be reused when each
chain is multiplied by an external continuation kernel. -/
theorem sum_profileRefinementChainReferenceCost_le_expHalf
    {n start a : ℕ} {rest : List ℕ} {delta : ℝ} {m : Profile n}
    (hn : 3 ≤ n) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hvalues : profileSegmentValues m start = a :: rest) :
    (∑ chain : GapChain (a :: rest), ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain)) ≤
      ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
        transitionSegmentProduct start (n - start) (profileAtScale m)) := by
  have hpos : ∀ c ∈ a :: rest, 0 < c := by
    intro c hc
    have hc' : c ∈ profileSegmentValues m start := by
      rw [hvalues]
      exact hc
    have := profileSegmentValues_entries_two_le
      hstart hstartn hm hdelta c hc'
    omega
  have href0 (chain : GapChain (a :: rest)) :
      0 ≤ (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
        gapChainMass (a :: rest) chain :=
    mul_nonneg (pow_nonneg (by positivity) _)
      (gapChainMass_nonneg chain)
  calc
    (∑ chain : GapChain (a :: rest), ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain)) =
      ENNReal.ofReal
        (∑ chain : GapChain (a :: rest),
          ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain)) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun chain _ ↦ href0 chain)).symm
    _ = ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          transitionProduct (a :: rest)) := by
      congr 1
      rw [← Finset.mul_sum, sum_gapChainMass_eq_transitionProduct _ hpos]
    _ ≤ ENNReal.ofReal
        (Real.exp (1 / 2 : ℝ) * transitionProduct (a :: rest)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp := one_add_inv_pow_six_profileSegmentValues_le_exp_half
        hn hstart hstartn hm hdelta
      have hexp' :
          (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) ≤
            Real.exp (1 / 2 : ℝ) := by
        simpa only [hvalues] using hexp
      exact mul_le_mul_of_nonneg_right hexp' (transitionProduct_nonneg _)
    _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
        transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      rw [← hvalues, transitionProduct_profileSegmentValues hstartn]

/-- The population at the head of a constrained profile segment is bounded
by the ambient `3 n²` envelope. -/
theorem profileSegmentValues_head_le_three_mul_sq
    {n start a : ℕ} {rest : List ℕ} {delta : ℝ} {m : Profile n}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hvalues : profileSegmentValues m start = a :: rest) :
    a ≤ 3 * n ^ 2 := by
  apply profileSegmentValues_entries_le_three_mul_sq
    hstart hstartn hm hdelta a
  rw [hvalues]
  simp

/-- Sum of every corrected recursive code row for one exact constrained
profile continuation. -/
theorem eventually_recursiveProfileGapChainRows_le :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (start : ℕ), 2 ≤ start → start ≤ n →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m start = a :: rest →
      ∀ entrance : Fin a → ProfileCycleMiddlePoint n start center,
        (∑ chain : GapChain (a :: rest),
          ∏ i : Fin a,
            ∑ w, recursiveProfileGapKernelENNReal n start center
              (profileRefinementTrees a rest chain i) (entrance i) w) ≤
          ENNReal.ofReal (Real.exp 1 *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
  filter_upwards [eventually_prod_profileRefinementTreeKernelRows_le,
    eventually_ge_atTop 2] with n hrow hn
  intro center delta m hm hdelta start hstart hstartn a rest hvalues entrance
  have hdepth : start + rest.length ≤ n := by
    have hlength : (a :: rest).length = n + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have hpos : ∀ c ∈ a :: rest, 0 < c := by
    intro c hc
    have hc' : c ∈ profileSegmentValues m start := by
      rw [hvalues]
      exact hc
    have := profileSegmentValues_entries_two_le
      hstart hstartn hm hdelta c hc'
    omega
  have href0 (chain : GapChain (a :: rest)) :
      0 ≤ (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
        gapChainMass (a :: rest) chain :=
    mul_nonneg (pow_nonneg (by positivity) _)
      (gapChainMass_nonneg chain)
  calc
    _ ≤ ∑ chain : GapChain (a :: rest), ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
      exact Finset.sum_le_sum fun chain _ =>
        hrow start (by omega) a rest hdepth chain center entrance
    _ = ENNReal.ofReal
          (∑ chain : GapChain (a :: rest),
            ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain)) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun chain _ => href0 chain)).symm
    _ = ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            transitionProduct (a :: rest)) := by
      congr 1
      rw [← Finset.mul_sum, sum_gapChainMass_eq_transitionProduct _ hpos]
    _ ≤ ENNReal.ofReal
          (Real.exp 1 * transitionProduct (a :: rest)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp := one_add_inv_pow_six_profileSegmentValues_le_exp_one
        hn hstart hstartn hm hdelta
      have hexp' :
          (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) ≤
            Real.exp 1 := by
        simpa only [hvalues] using hexp
      exact mul_le_mul_of_nonneg_right hexp' (transitionProduct_nonneg _)
    _ = ENNReal.ofReal (Real.exp 1 *
          transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      rw [← hvalues, transitionProduct_profileSegmentValues hstartn]

/-- Sharpened recursive row estimate reserving half of the exponential
budget for the retained outer prefix. -/
theorem eventually_recursiveProfileGapChainRows_le_expHalf :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (start : ℕ), 2 ≤ start → start ≤ n →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m start = a :: rest →
      ∀ entrance : Fin a → ProfileCycleMiddlePoint n start center,
        (∑ chain : GapChain (a :: rest),
          ∏ i : Fin a,
            ∑ w, recursiveProfileGapKernelENNReal n start center
              (profileRefinementTrees a rest chain i) (entrance i) w) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
  filter_upwards [eventually_prod_profileRefinementTreeKernelRows_le,
    eventually_ge_atTop 3] with n hrow hn
  intro center delta m hm hdelta start hstart hstartn a rest hvalues entrance
  have hdepth : start + rest.length ≤ n := by
    have hlength : (a :: rest).length = n + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have hpos : ∀ c ∈ a :: rest, 0 < c := by
    intro c hc
    have hc' : c ∈ profileSegmentValues m start := by
      rw [hvalues]
      exact hc
    have := profileSegmentValues_entries_two_le
      hstart hstartn hm hdelta c hc'
    omega
  have href0 (chain : GapChain (a :: rest)) :
      0 ≤ (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
        gapChainMass (a :: rest) chain :=
    mul_nonneg (pow_nonneg (by positivity) _)
      (gapChainMass_nonneg chain)
  calc
    _ ≤ ∑ chain : GapChain (a :: rest), ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
      exact Finset.sum_le_sum fun chain _ =>
        hrow start (by omega) a rest hdepth chain center entrance
    _ = ENNReal.ofReal
          (∑ chain : GapChain (a :: rest),
            ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain)) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun chain _ => href0 chain)).symm
    _ = ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            transitionProduct (a :: rest)) := by
      congr 1
      rw [← Finset.mul_sum, sum_gapChainMass_eq_transitionProduct _ hpos]
    _ ≤ ENNReal.ofReal
          (Real.exp (1 / 2 : ℝ) * transitionProduct (a :: rest)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp := one_add_inv_pow_six_profileSegmentValues_le_exp_half
        hn hstart hstartn hm hdelta
      have hexp' :
          (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) ≤
            Real.exp (1 / 2 : ℝ) := by
        simpa only [hvalues] using hexp
      exact mul_le_mul_of_nonneg_right hexp' (transitionProduct_nonneg _)
    _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
          transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      rw [← hvalues, transitionProduct_profileSegmentValues hstartn]

end

end Erdos1165.AnnularRecursiveProfileTailUpper
