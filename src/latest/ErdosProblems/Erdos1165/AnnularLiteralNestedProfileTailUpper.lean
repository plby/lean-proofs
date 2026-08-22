/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularLiteralNestedProfileUpper
import ErdosProblems.Erdos1165.ProfileWeightUpper

/-!
# Literal nested-profile upper bound from an arbitrary retained scale

The pair splice retains the profile prefix through the padded separation
scale.  Its unrestricted replacement row therefore carries only the suffix
transition product.  This file gives the walk-facing nested-kernel estimate
for that suffix, with the same uniform `exp 1` loss as the full-profile
bound.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularLiteralNestedProfileTailUpper

open AnnularIntegratedProfileKernel AnnularLiteralNestedProfileUpper
open AnnularNestedProfileKernel AnnularProfileUniformUpperLoss
open AnnularProfileNestedEdge AnnularRadialProfileWords
open AppendixPairMoment
open AppendixFirstMoment PathInsertion ProfileGapChain ProfileSmallBall
open ProfileListExponent ProfileWeightUpper ThickPoint

noncomputable section

/-- Profile values at the retained scale and every subsequent internal
scale through `n`. -/
def profileSegmentValues {n : ℕ} (m : Profile n) (start : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (n + 1 - start) ↦
    profileAtScale m (start + i.1)

@[simp] theorem profileSegmentValues_length
    {n : ℕ} (m : Profile n) (start : ℕ) :
    (profileSegmentValues m start).length = n + 1 - start := by
  simp [profileSegmentValues]

theorem transitionProduct_profileSegmentValues
    {n start : ℕ} (hstartn : start ≤ n) (m : Profile n) :
    transitionProduct (profileSegmentValues m start) =
      transitionSegmentProduct start (n - start) (profileAtScale m) := by
  unfold profileSegmentValues
  rw [transitionProduct_ofFn_eq_segment]
  congr 1
  omega

private theorem profileSegmentValues_entries_two_le
    {n start : ℕ} {delta : ℝ} {m : Profile n}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    ∀ a ∈ profileSegmentValues m start, 2 ≤ a := by
  rw [profileSegmentValues, List.forall_mem_ofFn_iff]
  intro i
  have hcancel : start + (n + 1 - start) = n + 1 :=
    Nat.add_sub_of_le (by omega)
  have hiSum : start + i.1 ≤ n := by omega
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
  have hcancel : start + (n + 1 - start) = n + 1 :=
    Nat.add_sub_of_le (by omega)
  have hiSum : start + i.1 ≤ n := by omega
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
  have hproduct :
      (profileSegmentValues m start).length * (3 * n ^ 2) ≤
        n * (3 * n ^ 2) :=
    Nat.mul_le_mul_right (3 * n ^ 2) hlength
  calc
    radialWordLength (profileSegmentValues m start) ≤
        2 * (profileSegmentValues m start).sum :=
      radialWordLength_le_two_mul_sum _
    _ ≤ 2 * ((profileSegmentValues m start).length * (3 * n ^ 2)) :=
      Nat.mul_le_mul_left 2 hsum'
    _ ≤ 2 * (n * (3 * n ^ 2)) := Nat.mul_le_mul_left 2 hproduct
    _ = 6 * n ^ 3 := by ring

private theorem one_add_inv_pow_six_profileSegmentValues_le_exp_one
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

/-- Eventual literal nested-kernel upper bound for the exact profile tail
beginning at any retained scale. -/
theorem eventually_literalNestedProfileTailSum_toReal_le :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ)
      (m : Profile n), IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (start : ℕ), 2 ≤ start → start ≤ n →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m start = a :: rest →
      ∀ entrance : BoundaryVector (ProfileNestedState n center)
          (start - 2) a,
        (∑ chain : GapChain (a :: rest),
          nestedGapChainKernelENNReal
            (literalProfileNestedEdgeKernelENNReal n center)
            (start - 2) a rest entrance chain).toReal ≤
          Real.exp 1 * transitionSegmentProduct
            start (n - start) (profileAtScale m) := by
  filter_upwards [eventually_literalProfileNestedEdgeUpperAt_inv_pow_six,
    eventually_ge_atTop 2] with n hupper hn
  intro center delta m hm hdelta start hstart hstartn a rest hvalues entrance
  have hpos : ∀ c ∈ a :: rest, 0 < c := by
    intro c hc
    have hc' : c ∈ profileSegmentValues m start := by
      rw [hvalues]
      exact hc
    have := profileSegmentValues_entries_two_le
      hstart hstartn hm hdelta c hc'
    omega
  have hedge := literalProfileNestedEdgeKernelENNReal_ne_top n center
  have hlocal : ∀ d, start - 2 ≤ d →
      d < start - 2 + rest.length →
      NestedEdgeUpperAtENNReal (1 / (n : ℝ) ^ 6)
        (literalProfileNestedEdgeKernelENNReal n center) d := by
    intro d hd hlt
    apply hupper center d
    have hlength : (a :: rest).length = n + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have hraw :
      (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal
          (literalProfileNestedEdgeKernelENNReal n center)
          (start - 2) a rest entrance chain).toReal ≤
        (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          transitionProduct (a :: rest) := by
    rw [ENNReal.toReal_sum]
    · rw [← sum_gapChainMass_eq_transitionProduct (a :: rest) hpos,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun chain _ ↦
        nestedGapChainKernelENNReal_toReal_le_on
          (by positivity) hedge (start - 2) a rest hlocal entrance chain
    · intro chain _
      exact nestedGapChainKernelENNReal_ne_top hedge
        (start - 2) a rest entrance chain
  calc
    _ ≤ (1 + 1 / (n : ℝ) ^ 6) ^
          radialWordLength (profileSegmentValues m start) *
        transitionProduct (profileSegmentValues m start) := by
      simpa only [hvalues] using hraw
    _ ≤ Real.exp 1 * transitionProduct (profileSegmentValues m start) :=
      mul_le_mul_of_nonneg_right
        (one_add_inv_pow_six_profileSegmentValues_le_exp_one
          hn hstart hstartn hm hdelta)
        (transitionProduct_nonneg _)
    _ = Real.exp 1 * transitionSegmentProduct
          start (n - start) (profileAtScale m) := by
      rw [transitionProduct_profileSegmentValues hstartn]

end

end Erdos1165.AnnularLiteralNestedProfileTailUpper
