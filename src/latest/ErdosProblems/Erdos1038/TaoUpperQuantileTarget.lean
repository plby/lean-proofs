import ErdosProblems.Erdos1038.TaoUpperClosedTarget
import ErdosProblems.Erdos1038.TaoQuantile

/-!
# Instantiating Tao's quantile with the closed polynomial target

The strict volume excess and the leftmost-point normalization from
`TaoUpperClosedTarget` provide exactly the mass hypothesis needed by
`exists_volumeCumulative_cap`.  This module packages the resulting quantile
and proves that all positive-level source points rearrange into the closed
polynomial target.
-/

open scoped ENNReal
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

theorem isClosed_taoNormalizedRightTarget
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    IsClosed (taoNormalizedRightTarget f hf) := by
  exact (isClosed_leftNormalizedClosedTarget hf).inter isClosed_Ici

theorem taoNormalizedRightTarget_subset_Iic_four
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    taoNormalizedRightTarget f hf ⊆ Iic (4 : ℝ) := by
  intro x hx
  have hxTarget := hx.1
  change x + closedUnitSublevelLeft f hf ∈
    closedUnitSublevelSet f at hxTarget
  have hxUpper := (closedUnitSublevelSet_subset_Icc hf hxTarget).2
  have hleftMem := (closedUnitSublevelLeft_isLeast hf).1
  have hleftLower :=
    (closedUnitSublevelSet_subset_Icc hf hleftMem).1
  change x ≤ (4 : ℝ)
  linarith

/-- At the non-strict sharp threshold, the normalized target still has
enough mass to the right of the translated root interval. -/
theorem taoNormalizedRightTarget_mass_of_le
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f) :
    ENNReal.ofReal
        (taoUpperEdge - taoNormalizedSourceLeft f hf) ≤
      volume (taoNormalizedRightTarget f hf) := by
  let A := leftNormalizedClosedTarget f hf
  let l := taoNormalizedSourceLeft f hf
  let E := taoNormalizedRightTarget f hf
  have hl0 : 0 ≤ l := (taoNormalizedSourceLeft_pos hf hleft).le
  have hlM : l ≤ taoUpperEdge :=
    (taoNormalizedSourceLeft_lt_upperEdge hf).le
  have hAvolume : volume A = sublevelVolume f :=
    volume_leftNormalizedClosedTarget hf
  have hAsubset : A ⊆ Ici (0 : ℝ) :=
    leftNormalizedClosedTarget_subset_Ici_zero hf
  have hsplit : A = (A ∩ Iio l) ∪ E := by
    ext x
    constructor
    · intro hx
      by_cases hxl : x < l
      · exact Or.inl ⟨hx, hxl⟩
      · exact Or.inr ⟨hx, le_of_not_gt hxl⟩
    · rintro (hx | hx) <;> exact hx.1
  have hleftPart : volume (A ∩ Iio l) ≤ ENNReal.ofReal l := by
    calc
      volume (A ∩ Iio l) ≤ volume (Ico (0 : ℝ) l) := by
        apply measure_mono
        intro x hx
        exact ⟨hAsubset hx.1, hx.2⟩
      _ = ENNReal.ofReal l := by
        rw [Real.volume_Ico]
        simp
  have htotal : ENNReal.ofReal taoUpperEdge ≤
      ENNReal.ofReal l + volume E := by
    calc
      ENNReal.ofReal taoUpperEdge ≤ volume A := by
        rw [hAvolume]
        exact hvolume
      _ = volume ((A ∩ Iio l) ∪ E) :=
        congrArg (volume : Set ℝ → ℝ≥0∞) hsplit
      _ ≤ volume (A ∩ Iio l) + volume E := by
        exact measure_union_le (μ := (volume : Measure ℝ)) _ _
      _ ≤ ENNReal.ofReal l + volume E :=
        add_le_add hleftPart le_rfl
  apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal l + ENNReal.ofReal (taoUpperEdge - l) =
        ENNReal.ofReal taoUpperEdge := by
      rw [← ENNReal.ofReal_add hl0 (sub_nonneg.mpr hlM)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal l + volume E := htotal

/-- A strict counterexample to the upper bound canonically supplies Tao's
expansive quantile on `[t₀-1, 2√2]`. -/
theorem exists_closedTarget_quantileData
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge < sublevelVolume f) :
    ∃ Q : QuantileData,
      Q.left = taoNormalizedSourceLeft f hf ∧
      Q.upper = taoUpperEdge ∧
      Q.F = volumeCumulative (taoNormalizedRightTarget f hf)
        (taoNormalizedSourceLeft f hf) ∧
      ∀ x ∈ Ioc (taoNormalizedSourceLeft f hf) taoUpperEdge,
        Q.rearrangement x ∈ taoNormalizedRightTarget f hf := by
  let E := taoNormalizedRightTarget f hf
  let l := taoNormalizedSourceLeft f hf
  have hlu : l ≤ taoUpperEdge :=
    (taoNormalizedSourceLeft_lt_upperEdge hf).le
  have hmass : ENNReal.ofReal (taoUpperEdge - l) < volume E := by
    exact taoNormalizedRightTarget_mass hf hleft hvolume
  rcases exists_volumeCumulative_cap E l taoUpperEdge hlu
      (taoNormalizedRightTarget_subset_Ici hf) hmass with
    ⟨cap, hlcap, htop⟩
  let Q : QuantileData := volumeQuantileData E l taoUpperEdge cap
    hlu hlcap htop.le
  refine ⟨Q, rfl, rfl, rfl, ?_⟩
  intro x hx
  exact Q.rearrangement_mem_of_volumeCumulative_of_isClosed
    E rfl (isClosed_taoNormalizedRightTarget hf) hx

/-- Non-strict threshold version, using the uniform cap `4` for the
normalized closed target. -/
theorem exists_closedTarget_quantileData_of_le
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f) :
    ∃ Q : QuantileData,
      Q.left = taoNormalizedSourceLeft f hf ∧
      Q.upper = taoUpperEdge ∧
      Q.F = volumeCumulative (taoNormalizedRightTarget f hf)
        (taoNormalizedSourceLeft f hf) ∧
      ∀ x ∈ Ioc (taoNormalizedSourceLeft f hf) taoUpperEdge,
        Q.rearrangement x ∈ taoNormalizedRightTarget f hf := by
  let E := taoNormalizedRightTarget f hf
  let l := taoNormalizedSourceLeft f hf
  have hlu : l ≤ taoUpperEdge :=
    (taoNormalizedSourceLeft_lt_upperEdge hf).le
  have hlcap : l ≤ (4 : ℝ) := by
    have hMfour : taoUpperEdge < 4 := by
      unfold taoUpperEdge
      nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]
    exact hlu.trans hMfour.le
  have hmass : ENNReal.ofReal (taoUpperEdge - l) ≤ volume E := by
    exact taoNormalizedRightTarget_mass_of_le hf hleft hvolume
  have htop : taoUpperEdge - l ≤ volumeCumulative E l 4 := by
    exact volumeCumulative_at_bounded_cap E l taoUpperEdge 4
      (taoNormalizedRightTarget_subset_Ici hf)
      (taoNormalizedRightTarget_subset_Iic_four hf) hmass
  let Q : QuantileData := volumeQuantileData E l taoUpperEdge 4
    hlu hlcap htop
  refine ⟨Q, rfl, rfl, rfl, ?_⟩
  intro x hx
  exact Q.rearrangement_mem_of_volumeCumulative_of_isClosed
    E rfl (isClosed_taoNormalizedRightTarget hf) hx

end

end Erdos1038
