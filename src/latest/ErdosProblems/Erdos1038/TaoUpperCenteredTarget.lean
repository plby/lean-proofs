import ErdosProblems.Erdos1038.TaoUpperQuantileTarget

/-!
# Centered quantile contradiction for the polynomial target

The quantile is constructed in coordinates where the left closed-target
endpoint is zero and the empirical root interval is centered at `t₀`.
Its pushforward is then translated back to the original polynomial
coordinates.  This module packages the common measure-theoretic argument
used by all three of Tao's explicit trials.
-/

open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

namespace QuantileData

private theorem self_le_rearrangement_of_left_le
    (Q : QuantileData) {x : ℝ} (hx : Q.left ≤ x) :
    x ≤ Q.rearrangement x := by
  have hleftMem : Q.left ∈ Icc Q.left Q.upper :=
    ⟨le_rfl, Q.h_left_upper⟩
  have hbase : Q.left ≤ Q.rearrangement Q.left := by
    rw [Q.rearrangement_of_mem hleftMem]
    exact Q.self_le_quantile ⟨Q.left, hleftMem⟩
  have hexpansive := Q.rearrangement_expansive hx
  linarith

/-- A source point mapped into the empirical root interval must itself lie
in the translated root interval.  This localizes every possible root fiber
to the atomless part of the source trial measure. -/
theorem centeredRearrangement_mem_rootSet_imp_source_mem
    (Q : QuantileData) (f : Polynomial ℝ) (hf : IsAdmissible f)
    (center : ℝ) (hleft : Q.left = center - 1)
    {s : ℝ} (hs : Q.centeredRearrangement center s ∈ rootSet f) :
    s ∈ Icc (center - 1) (center + 1) := by
  have hroot : Q.centeredRearrangement center s ∈ Icc (-1 : ℝ) 1 :=
    hf.root_mem_Icc (mem_rootSet_iff.mp hs)
  have hsourceLower : center - 1 ≤ s := by
    apply le_of_not_gt
    intro hslt
    have hsQ : s < Q.left := by rwa [hleft]
    rw [centeredRearrangement, Q.rearrangement_of_lt_left hsQ] at hroot
    linarith [hroot.1]
  have hQle : Q.left ≤ s := by rwa [hleft]
  have hself := self_le_rearrangement_of_left_le Q hQle
  constructor
  · exact hsourceLower
  · change Q.rearrangement s - center ∈ Icc (-1 : ℝ) 1 at hroot
    linarith [hroot.2]

/-- Common contradiction theorem for Tao's three source trial measures.

The first support branch consists of fixed points to the left which already
map into the closed polynomial target.  The second branch is rearranged
from the normalized right target.  Atomlessness is required only on the
translated root interval, exactly where a pushed empirical-root collision
could occur. -/
theorem false_of_normalizedCenteredQuantile_pushforward
    (Q : QuantileData) (f : Polynomial ℝ) (hf : IsAdmissible f)
    (ν : Measure ℝ)
    (hleft : Q.left = taoNormalizedSourceLeft f hf)
    (hF : Q.F = volumeCumulative (taoNormalizedRightTarget f hf) Q.left)
    (hsupport : ∀ᵐ s ∂ν,
      (s < Q.left ∧
          Q.centeredRearrangement (taoNormalizedCenter f hf) s ∈
            closedUnitSublevelSet f) ∨
        s ∈ Ioc Q.left Q.upper)
    (hsingleton : ∀ s ∈
        Icc (taoNormalizedCenter f hf - 1)
          (taoNormalizedCenter f hf + 1),
      ν {s} = 0)
    (hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |Q.extendedInverseCoordinate
          (t + taoNormalizedCenter f hf) - s|) ν)
    (htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |t - Q.centeredRearrangement (taoNormalizedCenter f hf) s|) ν)
    (htrial : ∀ s ∈
        Icc (taoNormalizedCenter f hf - 1)
          (taoNormalizedCenter f hf + 1),
      taoTrialMeasurePotential ν s < 0) :
    False := by
  let center := taoNormalizedCenter f hf
  have hleftCenter : Q.left = center - 1 := by
    simpa [center, taoNormalizedSourceLeft] using! hleft
  have hbasicSupport : ∀ᵐ s ∂ν,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact Or.inl hsFixed.1
    · exact Or.inr ⟨hsInterval.1.le, hsInterval.2⟩
  have hpushedMem :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        x ∈ closedUnitSublevelSet f := by
    apply Q.ae_map_centeredRearrangement_mem_of_volumeCumulative
      (taoNormalizedRightTarget f hf) (closedUnitSublevelSet f) center
      hF (isClosed_taoNormalizedRightTarget hf)
      (isClosed_closedUnitSublevelSet f)
    · intro x hx
      have hxTarget := hx.1
      change x + closedUnitSublevelLeft f hf ∈
        closedUnitSublevelSet f at hxTarget
      change x - center ∈ closedUnitSublevelSet f
      simpa [center, taoNormalizedCenter, sub_eq_add_neg] using! hxTarget
    · simpa [center] using! hsupport
  have hpushedRoots :
      (Measure.map (Q.centeredRearrangement center) ν) (rootSet f) = 0 := by
    apply Q.map_centeredRearrangement_rootSet_eq_zero f ν center
    intro s hs
    apply hsingleton s
    simpa [center] using!
      Q.centeredRearrangement_mem_rootSet_imp_source_mem
        f hf center hleftCenter hs
  have hpushedNonnegOn :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        x ∈ closedUnitSublevelSet f →
          0 ≤ taoEmpiricalPotential f hf x :=
    ae_taoEmpiricalPotential_nonneg_on_closedUnitSublevelSet hf
      (Measure.map (Q.centeredRearrangement center) ν) hpushedRoots
  have hpushedNonneg :
      ∀ᵐ x ∂(Measure.map (Q.centeredRearrangement center) ν),
        0 ≤ taoEmpiricalPotential f hf x := by
    filter_upwards [hpushedMem, hpushedNonnegOn] with x hx hnonneg
    exact hnonneg hx
  have hnot := Q.not_taoEmpiricalPotential_nonneg_ae_of_centeredQuantile_pushforward
    f hf ν center hleftCenter hbasicSupport
      (by simpa [center] using! hsingleton)
      (by simpa [center] using! hsource)
      (by simpa [center] using! htarget)
      (by simpa [center] using! htrial)
  exact hnot hpushedNonneg

end QuantileData

end

end Erdos1038
