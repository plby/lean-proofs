import Wikipedia.NoExoticSixSphere.RegularValueNeighborhood
import Wikipedia.NoExoticSixSphere.SphereTargetCorrection
import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder

/-!
# Relative regularization reduced to a nearby regular value

For a smooth collared sphere homotopy with compact spatial source, a
sufficiently nearby regular value produces an actual globally regular
collared cylinder at the original value. Both endpoint maps are unchanged,
and the homotopy to the corrected map fixes whole end neighborhoods.

The neighborhood size is constructed from endpoint regularity. Existence of
a regular value in that neighborhood is deliberately not assumed as a
global principle or asserted here: that is the remaining Sard step.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

variable {B H M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

theorem exists_regularCylinderCorrectionRadius {n : ℕ}
    (F : C(ℝ × M, Sphere n)) (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ F)
    (f₀ f₁ : C(M, Sphere n)) (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (hleft : ∀ t ≤ (1 / 4 : ℝ), ∀ x, F (t, x) = f₀ x)
    (hright : ∀ t, (3 / 4 : ℝ) ≤ t → ∀ x, F (t, x) = f₁ x)
    (b : Sphere n)
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv I (𝓡 n) f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv I (𝓡 n) f₁ x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : Sphere n, dist c b < ε →
      (∀ p, F p = c → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) F p)) →
      ∃ d : RegularCollaredCylinder (M := M) I (𝓡 n) b 0 1,
        d.leftMap = f₀ ∧ d.rightMap = f₁ ∧
        Nonempty (F.HomotopyRel d.map {p | p.1 ≤ 1 / 8 ∨ 7 / 8 ≤ p.1}) := by
  obtain ⟨V, hV, hbV, hr₀, hr₁⟩ := exists_commonRegularValueNeighborhood h₀ h₁ hreg₀ hreg₁
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbV)
  refine ⟨min (1 / 4) (ε / 4), lt_min (by norm_num) (by positivity), ?_⟩
  intro c hc hreg
  have hcquarter : dist c b < 1 / 4 := hc.trans_le (min_le_left _ _)
  have hceps : dist c b < ε / 4 := hc.trans_le (min_le_right _ _)
  have hchalf : dist c b < 1 / 2 := by linarith
  have haV : ∀ t, SphereTargetCorrection.value b c hchalf t ∈ V := by
    intro t
    apply hball
    exact (CollaredValueCurve.dist_curve_le b c (by linarith) t).trans_lt (by linarith)
  let G := SphereTargetCorrection.corrected b c hchalf F
  have hG := SphereTargetCorrection.contMDiff_corrected b c hchalf hF
  have hGleft : ∀ t ∈ Iio (1 / 8 : ℝ), ∀ x, G (t, x) = f₀ x := by
    intro t ht x
    change t < 1 / 8 at ht
    change SphereTargetCorrection.corrected b c hchalf F (t, x) = _
    rw [SphereTargetCorrection.corrected_eq_of_cutoff_zero b c hchalf F
      (CollaredValueCurve.cutoff_left ht.le)]
    exact hleft t (by linarith) x
  have hGright : ∀ t ∈ Ioi (7 / 8 : ℝ), ∀ x, G (t, x) = f₁ x := by
    intro t ht x
    change 7 / 8 < t at ht
    change SphereTargetCorrection.corrected b c hchalf F (t, x) = _
    rw [SphereTargetCorrection.corrected_eq_of_cutoff_zero b c hchalf F
      (CollaredValueCurve.cutoff_right ht.le)]
    exact hright t (by linarith) x
  let d : RegularCollaredCylinder (M := M) I (𝓡 n) b 0 1 :=
    { map := G
      leftMap := f₀
      rightMap := f₁
      smooth_map := hG
      smooth_left := h₀
      smooth_right := h₁
      regular_map := SphereTargetCorrection.regular_corrected b c hchalf hF h₀ h₁ hleft hright
        (fun t x hx ↦ hr₀ _ (haV t) x hx) (fun t x hx ↦ hr₁ _ (haV t) x hx) hreg
      regular_left := hreg₀
      regular_right := hreg₁
      time_lt := by norm_num
      leftTimes := ⟨Iio (1 / 8 : ℝ), isOpen_Iio⟩
      rightTimes := ⟨Ioi (7 / 8 : ℝ), isOpen_Ioi⟩
      left_mem := by norm_num
      right_mem := by norm_num
      left_eq := hGleft
      right_eq := hGright }
  exact ⟨d, rfl, rfl, ⟨SphereTargetCorrection.homotopy b c hchalf F⟩⟩

end NoExoticSixSphere
