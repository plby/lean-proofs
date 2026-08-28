import Wikipedia.SmoothSixDPoincare.ControlledMorseBlock
import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints

/-!
# Isolating a critical point whose critical value is unique

Finiteness of the native critical set gives a value gap. The handle radius
can be chosen inside that gap and inside the prescribed exact-field chart
neighborhood simultaneously. Uniqueness of the chosen critical value is
explicit; this file does not assert that every Morse function has it.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped Topology ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

/-- A finite set of values separates a point with a unique value from all the others. -/
theorem exists_isolating_radius {X : Type*} {f : X → ℝ} {K : Set X} (hK : K.Finite)
    (p : X) (hunique : ∀ x ∈ K, f x = f p → x = p) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∀ x ∈ K, f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  have hfin : (f '' (K \ {p})).Finite := (hK.subset sdiff_subset).image f
  have hnot : f p ∉ f '' (K \ {p}) := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (mem_singleton_iff.mpr (hunique x hx.1 heq))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl (f p) hnot
  let ρ := min (R / 2) (min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro x hx hval
  by_contra hxp
  have hd : dist (f x) (f p) < δ := by
    rw [Real.dist_eq]
    have ha : |f x - f p| ≤ ρ ^ 2 := abs_le.mpr ⟨by linarith [hval.1], by linarith [hval.2]⟩
    exact ha.trans_lt hρsq
  exact hball hd ⟨x, ⟨hx, by simpa only [mem_singleton_iff] using hxp⟩, rfl⟩

namespace SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- Fit the isolated critical band and its exact-field block below a prescribed radius. -/
theorem exists_isolated_fieldCompatibleBlock_lt
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ), ρ < ε ∧ ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      (∀ x ∈ W, V x = c.descentField x) ∧
      (closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
          c.splitChart.target ∩ c.splitChart.symm ⁻¹' W) ∧
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨R, hR, W, hW, hpW, heqW, hblock⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρbound, hband⟩ :=
    exists_isolating_radius hfinite p hunique (lt_min hR hε)
  have hρR : ρ < R := hρbound.trans_le (min_le_left _ _)
  have hρε : ρ < ε := hρbound.trans_le (min_le_right _ _)
  refine ⟨ρ, hρ, hρε, W, hW, hpW, heqW, ?_, hband⟩
  intro z hz
  apply hblock
  have hr : 2 * ρ ≤ 2 * R := mul_le_mul_of_nonneg_left hρR.le (by norm_num)
  exact ⟨closedBall_subset_closedBall hr hz.1, closedBall_subset_closedBall hr hz.2⟩

open Classical in
/-- Choose an isolated critical band and a full handle block within the exact-field neighborhood. -/
theorem exists_isolated_fieldCompatibleBlock
    (hfinite : (ManifoldMorse.criticalPoints E f).Finite)
    (hunique : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) :
    ∃ ρ > (0 : ℝ), ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      (∀ x ∈ W, V x = c.descentField x) ∧
      (closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
          c.splitChart.target ∩ c.splitChart.symm ⁻¹' W) ∧
      ∀ x ∈ ManifoldMorse.criticalPoints E f,
        f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨ρ, hρ, _, W, hW, hpW, heqW, hblock, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq zero_lt_one
  exact ⟨ρ, hρ, W, hW, hpW, heqW, hblock, hband⟩

end SignedMorseChart
end Wikipedia.SmoothSixDPoincare.ManifoldMorse
