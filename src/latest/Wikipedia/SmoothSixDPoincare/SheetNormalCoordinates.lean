import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.TransverseNormalLinearMap

/-!
# Actual normal coordinates and their native derivatives

The normal coordinate is the second component of the inverse of a genuine
ambient chart. Its native derivative is surjective. If the chart identifies a
sheet with the zero normal section, its normal-coordinate map on that sheet
is locally zero, so the derivative annihilates the actual sheet tangent map.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)

def normalCoordinate : M → B := Prod.snd ∘ Φ.symm

theorem contMDiffOn_normalCoordinate :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, B) ∞ (normalCoordinate Φ) Φ.target := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) :=
    contDiff_snd.contMDiff
  exact hs.comp_contMDiffOn Φ.contMDiffOn_invFun

theorem mfderiv_normalCoordinate {p : M} (hp : p ∈ Φ.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p =
      (ContinuousLinearMap.snd ℝ D B).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm p) := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) :=
    contDiff_snd.contMDiff
  have hd : mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (Φ.symm p) =
      ContinuousLinearMap.snd ℝ D B := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.snd ℝ D B).fderiv
  rw [normalCoordinate, mfderiv_comp p (hs.mdifferentiableAt (by simp))
    (Φ.symm.mdifferentiableAt (by simp) hp), hd]
  rfl

theorem surjective_mfderiv_normalCoordinate {p : M} (hp : p ∈ Φ.target) :
    Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p) := by
  rw [mfderiv_normalCoordinate Φ hp]
  exact (show Surjective (ContinuousLinearMap.snd ℝ D B) from fun w => ⟨(0, w), rfl⟩).comp
    (PartialChart.bijective_mfderiv Φ.symm hp).2

variable {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace G N]

/-- The normal coordinate of every nearby point of the full first sheet is exactly zero. -/
theorem normalCoordinate_sheet_eventually_zero {F : N → M}
    (hF : Continuous F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0)
    {x : N} (hx : F x ∈ Φ.target) :
    (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hy
  have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
  exact (hclean _ hq).mp ⟨y, (Φ.right_inv' hy).symm⟩

/-- The derivative of the actual normal coordinate annihilates the first sheet's tangent map. -/
theorem normalDerivative_comp_sheet_eq_zero {F : N → M}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0)
    {x : N} (hx : F x ∈ Φ.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)).comp
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) = 0 := by
  have heq := normalCoordinate_sheet_eventually_zero Φ hF.continuous hclean hx
  have hzero : mfderiv 𝓘(ℝ, G) 𝓘(ℝ, B) (normalCoordinate Φ ∘ F) x = 0 := by
    rw [heq.mfderiv_eq]
    simp only [mfderiv_const]
    rfl
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hx)
  rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))] at hzero
  exact hzero

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
