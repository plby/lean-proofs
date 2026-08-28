import Wikipedia.HopfProblem.OrbitPairCompactClockVelocity
import Wikipedia.HopfProblem.OrbitPairFamilyTimeCurves

/-!
# The supported ambient flow follows the original embedded sphere track

The original track curves and the constructed flow curves solve the same
native equation on the cutoff plateau and have the same initial value.
Uniqueness therefore gives pointwise tracking. Model comparison is by
equality, using the literal original cylinder atlas throughout.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

theorem integralCurve_congr_model {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I J : ModelWithCorners ℝ E H}
    (h : I = J) (w : X → E) (γ : ℝ → X) (hγ : IsMIntegralCurve (I := I) γ w) :
    IsMIntegralCurve (I := J) γ w := by
  subst J
  exact hγ

variable {G N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

attribute [local instance] cylinderChartedSpace cylinder_isManifold

theorem supportedField_native_smooth (v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N)) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)).tangent ∞
      (fun p => (⟨p, v.vector p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (ℝ × N))) := by
  have hs := smooth_field_congr_model
    (hJ := by
      rw [← modelWithCornersSelf_prod]
      exact cylinder_isManifold)
    (modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := G)) v.vector v.smooth
  simpa +instances only [cylinderChartedSpace] using hs

theorem supportedField_native_integralCurve
    (v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N)) (p : ℝ × N) :
    IsMIntegralCurve (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) (fun s => v.flow s p) v.vector := by
  have hc := integralCurve_congr_model
    (modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := G)) v.vector
    (fun s => v.flow s p) (v.integralCurve p)
  simpa +instances only [cylinderChartedSpace] using hc

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem flow_follows_track {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) ∞ F)
    (v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N))
    (hmatch : ∀ q : ℝ × M, q.1 ∈ Icc (-2 : ℝ) 2 →
      v.vector (track F q) = (1, timeVelocity (I := I) (J := 𝓘(ℝ, G)) F q))
    {s : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (x : M) :
    v.flow s (track F (0, x)) = track F (s, x) := by
  have htrack : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) ∞ (track F) :=
    contMDiff_fst.prodMk hF
  have hcurve : IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, G))
      (fun u => track F (u, x)) v.vector (Ioo (-2 : ℝ) 2) := by
    apply isMIntegralCurveOn_family_of_velocity htrack x
    intro u hu
    exact (hmatch (u, x) ⟨hu.1.le, hu.2.le⟩).trans (timeVelocity_track hF (u, x)).symm
  have hv := (supportedField_native_smooth v).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (by norm_num) hv
    ((supportedField_native_integralCurve v (track F (0, x))).isMIntegralCurveOn _)
    hcurve (v.flow_zero _) hs

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
