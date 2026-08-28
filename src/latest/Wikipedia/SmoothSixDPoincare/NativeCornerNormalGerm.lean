import Wikipedia.SmoothSixDPoincare.CornerNormalDerivative
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Normal transversality for the actual native centered corner germs

Specialize the normal derivative theorem to the genuine centered chart of
the complementary sheet. The derivative used is the original sheet map's
native derivative at its original crossing point.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {D B E M A Z N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]

/-- The prescribed native corner axis has nonzero derivative in the actual normal coordinates. -/
theorem native_corner_normalDerivative_ne_zero
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)
    {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0)
    {x : N} {y : P} (hx : F x ∈ Φ.target) (hxy : G y = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B)
    {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W)
    (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W) {v : Z} (hv : v ≠ 0)
    (haxis : ∀ t, (0, t) ∈ W →
      k (0, t) = G (NativeParametrization.centered (D := Z) y (t • v))) :
    fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k) (0, 0) (0, 1) ≠ 0 := by
  let c := NativeParametrization.centered (D := Z) y
  have hc : (0 : Z) ∈ c.source := NativeParametrization.zero_mem_centered_source y
  have hcy : c (0 : Z) = y := NativeParametrization.centered_zero y
  have hxy' : G (c 0) = F x := (congrArg G hcy).trans hxy
  have ht' : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c 0))) := by
    rwa [hcy]
  exact (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean
    c hc hx hxy' ht' hdim hk hW h0W hv haxis).1

end Wikipedia.SmoothSixDPoincare
