import Wikipedia.NoExoticSixSphere.EmbeddedTimeBoundaryGermParity
import Wikipedia.NoExoticSixSphere.FourDiskOperatorSourceCoordinates

/-!
# Signed boundary-germ parity in exact source coordinates

Keep the original operator before a fixed source-coordinate change.
Its extendability is equivalent to that of the changed operator, in both
directions. The native chain rule gives the actual changed radial time
derivative. No orientation assumption on the fixed coordinates is needed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (6 + 1)) M]
  [IsManifold (𝓡 (6 + 1)) ∞ M] (e : EuclideanEmbedding (6 + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

theorem sphereParity_zero_iff_signed_reparametrized_germOperator_extends
    (positive : Bool) (R : Vector 4 ≃L[ℝ] Vector 4)
    (f : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ s : Sphere 3, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g (R s.val))
    (hb : ∀ s : Sphere 3, g (R s.val) = (f s).val)
    (P : C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)))
    (hP : ∀ s : Sphere 3, (P s).val = e.normalFourDiskOperator a g (R s.val))
    (hheight : ∀ s : Sphere 3, 0 <
      if positive then fderiv ℝ (t ∘ g) (R s.val) (R s.val)
      else -fderiv ℝ (t ∘ g) (R s.val) (R s.val)) : letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 ↔ Extends P := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  let Q := CollaredDiskFrame.collarSourceChange (ContinuousLinearEquiv.refl ℝ e.NormalModel) R
  let P' : C(Sphere 3,
      Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) :=
    (Monomorphism.recoordinateHomeomorph
      (ContinuousLinearEquiv.refl ℝ (Vector e.ambientDimension)) Q : C(_, _)).comp P
  have hP' (s : Sphere 3) : (P' s).val = e.normalFourDiskOperator a (g ∘ R) s.val := by
    change (P s).val.comp Q.toContinuousLinearMap = _
    rw [hP, e.normalFourDiskOperator_comp_coordinates a g R s.val (hg s)]
  have hg' (s : Sphere 3) : ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ (g ∘ R) s.val :=
    (hg s).comp s.val R.contDiff.contMDiff.contMDiffAt
  have hh (s : Sphere 3) : 0 <
      if positive then fderiv ℝ (t ∘ (g ∘ R)) s.val s.val
      else -fderiv ℝ (t ∘ (g ∘ R)) s.val s.val := by
    have hT : DifferentiableAt ℝ (t ∘ g) (R s.val) :=
      (ht.contMDiffAt.comp (R s.val) (hg s)).contDiffAt.differentiableAt (by simp)
    have hD : fderiv ℝ (t ∘ (g ∘ R)) s.val =
        (fderiv ℝ (t ∘ g) (R s.val)).comp R.toContinuousLinearMap :=
      (hT.hasFDerivAt.comp s.val R.hasFDerivAt).fderiv
    rw [hD]
    exact hheight s
  have hcrit := sphereParity_zero_iff_signed_germOperator_extends e r t ht hreg a m
    positive f (g ∘ R) hg' hb P' hP' hh hf hi hd
  have hExt : Extends P' ↔ Extends P :=
    Monomorphism.extends_recoordinate_iff
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector e.ambientDimension)) (fun _ ↦ Q)
      continuous_const continuous_const continuous_const continuous_const P P' (fun _ ↦ rfl)
  exact hcrit.trans hExt

end NoExoticSixSphere.EmbeddedTime
