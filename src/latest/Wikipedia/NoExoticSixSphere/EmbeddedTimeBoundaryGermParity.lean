import Wikipedia.NoExoticSixSphere.BoundaryGermParity
import Wikipedia.NoExoticSixSphere.EmbeddedSignedTimeGraph
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame
import Wikipedia.NoExoticSixSphere.CollaredBoundaryOperatorCoordinates

/-!
# Actual induced-boundary parity from either signed native boundary germ

Only smoothness at the original sphere is required of the manifold-valued
map. Positive or negative time graph gives the same original outward
boundary frame, with the sign-dependent normal-coordinate change explicit.
This applies at either end of an annulus without filling its missing disk.
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

theorem sphereParity_zero_iff_signed_germOperator_extends
    (positive : Bool) (f : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ s : Sphere 3, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g s.val)
    (hb : ∀ s : Sphere 3, g s.val = (f s).val)
    (P : C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)))
    (hP : ∀ s : Sphere 3, (P s).val = e.normalFourDiskOperator a g s.val)
    (hheight : ∀ s : Sphere 3, 0 <
      if positive then fderiv ℝ (t ∘ g) s.val s.val else -fderiv ℝ (t ∘ g) s.val s.val) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 ↔ Extends P := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  let eZ := zeroEmbedding (n := 6) e t ht hreg
  let aZ := zeroNormalFrame (n := 6) e r t ht hreg a m
  let F := signedTimeGraph e t positive g
  let A : C(Sphere 3, Vector (e.ambientDimension - 7) →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ (a.orthonormal (f s).val).val,
      a.contMDiff_orthonormal.continuous.comp (continuous_subtype_val.comp f.continuous)⟩
  let D : C(Sphere 3, Vector 4 →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ e.fourDiskDerivative g s.val,
      continuous_iff_continuousAt.mpr (fun s ↦
        (e.contDiffAt_fourDiskDerivative g s.val (hg s)).continuousAt.comp
          continuous_subtype_val.continuousAt)⟩
  let ν : C(Sphere 3, Vector e.ambientDimension) :=
    ⟨fun s ↦ signedTransverse e r t positive (f s),
      (contMDiff_signedTransverse e r t ht hreg positive).continuous.comp f.continuous⟩
  let ξ : C(Sphere 3, Vector e.ambientDimension →L[ℝ] ℝ) :=
    ⟨fun s ↦ signedTimeCovector e r t positive (f s).val,
      (contMDiff_signedTimeCovector e r t ht positive).continuous.comp
        (continuous_subtype_val.comp f.continuous)⟩
  let Q := signedNormalCoordinates (n := 6) e positive m
  have hN : eZ.ambientDimension = 3 + ((e.ambientDimension - 7) + 4) := by
    have h := e.dimension_le_ambient m
    change e.ambientDimension = 3 + ((e.ambientDimension - 7) + 4)
    omega
  have hF : ∀ s : Sphere 3, ContDiffAt ℝ ∞ F s.val :=
    fun s ↦ contDiffAt_signedTimeGraph e t ht positive g s.val (hg s)
  have hFb : ∀ s : Sphere 3, F s.val = (eZ.toFun (f s), 0) := by
    intro s
    change (e.toFun (g s.val), if positive then t (g s.val) else -t (g s.val)) =
      (e.toFun (f s).val, 0)
    rw [hb, (f s).property, neg_zero]
    cases positive <;> rfl
  have hP' : ∀ s : Sphere 3, (P s).val = OperatorSum.operator (A s) (D s) := by
    intro s
    rw [hP]
    change OperatorSum.operator (a.orthonormal (g s.val)).val (e.fourDiskDerivative g s.val) =
      OperatorSum.operator (a.orthonormal (f s).val).val (e.fourDiskDerivative g s.val)
    rw [hb]
  have haZ : ∀ s : Sphere 3, aZ.ambient (f s) =
      (OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap :=
    fun s ↦ zeroNormalFrame_signed_columns e r t ht hreg positive a m (f s)
  have hD : ∀ s : Sphere 3, fderiv ℝ F s.val = OutwardGraphFrame.graph (D s) (ξ s) := by
    intro s
    have h := signedTimeGraph_derivative e r t ht positive g s.val (hg s)
    rw [hb s] at h
    exact h
  have hA : ∀ s u, ξ s (A s u) = 0 :=
    fun s u ↦ signedTimeCovector_frame e r t positive a.normalized (f s).val u
  have hν : ∀ s, ξ s (ν s) < 0 :=
    fun s ↦ signedTimeCovector_transverse_neg e r t ht hreg positive (f s)
  have hH : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2 := by
    intro s
    rw [signedTimeGraph_heightDerivative e r t ht positive g s.val s.val (hg s)]
    exact hheight s
  exact eZ.sphereParity_zero_iff_outwardGermOperator_extends aZ hN f hf hi hd F hF hFb
    A D ν ξ Q P hP' haZ hD hA hν hH

end NoExoticSixSphere.EmbeddedTime
