import Wikipedia.HopfProblem.DegreeCollapseNormalFrameRetwisting
import Wikipedia.HopfProblem.DegreeCollapseSevenRadialAttachingData

/-!
# Retwisting the original seven-dimensional attaching tube

The stable disk-frame extension retains the original radial disk and normal
frame on a whole collar. The new transverse frame is precisely the old one
precomposed by the prescribed orthogonal twist. Projection to the original
seven-manifold coordinates therefore gives the actual reparametrized tube,
with the same original manifold and core sphere.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (D : DiskData (pole 3) (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)

theorem exists_retwisted_radial_product
    (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (normalFrameOnSphere e a f s).val)
    (r₀ : ℝ) (hr₀ : (1 / 2 : ℝ) < r₀) (hr₀1 : r₀ < 1)
    (hc : ∀ x ∈ closedBall (0 : Vector 4) 1, r₀ ≤ ‖x‖ →
      D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
      T x = boundaryFrameOperator
        (normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val)
    (ρ : C(Sphere 3, OrthogonalOperators 4))
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun s ↦ (ρ s).1.1))
    (z : UnitSphere (Vector 5))
    (Hρ : (OrthogonalStabilization.stabilizeMap z ρ).Homotopic
      (ContinuousMap.const _ (OrthogonalPaths.identity 5))) :
    ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T' : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ B : EightDimensionalFramedProduct.FramedProduct D.toFun T',
          (∀ s : Sphere 3, T' s.val = boundaryFrameOperator (normalFrameOnSphere e a f s).val) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
            T' x = boundaryFrameOperator
              (normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
            B.transverse x = B.transverse (SphereRadialRetraction.retract (pole 3) x).val) ∧
          (∀ s : Sphere 3, B.boundaryTransverse s = (A.boundaryTransverse s).comp (ρ s).1.1) ∧
          ∀ (R : EuclideanEmbedding.TubularRetraction e) (s : Sphere 3) (v : Vector 4),
            internalSphereTube e f B.boundaryTransverse R (s, v) =
              internalSphereTube e f A.boundaryTransverse R (s, (ρ s).1.1 v) := by
  have hDi : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
    have := e.dimension_le_ambient (f (pole 3))
    omega
  obtain ⟨r₁, -, hr₁1, T', B, hBT, hBC, -, hBc⟩ :=
    NormalFrameRetwisting.exists_retwisted_product_collar D.toFun T A
      (fun _ _ ↦ D.smooth.contDiffAt) hDi D.immersive hN (by omega)
      (pole 3) ρ hρ z Hρ
  let r := max r₀ r₁
  have hr : (1 / 2 : ℝ) < r := hr₀.trans_le (le_max_left _ _)
  have hr1 : r < 1 := max_lt hr₀1 hr₁1
  have hboundary (s : Sphere 3) :
      B.boundaryTransverse s = (A.boundaryTransverse s).comp (ρ s).1.1 := by
    unfold EightDimensionalFramedProduct.FramedProduct.boundaryTransverse
    rw [hBC]
    rfl
  refine ⟨r, hr, hr1, T', B, fun s ↦ (hBT s).trans (hTb s), ?_, hboundary, ?_⟩
  · intro x hx hxr
    have hx₀ : r₀ ≤ ‖x‖ := (le_max_left _ _).trans hxr
    have hx₁ : r₁ ≤ ‖x‖ := (le_max_right _ _).trans hxr
    obtain ⟨hDx, hTx, hCx⟩ := hc x hx hx₀
    obtain ⟨hT'x, hC'x⟩ := hBc x hx hx₁
    refine ⟨hDx, hT'x.trans hTx, ?_⟩
    rw [hC'x, hCx, hBC]
  · intro R s v
    change R.toFun (e.toFun (f s) + B.boundaryTransverse s v) =
      R.toFun (e.toFun (f s) + A.boundaryTransverse s ((ρ s).1.1 v))
    rw [hboundary]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
