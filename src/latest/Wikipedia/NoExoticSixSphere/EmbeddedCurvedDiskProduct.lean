import Wikipedia.NoExoticSixSphere.CurvedDiskProduct
import Wikipedia.NoExoticSixSphere.EmbeddedCoreProduct

/-!
# The corrected disk product remains embedded on a smaller whole product

The actual correction fixes both the embedded disk core and its derivative.
Compact-core injectivity supplies a positive transverse radius on which the
entire corrected product is embedded and immersive, inside the genuine
sphere-tube domain. No smallness estimate is substituted for this proof.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T) (R : TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include a hf hd hTb in
theorem exists_embedded_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) r,
      (s, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 3) ε ↦
        e.curvedDiskProduct f D A R χ (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 3) ε,
        ContDiffAt ℝ ∞ (e.curvedDiskProduct f D A R χ) (x, v) ∧
          Injective (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, v)) := by
  have hs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector 3) (hv : v ∈ closedBall (0 : Vector 3) r) :
      ContDiffAt ℝ ∞ (e.curvedDiskProduct f D A R χ) (x, v) :=
    e.contDiffAt_curvedDiskProduct f D A R χ hf hx v
      (hdom (SphereRadialRetraction.retract b x) v hv)
  have hcore : InjOn (fun x ↦ e.curvedDiskProduct f D A R χ (x, 0))
      (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    have hD : D.toFun x = D.toFun y := by simpa only [e.curvedDiskProduct_core] using he
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hD)
  have hdi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      Injective (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, 0)) := by
    rw [e.fderiv_curvedDiskProduct_core f D A R χ hf a hd hTb hx]
    exact A.immersive x hx 0 (mem_closedBall_self A.radius_pos.le)
  exact exists_embedded_core_product (e.curvedDiskProduct f D A R χ) r hr hs hcore hdi

end NoExoticSixSphere.EuclideanEmbedding
