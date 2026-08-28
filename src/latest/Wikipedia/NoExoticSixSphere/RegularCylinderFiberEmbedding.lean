import Wikipedia.NoExoticSixSphere.CylinderFiberNormalFrame
import Wikipedia.NoExoticSixSphere.EuclideanEmbedding
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# The original noncompact regular cylinder fiber as a closed Euclidean embedding

The regular-fiber atlas is retained. The first ambient coordinate is the
original time, and the remaining coordinates are the original sphere
coordinates. Closedness and derivative injectivity are proved for this
actual inclusion; no compactness of the full fiber is required.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCylinderFiber

open Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (k : ℕ) (hd : m = n + k)

def embedding :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    EuclideanEmbedding (k + 1) {p : ℝ × Sphere m // f p = b} := by
  let := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  let L := (EuclideanProduct.headIsometry (m + 1)).toContinuousLinearEquiv
  have hL : ContMDiff 𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))))
      (𝓡 (m + 2)) ∞ L := L.contDiff.contMDiff
  have hA := CylinderFiberNormalFrame.contMDiff_ambientInclusion f hf b hreg k hd
  refine {
    ambientDimension := m + 2
    toFun := L ∘ CylinderFiberNormalFrame.ambientInclusion f b
    smooth := L.contDiff.contMDiff.comp hA
    closedEmbedding := ?_
    injective_mfderiv := ?_
  }
  · have hprod : Topology.IsClosedEmbedding
        (fun p : ℝ × Sphere m ↦ (p.1, p.2.val)) :=
      Topology.IsClosedEmbedding.id.prodMap isClosed_sphere.isClosedEmbedding_subtypeVal
    let P := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
      (EuclideanSpace ℝ (Fin (m + 1)))).symm
    exact L.toHomeomorph.isClosedEmbedding.comp
      (P.toHomeomorph.isClosedEmbedding.comp
          (hprod.comp (isClosed_eq f.continuous continuous_const).isClosedEmbedding_subtypeVal))
  · intro p
    rw [mfderiv_comp p (hL.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
    exact L.injective.comp
      (CylinderFiberNormalFrame.injective_ambientDifferential f hf b hreg k hd p)

theorem embedding_apply (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (embedding f hf b hreg k hd).toFun p =
      EuclideanProduct.coordinates (m + 1) (p.val.1, p.val.2.val) := rfl

theorem embedding_time (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (embedding f hf b hreg k hd).toFun p (0 : Fin (m + 2)) = p.val.1 := rfl

end NoExoticSixSphere.RegularCylinderFiber
