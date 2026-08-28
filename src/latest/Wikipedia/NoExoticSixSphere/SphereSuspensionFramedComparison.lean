import Wikipedia.NoExoticSixSphere.SphereSuspensionFrameCoordinates
import Wikipedia.NoExoticSixSphere.RegularFiberTargetChartFrame
import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph

/-!
# The actual stabilized framed comparison of regular suspension fibers

Use the native fiber diffeomorphism and the fixed ambient and normal
isometries. The full frame identity follows from the actual orthogonal
right inverse formula. Both regular-fiber atlases and both embeddings
are the original ones; no smooth structure or frame is reassigned.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse RegularSphereFiber

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (k : ℕ) (hd : m = n + k) (a₀ : Sphere m)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞) (hb : b ∈ c.source)
  (g : C(Sphere (m + 1), Sphere (n + 1)))
  (hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g)
  (hgreg : ∀ y, g y = equator n b → Function.Surjective
    (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g y))
  (hgfiber : ∀ y, g y = equator n b ↔ ∃ x : Sphere m, y = equator m x ∧ f x = b)
  (hgerm : ∀ x, f x = b →
    (g : Sphere (m + 1) → Sphere (n + 1)) =ᶠ[𝓝 (equator m x)] map f)
  (a : Sphere (m + 1))

def fiberFramedDiffeomorph :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    letI := regularFiberAtlas g hg (equator n b) hgreg k (by
      simp only [finrank_euclideanSpace_fin]; omega);
    StabilizedFramedDiffeomorph
      (embedding f hf b hreg k hd) (frameWithTargetChart f hf b hreg k hd a₀ c hb)
      (embedding g hg (equator n b) hgreg k (by omega))
      (frameWithTargetChart g hg (equator n b) hgreg k (by omega) a
        (targetCylinderChart c) (equator_mem_targetCylinderChart c b hb)) := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  let := regularFiberAtlas g hg (equator n b) hgreg k (by
    simp only [finrank_euclideanSpace_fin]; omega)
  refine StabilizedFramedDiffeomorph.ofReverseNormal 1
    (fiberDiffeomorph f hf b hreg k hd g hg hgreg hgfiber)
    (ambientSuspensionIsometry (m + 1)) (normalSuspensionIsometry k hd) ?_ ?_
  · intro x
    change (equator m x.val).val =
      ambientSuspensionIsometry (m + 1) (appendZeroMap (m + 1) 1 x.val.val)
    rw [ambientSuspensionIsometry_appendZero, equator_val_join]
  · intro x v
    have hcol := normalSuspension_block k hd
      (orthogonalRightInverse (fderiv ℝ
        (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀) x.val.val))
      (orthogonalRightInverse (fderiv ℝ
        (SphereFiberNormalFrame.equationsWithTargetChart g (equator n b)
          (targetCylinderChart c) a) (equator m x.val).val))
      (normalOperator_smoothSuspension f b c hf hb g hg a a₀ x.val x.property
        (hreg x.val x.property) (hgerm x.val x.property)) v
    rw [frameWithTargetChart_ambient g hg (equator n b) hgreg k (by omega) a
      (targetCylinderChart c) (equator_mem_targetCylinderChart c b hb),
      frameWithTargetChart_ambient f hf b hreg k hd a₀ c hb]
    exact hcol

end NoExoticSixSphere.SphereMapSuspension
