import Wikipedia.NoExoticSixSphere.RegularCylinderFiberNormalFrame
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskLinkParity

/-!
# The actual punctured-disk frame in the original seven-dimensional fiber

The frame is built from the original regular-fiber equations, not supplied
as an extra hypothesis. Every retained linking sphere has obstruction one.
No two-connectivity, global boundary relation, or boundary obstruction
vanishing is inferred from this local result.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCylinderFiber

open GLOrthonormalization Stiefel

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (hd : m = n + 6) (a : Sphere m)
  (g : Vector 4 → {p : ℝ × Sphere m // f p = b})

def fourDiskFrame :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) →
      (P : GenericFourDisk.ParityBallSystem g) →
        C(P.puncturedDisk, Space (3 + (((m + 2 - 7) + 2) + 2)) (((m + 2 - 7) + 2) + 2)) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P
  exact (embedding f hf b hreg 6 hd).puncturedFourDiskGlobalFrameMap
    (normalFrame f hf b hreg 6 hd a) g hg P

theorem fourDiskFrame_link_obstruction :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourDisk.ParityBallSystem g) (x : DiskDoublePoints.singularSet g),
      sphereThirdObstruction ((m + 2 - 7) + 2)
        ((fourDiskFrame f hf b hreg hd a g hg P).comp (P.linkingSphere x)) = 1 := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P x
  exact (embedding f hf b hreg 6 hd).fourDiskLinkObstruction_one
    (normalFrame f hf b hreg 6 hd a) g hg P x

end NoExoticSixSphere.RegularCylinderFiber
