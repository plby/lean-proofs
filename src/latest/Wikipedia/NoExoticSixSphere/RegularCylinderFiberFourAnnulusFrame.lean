import Wikipedia.NoExoticSixSphere.RegularCylinderFiberNormalFrame
import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusLinkParity

/-!
# The original regular-fiber frame on the actual punctured annulus

The normal frame is constructed from the original regular-fiber equations,
not supplied as an extra framing hypothesis. It and the actual annulus
derivative give the global frame on the retained punctured domain. Every
original linking sphere has obstruction one. A relation between the two
endpoint obstructions is not assumed or inferred from this local result.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCylinderFiber

open GLOrthonormalization Stiefel SphereAnnulus

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (hd : m = n + 6) (a : Sphere m)
  (g : Vector 4 → {p : ℝ × Sphere m // f p = b})

def fourAnnulusFrame :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    (∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) →
      (P : GenericFourAnnulus.ParityBallSystem g) →
        C(P.puncturedAnnulus,
          Space (3 + (((m + 2 - 7) + 2) + 2)) (((m + 2 - 7) + 2) + 2)) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P
  exact (embedding f hf b hreg 6 hd).puncturedFourAnnulusGlobalFrameMap
    (normalFrame f hf b hreg 6 hd a) g hg P

theorem fourAnnulusFrame_link_obstruction :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourAnnulus.ParityBallSystem g) (x : AnnulusDoublePoints.singularSet g),
      sphereThirdObstruction ((m + 2 - 7) + 2)
        ((fourAnnulusFrame f hf b hreg hd a g hg P).comp (P.linkingSphere x)) = 1 := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P x
  exact (embedding f hf b hreg 6 hd).fourAnnulusLinkObstruction_one
    (normalFrame f hf b hreg 6 hd a) g hg P x

end NoExoticSixSphere.RegularCylinderFiber
