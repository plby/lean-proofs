import Wikipedia.NoExoticSixSphere.RegularCylinderFiberFourAnnulusFrame
import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusRawFrame

/-!
# Two-ended homotopy for the frame constructed from the original fiber equations

The normal columns are the actual frame constructed from the original
regular-fiber equations. An even intrinsic singularity count identifies
the two endpoint frame obstructions and gives a homotopy of the original
injective operators. No extra normal framing or endpoint extension is
assumed.
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

def fourAnnulusOperator :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    (∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) →
      (P : GenericFourAnnulus.ParityBallSystem g) →
        C(P.puncturedAnnulus, Monomorphism.Space (m + 2) ((m + 2 - 7) + 4)) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P
  exact (embedding f hf b hreg 6 hd).puncturedRawFourAnnulusOperatorMap
    (normalFrame f hf b hreg 6 hd a) g hg P

theorem fourAnnulusOperator_value :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourAnnulus.ParityBallSystem g) (x : P.puncturedAnnulus),
      (fourAnnulusOperator f hf b hreg hd a g hg P x).val =
        OperatorSum.operator (normalOperator f hf b hreg 6 hd a (g x.val))
          (fderiv ℝ ((embedding f hf b hreg 6 hd).toFun ∘ g) x.val) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P x
  change OperatorSum.operator ((normalFrame f hf b hreg 6 hd a).ambient (g x.val))
    (fderiv ℝ ((embedding f hf b hreg 6 hd).toFun ∘ g) x.val) = _
  rw [normalFrame_ambient]
  rfl

theorem fourAnnulusFrame_outer_obstruction_eq_inner :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourAnnulus.ParityBallSystem g),
      Even (AnnulusDoublePoints.singularSet g).ncard →
        sphereThirdObstruction ((m + 2 - 7) + 2)
            ((fourAnnulusFrame f hf b hreg hd a g hg P).comp P.outerBoundary) =
          sphereThirdObstruction ((m + 2 - 7) + 2)
            ((fourAnnulusFrame f hf b hreg hd a g hg P).comp P.innerBoundary) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P heven
  exact (embedding f hf b hreg 6 hd).fourAnnulusOuterObstruction_eq_inner
    (normalFrame f hf b hreg 6 hd a) g hg P heven

theorem fourAnnulusOperator_outer_homotopic_inner :
    letI := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourAnnulus.ParityBallSystem g),
      Even (AnnulusDoublePoints.singularSet g).ncard →
        ((fourAnnulusOperator f hf b hreg hd a g hg P).comp P.outerBoundary).Homotopic
          ((fourAnnulusOperator f hf b hreg hd a g hg P).comp P.innerBoundary) := by
  let _ := regularFiberAtlas f hf b hreg 7 (CylinderFiberNormalFrame.dimension_eq hd)
  intro hg P heven
  exact (embedding f hf b hreg 6 hd).puncturedRawFourAnnulusOperatorMap_outer_homotopic_inner
    (normalFrame f hf b hreg 6 hd a) g hg P heven

end NoExoticSixSphere.RegularCylinderFiber
