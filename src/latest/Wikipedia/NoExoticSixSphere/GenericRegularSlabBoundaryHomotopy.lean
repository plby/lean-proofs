import Wikipedia.NoExoticSixSphere.GenericRegularSlabCylinder
import Wikipedia.NoExoticSixSphere.RegularCylinderFiberAnnulusBoundaryHomotopy

/-!
# Constructing the two-ended operator homotopy with the original collars

The generic annulus is constructed from the original collared cylinder.
Its intrinsic singularities have even cardinality by the actual compact
double-point curve. The prescribed equation frame then gives homotopic
boundary operators on this same annulus. Both original endpoint maps,
both original collar derivatives, and protected collars are retained.
The parity relation and the homotopy are conclusions, not hypotheses.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)}
  (D : d.CollaredCylinderExtension 3 f₀ f₁) (b : NoExoticSixSphere.Sphere 3)

theorem exists_original_boundary_operator_homotopy (hd : m = n + 6)
    (a : NoExoticSixSphere.Sphere m)
    (hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁))
    (hi₀ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₀) q))
    (hi₁ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₁) q))
    (hinj₀ : Injective f₀) (hinj₁ : Injective f₁)
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    let L := EuclideanProduct.coordinates (m + 1)
    ∃ (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
      (hg : ∀ x ∈ SphereAnnulus.domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
      (P : GenericFourAnnulus.ParityBallSystem g),
      (∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f₀ q).val) ∧
      (∀ q : NoExoticSixSphere.Sphere 3, g ((2 : ℝ) • q.val) = (f₁ q).val) ∧
      (∀ q : NoExoticSixSphere.Sphere 3,
        fderiv ℝ (e.toFun ∘ g) q.val = fderiv ℝ (L ∘ leftCollar D b) q.val ∧
        fderiv ℝ (e.toFun ∘ g) ((2 : ℝ) • q.val) =
          fderiv ℝ (L ∘ rightCollar D b) ((2 : ℝ) • q.val)) ∧
      (∀ x : Vector 4, 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t) ∧
      ((RegularCylinderFiber.fourAnnulusOperator d.map d.smooth_map z d.regular_map
          hd a g hg P).comp P.outerBoundary).Homotopic
        ((RegularCylinderFiber.fourAnnulusOperator d.map d.smooth_map z d.regular_map
          hd a g hg P).comp P.innerBoundary) ∧
      ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
        P.closedHoles ⊆ {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁} ∧
        ∀ x : SphereAnnulus.domain 3, ‖x.val‖ ≤ r₀ ∨ r₁ ≤ ‖x.val‖ →
          g x.val = (D.map (SphereAnnulus.toCylinder b x)).val := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  obtain ⟨g, r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hgs, hboundary₀, hboundary₁,
    hcollars, _, _, hderiv, hgV, _, _, heven, ⟨P, hP⟩, _⟩ :=
    exists_generic_with_original_ends D b hd hf₀ hf₁ hi₀ hi₁ hinj₀ hinj₁ h₀ h₁
  exact ⟨g, hgs, P, hboundary₀, hboundary₁, hderiv, hgV,
    RegularCylinderFiber.fourAnnulusOperator_outer_homotopic_inner
      d.map d.smooth_map z d.regular_map hd a g hgs P heven,
    r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hP, hcollars⟩

end NoExoticSixSphere.RegularSlabCylinderCollar
