import Wikipedia.NoExoticSixSphere.AnnulusClockCollarImmersion
import Wikipedia.NoExoticSixSphere.SmoothSlabCylinderCollarControl

/-!
# The same constructed smooth annulus is immersive at both original ends

The retained original collar derivatives and their proved injectivity
give actual ambient boundary immersion. The existence theorem keeps
the same smoothed map, exact original endpoint values, protected collars,
and strict-time interior values. Interior immersion is not asserted.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem.DegreeCollapse

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredCylinderExtension p f₀ f₁) (b : NoExoticSixSphere.Sphere p)

theorem boundary_immersive_of_original_collars (k : ℕ) (hd : m = n + k)
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁))
    (hi₀ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₀) q))
    (hi₁ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₁) q))
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (_hgs : ∀ x ∈ SphereAnnulus.domain p,
        ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x)
      (_hgeq : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val)
      (q : NoExoticSixSphere.Sphere p),
      Injective (fderiv ℝ
        ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun ∘ g)
          q.val) ∧
      Injective (fderiv ℝ
        ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun ∘ g)
          ((2 : ℝ) • q.val)) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  intro hgs hgeq q
  let L := EuclideanProduct.coordinates (m + 1)
  constructor
  · rw [fderiv_left_of_original_collar D b k hd hf₀ h₀ g hgs hgeq q]
    have he := (L.hasFDerivAt.comp q.val
      ((contDiff_leftCollar D b hf₀).differentiable (by simp) q.val).hasFDerivAt).fderiv
    rw [he]
    exact L.injective.comp (injective_fderiv_leftCollar D b hf₀ hi₀ q)
  · rw [fderiv_right_of_original_collar D b k hd hf₁ h₁ g hgs hgeq q]
    have he := (L.hasFDerivAt.comp ((2 : ℝ) • q.val)
      ((contDiff_rightCollar D b hf₁).differentiable
        (by simp) ((2 : ℝ) • q.val)).hasFDerivAt).fderiv
    rw [he]
    exact L.injective.comp (injective_fderiv_rightCollar D b hf₁ hi₁ q)

theorem exists_smooth_with_immersive_boundary (k : ℕ) (hd : m = n + k)
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁))
    (hi₀ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₀) q))
    (hi₁ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₁) q))
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    ∃ g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
      (∀ x ∈ SphereAnnulus.domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x) ∧
      (∀ q : NoExoticSixSphere.Sphere p, g q.val = (f₀ q).val) ∧
      (∀ q : NoExoticSixSphere.Sphere p, g ((2 : ℝ) • q.val) = (f₁ q).val) ∧
      (∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val) ∧
      (∀ x : Vector (p + 1), 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t) ∧
      ∀ q : NoExoticSixSphere.Sphere p,
        Injective (fderiv ℝ
          ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun ∘ g)
            q.val) ∧
        Injective (fderiv ℝ
          ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun ∘ g)
            ((2 : ℝ) • q.val)) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  obtain ⟨g, hgs, hg₀, hg₁, hgeq, hgV⟩ :=
    exists_smooth_with_original_collars D b k hd hf₀ hf₁ h₀ h₁
  exact ⟨g, hgs, hg₀, hg₁, hgeq, hgV,
    boundary_immersive_of_original_collars D b k hd hf₀ hf₁ hi₀ hi₁ h₀ h₁ g hgs hgeq⟩

end NoExoticSixSphere.RegularSlabCylinderCollar
