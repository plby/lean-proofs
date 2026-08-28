import Wikipedia.NoExoticSixSphere.SmoothRegularSlabCylinder
import Wikipedia.NoExoticSixSphere.RegularSlabCylinderCollarInjectivity
import Wikipedia.NoExoticSixSphere.AnnulusDerivativeUniqueness

/-!
# The original collar derivatives and injectivity survive annulus smoothing

Within-derivative uniqueness on the actual closed annulus identifies the
ordinary ambient derivative at each endpoint sphere with the prescribed
original collar derivative. Equality outside the annulus is not assumed.
The exact retained values also preserve injectivity on both protected
collars, using the actual sphere-cylinder coordinate homeomorphism.
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

theorem fderiv_left_of_original_collar (k : ℕ) (hd : m = n + k)
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀))
    (h₀ : ∀ q, (f₀ q).val.val.1 = s)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (_hgs : ∀ x ∈ SphereAnnulus.domain p,
        ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x)
      (_hgeq : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val)
      (q : NoExoticSixSphere.Sphere p),
      fderiv ℝ ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun
          ∘ g) q.val =
        fderiv ℝ (EuclideanProduct.coordinates (m + 1) ∘ leftCollar D b) q.val := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  intro hgs hgeq q
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
  let L := EuclideanProduct.coordinates (m + 1)
  have hq : q.val ∈ SphereAnnulus.domain p := by
    constructor <;> rw [ClosedHemisphere.unit_norm] <;> norm_num
  have hdiff : DifferentiableAt ℝ (e.toFun ∘ g) q.val :=
    ((e.smooth.contMDiffAt.comp q.val (hgs q.val hq)).contDiffAt).differentiableAt (by simp)
  have hH := L.contDiff.comp (contDiff_leftCollar D b hf₀)
  apply SphereAnnulus.fderiv_eq_of_inner_collar (e.toFun ∘ g) (L ∘ leftCollar D b) (9 / 8)
    (fun y hy hyr ↦ ?_) hq (by rw [ClosedHemisphere.unit_norm]; norm_num)
    hdiff (hH.differentiable (by simp) q.val)
  rw [comp_apply, hgeq ⟨y, hy⟩ (Or.inl hyr)]
  change L (ambient D b ⟨y, hy⟩) = L (leftCollar D b y)
  rw [ambient_eq_leftCollar D b h₀ ⟨y, hy⟩ (by change ‖y‖ ≤ 4 / 3; linarith)]

theorem fderiv_right_of_original_collar (k : ℕ) (hd : m = n + k)
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁))
    (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd)
    ∀ (_hgs : ∀ x ∈ SphereAnnulus.domain p,
        ContMDiffAt (𝓡 (p + 1)) (𝓡 (k + 1)) ∞ g x)
      (_hgeq : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val)
      (q : NoExoticSixSphere.Sphere p),
      fderiv ℝ ((RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd).toFun
          ∘ g) ((2 : ℝ) • q.val) =
        fderiv ℝ (EuclideanProduct.coordinates (m + 1) ∘ rightCollar D b) ((2 : ℝ) • q.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  intro hgs hgeq q
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map k hd
  let L := EuclideanProduct.coordinates (m + 1)
  have hn : ‖(2 : ℝ) • q.val‖ = 2 := by
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num
  have hq : (2 : ℝ) • q.val ∈ SphereAnnulus.domain p := by
    constructor <;> rw [hn] <;> norm_num
  have hdiff : DifferentiableAt ℝ (e.toFun ∘ g) ((2 : ℝ) • q.val) :=
    ((e.smooth.contMDiffAt.comp _ (hgs _ hq)).contDiffAt).differentiableAt (by simp)
  have hH := L.contDiff.comp (contDiff_rightCollar D b hf₁)
  apply SphereAnnulus.fderiv_eq_of_outer_collar (e.toFun ∘ g) (L ∘ rightCollar D b) (15 / 8)
    (fun y hy hyr ↦ ?_) hq (by rw [hn]; norm_num)
    hdiff (hH.differentiable (by simp) ((2 : ℝ) • q.val))
  rw [comp_apply, hgeq ⟨y, hy⟩ (Or.inr hyr)]
  change L (ambient D b ⟨y, hy⟩) = L (rightCollar D b y)
  rw [ambient_eq_rightCollar D b h₁ ⟨y, hy⟩ (by change 7 / 4 ≤ ‖y‖; linarith)]

theorem injOn_original_annulus_collars
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (hf₀ : Injective f₀) (hf₁ : Injective f₁)
    (g : Vector (p + 1) → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z})
    (hgeq : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
      g x.val = (D.map (SphereAnnulus.toCylinder b x)).val) :
    Set.InjOn g {x : Vector (p + 1) | x ∈ SphereAnnulus.domain p ∧
      (‖x‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x‖)} := by
  intro x hx y hy he
  have htime (v : SphereAnnulus.domain p) (hv : ‖v.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖v.val‖) :
      ((SphereAnnulus.toCylinder b v).1 : ℝ) ≤ 1 / 3 ∨
        2 / 3 ≤ ((SphereAnnulus.toCylinder b v).1 : ℝ) := by
    change (SphereAnnulus.time v : ℝ) ≤ 1 / 3 ∨ 2 / 3 ≤ (SphereAnnulus.time v : ℝ)
    have hl := v.property.1
    rcases hv with hv | hv
    · exact Or.inl ((SphereAnnulus.time_le_third_iff v).mpr (by nlinarith))
    · exact Or.inr ((SphereAnnulus.two_thirds_le_time_iff v).mpr (by nlinarith))
  have hm : D.map (SphereAnnulus.toCylinder b ⟨x, hx.1⟩) =
      D.map (SphereAnnulus.toCylinder b ⟨y, hy.1⟩) :=
    Subtype.ext ((hgeq ⟨x, hx.1⟩ hx.2).symm.trans (he.trans (hgeq ⟨y, hy.1⟩ hy.2)))
  have hc := D.injOn_end_collars h₀ h₁ hf₀ hf₁
    (htime ⟨x, hx.1⟩ hx.2) (htime ⟨y, hy.1⟩ hy.2) hm
  have hxy : (⟨x, hx.1⟩ : SphereAnnulus.domain p) = ⟨y, hy.1⟩ :=
    (SphereAnnulus.homeomorph b).injective hc
  exact congrArg Subtype.val hxy

end NoExoticSixSphere.RegularSlabCylinderCollar
