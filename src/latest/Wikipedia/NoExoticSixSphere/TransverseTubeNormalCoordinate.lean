import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Native transversality gives invertible actual tube-normal coordinates

Use the inverse of a genuine partial diffeomorphism from a sphere-normal
product to the original six-manifold. Its normal projection annihilates
the original core derivative and is surjective. Native transversality
therefore makes its composite with the other sphere's derivative
surjective, hence invertible in dimension three. The resulting local
diffeomorphism is the actual normal coordinate, not a replacement map.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.TubeNormalCoordinates

local notation "V3" => EuclideanSpace ℝ (Fin 3)
local notation "V6" => EuclideanSpace ℝ (Fin 6)

/-- Projection killing one transverse summand is surjective on the other summand. -/
theorem surjective_comp_of_kills_left (A B : V3 →L[ℝ] V6) (N : V6 →L[ℝ] V3)
    (hAB : Surjective (A.coprod B)) (hN : Surjective N) (hNA : N.comp A = 0) :
    Surjective (N.comp B) := by
  intro w
  obtain ⟨v, hv⟩ := hN w
  obtain ⟨⟨a, b⟩, hab⟩ := hAB v
  have hzero : N (A a) = 0 := congrArg (fun L : V3 →L[ℝ] V3 => L a) hNA
  refine ⟨b, ?_⟩
  change N (B b) = w
  calc
    N (B b) = N (A a + B b) := by rw [map_add, hzero, zero_add]
    _ = w := (congrArg N hab).trans hv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V6 M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 3)) (𝓡 6) (Sphere 3 × V3) M ∞)

/-- The actual normal coordinate of the supplied tube inverse. -/
def normal (g : Sphere 3 → M) (x : Sphere 3) : V3 := (Φ.symm (g x)).2

/-- Normal-coordinate smoothness holds on the original inverse-tube domain. -/
theorem contMDiffOn_normal (g : Sphere 3 → M) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (normal Φ g) (g ⁻¹' Φ.target) :=
  contMDiff_snd.comp_contMDiffOn
    (Φ.contMDiffOn_invFun.comp hg.contMDiffOn (fun _ hx => hx))

/-- The differential retains the original inverse-tube derivative and normal projection. -/
theorem mfderiv_normal (g : Sphere 3 → M) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (x : Sphere 3) (hx : g x ∈ Φ.target) :
    mfderiv (𝓡 3) (𝓡 3) (normal Φ g) x =
      ((ContinuousLinearMap.snd ℝ V3 V3).comp
        (mfderiv (𝓡 6) ((𝓡 3).prod (𝓡 3)) Φ.symm (g x))).comp
          (mfderiv (𝓡 3) (𝓡 6) g x) := by
  have hΦ : ContMDiffAt (𝓡 6) ((𝓡 3).prod (𝓡 3)) ∞ Φ.symm (g x) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hx)
  have hcomp := hΦ.comp x hg.contMDiffAt
  have h₁ : (mfderiv (𝓡 3) (𝓡 3) (normal Φ g) x : V3 →L[ℝ] V3) =
      (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 3) Prod.snd (Φ.symm (g x)) :
        (V3 × V3) →L[ℝ] V3).comp
          (mfderiv (𝓡 3) ((𝓡 3).prod (𝓡 3)) (Φ.symm ∘ g) x) :=
    mfderiv_comp x mdifferentiableAt_snd (hcomp.mdifferentiableAt (by simp))
  have h₂ : (mfderiv (𝓡 3) ((𝓡 3).prod (𝓡 3)) (Φ.symm ∘ g) x :
      V3 →L[ℝ] (V3 × V3)) =
      (mfderiv (𝓡 6) ((𝓡 3).prod (𝓡 3)) Φ.symm (g x) : V6 →L[ℝ] (V3 × V3)).comp
        (mfderiv (𝓡 3) (𝓡 6) g x) :=
    mfderiv_comp x (hΦ.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  have hs : (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 3) Prod.snd (Φ.symm (g x)) :
      (V3 × V3) →L[ℝ] V3) = ContinuousLinearMap.snd ℝ V3 V3 := mfderiv_snd
  exact h₁.trans (congrArg₂ (fun (A : (V3 × V3) →L[ℝ] V3)
    (B : V3 →L[ℝ] (V3 × V3)) => A.comp B) hs h₂)

/-- The original core has identically zero normal coordinate near every valid tube point. -/
theorem normal_core_eventually (f : Sphere 3 → M)
    (hcore : ∀ s, Φ (s, 0) = f s) (x : Sphere 3) (hx : (x, 0) ∈ Φ.source) :
    normal Φ f =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : ∀ᶠ s in 𝓝 x, (s, (0 : V3)) ∈ Φ.source :=
    (continuous_id.prodMk continuous_const).continuousAt (Φ.open_source.mem_nhds hx)
  filter_upwards [hn] with s hs
  change (Φ.symm (f s)).2 = 0
  exact congrArg Prod.snd ((congrArg Φ.symm (hcore s).symm).trans (Φ.left_inv hs))

/-- The actual inverse normal projection kills the original core derivative. -/
theorem normal_derivative_kills_core (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hcore : ∀ s, Φ (s, 0) = f s)
    (x : Sphere 3) (hx : (x, 0) ∈ Φ.source) :
    ((ContinuousLinearMap.snd ℝ V3 V3).comp
      (mfderiv (𝓡 6) ((𝓡 3).prod (𝓡 3)) Φ.symm (f x))).comp
        (mfderiv (𝓡 3) (𝓡 6) f x) = 0 := by
  have ht : f x ∈ Φ.target := hcore x ▸ Φ.map_source hx
  rw [← mfderiv_normal Φ f hf x ht, (normal_core_eventually Φ f hcore x hx).mfderiv_eq,
    mfderiv_const]
  rfl

/-- Native transversality makes the actual normal-coordinate derivative surjective. -/
theorem surjective_mfderiv_normal (f g : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hcore : ∀ s, Φ (s, 0) = f s) (x y : Sphere 3) (hx : (x, 0) ∈ Φ.source)
    (hxy : f x = g y)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) g y))) :
    Surjective (mfderiv (𝓡 3) (𝓡 3) (normal Φ g) y) := by
  have htarget : g y ∈ Φ.target := (hcore x).trans hxy ▸ Φ.map_source hx
  have hi : IsLocalDiffeomorphAt (𝓡 6) ((𝓡 3).prod (𝓡 3)) ∞ Φ.symm (g y) :=
    ⟨Φ.symm, htarget, fun _ _ => rfl⟩
  rw [mfderiv_normal Φ g hg y htarget]
  apply surjective_comp_of_kills_left (mfderiv (𝓡 3) (𝓡 6) f x) _ _ ht
  · exact (show Surjective (ContinuousLinearMap.snd ℝ V3 V3) from
      fun v => ⟨(0, v), rfl⟩).comp (hi.mfderivToContinuousLinearEquiv (by simp)).surjective
  · rw [← hxy]
    exact normal_derivative_kills_core Φ f hf hcore x hx

/-- A transverse intersection gives a genuine local diffeomorphism in the normal coordinate. -/
theorem isLocalDiffeomorphAt_normal (f g : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hcore : ∀ s, Φ (s, 0) = f s) (x y : Sphere 3) (hx : (x, 0) ∈ Φ.source)
    (hxy : f x = g y)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) g y))) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (normal Φ g) y := by
  have hs := surjective_mfderiv_normal Φ f g hf hg hcore x y hx hxy ht
  let D : V3 →L[ℝ] V3 := mfderiv (𝓡 3) (𝓡 3) (normal Φ g) y
  have hi : Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hs
  have hinv : D.IsInvertible :=
    ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩
  have htarget : g y ∈ Φ.target := (hcore x).trans hxy ▸ Φ.map_source hx
  exact Wikipedia.SmoothSixDPoincare.isLocalDiffeomorphAt_boundaryless
    (Φ.open_target.preimage hg.continuous) htarget
    (contMDiffOn_normal Φ g hg) hinv

end NoExoticSixSphere.TubeNormalCoordinates
