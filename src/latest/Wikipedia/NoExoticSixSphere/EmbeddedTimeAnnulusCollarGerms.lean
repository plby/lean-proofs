import Wikipedia.NoExoticSixSphere.EmbeddedTimeSphereCollar
import Wikipedia.NoExoticSixSphere.SphereCollarInversion

/-!
# The actual two annulus boundary germs

Compose the original inward gradient collar with unit inversion at the
inner sphere, and with half scaling at the outer sphere. Both original
boundary maps are retained. Their embedded differentials are injective;
the radial time derivative is positive at radius one and negative at
radius two. All manifold structures are the original native structures.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

namespace SphereAnnulus

def halfCoordinates (p : ℕ) : Vector (p + 1) ≃L[ℝ] Vector (p + 1) :=
  (LinearEquiv.smulOfNeZero ℝ (Vector (p + 1)) (1 / 2) (by norm_num)).toContinuousLinearEquiv

theorem halfCoordinates_apply {p : ℕ} (x : Vector (p + 1)) :
    halfCoordinates p x = (1 / 2 : ℝ) • x := rfl

theorem halfCoordinates_double {p : ℕ} (x : Vector (p + 1)) :
    halfCoordinates p ((2 : ℝ) • x) = x := by
  rw [halfCoordinates_apply, smul_smul]
  norm_num

theorem norm_halfCoordinates {p : ℕ} (x : Vector (p + 1)) :
    ‖halfCoordinates p x‖ = ‖x‖ / 2 := by
  rw [halfCoordinates_apply, norm_smul]
  norm_num
  ring

end SphereAnnulus

namespace EmbeddedTime

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

def innerAnnulusCollar (b : Sphere p) (f : Sphere p → {x : M // t x = 0}) :
    Vector (p + 1) → M := sphereCollar e r t b f ∘ SphereCollarInversion.map

def outerAnnulusCollar (b : Sphere p) (f : Sphere p → {x : M // t x = 0}) :
    Vector (p + 1) → M := sphereCollar e r t b f ∘ SphereAnnulus.halfCoordinates p

theorem innerAnnulusCollar_coe (b : Sphere p) (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) : innerAnnulusCollar e r t b f s.val = (f s).val := by
  change sphereCollar e r t b f (SphereCollarInversion.map s.val) = _
  rw [SphereCollarInversion.map_coe, sphereCollar_coe]

theorem outerAnnulusCollar_double (b : Sphere p) (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) : outerAnnulusCollar e r t b f ((2 : ℝ) • s.val) = (f s).val := by
  change sphereCollar e r t b f (SphereAnnulus.halfCoordinates p ((2 : ℝ) • s.val)) = _
  rw [SphereAnnulus.halfCoordinates_double, sphereCollar_coe]

theorem contMDiffAt_innerAnnulusCollar_coe (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (innerAnnulusCollar e r t b f) s.val := by
  let := zeroAtlas t ht hreg
  intro hf
  have hs : s.val ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ClosedHemisphere.unit_norm]
    exact one_ne_zero)
  have hg : ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (sphereCollar e r t b f)
      (SphereCollarInversion.map s.val) := by
    rw [SphereCollarInversion.map_coe]
    exact contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  exact hg.comp s.val (SphereCollarInversion.contDiffAt_map hs).contMDiffAt

theorem contMDiffAt_outerAnnulusCollar_double (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (outerAnnulusCollar e r t b f)
        ((2 : ℝ) • s.val) := by
  let := zeroAtlas t ht hreg
  intro hf
  have hg : ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (sphereCollar e r t b f)
      (SphereAnnulus.halfCoordinates p ((2 : ℝ) • s.val)) := by
    rw [SphereAnnulus.halfCoordinates_double]
    exact contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  exact hg.comp _ (SphereAnnulus.halfCoordinates p).contDiff.contMDiff.contMDiffAt

theorem injective_fderiv_innerAnnulusCollar_coe (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → (∀ q, Injective (mfderiv (𝓡 p) (𝓡 n) f q)) →
      Injective (fderiv ℝ (e.toFun ∘ innerAnnulusCollar e r t b f) s.val) := by
  let := zeroAtlas t ht hreg
  intro hf hd
  have hs : s.val ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ClosedHemisphere.unit_norm]
    exact one_ne_zero)
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hE : DifferentiableAt ℝ (e.toFun ∘ sphereCollar e r t b f)
      (SphereCollarInversion.map s.val) := by
    rw [SphereCollarInversion.map_coe]
    exact (e.smooth.contMDiffAt.comp s.val hg).contDiffAt.differentiableAt (by simp)
  have hI := (SphereCollarInversion.contDiffAt_map hs).differentiableAt (by simp)
  have hD := (hE.hasFDerivAt.comp s.val hI.hasFDerivAt).fderiv
  rw [SphereCollarInversion.map_coe] at hD
  change Injective (fderiv ℝ ((e.toFun ∘ sphereCollar e r t b f) ∘
    SphereCollarInversion.map) s.val)
  rw [hD, fderiv_embedded_sphereCollar_coe e r t ht hreg b f s hf]
  exact (injective_fderiv_sphereCollarAmbient_coe e r t ht hreg b f s hf hd).comp
    (SphereCollarInversion.injective_fderiv_map hs)

theorem injective_fderiv_outerAnnulusCollar_double (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → (∀ q, Injective (mfderiv (𝓡 p) (𝓡 n) f q)) →
      Injective (fderiv ℝ (e.toFun ∘ outerAnnulusCollar e r t b f)
        ((2 : ℝ) • s.val)) := by
  let := zeroAtlas t ht hreg
  intro hf hd
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hE : DifferentiableAt ℝ (e.toFun ∘ sphereCollar e r t b f)
      (SphereAnnulus.halfCoordinates p ((2 : ℝ) • s.val)) := by
    rw [SphereAnnulus.halfCoordinates_double]
    exact (e.smooth.contMDiffAt.comp s.val hg).contDiffAt.differentiableAt (by simp)
  have hD := (hE.hasFDerivAt.comp ((2 : ℝ) • s.val)
    (SphereAnnulus.halfCoordinates p).hasFDerivAt).fderiv
  rw [SphereAnnulus.halfCoordinates_double] at hD
  change Injective (fderiv ℝ ((e.toFun ∘ sphereCollar e r t b f) ∘
    SphereAnnulus.halfCoordinates p) ((2 : ℝ) • s.val))
  rw [hD, fderiv_embedded_sphereCollar_coe e r t ht hreg b f s hf]
  exact (injective_fderiv_sphereCollarAmbient_coe e r t ht hreg b f s hf hd).comp
    (SphereAnnulus.halfCoordinates p).injective

theorem fderiv_time_innerAnnulusCollar_radial_pos (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      0 < fderiv ℝ (t ∘ innerAnnulusCollar e r t b f) s.val s.val := by
  let := zeroAtlas t ht hreg
  intro hf
  have hs : s.val ≠ 0 := norm_ne_zero_iff.mp (by
    rw [ClosedHemisphere.unit_norm]
    exact one_ne_zero)
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hT : DifferentiableAt ℝ (t ∘ sphereCollar e r t b f)
      (SphereCollarInversion.map s.val) := by
    rw [SphereCollarInversion.map_coe]
    exact (ht.contMDiffAt.comp s.val hg).contDiffAt.differentiableAt (by simp)
  have hI := (SphereCollarInversion.contDiffAt_map hs).differentiableAt (by simp)
  have hD := (hT.hasFDerivAt.comp s.val hI.hasFDerivAt).fderiv
  rw [SphereCollarInversion.map_coe] at hD
  change 0 < fderiv ℝ ((t ∘ sphereCollar e r t b f) ∘ SphereCollarInversion.map) s.val s.val
  rw [hD]
  change 0 < fderiv ℝ (t ∘ sphereCollar e r t b f) s.val
    (fderiv ℝ SphereCollarInversion.map s.val s.val)
  rw [SphereCollarInversion.fderiv_map_radial, map_neg]
  exact neg_pos.mpr (fderiv_time_sphereCollar_radial_neg e r t ht hreg b f s hf)

theorem fderiv_time_outerAnnulusCollar_radial_neg (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      fderiv ℝ (t ∘ outerAnnulusCollar e r t b f) ((2 : ℝ) • s.val)
        ((2 : ℝ) • s.val) < 0 := by
  let := zeroAtlas t ht hreg
  intro hf
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hT : DifferentiableAt ℝ (t ∘ sphereCollar e r t b f)
      (SphereAnnulus.halfCoordinates p ((2 : ℝ) • s.val)) := by
    rw [SphereAnnulus.halfCoordinates_double]
    exact (ht.contMDiffAt.comp s.val hg).contDiffAt.differentiableAt (by simp)
  have hD := (hT.hasFDerivAt.comp ((2 : ℝ) • s.val)
    (SphereAnnulus.halfCoordinates p).hasFDerivAt).fderiv
  rw [SphereAnnulus.halfCoordinates_double] at hD
  change fderiv ℝ ((t ∘ sphereCollar e r t b f) ∘ SphereAnnulus.halfCoordinates p)
    ((2 : ℝ) • s.val) ((2 : ℝ) • s.val) < 0
  rw [hD]
  change fderiv ℝ (t ∘ sphereCollar e r t b f) s.val
    (SphereAnnulus.halfCoordinates p ((2 : ℝ) • s.val)) < 0
  rw [SphereAnnulus.halfCoordinates_double]
  exact fderiv_time_sphereCollar_radial_neg e r t ht hreg b f s hf

end EmbeddedTime
end NoExoticSixSphere
