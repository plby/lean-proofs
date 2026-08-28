import Wikipedia.NoExoticSixSphere.SphereSuspensionSmooth
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# Suspension retains the actual smooth regular fiber

The equatorial inclusion is a smooth immersion for the existing sphere
atlases. It identifies the old regular fiber with the regular fiber of a
fiber-preserving smooth suspension. The source fiber keeps the atlas defined
by its original map; no smooth structure is transported from the target.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereMapSuspension

theorem contMDiff_equator (k : ℕ) : ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞ (equator k) := by
  have h := (SphereCylinder.contMDiff_point k).comp
    ((contMDiff_const (c := (0 : ℝ))).prodMk (contMDiff_id (I := 𝓡 k)))
  have he : (fun x : Sphere k ↦ SphereCylinder.point k (0, x)) = equator k :=
    funext (cylinder_point_zero k)
  change ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞
    (fun x : Sphere k ↦ SphereCylinder.point k (0, x)) at h
  rwa [he] at h

theorem inverse_equator (k : ℕ) (x : Sphere k) :
    SphereCylinder.inverse k (equator k x) = (0, x) := by
  rw [← cylinder_point_zero, SphereCylinder.inverse_point]

theorem injective_mfderiv_equator (k : ℕ) (x : Sphere k) :
    Function.Injective (mfderiv (𝓡 k) (𝓡 (k + 1)) (equator k) x) := by
  let r : Sphere (k + 1) → Sphere k := fun y ↦ (SphereCylinder.inverse k y).2
  have hr : ContMDiffAt (𝓡 (k + 1)) (𝓡 k) ∞ r (equator k x) :=
    contMDiffAt_snd.comp _ (SphereCylinder.contMDiffAt_inverse k (equator_mem_band k x))
  have he : r ∘ (equator k) = id := by
    funext y
    exact congrArg Prod.snd (inverse_equator k y)
  have hd := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    ((contMDiff_equator k).mdifferentiable (by simp) x)
  rw [he, mfderiv_id] at hd
  intro u v huv
  have hh := congrArg (mfderiv (𝓡 (k + 1)) (𝓡 k) r (equator k x)) huv
  change ((mfderiv (𝓡 (k + 1)) (𝓡 k) r (equator k x)).comp
    (mfderiv (𝓡 k) (𝓡 (k + 1)) (equator k) x)) u =
    ((mfderiv (𝓡 (k + 1)) (𝓡 k) r (equator k x)).comp
    (mfderiv (𝓡 k) (𝓡 (k + 1)) (equator k) x)) v at hh
  rw [← hd] at hh
  exact hh

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (k : ℕ) (hd : m = n + k)
  (g : C(Sphere (m + 1), Sphere (n + 1)))
  (hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g)
  (hgreg : ∀ y, g y = equator n b → Function.Surjective
    (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g y))
  (hgfiber : ∀ y, g y = equator n b ↔ ∃ x : Sphere m, y = equator m x ∧ f x = b)

def fiberDiffeomorph :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd)
    letI := regularFiberAtlas g hg (equator n b) hgreg k (by
      simp only [finrank_euclideanSpace_fin]; omega)
    {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
      {y : Sphere (m + 1) // g y = equator n b} := by
  let hdf : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + k := by simpa using hd
  let hdg : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + k := by
    simp only [finrank_euclideanSpace_fin]
    omega
  let := regularFiberAtlas f hf b hreg k hdf
  let := regularFiber_isManifold f hf b hreg k hdf
  let e : {x : Sphere m // f x = b} → Sphere (m + 1) := fun x ↦ equator m x.val
  have he : ContMDiff (𝓡 k) (𝓡 (m + 1)) ∞ e :=
    (contMDiff_equator m).comp (regularFiber_contMDiff_subtype_val f hf b hreg k hdf)
  have hei : Function.Injective e := (equator_injective m).comp Subtype.val_injective
  have himm : ∀ x, Function.Injective (mfderiv (𝓡 k) (𝓡 (m + 1)) e x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 k) (𝓡 (m + 1))
      ((equator m) ∘ (Subtype.val : {x : Sphere m // f x = b} → Sphere m)) x)
    rw [mfderiv_comp x ((contMDiff_equator m).mdifferentiable (by simp) x.val)
      ((regularFiber_contMDiff_subtype_val f hf b hreg k hdf).mdifferentiable (by simp) x)]
    exact (injective_mfderiv_equator m x.val).comp
      (regularFiber_injective_mfderiv_subtype_val f hf b hreg k hdf x)
  have heq : ∀ y, g y = equator n b ↔ ∃ x, e x = y := by
    intro y
    rw [hgfiber]
    constructor
    · rintro ⟨x, hy, hx⟩
      exact ⟨⟨x, hx⟩, hy.symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨x.val, hx.symm, x.property⟩
  exact diffeomorphToRegularFiber g hg (equator n b) hgreg k hdg e he hei himm heq

theorem fiberDiffeomorph_val (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd)
    letI := regularFiberAtlas g hg (equator n b) hgreg k (by
      simp only [finrank_euclideanSpace_fin]; omega)
    (fiberDiffeomorph f hf b hreg k hd g hg hgreg hgfiber x).val = equator m x.val := rfl

/-- The smooth representative and its fiber diffeomorphism are both constructed
from the original regular sphere map. No new atlas or fiber equivalence is an input. -/
theorem exists_smooth_suspension_with_fiber :
    ∃ g : C(Sphere (m + 1), Sphere (n + 1)),
      ∃ hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g,
      ∃ hgreg : ∀ y, g y = equator n b → Function.Surjective
        (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g y),
      (map f).Homotopic g ∧
      letI := regularFiberAtlas f hf b hreg k (by simpa using hd)
      letI := regularFiberAtlas g hg (equator n b) hgreg k (by
        simp only [finrank_euclideanSpace_fin]; omega)
      ∃ D : {x : Sphere m // f x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯
          {y : Sphere (m + 1) // g y = equator n b},
        ∀ x, (D x).val = equator m x.val := by
  obtain ⟨g, hg, H, hfiber, hgreg, _⟩ := exists_smooth_regular_suspension f hf b hreg
  exact ⟨g, hg, hgreg, H, fiberDiffeomorph f hf b hreg k hd g hg hgreg hfiber,
    fiberDiffeomorph_val f hf b hreg k hd g hg hgreg hfiber⟩

end NoExoticSixSphere.SphereMapSuspension
