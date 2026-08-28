import Wikipedia.NoExoticSixSphere.SphereSuspensionCylinder
import Wikipedia.NoExoticSixSphere.FiberPreservingSphereSmoothing

/-!
# Smooth suspension preserving an actual regular fiber

The literal suspension is smooth away from its poles. Its derivative is
surjective over an equatorial regular value because in the cylinder charts it
is the product of the identity with the original map. Relative approximation
then smooths the poles without altering a neighborhood of that fiber or
introducing any additional points into it.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereMapSuspension

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f)

include hf

theorem contMDiffAt_map {y : Sphere (m + 1)} (hy : y ∈ SphereCylinder.band m) :
    ContMDiffAt (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ (map f) y := by
  have hp : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun p : ℝ × Sphere m ↦ (p.1, f p.2)) :=
    contMDiff_fst.prodMk (hf.comp contMDiff_snd)
  have hc := (SphereCylinder.contMDiff_point n).contMDiffAt.comp y
    (hp.contMDiffAt.comp y (SphereCylinder.contMDiffAt_inverse m hy))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(SphereCylinder.isOpen_band m).mem_nhds hy] with z hz
  exact map_eq_cylinder f hz

theorem contMDiffOn_map :
    ContMDiffOn (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ (map f) (SphereCylinder.band m) :=
  fun _y hy ↦ (contMDiffAt_map f hf hy).contMDiffWithinAt

theorem surjective_mfderiv_product (p : ℝ × Sphere m)
    (hreg : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f p.2)) :
    Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m))
      ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (Prod.map (id : ℝ → ℝ) f) p) := by
  rw [mfderiv_prodMap mdifferentiableAt_id (hf.mdifferentiable (by simp) p.2), mfderiv_id]
  intro z
  obtain ⟨v, hv⟩ := hreg z.2
  exact ⟨(z.1, v), Prod.ext rfl hv⟩

theorem surjective_mfderiv_map_cylinder (p : ℝ × Sphere m)
    (hreg : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f p.2)) :
    Function.Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1))
      (map f) (SphereCylinder.point m p)) := by
  let P : ℝ × Sphere m → ℝ × Sphere n := Prod.map id f
  have hP : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞ P :=
    contMDiff_id.prodMap hf
  have hloc : IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 (n + 1)) ∞
      (SphereCylinder.point n) (P p) :=
    ⟨SphereCylinder.chart n, mem_univ _, fun _ _ ↦ rfl⟩
  have hs := (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hmap := (contMDiffAt_map f hf (SphereCylinder.tail_point_ne_zero m p)).mdifferentiableAt
    (by simp)
  have he : (map f) ∘ (SphereCylinder.point m) = (SphereCylinder.point n) ∘ P :=
    funext (map_cylinder_point f)
  have hd := mfderiv_comp p hmap ((SphereCylinder.contMDiff_point m).mdifferentiable (by simp) p)
  rw [he, mfderiv_comp p (hloc.mdifferentiableAt (by simp))
    (hP.mdifferentiable (by simp) p)] at hd
  have hsurj := hs.comp (surjective_mfderiv_product f hf p hreg)
  intro v
  obtain ⟨w, hw⟩ := hsurj v
  refine ⟨mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 (m + 1)) (SphereCylinder.point m) p w, ?_⟩
  exact (congrArg (fun L ↦ L w) hd).symm.trans hw

omit hf in
theorem equator_mem_band (k : ℕ) (x : Sphere k) : equator k x ∈ SphereCylinder.band k :=
  (latitude_mem_band_iff k middle x).mpr ⟨middle_ne_zero, middle_ne_one⟩

omit hf in
theorem cylinder_point_zero (k : ℕ) (x : Sphere k) :
    SphereCylinder.point k (0, x) = equator k x := by
  have h := SphereCylinder.point_inverse k (equator k x) (equator_mem_band k x)
  change SphereCylinder.point k (SphereCylinder.inverse k
    (Wikipedia.HopfProblem.SphereHomology.Latitude.point k middle x)) = equator k x at h
  rw [inverse_latitude k middle x middle_ne_zero middle_ne_one] at h
  simpa [Wikipedia.HopfProblem.SphereHomology.Latitude.height, middle] using h

theorem surjective_mfderiv_map_equator (x : Sphere m)
    (hreg : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    Function.Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) (map f) (equator m x)) := by
  rw [← cylinder_point_zero]
  exact surjective_mfderiv_map_cylinder f hf (0, x) hreg

/-- A globally smooth representative of suspension, with the exact old fiber
and its original differential retained near the equator. -/
theorem exists_smooth_regular_suspension (b : Sphere n)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    ∃ g : C(Sphere (m + 1), Sphere (n + 1)),
      ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g ∧ (map f).Homotopic g ∧
      (∀ y, g y = equator n b ↔ ∃ x : Sphere m, y = equator m x ∧ f x = b) ∧
      (∀ y, g y = equator n b → Function.Surjective
        (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1)) g y)) ∧
      ∃ U : Set (Sphere (m + 1)), IsOpen U ∧
        (map f) ⁻¹' {equator n b} ⊆ U ∧ EqOn g (map f) U := by
  have hsub : (map f) ⁻¹' {equator n b} ⊆ SphereCylinder.band m := by
    intro y hy
    obtain ⟨x, rfl, _⟩ := (map_eq_equator_iff f y b).mp hy
    exact equator_mem_band m x
  obtain ⟨g, hg, H, hgf, U, hU, hKU, heq⟩ :=
    exists_smoothSphereRepresentative_preserving_fiber (n + 1) (map f) (equator n b)
      (SphereCylinder.isOpen_band m) (contMDiffOn_map f hf) hsub
  refine ⟨g, hg, H, fun y ↦ (hgf y).trans (map_eq_equator_iff f y b), ?_, U, hU, hKU, heq⟩
  intro y hy
  have hfy := (hgf y).mp hy
  have he : (g : Sphere (m + 1) → Sphere (n + 1)) =ᶠ[𝓝 y] map f := by
    filter_upwards [hU.mem_nhds (hKU hfy)] with z hz
    exact heq hz
  rw [he.mfderiv_eq]
  obtain ⟨x, rfl, hxb⟩ := (map_eq_equator_iff f y b).mp hfy
  exact surjective_mfderiv_map_equator f hf x (hreg x hxb)

end NoExoticSixSphere.SphereMapSuspension
