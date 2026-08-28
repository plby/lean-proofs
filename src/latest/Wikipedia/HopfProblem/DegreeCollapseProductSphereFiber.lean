import Wikipedia.HopfProblem.DegreeCollapseSmashFiberProduct

/-!
# Non-basepoint fibers of the original product sphere suspension

The zero real-coordinate slice is an actual embedding of the old sphere.
The original product suspension commutes with this slice exactly.
Over a non-basepoint sliced value, the whole fiber lies in that slice,
so its homeomorphism with the old fiber retains the actual inclusion.
No replacement suspension map is introduced.
-/

noncomputable section

open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.DegreeCollapse.ProductSphereFiber

open NoExoticSixSphere SphereComposition CubicalSphereSuspension
open SuspensionProductComparison JamesSphere

theorem productSphereHomeomorph_infty (n : ℕ) :
    productSphereHomeomorph n ∞ = spherePole (n + 1) :=
  euclideanOnePointSphere_infty (n + 1)

def slice (n : ℕ) : C(Sphere n, Sphere (n + 1)) :=
  ⟨fun x ↦ productSphereHomeomorph n
    (OnePointProduct.map ((euclideanOnePointSphere n).symm x, (↑(0 : ℝ) : OnePoint ℝ))),
    (productSphereHomeomorph n).continuous.comp
      (OnePointProduct.continuous_map.comp
        ((euclideanOnePointSphere n).symm.continuous.prodMk continuous_const))⟩

theorem slice_pole (n : ℕ) : slice n (spherePole n) = spherePole (n + 1) := by
  change productSphereHomeomorph n
    (OnePointProduct.map ((euclideanOnePointSphere n).symm (spherePole n), ↑(0 : ℝ))) = _
  rw [inverseSphere_pole, OnePointProduct.map_infty_left, productSphereHomeomorph_infty]

theorem slice_eq_pole_iff (n : ℕ) (x : Sphere n) :
    slice n x = spherePole (n + 1) ↔ x = spherePole n := by
  change productSphereHomeomorph n
    (OnePointProduct.map ((euclideanOnePointSphere n).symm x, ↑(0 : ℝ))) = _ ↔ _
  rw [← productSphereHomeomorph_infty, (productSphereHomeomorph n).injective.eq_iff,
    OnePointProduct.map_eq_infty_iff, sphere_coordinates_eq_infty_iff]
  simp only [OnePoint.coe_ne_infty, or_false]

theorem slice_injective (n : ℕ) : Function.Injective (slice n) := by
  intro x y h
  by_cases hx : x = spherePole n
  · have hy : slice n y = spherePole (n + 1) :=
      h.symm.trans ((congrArg (slice n) hx).trans (slice_pole n))
    exact hx.trans ((slice_eq_pole_iff n y).mp hy).symm
  · have he := (productSphereHomeomorph n).injective h
    change OnePointProduct.map
      ((euclideanOnePointSphere n).symm x, (↑(0 : ℝ) : OnePoint ℝ)) =
      OnePointProduct.map
        ((euclideanOnePointSphere n).symm y, (↑(0 : ℝ) : OnePoint ℝ)) at he
    rw [euclideanOnePointSphere_symm_of_ne n hx, OnePointProduct.map_coe] at he
    have hy := (OnePointProduct.map_eq_coe_iff _ (sphereProjection n x, (0 : ℝ))).mp he.symm
    exact (euclideanOnePointSphere n).symm.injective
      ((euclideanOnePointSphere_symm_of_ne n hx).trans hy.1.symm)

variable {m n : ℕ} (f : Based m n)

theorem product_formula (p : OnePoint (EuclideanSpace ℝ (Fin m)) × OnePoint ℝ) :
    (productBasedMap f).val (productSphereHomeomorph m (OnePointProduct.map p)) =
      productSphereHomeomorph n (OnePointProduct.map (compactMap f p.1, p.2)) := by
  change productSphereHomeomorph n
    (OnePointProduct.productMap (compactMap f) (ContinuousMap.id (OnePoint ℝ))
      (compactMap_infty f) (ContinuousMap.id_apply ∞) ((productSphereHomeomorph m).symm
        (productSphereHomeomorph m (OnePointProduct.map p)))) = _
  rw [Homeomorph.symm_apply_apply, OnePointProduct.productMap_apply]
  rfl

theorem product_slice (x : Sphere m) : (productBasedMap f).val (slice m x) = slice n (f.val x) := by
  change (productBasedMap f).val (productSphereHomeomorph m
    (OnePointProduct.map ((euclideanOnePointSphere m).symm x, (↑(0 : ℝ) : OnePoint ℝ)))) = _
  rw [product_formula]
  change productSphereHomeomorph n (OnePointProduct.map
    ((euclideanOnePointSphere n).symm
      (f.val (euclideanOnePointSphere m ((euclideanOnePointSphere m).symm x))), ↑(0 : ℝ))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

variable (b : Sphere n)

theorem fiberMap_mem (x : SmashFiberProduct.Fiber f b) :
    (productBasedMap f).val (slice m x.val) = slice n b := by
  rw [product_slice, x.property]

def fiberMap : C(SmashFiberProduct.Fiber f b,
    SmashFiberProduct.Fiber (productBasedMap f) (slice n b)) :=
  ⟨fun x ↦ ⟨slice m x.val, fiberMap_mem f b x⟩,
    ((slice m).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem fiberMap_bijective (hb : b ≠ spherePole n) : Function.Bijective (fiberMap f b) := by
  constructor
  · intro x y h
    exact Subtype.ext (slice_injective m (congrArg Subtype.val h))
  · intro y
    obtain ⟨p, hp⟩ := OnePointProduct.map_surjective ((productSphereHomeomorph m).symm y.val)
    have hy : productSphereHomeomorph m (OnePointProduct.map p) = y.val :=
      (congrArg (productSphereHomeomorph m) hp).trans
        ((productSphereHomeomorph m).apply_symm_apply y.val)
    have hm : OnePointProduct.map (compactMap f p.1, p.2) =
        OnePointProduct.map ((euclideanOnePointSphere n).symm b, ↑(0 : ℝ)) :=
      (productSphereHomeomorph n).injective
        ((product_formula f p).symm.trans
          ((congrArg (productBasedMap f).val hy).trans y.property))
    rw [euclideanOnePointSphere_symm_of_ne n hb, OnePointProduct.map_coe] at hm
    have hparts := (OnePointProduct.map_eq_coe_iff _ (sphereProjection n b, (0 : ℝ))).mp hm
    have hf : f.val (euclideanOnePointSphere m p.1) = b := by
      apply (euclideanOnePointSphere n).symm.injective
      change compactMap f p.1 = (euclideanOnePointSphere n).symm b
      exact hparts.1.trans (euclideanOnePointSphere_symm_of_ne n hb).symm
    refine ⟨⟨euclideanOnePointSphere m p.1, hf⟩, ?_⟩
    apply Subtype.ext
    change productSphereHomeomorph m (OnePointProduct.map
      ((euclideanOnePointSphere m).symm (euclideanOnePointSphere m p.1), ↑(0 : ℝ))) = y.val
    rw [Homeomorph.symm_apply_apply, ← hparts.2]
    exact hy

def fiberHomeomorph (hb : b ≠ spherePole n) :
    SmashFiberProduct.Fiber f b ≃ₜ
      SmashFiberProduct.Fiber (productBasedMap f) (slice n b) := by
  let : CompactSpace (SmashFiberProduct.Fiber f b) :=
    isCompact_iff_compactSpace.mp ((isClosed_singleton.preimage f.val.continuous).isCompact)
  let e := Equiv.ofBijective (fiberMap f b) (fiberMap_bijective f b hb)
  exact e.toHomeomorphOfContinuousClosed (fiberMap f b).continuous
    (fiberMap f b).continuous.isClosedMap

theorem fiberHomeomorph_val (hb : b ≠ spherePole n) (x : SmashFiberProduct.Fiber f b) :
    (fiberHomeomorph f b hb x).val = slice m x.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ProductSphereFiber
