import Wikipedia.HopfProblem.DegreeCollapseHyperbolicPairCorrection

/-!
# An actual cyclic-kernel quadratic reduction splits off a hyperbolic plane

Given a hyperbolic pair and an onto map from its first orthogonal kernel
whose kernel is precisely the first vector's line, construct explicit
coordinates on the whole space. The first coordinate is the supplied
quotient map after projection; the other two are the original polar
coordinates. Their inverse is proved by correction of an actual lift.
Quadratic compatibility makes this a bundled isometry, without a
nondegeneracy or finite-dimensionality hypothesis.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction

open NoExoticSixSphere.Arf

variable {V W : Type*} [AddCommGroup V] [Module F₂ V] [AddCommGroup W] [Module F₂ W]
  (q : QuadraticForm F₂ V) (B : V →ₗ[F₂] V →ₗ[F₂] F₂) (hB : q.polarBilin = B)
  (a b : V) (ha : q a = 0) (hb : q b = 0) (hab : B a b = 1)
  (F : LinearMap.ker (B a) →ₗ[F₂] W)
  (hFker : LinearMap.ker F = Submodule.span F₂ {leftInKernel q B hB a ha})

include hFker in
theorem left_maps_zero : F (leftInKernel q B hB a ha) = 0 := by
  change leftInKernel q B hB a ha ∈ LinearMap.ker F
  rw [hFker]
  exact Submodule.subset_span (mem_singleton _)

def splitMap : V →ₗ[F₂] W × (F₂ × F₂) :=
  (F.comp (projection B a b hab)).prod ((B b).prod (B a))

theorem splitMap_apply (x : V) :
    splitMap B a b hab F x = (F (projection B a b hab x), (B b x, B a x)) := rfl

include hB ha hb hFker in
theorem splitMap_eq_zero (x : V) (hx : splitMap B a b hab F x = 0) : x = 0 := by
  have hF : F (projection B a b hab x) = 0 := congrArg Prod.fst hx
  have hbx : B b x = 0 := congrArg (fun v : W × (F₂ × F₂) ↦ v.2.1) hx
  have hax : B a x = 0 := congrArg (fun v : W × (F₂ × F₂) ↦ v.2.2) hx
  have hp : (projection B a b hab x).val = x := by
    rw [projection_val, hax, zero_smul, sub_zero]
  have hs : projection B a b hab x ∈ Submodule.span F₂ {leftInKernel q B hB a ha} := by
    rw [← hFker]
    exact hF
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hs
  have hba : B b a = 1 := (symmetric q B hB b a).trans hab
  have hkzero : k = 0 := by
    have hc := congrArg (fun v : LinearMap.ker (B a) ↦ B b v.val) hk
    change B b (k • a) = B b (projection B a b hab x).val at hc
    rw [map_smul, hba, smul_eq_mul, mul_one,
      right_coordinate_projection q B hB a b hb hab, hbx] at hc
    exact hc
  rw [hkzero, zero_smul] at hk
  exact hp.symm.trans (congrArg Subtype.val hk.symm)

include hB ha hb hFker in
theorem splitMap_injective : Injective (splitMap B a b hab F) := by
  intro x y hxy
  have hz : splitMap B a b hab F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (splitMap_eq_zero q B hB a b ha hb hab F hFker (x - y) hz)

include hB ha hb hFker in
theorem splitMap_adjusted (x : LinearMap.ker (B a)) (s t : F₂) :
    splitMap B a b hab F (x.val + (s - B b x.val) • a + t • b) = (F x, (s, t)) := by
  have hpa : projection B a b hab a = leftInKernel q B hB a ha :=
    projection_fixed B a b hab (leftInKernel q B hB a ha)
  have hp : projection B a b hab (x.val + (s - B b x.val) • a + t • b) =
      x + (s - B b x.val) • leftInKernel q B hB a ha := by
    rw [map_add, map_add, map_smul, map_smul, projection_fixed, hpa, projection_right,
      smul_zero, add_zero]
  have hba : B b a = 1 := (symmetric q B hB b a).trans hab
  rw [splitMap_apply]
  apply Prod.ext
  · rw [hp, map_add, map_smul, left_maps_zero q B hB a ha F hFker, smul_zero, add_zero]
  · apply Prod.ext
    · change B b (x.val + (s - B b x.val) • a + t • b) = s
      rw [map_add, map_add, map_smul, map_smul, hba, self_zero q B hB b hb]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
      ring
    · change B a (x.val + (s - B b x.val) • a + t • b) = t
      rw [map_add, map_add, map_smul, map_smul,
        show B a x.val = 0 from x.property, self_zero q B hB a ha, hab]
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add]

include hB ha hb hFker in
theorem splitMap_surjective (hF : Surjective F) : Surjective (splitMap B a b hab F) := by
  rintro ⟨w, s, t⟩
  obtain ⟨x, hx⟩ := hF w
  exact ⟨x.val + (s - B b x.val) • a + t • b,
    (splitMap_adjusted q B hB a b ha hb hab F hFker x s t).trans (congrArg (fun v ↦ (v, (s, t))) hx)⟩

variable (q' : QuadraticForm F₂ W) (hquad : ∀ x : LinearMap.ker (B a), q' (F x) = q x.val)

include hB hb hquad in
theorem splitMap_quadratic (x : V) :
    (q'.prod hyperbolicPlane) (splitMap B a b hab F x) = q x := by
  change q' (F (projection B a b hab x)) + plane 0 0 (B b x, B a x) = q x
  rw [hquad, projection_quadratic q B hB a b hb hab, plane_apply]
  simp only [zero_mul, zero_add, add_zero]
  ring

def splitIsometry (hF : Surjective F) : q.IsometryEquiv (q'.prod hyperbolicPlane) where
  toLinearEquiv := LinearEquiv.ofBijective (splitMap B a b hab F)
    ⟨splitMap_injective q B hB a b ha hb hab F hFker,
      splitMap_surjective q B hB a b ha hb hab F hFker hF⟩
  map_app' := splitMap_quadratic q B hB a b hb hab F q' hquad

end Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction
