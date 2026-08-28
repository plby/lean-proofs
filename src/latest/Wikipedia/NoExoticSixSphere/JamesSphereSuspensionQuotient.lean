import Wikipedia.NoExoticSixSphere.JamesSphereExcursions

/-!
# The actual sphere-loop evaluation is a suspension quotient

The one-dimensional clock identifies only the interval endpoints. The
product-compactification evaluation is surjective and hence a quotient
map. Its interior time slices are closed embeddings, and an individual
nonconstant generator separates distinct interior times.
-/

noncomputable section

open Set Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere

namespace OnePointProduct

theorem map_left_coe_injective {E F : Type*} (x : E) :
    Function.Injective (fun y : OnePoint F ↦ map ((x : OnePoint E), y)) := by
  intro y z h
  change map ((x : OnePoint E), y) = map ((x : OnePoint E), z) at h
  induction y using OnePoint.rec with
  | infty =>
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z =>
      rw [map_infty_right, map_coe] at h
      exact False.elim (OnePoint.coe_ne_infty (x, z) h.symm)
  | coe y =>
    induction z using OnePoint.rec with
    | infty =>
      rw [map_coe, map_infty_right] at h
      exact False.elim (OnePoint.coe_ne_infty (x, y) h)
    | coe z =>
      rw [map_coe, map_coe] at h
      exact congrArg (fun a : F ↦ (a : OnePoint F))
        (congrArg Prod.snd (OnePoint.coe_injective h))

end OnePointProduct

namespace JamesSphere

theorem clock_eq_iff (s t : I) :
    CubicalProductSuspension.clock s = CubicalProductSuspension.clock t ↔
      s = t ∨ (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
  change (euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ : Fin 1 ↦ s)) =
    (euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ : Fin 1 ↦ t)) ↔ _
  rw [(euclideanOnePointSphere 1).symm.injective.eq_iff, SmoothCube.quotient_eq_iff]
  constructor
  · rintro (he | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
    · exact Or.inl (congrFun he 0)
    · exact Or.inr ⟨hi, hj⟩
  · rintro (rfl | ⟨hs, ht⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨0, hs⟩, ⟨0, ht⟩⟩

theorem clock_surjective : Function.Surjective CubicalProductSuspension.clock := by
  intro y
  obtain ⟨u, hu⟩ := SmoothCube.quotient_surjective (by norm_num : 0 < 1)
    (euclideanOnePointSphere 1 y)
  have he : (fun _ : Fin 1 ↦ u 0) = u := by
    funext i
    exact congrArg u (Subsingleton.elim 0 i)
  refine ⟨u 0, ?_⟩
  change (euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ : Fin 1 ↦ u 0)) = y
  rw [he, hu, Homeomorph.symm_apply_apply]

theorem loopEvaluation_surjective (n : ℕ) : Function.Surjective (loopEvaluation n) := by
  intro y
  obtain ⟨⟨a, v⟩, h⟩ := OnePointProduct.map_surjective
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr.symm
      ((euclideanOnePointSphere (n + 1)).symm y))
  obtain ⟨t, ht⟩ := clock_surjective v
  refine ⟨(euclideanOnePointSphere n a, t), ?_⟩
  change euclideanOnePointSphere (n + 1)
    ((EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm
        (euclideanOnePointSphere n a), CubicalProductSuspension.clock t))) = y
  rw [Homeomorph.symm_apply_apply, ht, h, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

theorem loopEvaluation_isQuotientMap (n : ℕ) : IsQuotientMap (loopEvaluation n) :=
  IsQuotientMap.of_surjective_continuous (loopEvaluation_surjective n)
    (loopEvaluation n).continuous

theorem loopEvaluation_time_injective (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n)
    {s t : I} (hs₀ : 0 < (s : ℝ)) (hs₁ : (s : ℝ) < 1)
    (h : loopEvaluation n (x, s) = loopEvaluation n (x, t)) : s = t := by
  have hx' : (euclideanOnePointSphere n).symm x ≠ OnePoint.infty := by
    intro he
    have he' := congrArg (euclideanOnePointSphere n) he
    rw [Homeomorph.apply_symm_apply, euclideanOnePointSphere_infty] at he'
    exact hx he'
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hx'
  have he := (EuclideanFactorProduct.productCoordinates n 1).onePointCongr.injective
    ((euclideanOnePointSphere (n + 1)).injective h)
  change OnePointProduct.map ((euclideanOnePointSphere n).symm x,
      CubicalProductSuspension.clock s) =
    OnePointProduct.map ((euclideanOnePointSphere n).symm x,
      CubicalProductSuspension.clock t) at he
  rw [← hv] at he
  have hc := (clock_eq_iff s t).mp (OnePointProduct.map_left_coe_injective v he)
  rcases hc with hc | ⟨hc, _⟩
  · exact hc
  · rcases hc with hc | hc
    · have hz := congrArg Subtype.val hc
      change (s : ℝ) = 0 at hz
      linarith
    · have hz := congrArg Subtype.val hc
      change (s : ℝ) = 1 at hz
      linarith

def timeSlice (n : ℕ) (t : I) : C(Sphere n, Sphere (n + 1)) :=
  (loopEvaluation n).comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩

theorem timeSlice_isClosedEmbedding (n : ℕ) (t : I) (ht₀ : 0 < (t : ℝ))
    (ht₁ : (t : ℝ) < 1) : IsClosedEmbedding (timeSlice n t) :=
  (timeSlice n t).continuous.isClosedEmbedding
    (loopEvaluation_injective n t (clock_ne_infty t ht₀ ht₁))

end JamesSphere

end NoExoticSixSphere
