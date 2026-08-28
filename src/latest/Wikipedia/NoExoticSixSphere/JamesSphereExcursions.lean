import Wikipedia.NoExoticSixSphere.JamesSphereLoopMap
import Wikipedia.NoExoticSixSphere.MooreFreeExcursions

/-!
# The concrete sphere generators are distinct loop excursions

The clock reaches infinity only at the two interval endpoints. A non-pole
letter therefore makes exactly one positive-duration excursion. Evaluating
at any interior clock value recovers the sphere letter. These properties
will give separation of the actual James space through its Moore-loop map.
-/

noncomputable section

open scoped unitInterval OnePoint

namespace NoExoticSixSphere

namespace OnePointProduct

variable {E F : Type*}

theorem map_right_coe_injective (y : F) :
    Function.Injective (fun x : OnePoint E ↦ map (x, (y : OnePoint F))) := by
  intro x z h
  change map (x, (y : OnePoint F)) = map (z, (y : OnePoint F)) at h
  induction x using OnePoint.rec with
  | infty =>
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z =>
      rw [map_infty_left, map_coe] at h
      exact False.elim (OnePoint.coe_ne_infty (z, y) h.symm)
  | coe x =>
    induction z using OnePoint.rec with
    | infty =>
      rw [map_coe, map_infty_left] at h
      exact False.elim (OnePoint.coe_ne_infty (x, y) h)
    | coe z =>
      rw [map_coe, map_coe] at h
      exact congrArg (fun a : E ↦ (a : OnePoint E))
        (congrArg Prod.fst (OnePoint.coe_injective h))

end OnePointProduct

namespace JamesSphere

theorem clock_ne_infty (t : I) (h₀ : 0 < (t : ℝ)) (h₁ : (t : ℝ) < 1) :
    CubicalProductSuspension.clock t ≠ OnePoint.infty := by
  intro h
  have he := congrArg (euclideanOnePointSphere 1) h
  change euclideanOnePointSphere 1
    ((euclideanOnePointSphere 1).symm (SmoothCube.quotient 1 (fun _ : Fin 1 ↦ t))) = _ at he
  rw [Homeomorph.apply_symm_apply, euclideanOnePointSphere_infty] at he
  obtain ⟨i, hi⟩ := (SmoothCube.quotient_eq_pole_iff 1 (fun _ : Fin 1 ↦ t)).mp he
  rcases hi with hi | hi
  · have hz : (t : ℝ) = 0 := congrArg Subtype.val hi
    linarith
  · have hz : (t : ℝ) = 1 := congrArg Subtype.val hi
    linarith

theorem loopEvaluation_ne_pole (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n)
    (t : I) (h₀ : 0 < (t : ℝ)) (h₁ : (t : ℝ) < 1) :
    loopEvaluation n (x, t) ≠ spherePole (n + 1) := by
  intro h
  rw [← euclideanOnePointSphere_infty (n + 1)] at h
  have he := (euclideanOnePointSphere (n + 1)).injective h
  have he' : (EuclideanFactorProduct.productCoordinates n 1).onePointCongr
      (OnePointProduct.map ((euclideanOnePointSphere n).symm x,
        CubicalProductSuspension.clock t)) =
      (EuclideanFactorProduct.productCoordinates n 1).onePointCongr OnePoint.infty := by
    simpa using he
  have hm := (EuclideanFactorProduct.productCoordinates n 1).onePointCongr.injective he'
  rcases (OnePointProduct.map_eq_infty_iff _).mp hm with hl | hr
  · have he := congrArg (euclideanOnePointSphere n) hl
    rw [Homeomorph.apply_symm_apply, euclideanOnePointSphere_infty] at he
    exact hx he
  · exact clock_ne_infty t h₀ h₁ hr

theorem loopEvaluation_injective (n : ℕ) (t : I)
    (ht : CubicalProductSuspension.clock t ≠ OnePoint.infty) :
    Function.Injective (fun x : Sphere n ↦ loopEvaluation n (x, t)) := by
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp ht
  intro x y h
  have he := (euclideanOnePointSphere (n + 1)).injective h
  have hm := (EuclideanFactorProduct.productCoordinates n 1).onePointCongr.injective he
  change OnePointProduct.map ((euclideanOnePointSphere n).symm x,
      CubicalProductSuspension.clock t) =
    OnePointProduct.map ((euclideanOnePointSphere n).symm y,
      CubicalProductSuspension.clock t) at hm
  rw [← hv] at hm
  exact (euclideanOnePointSphere n).symm.injective
    (OnePointProduct.map_right_coe_injective v hm)

theorem unitLoop_injective (n : ℕ) : Function.Injective (unitLoop n) := by
  let t : I := ⟨1 / 2, by constructor <;> norm_num⟩
  have ht : CubicalProductSuspension.clock t ≠ OnePoint.infty :=
    clock_ne_infty t (by norm_num [t]) (by norm_num [t])
  intro x y h
  apply loopEvaluation_injective n t ht
  exact congrArg (fun p : Path (spherePole (n + 1)) (spherePole (n + 1)) ↦ p t) h

theorem mooreGenerator_injective (n : ℕ) : Function.Injective (mooreGenerator n) := by
  intro x y h
  apply unitLoop_injective n
  have he := congrArg Moore.Loop.toPath h
  simpa only [toPath_mooreGenerator] using he

theorem mooreGenerator_isExcursion (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    Moore.Loop.IsExcursion (mooreGenerator n x) := by
  have hd : 0 < dist x (spherePole n) := dist_pos.mpr hx
  refine ⟨hd, ?_⟩
  intro t ht htd
  change t < dist x (spherePole n) at htd
  have h₀ : 0 < t / dist x (spherePole n) := div_pos ht hd
  have h₁ : t / dist x (spherePole n) < 1 :=
    (div_lt_iff₀ hd).mpr (by simpa only [one_mul] using htd)
  let s : I := ⟨t / dist x (spherePole n), le_of_lt h₀, le_of_lt h₁⟩
  change (unitLoop n x).extend (t / dist x (spherePole n)) ≠ spherePole (n + 1)
  rw [(unitLoop n x).extend_apply
    (show t / dist x (spherePole n) ∈ Set.Icc (0 : ℝ) 1 from s.property)]
  exact loopEvaluation_ne_pole n hx s h₀ h₁

end JamesSphere

end NoExoticSixSphere
