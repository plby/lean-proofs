import Wikipedia.NoExoticSixSphere.StereographicFiberEquations

/-!
# The original sphere map in its actual source and target compactifications

The compactified map is exactly the original map conjugated by the two
stereographic homeomorphisms. Its finite zero fiber is the original regular
fiber's chart embedding. Its local finite formula is the original system
of equations; no separately chosen collapse map is substituted.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.StereographicFiber

open SpherePoleCompactification

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n)) (b : Sphere n)
  (a : Sphere (n + k)) (ha : f a = -b)

def compactMap :
    C(OnePoint (EuclideanSpace ℝ (Fin (n + k))), OnePoint (EuclideanSpace ℝ (Fin n))) :=
  ⟨fun z ↦ (homeomorph (-b)).symm (f (homeomorph a z)),
    (homeomorph (-b)).symm.continuous.comp (f.continuous.comp (homeomorph a).continuous)⟩

include ha in
theorem compactMap_infty : compactMap f b a OnePoint.infty = OnePoint.infty := by
  change (homeomorph (-b)).symm (f (homeomorph a OnePoint.infty)) = _
  rw [homeomorph_infty, ha]
  apply (homeomorph (-b)).injective
  rw [Homeomorph.apply_symm_apply, homeomorph_infty]

include ha in
theorem compactMap_zero_iff (z : OnePoint (EuclideanSpace ℝ (Fin (n + k)))) :
    compactMap f b a z = ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) ↔
      ∃ x : {x : Sphere (n + k) // f x = b}, (inclusion f b a x : OnePoint _) = z := by
  have ht : homeomorph (-b) ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) = b := by
    rw [homeomorph_zero, neg_neg]
  constructor
  · intro h
    have hz : f (homeomorph a z) = b := by
      have H := congrArg (homeomorph (-b)) h
      change homeomorph (-b) ((homeomorph (-b)).symm (f (homeomorph a z))) = _ at H
      simpa only [Homeomorph.apply_symm_apply, ht] using H
    let x : {x : Sphere (n + k) // f x = b} := ⟨homeomorph a z, hz⟩
    refine ⟨x, ?_⟩
    have hx := homeomorph_symm_of_ne a (fiber_ne_pole f b a ha x)
    exact hx.symm.trans ((homeomorph a).symm_apply_apply z)
  · rintro ⟨x, rfl⟩
    change (homeomorph (-b)).symm (f (homeomorph a (inclusion f b a x : OnePoint _))) = _
    rw [homeomorph_coe]
    change (homeomorph (-b)).symm (finiteMap f a (inclusion f b a x)) = _
    rw [finiteMap_inclusion f b a ha]
    apply (homeomorph (-b)).injective
    rw [Homeomorph.apply_symm_apply, ht]

theorem compactMap_local_formula {y : EuclideanSpace ℝ (Fin (n + k))}
    (hy : y ∈ neighborhood f b a) :
    compactMap f b a (y : OnePoint _) = (coordinates f b a y : OnePoint _) := by
  change (homeomorph (-b)).symm (f (homeomorph a (y : OnePoint _))) = _
  rw [homeomorph_coe]
  exact homeomorph_symm_of_ne (-b) hy.1

end NoExoticSixSphere.StereographicFiber
