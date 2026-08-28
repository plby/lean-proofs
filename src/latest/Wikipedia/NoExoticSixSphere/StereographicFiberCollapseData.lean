import Wikipedia.NoExoticSixSphere.StereographicFiberFrame
import Wikipedia.NoExoticSixSphere.StereographicFiberCompactMap
import Wikipedia.NoExoticSixSphere.LocalSphereCollapse
import Wikipedia.NoExoticSixSphere.IteratedSphereHomotopyEquivalence

/-!
# Framed collapse data retaining the original regular sphere map

The compactified original map, its exact regular equations, and their
induced frame satisfy every field of `FramedCollapseData`. The sphere map
of these data is the original map conjugated by explicit homeomorphisms.
Their inverse homotopies preserve nullity at every finite suspension stage.
No identification with a separately chosen tubular collapse is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

open SpherePoleCompactification

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n))
  (hf : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x))
  (a : Sphere (n + k)) (ha : f a = -b)

def framedCoordinates : EuclideanSpace ℝ (Fin (n + k)) →
    EuclideanSpace ℝ (Fin (n + k - k)) :=
  (normalCoordinates n k).symm.toContinuousLinearMap ∘ coordinates f b a

include hf in
theorem framedCoordinates_derivative {y : EuclideanSpace ℝ (Fin (n + k))}
    (hy : y ∈ neighborhood f b a) :
    fderiv ℝ (framedCoordinates f b a) y =
      (normalCoordinates n k).symm.toContinuousLinearMap.comp
        (fderiv ℝ (coordinates f b a) y) := by
  have hc := ((contDiffOn_coordinates f hf b a).contDiffAt
    ((isOpen_neighborhood f hf b a).mem_nhds hy)).differentiableAt (by simp)
  rw [framedCoordinates, fderiv_comp y
    (normalCoordinates n k).symm.toContinuousLinearMap.differentiableAt hc,
    ContinuousLinearMap.fderiv]

def framedCompactMap :
    C(OnePoint (EuclideanSpace ℝ (Fin (n + k))),
      OnePoint (EuclideanSpace ℝ (Fin (n + k - k)))) :=
  ((normalCoordinates n k).symm.toHomeomorph.onePointCongr : C(_, _)).comp (compactMap f b a)

include ha in
theorem framedCompactMap_zero_iff (z : OnePoint (EuclideanSpace ℝ (Fin (n + k)))) :
    framedCompactMap f b a z = ((0 : EuclideanSpace ℝ (Fin (n + k - k))) : OnePoint _) ↔
      ∃ x : {x : Sphere (n + k) // f x = b}, (inclusion f b a x : OnePoint _) = z := by
  let Q := (normalCoordinates n k).symm.toHomeomorph.onePointCongr
  have hz : Q ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) =
      ((0 : EuclideanSpace ℝ (Fin (n + k - k))) : OnePoint _) := by
    change (((normalCoordinates n k).symm 0 : EuclideanSpace ℝ (Fin (n + k - k))) :
      OnePoint (EuclideanSpace ℝ (Fin (n + k - k)))) = _
    rw [map_zero]
  change Q (compactMap f b a z) = _ ↔ _
  rw [← hz, Q.injective.eq_iff, compactMap_zero_iff f b a ha]

def collapseData :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (embedding f hf b hreg a ha).FramedCollapseData (frame f hf b hreg a ha) := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  exact {
    radius := 1
    radius_pos := zero_lt_one
    neighborhood := neighborhood f b a
    open_neighborhood := isOpen_neighborhood f hf b a
    range_subset := by
      rintro _ ⟨x, rfl⟩
      exact inclusion_mem_neighborhood f b hreg a ha x
    coordinates := framedCoordinates f b a
    smooth_coordinates :=
      (normalCoordinates n k).symm.toContinuousLinearMap.contDiff.comp_contDiffOn
        (contDiffOn_coordinates f hf b a)
    surjective_differential := by
      intro y hy
      change EuclideanSpace ℝ (Fin (n + k)) at y
      change Surjective (fderiv ℝ (framedCoordinates f b a) y)
      rw [framedCoordinates_derivative f hf b a hy]
      exact (normalCoordinates n k).symm.surjective.comp
        (surjective_fderiv_coordinates f hf b a hy)
    differential_frame := by
      intro x v
      rw [one_smul]
      change fderiv ℝ (framedCoordinates f b a) (inclusion f b a x)
        ((frame f hf b hreg a ha).ambient x v) = v
      rw [framedCoordinates_derivative f hf b a (inclusion_mem_neighborhood f b hreg a ha x)]
      change (normalCoordinates n k).symm (fderiv ℝ (coordinates f b a) (inclusion f b a x)
        ((frame f hf b hreg a ha).ambient x v)) = v
      exact (congrArg (normalCoordinates n k).symm
        (fderiv_coordinates_frame f hf b hreg a ha x v)).trans
          ((normalCoordinates n k).symm_apply_apply v)
    map := framedCompactMap f b a
    map_infty := by
      change (normalCoordinates n k).symm.toHomeomorph.onePointCongr
        (compactMap f b a OnePoint.infty) = OnePoint.infty
      rw [compactMap_infty f b a ha]
      rfl
    zero_fiber := framedCompactMap_zero_iff f b a ha
    local_formula := by
      intro y hy
      change EuclideanSpace ℝ (Fin (n + k)) at y
      change (normalCoordinates n k).symm.toHomeomorph.onePointCongr
        (compactMap f b a (y : OnePoint (EuclideanSpace ℝ (Fin (n + k))))) = _
      rw [compactMap_local_formula f b a hy]
      rfl }

def sourceChange {m : ℕ} (a : Sphere m) : Sphere m ≃ₜ Sphere m :=
  (homeomorph a).symm.trans (euclideanOnePointSphere m)

def targetChange : Sphere n ≃ₜ Sphere (n + k - k) :=
  ((homeomorph (-b)).symm.trans (normalCoordinates n k).symm.toHomeomorph.onePointCongr).trans
    (euclideanOnePointSphere (n + k - k))

theorem collapse_square :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (targetChange (k := k) b).toHomotopyEquiv.toFun.comp f =
      (collapseData f hf b hreg a ha).sphereMap.comp (sourceChange a).toHomotopyEquiv.toFun := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  apply ContinuousMap.ext
  intro y
  change euclideanOnePointSphere (n + k - k)
    ((normalCoordinates n k).symm.toHomeomorph.onePointCongr
      ((homeomorph (-b)).symm (f y))) =
    euclideanOnePointSphere (n + k - k)
      ((normalCoordinates n k).symm.toHomeomorph.onePointCongr ((homeomorph (-b)).symm
        (f (homeomorph a ((euclideanOnePointSphere (n + k)).symm
          (euclideanOnePointSphere (n + k) ((homeomorph a).symm y)))))))
  rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

theorem iterate_collapse_nullhomotopic_iff (r : ℕ) :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (SphereMapSuspension.iterate (collapseData f hf b hreg a ha).sphereMap r).Nullhomotopic ↔
      (SphereMapSuspension.iterate f r).Nullhomotopic := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  exact (SphereMapSuspension.iterate_nullhomotopic_iff_of_equiv_square
    (sourceChange a).toHomotopyEquiv (targetChange (k := k) b).toHomotopyEquiv f
    (collapseData f hf b hreg a ha).sphereMap
    (by
      rw [collapse_square f hf b hreg a ha]
      exact ContinuousMap.Homotopic.refl _) r).symm

end NoExoticSixSphere.StereographicFiber
