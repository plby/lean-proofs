import Wikipedia.HopfProblem.DegreeCollapseCuspStraightening
import Wikipedia.HopfProblem.DegreeCollapseSupportedCuspImmersion

/-!
# A genuine compact modification of the standard three-plane

Conjugate the supported cusp by the constructed source and ambient
diffeomorphisms. The initial map is exactly the standard plane, every slice
agrees with it off one compact source set, and the endpoint has one actual
double point. Insertion into an arbitrary manifold patch is a separate step.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization WhitneyCusp

def longMap (β : Cutoff) (t : ℝ) (x : Vector 3) : Vector 6 :=
  targetDiffeomorph (map β.value t (sourceDiffeomorph.symm x))

def longSupport (β : Cutoff) : Set (Vector 3) := sourceDiffeomorph '' tsupport β.value

theorem isCompact_longSupport (β : Cutoff) : IsCompact (longSupport β) :=
  β.compact.isCompact.image sourceDiffeomorph.continuous

theorem contDiff_longMap (β : Cutoff) : ContDiff ℝ ∞ (uncurry (longMap β)) := by
  have hS : ContDiff ℝ ∞ (fun p : ℝ × Vector 3 ↦ (p.1, sourceDiffeomorph.symm p.2)) :=
    contDiff_fst.prodMk (sourceDiffeomorph.symm.contMDiff.contDiff.comp contDiff_snd)
  exact targetDiffeomorph.contMDiff.contDiff.comp ((contDiff_map β.smooth).comp hS)

theorem longMap_neg_one (β : Cutoff) (x : Vector 3) : longMap β (-1) x = plane x := by
  change targetDiffeomorph (map β.value (-1) (sourceDiffeomorph.symm x)) = plane x
  rw [map_neg_one, straighten_base, sourceDiffeomorph.apply_symm_apply]

theorem longMap_eq_plane_off_support (β : Cutoff) (t : ℝ) {x : Vector 3}
    (hx : x ∉ longSupport β) : longMap β t x = plane x := by
  have hu : sourceDiffeomorph.symm x ∉ tsupport β.value := by
    intro hu
    exact hx ⟨sourceDiffeomorph.symm x, hu, sourceDiffeomorph.apply_symm_apply x⟩
  change targetDiffeomorph (map β.value t (sourceDiffeomorph.symm x)) = plane x
  rw [map_eq_base_off_support β.value t hu, straighten_base, sourceDiffeomorph.apply_symm_apply]

theorem injective_fderiv_longMap (β : Cutoff) {t : ℝ} (ht : t ≠ 0) (x : Vector 3) :
    Injective (fderiv ℝ (longMap β t) x) := by
  let F : Vector 3 → Vector 6 := map β.value t
  let S : Vector 3 → Vector 3 := sourceDiffeomorph.symm
  let T : Vector 6 → Vector 6 := targetDiffeomorph
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_map β.smooth).comp
      (show ContDiff ℝ ∞ (fun y : Vector 3 ↦ (t, y)) from contDiff_const.prodMk contDiff_id)
  have hS : ContDiff ℝ ∞ S := sourceDiffeomorph.symm.contMDiff.contDiff
  have hT : ContDiff ℝ ∞ T := targetDiffeomorph.contMDiff.contDiff
  have hSi : Injective (fderiv ℝ S x) := by
    have h := (sourceDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x).injective
    change Injective (mfderiv 𝓘(ℝ, Vector 3) 𝓘(ℝ, Vector 3) sourceDiffeomorph.symm x) at h
    rwa [mfderiv_eq_fderiv] at h
  have hTi : Injective (fderiv ℝ T (F (S x))) := by
    have h := (targetDiffeomorph.mfderivToContinuousLinearEquiv (by simp) (F (S x))).injective
    change Injective (mfderiv 𝓘(ℝ, Vector 6) 𝓘(ℝ, Vector 6) targetDiffeomorph (F (S x))) at h
    rwa [mfderiv_eq_fderiv] at h
  have hFd := hF.differentiable (by simp) (S x)
  have hSd := hS.differentiable (by simp) x
  have hTd := hT.differentiable (by simp) (F (S x))
  change Injective (fderiv ℝ (T ∘ (F ∘ S)) x)
  rw [fderiv_comp x hTd (hFd.comp x hSd), fderiv_comp x hFd hSd]
  exact hTi.comp ((injective_fderiv_of_parameter_ne_zero β ht (S x)).comp hSi)

theorem longMap_endpoint_eq_iff (β : Cutoff) (x y : Vector 3) :
    longMap β 1 x = longMap β 1 y ↔ x = y ∨
      (x = sourceDiffeomorph (axis 1) ∧ y = sourceDiffeomorph (axis (-1))) ∨
      (x = sourceDiffeomorph (axis (-1)) ∧ y = sourceDiffeomorph (axis 1)) := by
  constructor
  · intro h
    have h' : map β.value 1 (sourceDiffeomorph.symm x) =
        map β.value 1 (sourceDiffeomorph.symm y) := targetDiffeomorph.injective h
    rcases (endpoint_map_eq_iff β _ _).mp h' with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl (sourceDiffeomorph.symm.injective hxy)
    · right
      left
      exact ⟨(sourceDiffeomorph.apply_symm_apply x).symm.trans (congrArg sourceDiffeomorph hx),
        (sourceDiffeomorph.apply_symm_apply y).symm.trans (congrArg sourceDiffeomorph hy)⟩
    · right
      right
      exact ⟨(sourceDiffeomorph.apply_symm_apply x).symm.trans (congrArg sourceDiffeomorph hx),
        (sourceDiffeomorph.apply_symm_apply y).symm.trans (congrArg sourceDiffeomorph hy)⟩
  · have hc : longMap β 1 (sourceDiffeomorph (axis 1)) =
        longMap β 1 (sourceDiffeomorph (axis (-1))) := by
      change targetDiffeomorph
          (map β.value 1 (sourceDiffeomorph.symm (sourceDiffeomorph (axis 1)))) =
        targetDiffeomorph (map β.value 1 (sourceDiffeomorph.symm (sourceDiffeomorph (axis (-1)))))
      rw [sourceDiffeomorph.symm_apply_apply, sourceDiffeomorph.symm_apply_apply, axis_crossing]
    rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hc
    · exact hc.symm

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
