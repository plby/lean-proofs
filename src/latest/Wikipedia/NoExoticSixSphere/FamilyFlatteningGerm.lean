import Wikipedia.NoExoticSixSphere.FamilyFlatteningRegular
import Wikipedia.NoExoticSixSphere.FlatSmoothGerm

/-!
# A nondegenerate flat germ for an actual family

An invertible leading block and a regular zero of the original Schur
residual produce genuine time-preserving source coordinates and a smooth
representative of the flattened germ with nondegenerate vertical derivative.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne SymmetricDifference

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : T → E × ℝ → E × F}

def Data.forward (d : Data f) (q : E × (T × ℝ)) : (T × E) × ℝ :=
  flatOrder.symm (d.coord q)

omit [FiniteDimensional ℝ T] in
theorem Data.forward_mem_target (d : Data f) {q : E × (T × ℝ)}
    (hq : q ∈ d.coord.source) : d.forward q ∈ d.target := by
  change flatOrder (flatOrder.symm (d.coord q)) ∈ d.coord.target
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact d.coord.toOpenPartialHomeomorph.map_source hq

omit [FiniteDimensional ℝ T] in
theorem Data.inverse_forward (d : Data f) {q : E × (T × ℝ)}
    (hq : q ∈ d.coord.source) : d.inverse (d.forward q) = q := by
  change d.coord.symm (flatOrder (flatOrder.symm (d.coord q))) = q
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact d.coord.toOpenPartialHomeomorph.left_inv hq

omit [FiniteDimensional ℝ T] in
theorem Data.forward_apply (d : Data f) (q : E × (T × ℝ)) :
    d.forward q = ((q.2.1, head f q), q.2.2) := by
  unfold Data.forward
  rw [d.coord_apply]
  rfl

theorem exists_flattened_germ (f : T → E × ℝ → E × F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (q : E × (T × ℝ))
    (hq : spatial f q ∈ chart) (hz : residual (spatial f q) = 0)
    (hb : Bijective (fderiv ℝ (fun p ↦ residual (spatial f p)) q)) :
    ∃ d : Data f, q ∈ d.coord.source ∧
      ∃ g : (T × E) × ℝ → F, ContDiff ℝ ∞ g ∧
        g =ᶠ[𝓝 (d.forward q)] d.flattened ∧ vertical g (d.forward q) = 0 ∧
        Bijective (fderiv ℝ (vertical g) (d.forward q)) := by
  obtain ⟨d, hdq⟩ := exists_data f hf q hq
  have hr := d.forward_mem_target hdq
  obtain ⟨g, hg, he, hv, hD⟩ := exists_global_representative d.target.isOpen hr
    (d.contDiffOn_flattened hf)
  refine ⟨d, hdq, g, hg, he, ?_, ?_⟩
  · rw [hv, d.vertical_flattened_eq hf hr, d.inverse_forward hdq]
    exact hz
  · rw [hD]
    apply d.bijective_fderiv_vertical hf hr
    simpa only [d.inverse_forward hdq] using hb

end NoExoticSixSphere.FamilyFlattening
