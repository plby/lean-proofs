import Wikipedia.HopfProblem.StandardSixSphereCircleModelBasic

/-!
# The literal equatorial two-sphere

The equator is identified with the ordinary unit sphere in the first three
Euclidean coordinates.  This identifies existing subspace topologies only.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

theorem isClosed_equator : IsClosed equator :=
  isClosed_eq (continuous_normal.comp continuous_subtype_val) continuous_const

theorem equatorAmbient_mem_sphere (v : BaseSphere) : join v.val 0 ∈ Sphere := by
  apply mem_sphere_of_norm_sq
  rw [join_norm_sq, baseSphere_norm, norm_zero, one_pow, zero_pow (by decide), add_zero]

def equatorPoint (v : BaseSphere) : ↥equator :=
  ⟨⟨join v.val 0, equatorAmbient_mem_sphere v⟩, normal_join v.val 0⟩

@[simp] theorem equatorPoint_val_val (v : BaseSphere) :
    (equatorPoint v).val.val = join v.val 0 := rfl

theorem base_norm_of_equator (p : ↥equator) : ‖base p.val.val‖ = 1 := by
  have h := sphere_norm_sq p.val
  have hn : normal p.val.val = 0 := p.property
  rw [hn, norm_zero, zero_pow (by decide), add_zero] at h
  nlinarith [norm_nonneg (base p.val.val)]

def equatorBase (p : ↥equator) : BaseSphere :=
  ⟨base p.val.val, by
    simpa only [Metric.mem_sphere, dist_zero_right] using base_norm_of_equator p⟩

@[simp] theorem equatorBase_val (p : ↥equator) :
    (equatorBase p).val = base p.val.val := rfl

theorem equatorBase_equatorPoint (v : BaseSphere) : equatorBase (equatorPoint v) = v := by
  apply Subtype.ext
  exact base_join v.val 0

theorem equatorPoint_equatorBase (p : ↥equator) : equatorPoint (equatorBase p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  have hn : normal p.val.val = 0 := p.property
  change join (base p.val.val) 0 = p.val.val
  rw [← hn, join_base_normal]

theorem continuous_equatorPoint : Continuous equatorPoint := by
  have h : Continuous (fun v : BaseSphere => join v.val 0) :=
    Continuous.comp (g := fun q : Base × Normal => join q.1 q.2)
      (f := fun v : BaseSphere => (v.val, 0)) continuous_join
      (continuous_subtype_val.prodMk continuous_const)
  exact (h.subtype_mk _).subtype_mk _

theorem continuous_equatorBase : Continuous equatorBase :=
  (continuous_base.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- The standard `S²` parametrizes the actual equator by `v ↦ (v,0)`. -/
def equatorHomeomorph : BaseSphere ≃ₜ ↥equator where
  toFun := equatorPoint
  invFun := equatorBase
  left_inv := equatorBase_equatorPoint
  right_inv := equatorPoint_equatorBase
  continuous_toFun := continuous_equatorPoint
  continuous_invFun := continuous_equatorBase

@[simp] theorem equatorHomeomorph_apply (v : BaseSphere) :
    (equatorHomeomorph v).val.val = join v.val 0 := rfl

@[simp] theorem equatorHomeomorph_symm_apply (p : ↥equator) :
    (equatorHomeomorph.symm p).val = base p.val.val := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
