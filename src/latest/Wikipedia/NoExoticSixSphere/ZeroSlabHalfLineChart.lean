import Wikipedia.NoExoticSixSphere.SphereIntersectionTrace

/-!
# Half-line coordinates on the actual zero slice of a closed time slab

The model is the genuine subset `{(v,t) | v = 0, 0 ≤ t ≤ 1}` with its
subtype topology. Projection to time is a homeomorphism with the unit
interval. Restricting below its upper end gives an explicit half-line chart.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.ZeroSlab

open InvolutionQuotient

variable (F : Type*) [TopologicalSpace F] [Zero F]

def model : Set (F × ℝ) := {q | q.1 = 0 ∧ q.2 ∈ Icc 0 1}

def timeHomeomorph : model F ≃ₜ unitInterval where
  toFun q := ⟨q.val.2, q.property.2⟩
  invFun t := ⟨(0, t.val), rfl, t.property⟩
  left_inv q := Subtype.ext (Prod.ext q.property.1.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.snd.subtype_mk _
  continuous_invFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

def initialIntervalChart : OpenPartialHomeomorph unitInterval HalfLine where
  toFun t := ⟨t.val, t.property.1⟩
  invFun v := ⟨min v.val 1, ⟨le_min v.property zero_le_one, min_le_right _ _⟩⟩
  source := {t | t.val < 1}
  target := {v | v.val < 1}
  map_source' _ ht := ht
  map_target' v hv := (min_le_left v.val 1).trans_lt hv
  left_inv' t _ := Subtype.ext (min_eq_left t.property.2)
  right_inv' v hv := Subtype.ext (min_eq_left hv.le)
  open_source := isOpen_lt continuous_subtype_val continuous_const
  open_target := isOpen_lt continuous_subtype_val continuous_const
  continuousOn_toFun := (continuous_subtype_val.subtype_mk _).continuousOn
  continuousOn_invFun := ((continuous_subtype_val.min continuous_const).subtype_mk _).continuousOn

def initialChart : OpenPartialHomeomorph (model F) HalfLine :=
  (timeHomeomorph F).toOpenPartialHomeomorph.trans initialIntervalChart

theorem initialChart_apply (q : model F) : (initialChart F q).val = q.val.2 := rfl

theorem initialChart_mem_source (q : model F) :
    q ∈ (initialChart F).source ↔ q.val.2 < 1 := by
  change (q ∈ (univ : Set (model F)) ∧ q.val.2 < 1) ↔ _
  simp only [mem_univ, true_and]

end NoExoticSixSphere.ZeroSlab
