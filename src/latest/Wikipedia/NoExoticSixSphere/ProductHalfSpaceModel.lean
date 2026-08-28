import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# The standard linear half-space model in real-product coordinates

Use the actual closed half-space `0 ≤ t` in `ℝ × K`, with inclusion as its
model map and the usual continuous clamp as its total inverse. This keeps
regular scalar normal forms in their native coordinates.
-/

noncomputable section

open Set Topology
open scoped Manifold

namespace NoExoticSixSphere.ProductHalfSpace

variable (K : Type*) [NormedAddCommGroup K] [NormedSpace ℝ K]

abbrev Space := {p : ℝ × K // 0 ≤ p.1}

def partialEquiv : PartialEquiv (Space K) (ℝ × K) where
  toFun := Subtype.val
  invFun p := ⟨(max p.1 0, p.2), le_max_right _ _⟩
  source := univ
  target := {p | 0 ≤ p.1}
  map_source' p _ := p.property
  map_target' _ _ := mem_univ _
  left_inv' p _ := Subtype.ext (Prod.ext (max_eq_left p.property) rfl)
  right_inv' _ hp := Prod.ext (max_eq_left hp) rfl

omit [NormedSpace ℝ K] in
theorem interior_halfSpace : interior {p : ℝ × K | 0 ≤ p.1} = {p | 0 < p.1} := by
  change interior ((Prod.fst : ℝ × K → ℝ) ⁻¹' Ici 0) = Prod.fst ⁻¹' Ioi 0
  rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Ici]

def model : ModelWithCorners ℝ (ℝ × K) (Space K) :=
  ModelWithCorners.ofConvexRange (partialEquiv K) rfl
    ((convex_Ici (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ K))
    continuous_subtype_val
    (((continuous_fst.max continuous_const).prodMk continuous_snd).subtype_mk _)
    (by rw [show (partialEquiv K).target = {p : ℝ × K | 0 ≤ p.1} from rfl,
      interior_halfSpace]; exact ⟨(1, 0), by change (0 : ℝ) < 1; exact zero_lt_one⟩)

theorem model_apply (p : Space K) : model K p = p.val := rfl

theorem model_range : range (model K) = {p : ℝ × K | 0 ≤ p.1} := Subtype.range_val

theorem model_symm_val {p : ℝ × K} (hp : 0 ≤ p.1) : ((model K).symm p).val = p :=
  Prod.ext (max_eq_left hp) rfl

theorem model_interior : interior (range (model K)) = {p : ℝ × K | 0 < p.1} := by
  rw [model_range, interior_halfSpace]

end NoExoticSixSphere.ProductHalfSpace
