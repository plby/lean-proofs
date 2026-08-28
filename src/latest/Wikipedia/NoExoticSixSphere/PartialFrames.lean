import Wikipedia.NoExoticSixSphere.OrthogonalGroupOperations
import Wikipedia.NoExoticSixSphere.ColumnCoordinates

/-!
# Actual spaces of partial orthonormal frames

`Stiefel.Space n r` is the space of norm-preserving real linear operators
from `ℝʳ` to `ℝⁿ`, with the operator-norm subspace topology. It is the genuine
space of ordered orthonormal `r`-frames, not a group assigned by its expected
homotopy type. Orthogonal operators act by postcomposition on all columns.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

abbrev Space (n r : ℕ) :=
  {A : Vector r →L[ℝ] Vector n // ∀ x, ‖A x‖ = ‖x‖}

def ofIsometry {n r : ℕ} (a : Vector r →ₗᵢ[ℝ] Vector n) : Space n r :=
  ⟨a.toContinuousLinearMap, a.norm_map⟩

def toIsometry {n r : ℕ} (a : Space n r) : Vector r →ₗᵢ[ℝ] Vector n where
  toLinearMap := a.val.toLinearMap
  norm_map' := a.property

@[simp] theorem toIsometry_apply {n r : ℕ} (a : Space n r) (x : Vector r) :
    toIsometry a x = a.val x := rfl

@[simp] theorem ofIsometry_toIsometry {n r : ℕ} (a : Space n r) :
    ofIsometry (toIsometry a) = a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem injective {n r : ℕ} (a : Space n r) : Function.Injective a.val :=
  (toIsometry a).injective

theorem dimension_le {n r : ℕ} (a : Space n r) : r ≤ n := by
  simpa only [finrank_euclideanSpace_fin] using
    LinearMap.finrank_le_finrank_of_injective (injective a)

def empty (n : ℕ) : Space n 0 :=
  ⟨0, fun x ↦ by rw [Subsingleton.elim x 0]; simp⟩

instance subsingleton_zero (n : ℕ) : Subsingleton (Space n 0) := by
  refine ⟨fun a b ↦ ?_⟩
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rw [Subsingleton.elim x 0, map_zero, map_zero]

def comp {p n r : ℕ} (a : Space p n) (b : Space n r) : Space p r :=
  ⟨a.val.comp b.val, fun x ↦ (a.property (b.val x)).trans (b.property x)⟩

@[simp] theorem comp_apply {p n r : ℕ} (a : Space p n) (b : Space n r) (x : Vector r) :
    (comp a b).val x = a.val (b.val x) := rfl

def action {n r : ℕ} (g : OrthogonalOperators n) (a : Space n r) : Space n r :=
  ⟨g.val.val.comp a.val, fun x ↦ (g.property (a.val x)).trans (a.property x)⟩

@[simp] theorem action_apply {n r : ℕ} (g : OrthogonalOperators n) (a : Space n r)
    (x : Vector r) : (action g a).val x = g.val.val (a.val x) := rfl

@[simp] theorem action_identity {n r : ℕ} (a : Space n r) :
    action (OrthogonalPaths.identity n) a = a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem action_mul {n r : ℕ} (g h : OrthogonalOperators n) (a : Space n r) :
    action (OrthogonalPaths.mul g h) a = action g (action h a) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {X : Type*} [TopologicalSpace X]

theorem continuous_comp {p n r : ℕ} (a : X → Space p n) (b : X → Space n r)
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x ↦ comp (a x) (b x)) :=
  ((continuous_subtype_val.comp ha).clm_comp (continuous_subtype_val.comp hb)).subtype_mk _

theorem continuous_action {n r : ℕ} (g : X → OrthogonalOperators n) (a : X → Space n r)
    (hg : Continuous g) (ha : Continuous a) : Continuous (fun x ↦ action (g x) (a x)) :=
  ((continuous_subtype_val.comp (continuous_subtype_val.comp hg)).clm_comp
    (continuous_subtype_val.comp ha)).subtype_mk _

def column {n r : ℕ} (v : UnitSphere (Vector r)) : C(Space n r, UnitSphere (Vector n)) where
  toFun a := ⟨a.val v.val, by
    simpa only [Metric.mem_sphere, dist_zero_right, a.property] using
      ClosedHemisphere.unit_norm v⟩
  continuous_toFun := (continuous_subtype_val.clm_apply continuous_const).subtype_mk _

@[simp] theorem column_apply {n r : ℕ} (v : UnitSphere (Vector r)) (a : Space n r) :
    (column v a).val = a.val v.val := rfl

end NoExoticSixSphere.Stiefel
