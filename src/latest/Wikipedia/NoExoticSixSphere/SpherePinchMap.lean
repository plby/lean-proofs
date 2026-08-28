import Wikipedia.NoExoticSixSphere.SphereHemisphereFold
import Wikipedia.NoExoticSixSphere.HemisphereMapGluing

/-!
# A sphere-sum map on the original sphere

Use the actual polynomial fold on each closed hemisphere and glue two maps
that agree at the collapsed equator point. The result is a genuine continuous
map on the original sphere, with exact formulas on both hemispheres.
No homotopy-group addition formula is asserted here.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereFold

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y] (v : UnitSphere E) (f g : C(UnitSphere E, Y))
  (hbase : f (antipode v) = g (antipode v))

include hbase in
theorem exists_pinch : ∃ F : C(UnitSphere E, Y),
    (∀ x : UnitSphere E, 0 ≤ height v x → F x = f (fold v x)) ∧
    (∀ x : UnitSphere E, height v x ≤ 0 → F x = g (fold v x)) := by
  let a : C(ClosedHemisphere v, Y) :=
    (f.comp (foldMap v)).comp ⟨Subtype.val, continuous_subtype_val⟩
  let b : C(ClosedHemisphere (antipode v), Y) :=
    (g.comp (foldMap v)).comp ⟨Subtype.val, continuous_subtype_val⟩
  have hab (x : Equator v) : a (equatorNorth v x) = b (equatorSouth v x) := by
    change f (fold v x.val) = g (fold v x.val)
    rw [(fold_eq_antipode_iff v x.val).mpr x.property, hbase]
  obtain ⟨F, hF, hG⟩ := exists_glued_hemisphereMap v a b hab
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    exact hF ⟨x, hx⟩
  · intro x hx
    have hy : x ∈ closedHemisphere (antipode v) := by
      change 0 ≤ inner ℝ (-(v : E)) (x : E)
      rw [inner_neg_left]
      exact neg_nonneg.mpr hx
    exact hG ⟨x, hy⟩

def pinch : C(UnitSphere E, Y) := (exists_pinch v f g hbase).choose

theorem pinch_north (x : UnitSphere E) (hx : 0 ≤ height v x) :
    pinch v f g hbase x = f (fold v x) := (exists_pinch v f g hbase).choose_spec.1 x hx

theorem pinch_south (x : UnitSphere E) (hx : height v x ≤ 0) :
    pinch v f g hbase x = g (fold v x) := (exists_pinch v f g hbase).choose_spec.2 x hx

theorem pinch_equator (x : UnitSphere E) (hx : height v x = 0) :
    pinch v f g hbase x = f (antipode v) := by
  rw [pinch_north v f g hbase x hx.ge, (fold_eq_antipode_iff v x).mpr hx]

theorem pinch_intersection_off_equator {Z : Type*} (k : Z → Y)
    (hm : f (antipode v) ∉ range k) (x : UnitSphere E) (y : Z)
    (hxy : pinch v f g hbase x = k y) : height v x ≠ 0 := by
  intro hx
  have he := pinch_equator v f g hbase x hx
  exact hm ⟨y, hxy.symm.trans he⟩

end NoExoticSixSphere.SphereFold
