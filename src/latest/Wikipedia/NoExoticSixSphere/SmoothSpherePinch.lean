import Wikipedia.NoExoticSixSphere.SpherePinchMap
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# Smoothness of the actual sphere-sum map

Away from the equator the map equals one of its two smooth fold composites
on a neighborhood. If both input maps are constant with the same value on
a neighborhood of the collapsed pole, the glued map is locally constant
near the equator. This proves smoothness in the original sphere atlas.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFold

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y] (v : UnitSphere E) (f g : C(UnitSphere E, Y))
  (hbase : f (antipode v) = g (antipode v))

theorem pinch_eventuallyEq_north (x : UnitSphere E) (hx : 0 < height v x) :
    (pinch v f g hbase : UnitSphere E → Y) =ᶠ[𝓝 x] fun y ↦ f (fold v y) := by
  have hopen : IsOpen {y : UnitSphere E | 0 < height v y} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact pinch_north v f g hbase y hy.le

theorem pinch_eventuallyEq_south (x : UnitSphere E) (hx : height v x < 0) :
    (pinch v f g hbase : UnitSphere E → Y) =ᶠ[𝓝 x] fun y ↦ g (fold v y) := by
  have hopen : IsOpen {y : UnitSphere E | height v y < 0} :=
    isOpen_lt (continuous_const.inner continuous_subtype_val) continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact pinch_south v f g hbase y hy.le

theorem pinch_eventuallyEq_const (m : Y) {U : Set (UnitSphere E)}
    (hU : IsOpen U) (hv : antipode v ∈ U) (hf : EqOn f (fun _ ↦ m) U)
    (hg : EqOn g (fun _ ↦ m) U) (x : UnitSphere E) (hx : height v x = 0) :
    (pinch v f g hbase : UnitSphere E → Y) =ᶠ[𝓝 x] fun _ ↦ m := by
  have hfx : fold v x ∈ U := (fold_eq_antipode_iff v x).mpr hx ▸ hv
  filter_upwards [(hU.preimage (continuous_fold v)).mem_nhds hfx] with y hy
  by_cases h : 0 ≤ height v y
  · rw [pinch_north v f g hbase y h]
    exact hf hy
  · rw [pinch_south v f g hbase y (lt_of_not_ge h).le]
    exact hg hy

end NoExoticSixSphere.SphereFold

namespace NoExoticSixSphere.SphereFold

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem contMDiff_pinch (v : Sphere 3) (f g : C(Sphere 3, M))
    (hbase : f (antipode v) = g (antipode v))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (m : M) {U : Set (Sphere 3)} (hU : IsOpen U) (hv : antipode v ∈ U)
    (hfU : EqOn f (fun _ ↦ m) U) (hgU : EqOn g (fun _ ↦ m) U) :
    ContMDiff (𝓡 3) (𝓡 6) ∞ (pinch v f g hbase) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  intro x
  rcases lt_trichotomy (height v x) 0 with hx | hx | hx
  · exact ((hg.comp (contMDiff_fold (n := 3) v)).contMDiffAt).congr_of_eventuallyEq
      (pinch_eventuallyEq_south v f g hbase x hx)
  · exact (contMDiff_const (I := 𝓡 3) (I' := 𝓡 6) (c := m)).contMDiffAt.congr_of_eventuallyEq
      (pinch_eventuallyEq_const v f g hbase m hU hv hfU hgU x hx)
  · exact ((hf.comp (contMDiff_fold (n := 3) v)).contMDiffAt).congr_of_eventuallyEq
      (pinch_eventuallyEq_north v f g hbase x hx)

end NoExoticSixSphere.SphereFold
