import Wikipedia.NoExoticSixSphere.SphereCapContraction
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Homotopy.Basic

/-!
# A smooth sphere self-map constant near a chosen pole

Choose a smooth bump inside a sufficiently small spherical cap, and normalize
the straight interpolation toward the pole. The actual map is smooth,
is homotopic to the identity fixing the pole and the complement of the
prescribed neighborhood, and stays in that neighborhood. Outside it the
map agrees with the identity on a neighborhood, not merely pointwise.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCap

open SphereFold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem exists_smooth_localFlattening (v : UnitSphere E) {U : Set (UnitSphere E)}
    (hU : IsOpen U) (hv : v ∈ U) :
    ∃ F : C(UnitSphere E, UnitSphere E),
      ContMDiff (𝓡 n) (𝓡 n) ∞ F ∧
      (ContinuousMap.id (UnitSphere E)).HomotopicRel F (Uᶜ ∪ {v}) ∧
      MapsTo F U U ∧
      (∀ x ∉ U, (F : UnitSphere E → UnitSphere E) =ᶠ[𝓝 x] id) ∧
      ∃ W : Set (UnitSphere E), IsOpen W ∧ v ∈ W ∧ EqOn F (fun _ ↦ v) W := by
  obtain ⟨c, hc, hc1, hcU⟩ := exists_cap_subset v hU hv
  have hopen : IsOpen {x : UnitSphere E | c < height v x} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have hvh : height v v = 1 := by
    change inner ℝ (v : E) (v : E) = 1
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm v, one_pow]
  have hvc : v ∈ {x : UnitSphere E | c < height v x} := by
    change c < height v v
    rwa [hvh]
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) v).mem_iff.mp
    (hopen.mem_nhds hvc)
  have hβU : tsupport β ⊆ U := hβ.trans hcU
  have hne (t : unitInterval) (x : UnitSphere E) :
      blend v x ((t : ℝ) * β x) ≠ 0 := by
    by_cases hz : β x = 0
    · rw [hz, mul_zero, blend_zero]
      exact ne_zero_of_mem_unit_sphere x
    · have hx := hβ (subset_tsupport β hz)
      exact blend_ne_zero v x (mul_nonneg t.2.1 β.nonneg) (hc.trans hx)
  let F : UnitSphere E → UnitSphere E := fun x ↦ contract v x (β x)
  have hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F := by
    have hi : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : UnitSphere E → E) :=
      contMDiff_coe_sphere (E := E) (n := n) (m := ∞)
    have ha : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun x ↦ blend v x (β x)) :=
      ((contMDiff_const.sub β.contMDiff).smul hi).add
        (β.contMDiff.smul contMDiff_const)
    intro x
    have hx : blend v x (β x) ≠ 0 := by
      have h := hne 1 x
      change blend v x (1 * β x) ≠ 0 at h
      simpa only [one_mul] using h
    exact (SphereRadialRetraction.contMDiffAt_retract (n := n) v hx).comp x ha.contMDiffAt
  let f : C(UnitSphere E, UnitSphere E) := ⟨F, hF.continuous⟩
  have H : (ContinuousMap.id (UnitSphere E)).HomotopyRel f (Uᶜ ∪ {v}) := {
    toFun := fun q ↦ contract v q.2 ((q.1 : ℝ) * β q.2)
    continuous_toFun := by
      have ha : Continuous (fun q : unitInterval × UnitSphere E ↦
          blend v q.2 ((q.1 : ℝ) * β q.2)) :=
        ((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).mul
          (β.continuous.comp continuous_snd))).smul
          (continuous_subtype_val.comp continuous_snd)).add
            (((continuous_subtype_val.comp continuous_fst).mul
              (β.continuous.comp continuous_snd)).smul continuous_const)
      apply continuous_iff_continuousAt.mpr
      intro q
      exact ContinuousAt.comp (f := fun q : unitInterval × UnitSphere E ↦
          blend v q.2 ((q.1 : ℝ) * β q.2))
        (SphereRadialRetraction.contMDiffAt_retract (n := n) v (hne q.1 q.2)).continuousAt
        ha.continuousAt
    map_zero_left := by
      intro x
      change contract v x ((0 : ℝ) * β x) = x
      rw [zero_mul, contract_zero]
    map_one_left := by
      intro x
      change contract v x ((1 : ℝ) * β x) = contract v x (β x)
      rw [one_mul]
    prop' := by
      intro t x hx
      rcases hx with hx | hx
      · have hz : β x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hβU h))
        change contract v x ((t : ℝ) * β x) = x
        rw [hz, mul_zero, contract_zero]
      · have hxv : x = v := mem_singleton_iff.mp hx
        subst x
        exact contract_pole v _ }
  refine ⟨f, hF, ⟨H⟩, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hz : β x = 0
    · change contract v x (β x) ∈ U
      rwa [hz, contract_zero]
    · exact hcU (contract_mem_cap v x β.mem_Icc hc.le (hβ (subset_tsupport β hz)))
  · intro x hx
    have hxt : x ∈ (tsupport β)ᶜ := fun h ↦ hx (hβU h)
    filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hxt] with y hy
    change contract v y (β y) = y
    rw [image_eq_zero_of_notMem_tsupport hy, contract_zero]
  · refine ⟨interior {x | β x = 1}, isOpen_interior, ?_, ?_⟩
    · exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
    · intro x hx
      have hxβ : β x = 1 := interior_subset (s := {x : UnitSphere E | β x = 1}) hx
      change contract v x (β x) = v
      rw [hxβ, contract_one]

end NoExoticSixSphere.SphereCap
