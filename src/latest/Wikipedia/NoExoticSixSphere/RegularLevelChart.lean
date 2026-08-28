import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Constructions

/-!
# Restricting a local normal form to its actual zero fiber

If the first coordinate of a partial homeomorphism is `f`, then its restriction
to `{x | f x = 0}` gives a chart with the remaining coordinates. The fiber
keeps its existing subtype topology. No transported topology is used.
-/

open Set Topology

namespace NoExoticSixSphere.RegularLevelChart

variable {M F K : Type*} [TopologicalSpace M] [TopologicalSpace F] [Zero F]
  [TopologicalSpace K] {f : M → F}
  (Φ : OpenPartialHomeomorph M (F × K))
  (hfirst : ∀ x ∈ Φ.source, (Φ x).1 = f x) (x₀ : {x : M // f x = 0})

noncomputable def inverse (z : K) : {x : M // f x = 0} := by
  classical
  exact if hz : (0, z) ∈ Φ.target then
    ⟨Φ.symm (0, z), (hfirst _ (Φ.map_target hz)).symm.trans
      (congrArg Prod.fst (Φ.right_inv hz))⟩ else x₀

theorem inverse_val {z : K} (hz : (0, z) ∈ Φ.target) :
    (inverse Φ hfirst x₀ z).val = Φ.symm (0, z) := by
  simp only [inverse, dif_pos hz]

include hfirst in
theorem zero_pair_image (x : {x : M // f x = 0}) (hx : (x : M) ∈ Φ.source) :
    (0, (Φ x).2) = Φ x :=
  Prod.ext ((hfirst x hx).trans x.property).symm rfl

noncomputable def chart : OpenPartialHomeomorph {x : M // f x = 0} K where
  toFun x := (Φ x).2
  invFun := inverse Φ hfirst x₀
  source := ((↑) : {x : M // f x = 0} → M) ⁻¹' Φ.source
  target := (fun z : K ↦ (0, z)) ⁻¹' Φ.target
  map_source' x hx := by
    change (0, (Φ x).2) ∈ Φ.target
    rw [zero_pair_image Φ hfirst x hx]
    exact Φ.map_source hx
  map_target' z hz := by
    change (inverse Φ hfirst x₀ z).val ∈ Φ.source
    rw [inverse_val Φ hfirst x₀ hz]
    exact Φ.map_target hz
  left_inv' x hx := by
    apply Subtype.ext
    have hz : (0, (Φ x).2) ∈ Φ.target := by
      rw [zero_pair_image Φ hfirst x hx]
      exact Φ.map_source hx
    rw [inverse_val Φ hfirst x₀ hz, zero_pair_image Φ hfirst x hx]
    exact Φ.left_inv hx
  right_inv' z hz := by
    rw [inverse_val Φ hfirst x₀ hz]
    exact congrArg Prod.snd (Φ.right_inv hz)
  open_source := Φ.open_source.preimage continuous_subtype_val
  open_target := Φ.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.comp_continuousOn
    (Φ.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx ↦ hx))
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (Φ.symm.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hz ↦ hz)).congr
    intro z hz
    exact inverse_val Φ hfirst x₀ hz

theorem chart_source : (chart Φ hfirst x₀).source =
    ((↑) : {x : M // f x = 0} → M) ⁻¹' Φ.source := rfl

theorem chart_target : (chart Φ hfirst x₀).target =
    (fun z : K ↦ (0, z)) ⁻¹' Φ.target := rfl

theorem chart_apply (x : {x : M // f x = 0}) : chart Φ hfirst x₀ x = (Φ x).2 := rfl

theorem chart_symm_val {z : K} (hz : z ∈ (chart Φ hfirst x₀).target) :
    ((chart Φ hfirst x₀).symm z).val = Φ.symm (0, z) :=
  inverse_val Φ hfirst x₀ hz

end NoExoticSixSphere.RegularLevelChart
