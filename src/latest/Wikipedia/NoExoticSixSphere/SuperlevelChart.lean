import Wikipedia.NoExoticSixSphere.ProductHalfSpaceModel
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Restricting an actual local normal form to a superlevel set

A sign-preserving local homeomorphism restricts to a genuine chart of the
existing superlevel subtype into the standard linear half-space. Values
outside chart domains use fallbacks only; all identities retain the actual
normal form on its proved source and target.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.SuperlevelChart

variable {M K : Type*} [TopologicalSpace M]
  [NormedAddCommGroup K] {f : M → ℝ}
  (Φ : OpenPartialHomeomorph M (ℝ × K))
  (hsign : ∀ y ∈ Φ.source, 0 ≤ (Φ y).1 ↔ 0 ≤ f y) (x₀ : {x : M // 0 ≤ f x})

def forward (x : {x : M // 0 ≤ f x}) : ProductHalfSpace.Space K := by
  classical
  exact if h : 0 ≤ (Φ x.val).1 then ⟨Φ x.val, h⟩ else ⟨(0, 0), le_rfl⟩

include hsign in
theorem forward_val (x : {x : M // 0 ≤ f x}) (hx : x.val ∈ Φ.source) :
    (forward Φ x).val = Φ x.val := by
  simp only [forward, dif_pos ((hsign x.val hx).mpr x.property)]

def inverse (z : ProductHalfSpace.Space K) : {x : M // 0 ≤ f x} := by
  classical
  exact if hz : z.val ∈ Φ.target then
    ⟨Φ.symm z.val, (hsign _ (Φ.map_target hz)).mp (by
      rw [Φ.right_inv hz]
      exact z.property)⟩ else x₀

theorem inverse_val {z : ProductHalfSpace.Space K} (hz : z.val ∈ Φ.target) :
    (inverse Φ hsign x₀ z).val = Φ.symm z.val := by
  simp only [inverse, dif_pos hz]

def chart : OpenPartialHomeomorph {x : M // 0 ≤ f x} (ProductHalfSpace.Space K) where
  toFun := forward Φ
  invFun := inverse Φ hsign x₀
  source := Subtype.val ⁻¹' Φ.source
  target := Subtype.val ⁻¹' Φ.target
  map_source' x hx := by
    change (forward Φ x).val ∈ Φ.target
    rw [forward_val Φ hsign x hx]
    exact Φ.map_source hx
  map_target' z hz := by
    change (inverse Φ hsign x₀ z).val ∈ Φ.source
    rw [inverse_val Φ hsign x₀ hz]
    exact Φ.map_target hz
  left_inv' x hx := by
    apply Subtype.ext
    have hz : (forward Φ x).val ∈ Φ.target := by
      rw [forward_val Φ hsign x hx]
      exact Φ.map_source hx
    rw [inverse_val Φ hsign x₀ hz, forward_val Φ hsign x hx]
    exact Φ.left_inv hx
  right_inv' z hz := by
    apply Subtype.ext
    rw [forward_val Φ hsign _ (by
      rw [inverse_val Φ hsign x₀ hz]
      exact Φ.map_target hz), inverse_val Φ hsign x₀ hz]
    exact Φ.right_inv hz
  open_source := Φ.open_source.preimage continuous_subtype_val
  open_target := Φ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (Φ.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx ↦ hx)).congr
    intro x hx
    exact forward_val Φ hsign x hx
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (Φ.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hz ↦ hz)).congr
    intro z hz
    exact inverse_val Φ hsign x₀ hz

theorem chart_source : (chart Φ hsign x₀).source = Subtype.val ⁻¹' Φ.source := rfl

theorem chart_target : (chart Φ hsign x₀).target = Subtype.val ⁻¹' Φ.target := rfl

theorem chart_apply_val (x : {x : M // 0 ≤ f x}) (hx : x.val ∈ Φ.source) :
    (chart Φ hsign x₀ x).val = Φ x.val := forward_val Φ hsign x hx

theorem chart_symm_val {z : ProductHalfSpace.Space K}
    (hz : z ∈ (chart Φ hsign x₀).target) :
    ((chart Φ hsign x₀).symm z).val = Φ.symm z.val := inverse_val Φ hsign x₀ hz

end NoExoticSixSphere.SuperlevelChart
