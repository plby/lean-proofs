import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# A manifold-valued fiber in a genuine target-chart domain

Restrict the domain to the open preimage of a target chart before subtracting
the coordinate of the specified value. The original fiber is homeomorphic
to the resulting zero fiber, with both topologies inherited as subspaces.
-/

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

namespace NoExoticSixSphere.ChartFiber

variable {B H M C H' N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : ContinuousMap M N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

def domain : Opens M := ⟨f ⁻¹' c.source, c.open_source.preimage f.continuous⟩

noncomputable def coordinates (b : N) (x : domain f c) : F := c (f x.val) - c b

theorem coordinates_zero_iff (b : N) (hb : b ∈ c.source) (x : domain f c) :
    coordinates f c b x = 0 ↔ f x.val = b := by
  change c (f x.val) - c b = 0 ↔ f x.val = b
  rw [sub_eq_zero]
  constructor
  · exact c.toPartialEquiv.injOn x.property hb
  · intro h
    exact congrArg c h

noncomputable def homeomorph (b : N) (hb : b ∈ c.source) :
    {x : M // f x = b} ≃ₜ {x : domain f c // coordinates f c b x = 0} where
  toFun x := ⟨⟨x.val, by change f x.val ∈ c.source; rw [x.property]; exact hb⟩,
    (coordinates_zero_iff f c b hb _).mpr x.property⟩
  invFun x := ⟨x.val.val, (coordinates_zero_iff f c b hb x.val).mp x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply IsInducing.subtypeVal.continuous_iff.mpr
    apply IsInducing.subtypeVal.continuous_iff.mpr
    exact continuous_subtype_val
  continuous_invFun := by
    have h : Continuous (fun x : {x : domain f c // coordinates f c b x = 0} ↦
        x.val.val) :=
      (continuous_subtype_val : Continuous (Subtype.val : domain f c → M)).comp
        continuous_subtype_val
    exact h.subtype_mk _

theorem homeomorph_val (b : N) (hb : b ∈ c.source) (x : {x : M // f x = b}) :
    (homeomorph f c b hb x).val.val = x.val := rfl

theorem homeomorph_symm_val (b : N) (hb : b ∈ c.source)
    (x : {x : domain f c // coordinates f c b x = 0}) :
    ((homeomorph f c b hb).symm x).val = x.val.val := rfl

theorem contMDiff_coordinates (hf : ContMDiff I J ∞ f) (b : N) :
    ContMDiff I 𝓘(ℝ, F) ∞ (coordinates f c b) := by
  have hfc : ContMDiff I J ∞ (fun x : domain f c ↦ f x.val) :=
    hf.comp contMDiff_subtype_val
  have hs : ContDiff ℝ ∞ (fun z : F ↦ z - c b) := contDiff_id.sub contDiff_const
  exact hs.contMDiff.comp (c.contMDiffOn_toFun.comp_contMDiff hfc (fun x ↦ x.property))

end NoExoticSixSphere.ChartFiber
