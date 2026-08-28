import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The zero-section inverse to projection from a vector-space product

The inverse is the specified zero section, not an arbitrary contraction
point. This keeps the inverse of the sphere-cylinder retraction exactly on
the equator, where the chart transition has already been computed.
-/

namespace NoExoticSixSphere.ZeroProduct

open ContinuousMap
open scoped unitInterval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (X : Type*) [TopologicalSpace X]

def scaling : (ContinuousMap.const E (0 : E)).Homotopy (ContinuousMap.id E) where
  toFun p := (p.1 : ℝ) • p.2
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).smul continuous_snd
  map_zero_left x := zero_smul ℝ x
  map_one_left x := one_smul ℝ x

def homotopyEquiv : (E × X) ≃ₕ X where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const X (0 : E)).prodMk (ContinuousMap.id X)
  left_inv := ⟨(scaling E).prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id X))⟩
  right_inv := .refl (ContinuousMap.id X)

theorem homotopyEquiv_apply (p : E × X) : homotopyEquiv E X p = p.2 := rfl

theorem homotopyEquiv_symm_apply (x : X) : (homotopyEquiv E X).symm x = (0, x) := rfl

end NoExoticSixSphere.ZeroProduct
