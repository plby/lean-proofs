import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Product neighborhoods in a time-constant cylinder fiber

On an open time interval where a cylinder map is independent of time, its
actual fiber is a product of that interval with the endpoint fiber. All
topologies here are the original subtype and product topologies.
-/

open Set Topology TopologicalSpace

namespace NoExoticSixSphere.CylinderFiberProduct

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (f : C(M, N)) (b : N) (U : Opens ℝ)

def timeDomain : Opens {p : ℝ × M // F p = b} :=
  ⟨{p | p.val.1 ∈ U}, U.isOpen.preimage (continuous_fst.comp continuous_subtype_val)⟩

noncomputable def homeomorph
    (hconstant : ∀ t ∈ U, ∀ x, F (t, x) = f x) :
    timeDomain F b U ≃ₜ U × {x : M // f x = b} where
  toFun p := (⟨p.val.val.1, p.property⟩,
    ⟨p.val.val.2, (hconstant _ p.property _).symm.trans p.val.property⟩)
  invFun p := ⟨⟨(p.1.val, p.2.val), (hconstant _ p.1.property _).trans p.2.property⟩,
    p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun p : timeDomain F b U ↦ p.val.val) :=
      (continuous_subtype_val : Continuous
        (Subtype.val : {p : ℝ × M // F p = b} → ℝ × M)).comp continuous_subtype_val
    exact (h.fst.subtype_mk _).prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have h : Continuous (fun p : U × {x : M // f x = b} ↦ (p.1.val, p.2.val)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (h.subtype_mk _).subtype_mk _

theorem homeomorph_time (hconstant : ∀ t ∈ U, ∀ x, F (t, x) = f x)
    (p : timeDomain F b U) :
    (homeomorph F f b U hconstant p).1.val = p.val.val.1 := rfl

theorem homeomorph_space (hconstant : ∀ t ∈ U, ∀ x, F (t, x) = f x)
    (p : timeDomain F b U) :
    (homeomorph F f b U hconstant p).2.val = p.val.val.2 := rfl

theorem homeomorph_symm_val (hconstant : ∀ t ∈ U, ∀ x, F (t, x) = f x)
    (p : U × {x : M // f x = b}) :
    ((homeomorph F f b U hconstant).symm p).val.val = (p.1.val, p.2.val) := rfl

end NoExoticSixSphere.CylinderFiberProduct
