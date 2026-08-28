import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Literal extension by the identity from an open subset

The maps below do not change the ambient topology.  They apply the given
map on the original open subtype and are the identity elsewhere.  The
composition formulas are pointwise statements about these actual maps.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge.Extension

variable {X : Type*} [TopologicalSpace X] (U : Opens X)

/-- Extend an endomorphism of the original open subtype by the identity. -/
def extend (f : U → U) (x : X) : X := by
  classical
  exact if hx : x ∈ U then (f ⟨x, hx⟩).val else x

@[simp] theorem extend_coe (f : U → U) (x : U) :
    extend U f x.val = (f x).val := by
  classical
  simp only [extend, dif_pos x.property]

theorem extend_of_mem (f : U → U) {x : X} (hx : x ∈ U) :
    extend U f x = (f ⟨x, hx⟩).val := by
  classical
  simp only [extend, dif_pos hx]

theorem extend_of_notMem (f : U → U) {x : X} (hx : x ∉ U) :
    extend U f x = x := by
  classical
  simp only [extend, dif_neg hx]

@[simp] theorem extend_id (x : X) : extend U id x = x := by
  classical
  by_cases hx : x ∈ U
  · rw [extend_of_mem U id hx]
    rfl
  · exact extend_of_notMem U id hx

/-- Every extension preserves the original open subset and its complement. -/
@[simp] theorem extend_mem_iff (f : U → U) (x : X) :
    extend U f x ∈ U ↔ x ∈ U := by
  classical
  by_cases hx : x ∈ U
  · rw [extend_of_mem U f hx]
    exact iff_of_true (f ⟨x, hx⟩).property hx
  · rw [extend_of_notMem U f hx]

theorem extend_comp (f g : U → U) (x : X) :
    extend U f (extend U g x) = extend U (f ∘ g) x := by
  classical
  by_cases hx : x ∈ U
  · rw [extend_of_mem U g hx, extend_coe, extend_of_mem U (f ∘ g) hx]
    rfl
  · rw [extend_of_notMem U g hx, extend_of_notMem U f hx,
      extend_of_notMem U (f ∘ g) hx]

/-- The inverse is extended by the same pointwise rule. -/
def extendEquiv (e : U ≃ U) : X ≃ X where
  toFun := extend U e
  invFun := extend U e.symm
  left_inv x := by
    rw [extend_comp]
    have he : (e.symm : U → U) ∘ e = id := funext e.symm_apply_apply
    rw [he, extend_id]
  right_inv x := by
    rw [extend_comp]
    have he : (e : U → U) ∘ e.symm = id := funext e.apply_symm_apply
    rw [he, extend_id]

@[simp] theorem extendEquiv_apply (e : U ≃ U) (x : X) :
    extendEquiv U e x = extend U e x := rfl

@[simp] theorem extendEquiv_symm_apply (e : U ≃ U) (x : X) :
    (extendEquiv U e).symm x = extend U e.symm x := rfl

/-- A common pointwise support remains a support after extension. -/
theorem extend_eq_self_of_notMem {K : Set X} (f : U → U)
    (hf : ∀ y : U, y.val ∉ K → f y = y) {x : X} (hx : x ∉ K) :
    extend U f x = x := by
  classical
  by_cases hxU : x ∈ U
  · rw [extend_of_mem U f hxU, hf ⟨x, hxU⟩ hx]
  · exact extend_of_notMem U f hxU

/-- Any quantity preserved on the open subset is preserved globally. -/
theorem extend_preserves {B : Type*} (p : X → B) (f : U → U)
    (hf : ∀ y : U, p (f y).val = p y.val) (x : X) :
    p (extend U f x) = p x := by
  classical
  by_cases hx : x ∈ U
  · rw [extend_of_mem U f hx]
    exact hf ⟨x, hx⟩
  · rw [extend_of_notMem U f hx]

theorem extend_family_zero (F : ℝ → U → U) (hzero : ∀ y, F 0 y = y) (x : X) :
    extend U (F 0) x = x := by
  have he : F 0 = id := funext hzero
  rw [he, extend_id]

theorem extend_family_add (F : ℝ → U → U)
    (hadd : ∀ s t y, F (s + t) y = F s (F t y)) (s t : ℝ) (x : X) :
    extend U (F (s + t)) x = extend U (F s) (extend U (F t) x) := by
  rw [extend_comp]
  exact congrArg (fun f : U → U => extend U f x) (funext (hadd s t))

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge.Extension
