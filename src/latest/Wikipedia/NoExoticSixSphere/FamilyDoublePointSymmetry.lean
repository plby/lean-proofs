import Wikipedia.NoExoticSixSphere.FamilyDoublePointClosure

/-!
# The swap involution on the actual family double-point closure
-/

open Set Function

namespace NoExoticSixSphere.FamilyEmbedding

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]

def swapPair (r : P × (E × E)) : P × (E × E) := (r.1, (r.2.2, r.2.1))

theorem swap_mem_closure_doublePoints (f : P → E → F) {r : P × (E × E)}
    (hr : r ∈ closure (doublePoints f)) : swapPair r ∈ closure (doublePoints f) := by
  have hm : MapsTo swapPair (doublePoints f) (doublePoints f) :=
    fun _ hq ↦ ⟨hq.1.symm, hq.2.symm⟩
  exact hm.closure
    (continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)) hr

def swapClosure (f : P → E → F) : closure (doublePoints f) ≃ₜ closure (doublePoints f) where
  toFun r := ⟨swapPair r.val, swap_mem_closure_doublePoints f r.property⟩
  invFun r := ⟨swapPair r.val, swap_mem_closure_doublePoints f r.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    ((continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)).comp
      continuous_subtype_val).subtype_mk _

theorem swapClosure_involutive (f : P → E → F) : Involutive (swapClosure f) :=
  fun _ ↦ Subtype.ext rfl

end NoExoticSixSphere.FamilyEmbedding
