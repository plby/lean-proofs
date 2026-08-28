import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

/-!
# Natural fibre identifications under base change and reparametrization

The fibres retain their original subspace topologies. Restriction to a
full base preimage and a bijective change of base coordinates identify
the same points, and hence preserve connectedness.
-/

open Function Set Topology

namespace Wikipedia.HopfProblem.FibreTopology

variable {X Y Z : Type*} [TopologicalSpace X]

/-- Restricting a map to a full base preimage does not change any of its fibres. -/
def restrictPreimageFibreHomeomorph (f : X → Y) (S : Set Y) (b : S) :
    (S.restrictPreimage f ⁻¹' {b}) ≃ₜ (f ⁻¹' {(b : Y)}) := by
  let forward : (S.restrictPreimage f ⁻¹' {b}) → (f ⁻¹' {(b : Y)}) := fun x =>
    ⟨x.val.val, congrArg (fun y : S => (y : Y)) x.property⟩
  let backward : (f ⁻¹' {(b : Y)}) → (S.restrictPreimage f ⁻¹' {b}) := fun x =>
    ⟨⟨x.val, by
      change f x.val ∈ S
      rw [show f x.val = b.val from x.property]
      exact b.property⟩, Subtype.ext x.property⟩
  refine {
    toFun := forward
    invFun := backward
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

@[simp] theorem restrictPreimageFibreHomeomorph_val (f : X → Y) (S : Set Y) (b : S)
    (x : S.restrictPreimage f ⁻¹' {b}) :
    (restrictPreimageFibreHomeomorph f S b x : X) = x.val.val := rfl

theorem restrictPreimage_fibre_isConnected (f : X → Y) (S : Set Y) (b : S)
    (h : IsConnected (f ⁻¹' {(b : Y)})) :
    IsConnected (S.restrictPreimage f ⁻¹' {b}) :=
  isConnected_iff_connectedSpace.mpr
    ((restrictPreimageFibreHomeomorph f S b).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp h))

omit [TopologicalSpace X] in
/-- An injective target coordinate does not alter the corresponding literal fibre. -/
theorem preimage_singleton_comp_injective (f : X → Y) (g : Y → Z)
    (hg : Injective g) (b : Y) :
    (g ∘ f) ⁻¹' {g b} = f ⁻¹' {b} := by
  ext x
  exact hg.eq_iff

theorem fibre_isConnected_comp_injective (f : X → Y) (g : Y → Z)
    (hg : Injective g) (b : Y) (h : IsConnected (f ⁻¹' {b})) :
    IsConnected ((g ∘ f) ⁻¹' {g b}) := by
  rw [preimage_singleton_comp_injective f g hg b]
  exact h

theorem fibre_isConnected_comp_homeomorph [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (e : Y ≃ₜ Z) (b : Z)
    (h : IsConnected (f ⁻¹' {e.symm b})) : IsConnected ((e ∘ f) ⁻¹' {b}) := by
  have he := fibre_isConnected_comp_injective f e e.injective (e.symm b) h
  simpa only [e.apply_symm_apply] using he

end Wikipedia.HopfProblem.FibreTopology
