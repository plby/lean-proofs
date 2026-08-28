import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Native bundle trivializations from product charts on open preimages

The topology on the source is unchanged. The input homeomorphism is
required to preserve the specified projection exactly.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.OrbitPair

variable {X B G : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace G] [One G] [Nonempty X]

/-- Package a projection-preserving product chart as a native trivialization. -/
def trivializationFromProduct (p : X → B) (hp : Continuous p) (U : TopologicalSpace.Opens B)
    (e : (p ⁻¹' (U : Set B)) ≃ₜ U × G)
    (he : ∀ x, (e x).1.val = p x.val) : Trivialization G p := by
  classical
  let forward : X → B × G := fun x =>
    (p x, if hx : p x ∈ U then (e ⟨x, hx⟩).2 else 1)
  let backward : B × G → X := fun z =>
    if hz : z.1 ∈ U then (e.symm (⟨z.1, hz⟩, z.2)).val else Classical.choice ‹Nonempty X›
  have hf (x : p ⁻¹' (U : Set B)) :
      forward x.val = ((e x).1.val, (e x).2) := by
    simp only [forward, dif_pos (show p x.val ∈ U from x.property), he x]
  have hb (z : U × G) : backward (z.1.val, z.2) = (e.symm z).val := by
    simp only [backward, dif_pos z.1.property]
  refine
    { toFun := forward
      invFun := backward
      source := p ⁻¹' (U : Set B)
      target := (U : Set B) ×ˢ univ
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := U.isOpen.preimage hp
      open_target := U.isOpen.prod isOpen_univ
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      baseSet := U
      open_baseSet := U.isOpen
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }
  · intro x hx
    exact ⟨hx, mem_univ _⟩
  · intro z hz
    rw [show backward z = (e.symm (⟨z.1, hz.1⟩, z.2)).val from hb (⟨z.1, hz.1⟩, z.2)]
    exact (e.symm (⟨z.1, hz.1⟩, z.2)).property
  · intro x hx
    rw [hf ⟨x, hx⟩, hb]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  · intro z hz
    rw [show backward z = (e.symm (⟨z.1, hz.1⟩, z.2)).val from hb (⟨z.1, hz.1⟩, z.2),
      hf, e.apply_symm_apply]
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc := ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).comp
      e.continuous
    exact hc.congr (fun x => (hf x).symm)
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : (U : Set B) ×ˢ (univ : Set G) =>
        (e.symm (⟨z.val.1, z.property.1⟩, z.val.2)).val) := by
      apply continuous_subtype_val.comp
      apply e.symm.continuous.comp
      exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact hc.congr (fun z => (hb (⟨z.val.1, z.property.1⟩, z.val.2)).symm)

@[simp] theorem trivializationFromProduct_baseSet (p : X → B) (hp : Continuous p)
    (U : TopologicalSpace.Opens B) (e : (p ⁻¹' (U : Set B)) ≃ₜ U × G)
    (he : ∀ x, (e x).1.val = p x.val) :
    (trivializationFromProduct p hp U e he).baseSet = U := rfl

end Wikipedia.HopfProblem.OrbitPair
