import ErdosProblems.Erdos19.Core

/-! # Transport under an injective map of vertices -/

namespace Erdos19.SetHypergraph

variable {X Y : Type*}

def vertexImage (H : SetHypergraph X) (f : X → Y) : SetHypergraph Y :=
  (Set.image f) '' H

noncomputable def vertexImageEdgeEquiv (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) : H ≃ H.vertexImage f :=
  Equiv.ofBijective (fun e ↦ ⟨f '' e.1, ⟨e.1, e.2, rfl⟩⟩) (by
    constructor
    · intro e g heg
      apply Subtype.ext
      apply hf.image_injective
      exact congrArg (fun e : H.vertexImage f ↦ e.1) heg
    · rintro ⟨e, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩)

@[simp] theorem vertexImageEdgeEquiv_val (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) (e : H) :
    (H.vertexImageEdgeEquiv f hf e).1 = f '' e.1 := rfl

@[simp] theorem vertexImageEdgeEquiv_ncard (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) (e : H) :
    (H.vertexImageEdgeEquiv f hf e).1.ncard = e.1.ncard :=
  Set.ncard_image_of_injective _ hf

theorem vertexImageEdgeEquiv_inter (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) (e g : H) :
    ((H.vertexImageEdgeEquiv f hf e).1 ∩ (H.vertexImageEdgeEquiv f hf g).1).Nonempty ↔
      (e.1 ∩ g.1).Nonempty := by
  rw [vertexImageEdgeEquiv_val, vertexImageEdgeEquiv_val, ← Set.image_inter hf]
  exact Set.image_nonempty

theorem vertexImage_isLinear_iff (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) : (H.vertexImage f).IsLinear ↔ H.IsLinear := by
  constructor
  · intro hlin e he g hg heg x hx y hy
    apply hf
    apply hlin (show f '' e ∈ H.vertexImage f from ⟨e, he, rfl⟩)
      (show f '' g ∈ H.vertexImage f from ⟨g, hg, rfl⟩)
      (fun h ↦ heg (hf.image_injective h))
    · exact ⟨Set.mem_image_of_mem f hx.1, Set.mem_image_of_mem f hx.2⟩
    · exact ⟨Set.mem_image_of_mem f hy.1, Set.mem_image_of_mem f hy.2⟩
  · intro hlin e he g hg heg
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨g', hg', rfl⟩ := hg
    rw [← Set.image_inter hf]
    exact (hlin he' hg' (fun h ↦ heg (congrArg (Set.image f) h))).image f

theorem vertexImage_edgeColorable_iff (H : SetHypergraph X) (f : X → Y)
    (hf : Function.Injective f) (q : ℕ) :
    (H.vertexImage f).EdgeColorable q ↔ H.EdgeColorable q := by
  let E := H.vertexImageEdgeEquiv f hf
  constructor
  · rintro ⟨c⟩
    refine ⟨{ color := fun e ↦ c (E e), valid := ?_ }⟩
    intro e g heg hinter
    exact c.valid (fun h ↦ heg (E.injective h))
      ((H.vertexImageEdgeEquiv_inter f hf e g).mpr hinter)
  · rintro ⟨c⟩
    refine ⟨{ color := fun e ↦ c (E.symm e), valid := ?_ }⟩
    intro e g heg hinter
    apply c.valid (fun h ↦ heg (E.symm.injective h))
    apply (H.vertexImageEdgeEquiv_inter f hf (E.symm e) (E.symm g)).mp
    change ((E (E.symm e)).1 ∩ (E (E.symm g)).1).Nonempty
    simpa only [E.apply_symm_apply] using hinter

theorem vertexImage_sum_pair_weight [Fintype X] [Fintype Y]
    (H : SetHypergraph X) (f : X → Y) (hf : Function.Injective f) :
    (∑ e : H.vertexImage f, e.1.ncard * (e.1.ncard - 1)) =
      ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
  classical
  symm
  apply Fintype.sum_equiv (H.vertexImageEdgeEquiv f hf)
  intro e
  simp only [vertexImageEdgeEquiv_ncard]

#print axioms vertexImage_isLinear_iff
#print axioms vertexImage_edgeColorable_iff
#print axioms vertexImage_sum_pair_weight

/-- Regard edges supported on `U` as sets of elements of the subtype `U`. -/
def onVertexSet (H : SetHypergraph X) (U : Set X) : SetHypergraph U :=
  {e | Subtype.val '' e ∈ H}

theorem vertexImage_onVertexSet_eq (H : SetHypergraph X) (U : Set X)
    (hsupport : ∀ e ∈ H, e ⊆ U) :
    (H.onVertexSet U).vertexImage Subtype.val = H := by
  ext e
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro he
    have hrange : e ⊆ Set.range (Subtype.val : U → X) := by
      intro x hx
      exact ⟨⟨x, hsupport e he hx⟩, rfl⟩
    have himage := Set.image_preimage_eq_of_subset hrange
    exact ⟨Subtype.val ⁻¹' e, by simpa only [onVertexSet, Set.mem_setOf_eq, himage] using he,
      himage⟩

#print axioms vertexImage_onVertexSet_eq

end Erdos19.SetHypergraph
