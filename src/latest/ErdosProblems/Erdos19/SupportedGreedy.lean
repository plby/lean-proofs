import ErdosProblems.Erdos19.VertexTransport

/-! # The elementary greedy bound measured on the actual support -/

namespace Erdos19.SetHypergraph

theorem edgeColorable_support_add_div_add_one {V : Type*} [Fintype V]
    (H : SetHypergraph V) (B : Set V) (hlinear : H.IsLinear)
    (r : ℕ) (hr : 2 ≤ r) (hmin : ∀ e : H, r ≤ e.1.ncard) (hsupport : ∀ e : H, e.1 ⊆ B) :
    H.EdgeColorable (B.ncard + B.ncard / (r - 1) + 1) := by
  classical
  let J := H.onVertexSet B
  have himage : J.vertexImage Subtype.val = H :=
    H.vertexImage_onVertexSet_eq B (fun e he ↦ hsupport ⟨e, he⟩)
  have hJlinear : J.IsLinear := by
    apply (J.vertexImage_isLinear_iff Subtype.val Subtype.val_injective).mp
    simpa only [himage] using hlinear
  have hJmin : ∀ e : J, r ≤ e.1.ncard := by
    intro e
    have h := hmin ⟨Subtype.val '' e.1, e.2⟩
    simpa only [Set.ncard_image_of_injective _ Subtype.val_injective] using h
  have hc := J.edgeColorable_card_add_div_add_one hJlinear r hr hJmin
  rw [Set.fintypeCard_eq_ncard] at hc
  have hc' := (J.vertexImage_edgeColorable_iff Subtype.val Subtype.val_injective _).mpr hc
  simpa only [himage] using hc'

theorem edgeColorable_two_mul_support_add_one {V : Type*} [Fintype V]
    (H : SetHypergraph V) (B : Set V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (hsupport : ∀ e : H, e.1 ⊆ B) :
    H.EdgeColorable (2 * B.ncard + 1) := by
  have h := H.edgeColorable_support_add_div_add_one B hlinear 2 le_rfl hmin hsupport
  simpa only [Nat.reduceSub, Nat.div_one, ← two_mul] using h

#print axioms edgeColorable_support_add_div_add_one
#print axioms edgeColorable_two_mul_support_add_one

end Erdos19.SetHypergraph
