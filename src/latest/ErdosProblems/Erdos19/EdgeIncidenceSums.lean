import ErdosProblems.Erdos19.MediumPaletteControl

/-! # Weighted sums under edge inclusion and a rank partition -/

namespace Erdos19.SetHypergraph

open Finset

variable {V : Type*} [Fintype V]

theorem sum_edge_weight_mono {H J : SetHypergraph V} (hJH : J ⊆ H)
    (weight : Set V → ℕ) :
    (∑ e : J, weight e.1) ≤ ∑ e : H, weight e.1 := by
  classical
  let incl : J ↪ H := ⟨fun e ↦ ⟨e.1, hJH e.2⟩, by
    intro e f hef
    exact Subtype.ext (congrArg (fun e : H ↦ e.1) hef)⟩
  calc
    _ = ∑ e ∈ univ.map incl, weight e.1 := by rw [sum_map]; rfl
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

theorem sum_rankAtLeast_add_rankBelow (H : SetHypergraph V) (R : ℕ)
    (weight : Set V → ℕ) :
    (∑ e : H.rankAtLeast R, weight e.1) +
      (∑ e : H.rankBelow R, weight e.1) = ∑ e : H, weight e.1 := by
  classical
  let above : {e : H // R ≤ e.1.ncard} ≃ H.rankAtLeast R :=
    { toFun := fun e ↦ ⟨e.1.1, e.1.2, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let below : {e : H // ¬R ≤ e.1.ncard} ≃ H.rankBelow R :=
    { toFun := fun e ↦ ⟨e.1.1, e.1.2, Nat.lt_of_not_ge e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, Nat.not_le.mpr e.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← above.sum_comp (fun e ↦ weight e.1), ← below.sum_comp (fun e ↦ weight e.1)]
  exact Fintype.sum_subtype_add_sum_subtype (fun e : H ↦ R ≤ e.1.ncard)
    (fun e : H ↦ weight e.1)

theorem incidence_le_pair_weight (H : SetHypergraph V)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) :
    (∑ e : H, e.1.ncard) ≤ ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
  apply sum_le_sum
  intro e _
  have he : 1 ≤ e.1.ncard - 1 := by have := hmin e; omega
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left e.1.ncard he

#print axioms sum_rankAtLeast_add_rankBelow

end Erdos19.SetHypergraph
