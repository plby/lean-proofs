import ErdosProblems.Erdos547.TransportHall

/-!
# Fractional Hall with different row and column types
-/

noncomputable section

namespace Erdos547.DPRS

open Finset
open scoped BigOperators

variable {U V : Type*} [Fintype U] [Fintype V]

open scoped Classical in
theorem exists_rectangular_transport (P : U → V → Prop) (a : U → ℝ) (b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ v, 0 ≤ b v)
    (hHall : ∀ S : Finset U, (∑ u ∈ S, a u) ≤
      ∑ v ∈ Finset.univ.filter (fun v ↦ ∃ u ∈ S, P u v), b v) :
    ∃ f : U → V → ℝ, (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, ¬ P u v → f u v = 0) ∧
      (∀ u, ∑ v, f u v = a u) ∧ (∀ v, ∑ u, f u v ≤ b v) := by
  classical
  let A : U ⊕ V → ℝ := Sum.elim a (fun _ ↦ 0)
  let B : U ⊕ V → ℝ := Sum.elim (fun _ ↦ 0) b
  let Q : U ⊕ V → U ⊕ V → Prop := fun x y ↦ match x, y with
    | .inl u, .inr v => P u v
    | _, _ => False
  have hA : ∀ x, 0 ≤ A x := by intro x; cases x with | inl u => exact ha u | inr v => rfl
  have hB : ∀ x, 0 ≤ B x := by intro x; cases x with | inl u => rfl | inr v => exact hb v
  have hQHall : ∀ S : Finset (U ⊕ V), (∑ x ∈ S, A x) ≤
      ∑ y ∈ Finset.univ.filter (fun y ↦ ∃ x ∈ S, Q x y), B y := by
    intro S
    let S₀ := Finset.univ.filter (fun u ↦ Sum.inl u ∈ S)
    have hrow : (∑ x ∈ S, A x) = ∑ u ∈ S₀, a u := by
      calc
        _ = ∑ x : U ⊕ V, if x ∈ S then A x else 0 := by simp
        _ = (∑ u : U, if Sum.inl u ∈ S then a u else 0) + ∑ _v : V, (0 : ℝ) := by
          rw [Fintype.sum_sum_type]
          simp only [A, Sum.elim_inl, Sum.elim_inr, ite_self]
        _ = _ := by simp only [Finset.sum_const_zero, add_zero, S₀, Finset.sum_filter]
    have hN (v : V) : (∃ x ∈ S, Q x (.inr v)) ↔ ∃ u ∈ S₀, P u v := by
      constructor
      · rintro ⟨x, hx, hP⟩
        cases x with
        | inl u => exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, hP⟩
        | inr v => exact hP.elim
      · rintro ⟨u, hu, hP⟩
        exact ⟨.inl u, (Finset.mem_filter.mp hu).2, hP⟩
    have hcol : (∑ y ∈ Finset.univ.filter (fun y ↦ ∃ x ∈ S, Q x y), B y) =
        ∑ v ∈ Finset.univ.filter (fun v ↦ ∃ u ∈ S₀, P u v), b v := by
      simp only [Finset.sum_filter, Fintype.sum_sum_type, B, Sum.elim_inl, Sum.elim_inr,
        ite_self, Finset.sum_const_zero, zero_add, hN]
    rw [hrow, hcol]
    exact hHall S₀
  obtain ⟨f, hf⟩ := Transport.exists_full_rows_of_hall Q A B hA hB hQHall
  have hLL (u z : U) : f.weight (.inl u) (.inl z) = 0 :=
    f.supported _ _ (fun h ↦ h)
  have hRR (u z : V) : f.weight (.inr u) (.inr z) = 0 :=
    f.supported _ _ (fun h ↦ h)
  refine ⟨fun u v ↦ f.weight (.inl u) (.inr v), fun u v ↦ f.nonnegative _ _, ?_, ?_, ?_⟩
  · exact fun u v hP ↦ f.supported _ _ hP
  · intro u
    have hh := hf (.inl u)
    simpa only [Transport.row, Fintype.sum_sum_type, hLL, Finset.sum_const_zero, zero_add,
      A, Sum.elim_inl] using hh
  · intro v
    have hh := f.col_bound (.inr v)
    simpa only [Fintype.sum_sum_type, hRR, Finset.sum_const_zero, add_zero,
      B, Sum.elim_inr] using hh

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_rectangular_transport
