import ErdosProblems.Erdos587.FiniteQuotientCoverage

/-! # One small reserve supplies every generated residue class -/

open scoped BigOperators

namespace Erdos587.CFP

lemma delta_quotient_eq_iff_sub_mem {G : Type*} [AddCommGroup G]
    (Δ : AddSubgroup G) (x y : G) :
    QuotientAddGroup.mk' Δ x = QuotientAddGroup.mk' Δ y ↔ x - y ∈ Δ := by
  constructor
  · intro h
    simpa only [sub_eq_add_neg, add_comm] using QuotientAddGroup.eq.mp h.symm
  · intro h
    apply Eq.symm
    apply QuotientAddGroup.eq.mpr
    simpa only [sub_eq_add_neg, add_comm] using h

theorem delta_exists_uniform_residue_pool {α G : Type*} [AddCommGroup G]
    (φ : α → G) (A : Finset α) (Δ : AddSubgroup G) [Δ.FiniteIndex]
    (r : ℕ) (hsize : Δ.index ≤ r + 1)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup φ D = generatedSubgroup φ A) :
    ∃ W ⊆ A, W.card ≤ Δ.index ^ 2 ∧
      ∀ x ∈ generatedSubgroup φ A, ∃ S ⊆ W, S.card + 1 ≤ Δ.index ∧
        (∑ a ∈ S, φ a) - x ∈ Δ := by
  classical
  let _ : Fintype (G ⧸ Δ) := Fintype.ofFinite _
  let ψ := QuotientAddGroup.mk' Δ
  let H := (generatedSubgroup φ A).map ψ
  let _ : Fintype H := Fintype.ofFinite _
  have hindex : Fintype.card (G ⧸ Δ) = Δ.index := by
    simp only [AddSubgroup.index, Nat.card_eq_fintype_card]
  have hHcard : Fintype.card H ≤ Δ.index := by
    exact (Fintype.card_le_of_injective (fun q : H => (q : G ⧸ Δ)) Subtype.val_injective).trans_eq
      hindex
  have hwitness (q : H) : ∃ S ⊆ A, S.card + 1 ≤ Δ.index ∧
      ψ (∑ a ∈ S, φ a) = (q : G ⧸ Δ) := by
    obtain ⟨x, hx, heq⟩ := AddSubgroup.mem_map.mp q.property
    obtain ⟨S, hSA, hcard, hmod⟩ := exists_small_subset_sum_mod_subgroup φ A Δ r hsize hstable hx
    exact ⟨S, hSA, hcard, ((delta_quotient_eq_iff_sub_mem Δ _ _).mpr hmod).trans heq⟩
  choose S hSA hScard hSsum using hwitness
  let W := Finset.univ.biUnion S
  have hSW (q : H) : S q ⊆ W := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, ha⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨q, _, haq⟩ := Finset.mem_biUnion.mp ha
    exact hSA q haq
  · calc
      W.card ≤ ∑ q : H, (S q).card := Finset.card_biUnion_le
      _ ≤ ∑ _q : H, Δ.index := Finset.sum_le_sum (fun q _ => by have := hScard q; omega)
      _ = Fintype.card H * Δ.index := by simp
      _ ≤ Δ.index * Δ.index := Nat.mul_le_mul_right _ hHcard
      _ = Δ.index ^ 2 := (pow_two _).symm
  · intro x hx
    let q : H := ⟨ψ x, AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
    refine ⟨S q, hSW q, hScard q, ?_⟩
    exact (delta_quotient_eq_iff_sub_mem Δ _ _).mp (hSsum q)

end Erdos587.CFP
