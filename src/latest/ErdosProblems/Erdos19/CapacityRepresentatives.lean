import ErdosProblems.Erdos19.Completion

/-! # A capacitated form of the completion Hall lemma -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_representatives_of_capacity_and_bounded_forbidden
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (capacity : V → ℕ) (L : I → Finset V) (a : ℕ)
    (htotal : Fintype.card I ≤ ∑ v : V, capacity v)
    (hlist : ∀ i, a ≤ ∑ v ∈ L i, capacity v)
    (hforbidden : ∀ v, ((univ : Finset I).filter fun i ↦ v ∉ L i).card ≤ a) :
    ∃ f : I → V, (∀ i, f i ∈ L i) ∧
      ∀ v, ((univ : Finset I).filter fun i ↦ f i = v).card ≤ capacity v := by
  classical
  let Slot := Σ v : V, Fin (capacity v)
  let lists : I → Finset Slot := fun i ↦ univ.filter fun p ↦ p.1 ∈ L i
  have hslots : Fintype.card Slot = ∑ v : V, capacity v := by
    simp only [Slot, Fintype.card_sigma, Fintype.card_fin]
  have hlists : ∀ i, (lists i).card = ∑ v ∈ L i, capacity v := by
    intro i
    have hsum : (lists i).card = ∑ p : Slot, if p.1 ∈ L i then 1 else 0 := by
      simp only [sum_boole]
      rfl
    rw [hsum, Fintype.sum_sigma]
    change (∑ v : V, ∑ _j : Fin (capacity v), if v ∈ L i then 1 else 0) = _
    calc
      (∑ v : V, ∑ _j : Fin (capacity v), if v ∈ L i then 1 else 0) =
          ∑ v : V, if v ∈ L i then capacity v else 0 := by
        apply sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ = ∑ v ∈ L i, capacity v := by simp [← sum_filter]
  obtain ⟨g, hg, hmem⟩ := exists_injective_mem_of_bounded_forbidden
    (univ : Finset Slot) lists a (by simpa only [card_univ, hslots] using htotal)
    (fun i ↦ by rw [hlists]; exact hlist i) (by
      intro p _
      simpa only [lists, mem_filter, mem_univ, true_and] using hforbidden p.1)
  let f : I → V := fun i ↦ (g i).1
  refine ⟨f, fun i ↦ (mem_filter.mp (hmem i)).2, ?_⟩
  intro v
  let code : {i : I // f i = v} → {p : Slot // p.1 = v} :=
    fun i ↦ ⟨g i.1, i.2⟩
  have hcode : Function.Injective code := by
    intro i j h
    exact Subtype.ext (hg (congrArg Subtype.val h))
  let equiv : {p : Slot // p.1 = v} ≃ Fin (capacity v) :=
    { toFun := fun p ↦ Fin.cast (congrArg capacity p.2) p.1.2
      invFun := fun i ↦ ⟨⟨v, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨w, i⟩, hw⟩
        dsimp only at hw
        subst w
        rfl
      right_inv := fun i ↦ rfl }
  have hcard := Fintype.card_le_of_injective code hcode
  have hcap : Fintype.card {p : Slot // p.1 = v} = capacity v := by
    simpa only [Fintype.card_fin] using Fintype.card_congr equiv
  rw [hcap] at hcard
  simpa only [Fintype.card_subtype] using hcard

#print axioms exists_representatives_of_capacity_and_bounded_forbidden

end Erdos19
