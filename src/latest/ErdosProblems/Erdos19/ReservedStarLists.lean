import ErdosProblems.Erdos19.Completion

/-! # A reserved palette guarantees Hall's condition for a remaining star

The palette available at the center may be larger than the reserved palette.
The reserved colors supply a uniform lower bound on each leaf's list; bounded
color-class coverage supplies the complementary Hall condition.
-/

namespace Erdos19

open Finset

theorem card_reserved_difference_lower {C : Type*} [DecidableEq C]
    (R X Y : Finset C) :
    R.card ≤ (R \ (X ∪ Y)).card + (R ∩ X).card + (R ∩ Y).card := by
  have hsplit := card_sdiff_add_card_inter R (X ∪ Y)
  have hmeet : R ∩ (X ∪ Y) = (R ∩ X) ∪ (R ∩ Y) := Finset.inter_union_distrib_left R X Y
  rw [hmeet] at hsplit
  have hbound := card_union_le (R ∩ X) (R ∩ Y)
  omega

theorem exists_star_colors_using_reserve {I C : Type*} [Fintype I]
    [Fintype C] [DecidableEq C]
    (reserved center : Finset C) (blocked : I → Finset C) (A d : ℕ)
    (hpalette : Fintype.card I + center.card ≤ Fintype.card C)
    (hcenter : (reserved ∩ center).card ≤ d)
    (hleaf : ∀ i, (reserved ∩ blocked i).card ≤ d)
    (hclass : ∀ c, c ∉ center → (univ.filter fun i ↦ c ∈ blocked i).card ≤ A)
    (hslack : A + 2 * d ≤ reserved.card) :
    ∃ color : I → C, Function.Injective color ∧
      ∀ i, color i ∉ center ∧ color i ∉ blocked i := by
  classical
  let P := (univ : Finset C) \ center
  let L : I → Finset C := fun i ↦ P \ blocked i
  have hP : Fintype.card I ≤ P.card := by
    have heq : P.card = Fintype.card C - center.card := by
      dsimp only [P]
      rw [card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  have hL : ∀ i, A ≤ (L i).card := by
    intro i
    have hbound := card_reserved_difference_lower reserved center (blocked i)
    have hc := hcenter
    have hl := hleaf i
    have hsub : reserved \ (center ∪ blocked i) ⊆ L i := by
      intro c hc
      obtain ⟨_, hnot⟩ := mem_sdiff.mp hc
      have hnc : c ∉ center := fun h ↦ hnot (mem_union_left _ h)
      have hnb : c ∉ blocked i := fun h ↦ hnot (mem_union_right _ h)
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hnc⟩, hnb⟩
    have hcard := card_le_card hsub
    omega
  have hforbidden : ∀ c ∈ P, (univ.filter fun i ↦ c ∉ L i).card ≤ A := by
    intro c hc
    have hnot := (mem_sdiff.mp hc).2
    have hfilter : (univ.filter fun i ↦ c ∉ L i) =
        (univ.filter fun i ↦ c ∈ blocked i) := by
      ext i
      simp [L, hc]
    rw [hfilter]
    exact hclass c hnot
  obtain ⟨color, hinj, hcolor⟩ := exists_injective_mem_of_bounded_forbidden P L A hP hL hforbidden
  refine ⟨color, hinj, ?_⟩
  intro i
  have h := mem_sdiff.mp (hcolor i)
  exact ⟨(mem_sdiff.mp h.1).2, h.2⟩

#print axioms exists_star_colors_using_reserve

end Erdos19
