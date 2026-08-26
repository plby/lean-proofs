import ErdosProblems.Erdos19.PartialColorIncidence
import ErdosProblems.Erdos19.ReservedStarLists

/-! # Selecting compatible colors for every edge of a two-edge star -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_compatible_star_colors (H : SetHypergraph V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (S T : Finset H) (hST : Disjoint S T)
    (u : V) (hTu : ∀ e ∈ T, u ∈ e.1) (hpair : ∀ e ∈ T, e.1.ncard = 2)
    (n : ℕ) (hvertices : Fintype.card V = n) (c : H → Fin n)
    (reserved : Finset (Fin n)) (A d : ℕ)
    (hcover : ∀ a, (H.coveredVertices {e | e ∈ S ∧ c e = a}).ncard ≤ A)
    (hcenter : (reserved ∩ H.usedColorsOn S c u).card ≤ d)
    (hleaf : ∀ e ∈ T, ∀ v ∈ e.1, (reserved ∩ H.usedColorsOn S c v).card ≤ d)
    (hslack : A + 2 * d ≤ reserved.card) :
    ∃ color : T → Fin n, Function.Injective color ∧
      ∀ e : T, ∀ v ∈ e.1.1, color e ∉ H.usedColorsOn S c v := by
  classical
  obtain ⟨other, hinj, hother⟩ := H.exists_star_other_vertices T u hpair hTu
  let blocked : T → Finset (Fin n) := fun e ↦ H.usedColorsOn S c (other e)
  have hpalette : Fintype.card T + (H.usedColorsOn S c u).card ≤ Fintype.card (Fin n) := by
    have h := H.used_colors_add_star_card_le hlinear hmin S T hST c u hTu
    rw [hvertices] at h
    simp only [Fintype.card_coe, Fintype.card_fin]
    omega
  have hblocked (e : T) : (reserved ∩ blocked e).card ≤ d := by
    apply hleaf e.1 e.2 (other e)
    rw [(hother e).2]
    exact Or.inr rfl
  have hclass : ∀ a, a ∉ H.usedColorsOn S c u →
      (univ.filter fun e : T ↦ a ∈ blocked e).card ≤ A := by
    intro a _
    exact (H.card_blocked_indices_le_cover S c other hinj a).trans (hcover a)
  obtain ⟨color, hcolorInj, hcolor⟩ := exists_star_colors_using_reserve reserved
    (H.usedColorsOn S c u) blocked A d hpalette hcenter hblocked hclass hslack
  refine ⟨color, hcolorInj, ?_⟩
  intro e v hv
  rw [(hother e).2] at hv
  rcases hv with rfl | rfl
  · exact (hcolor e).1
  · exact (hcolor e).2

#print axioms exists_compatible_star_colors

end Erdos19.SetHypergraph
