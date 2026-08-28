import ErdosProblems.Erdos577.CommonReplacement
import ErdosProblems.Erdos577.CliqueLabels

/-! Replacement alternatives from included rows and a three-vertex contact set. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma CommonReplacement.symm {b c z : V} {s : Finset V}
    (h : CommonReplacement G b c z s) : CommonReplacement G c b z s := by
  obtain ⟨u, hu, hbu, hcu, hrep⟩ := h
  exact ⟨u, hu, hcu, hbu, hrep⟩

lemma Quadrilateral.replace_in_three_contacts (q : Quadrilateral G) (z : V)
    (hz : z ∉ q.support) (s : Finset V) (hs : s ⊆ q.support) (hcard : 3 ≤ s.card)
    (hrow : ∀ v ∈ s, G.Adj z v) : ∃ u ∈ s, QuadOn G (insert z (q.support.erase u)) := by
  let indices : Finset (Fin 4) := univ.filter fun i ↦ q i ∈ s
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have himage : indices.image q = s := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hi).2
    · intro hv
      obtain ⟨i, rfl⟩ := (q.mem_support v).mp (hs hv)
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hv⟩, rfl⟩
  have hindices : 3 ≤ indices.card := by
    rw [← himage, card_image_of_injective _ hinj] at hcard
    exact hcard
  have hfinite : ∀ s : Finset (Fin 4), 3 ≤ s.card →
      ∃ i ∈ s, ∀ j : Fin 4, (SimpleGraph.cycleGraph 4).Adj i j → j ∈ s := by
    decide +kernel
  obtain ⟨i, hi, hneighbors⟩ := hfinite indices hindices
  refine ⟨q i, (mem_filter.mp hi).2, q.quad_replaceAt i z hz ?_⟩
  intro j hij
  exact hrow (q j) (mem_filter.mp (hneighbors j hij)).2

variable [DecidableRel G.Adj]

lemma common_replacement_clique_alternatives {s : Finset V} (hcl : G.IsNClique 4 s)
    (r c w : V) (hc : c ∉ s) (hw : w ∉ s)
    (hcr : 3 ≤ degreeIn G c s) (hwr : 2 ≤ degreeIn G w s)
    (hr : 0 < degreeIn G r s) (hsub : ∀ u ∈ s, G.Adj r u → G.Adj c u) :
    CommonReplacement G r w c s ∨ CommonReplacement G r c w s := by
  by_cases hcommon : ∃ u ∈ s, G.Adj r u ∧ G.Adj w u
  · obtain ⟨u, hu, hru, hwu⟩ := hcommon
    exact Or.inl ⟨u, hu, hru, hwu, clique_replace_of_degree_three hcl hc hcr hu⟩
  · obtain ⟨u, hu⟩ := card_pos.mp hr
    obtain ⟨hus, hru⟩ := mem_filter.mp hu
    have hwu : ¬G.Adj w u := fun he ↦ hcommon ⟨u, hus, hru, he⟩
    have hid := degreeIn_erase_add G w u hus
    rw [if_neg hwu] at hid
    have htwo : 2 ≤ degreeIn G w (s.erase u) := by omega
    exact Or.inr ⟨u, hus, hru, hsub u hus hru,
      (clique_replace_iff_two_contacts hcl hw hus).mpr htwo⟩

end Erdos577
