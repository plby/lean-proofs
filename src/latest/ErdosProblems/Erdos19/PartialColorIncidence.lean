import ErdosProblems.Erdos19.CoverBoundedExtension
import ErdosProblems.Erdos19.PairColoring

/-! # Colors incident with a vertex in a partial hypergraph coloring -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [DecidableEq C]

noncomputable def usedColorsOn (H : SetHypergraph V) (S : Finset H) (c : H → C)
    (v : V) : Finset C := (S.filter fun e ↦ v ∈ e.1).image c

theorem mem_usedColorsOn (H : SetHypergraph V) (S : Finset H) (c : H → C)
    (v : V) (a : C) :
    a ∈ H.usedColorsOn S c v ↔ ∃ e ∈ S, v ∈ e.1 ∧ c e = a := by
  simp only [usedColorsOn, mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hv⟩, hcolor⟩
    exact ⟨e, he, hv, hcolor⟩
  · rintro ⟨e, he, hv, hcolor⟩
    exact ⟨e, ⟨he, hv⟩, hcolor⟩

theorem usedColorsOn_iff_covered (H : SetHypergraph V) (S : Finset H) (c : H → C)
    (v : V) (a : C) :
    a ∈ H.usedColorsOn S c v ↔ v ∈ H.coveredVertices {e | e ∈ S ∧ c e = a} := by
  rw [H.mem_usedColorsOn]
  simp only [coveredVertices, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, hv, hcolor⟩
    exact ⟨e, ⟨he, hcolor⟩, hv⟩
  · rintro ⟨e, ⟨he, hcolor⟩, hv⟩
    exact ⟨e, he, hv, hcolor⟩

theorem exists_star_other_vertices (H : SetHypergraph V) (T : Finset H) (u : V)
    (hpair : ∀ e ∈ T, e.1.ncard = 2) (hcenter : ∀ e ∈ T, u ∈ e.1) :
    ∃ other : T → V, Function.Injective other ∧
      ∀ e : T, u ≠ other e ∧ e.1.1 = {u, other e} := by
  have hex (e : T) := exists_pair_at (hpair e.1 e.2) (hcenter e.1 e.2)
  choose other hne hsupport using hex
  refine ⟨other, ?_, fun e ↦ ⟨hne e, hsupport e⟩⟩
  intro e f hef
  apply Subtype.ext
  apply Subtype.ext
  rw [hsupport e, hsupport f, hef]

theorem card_blocked_indices_le_cover (H : SetHypergraph V) (S : Finset H)
    (c : H → C) {I : Type*} [Fintype I] (point : I → V)
    (hinj : Function.Injective point) (a : C) :
    (univ.filter fun i ↦ a ∈ H.usedColorsOn S c (point i)).card ≤
      (H.coveredVertices {e | e ∈ S ∧ c e = a}).ncard := by
  classical
  rw [← card_image_of_injective _ hinj]
  rw [Set.ncard_eq_toFinset_card']
  apply card_le_card
  intro v hv
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
  exact Set.mem_toFinset.mpr ((H.usedColorsOn_iff_covered S c (point i) a).mp
    (mem_filter.mp hi).2)

theorem used_colors_add_star_card_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (S T : Finset H) (hST : Disjoint S T)
    (c : H → C) (u : V) (hTu : ∀ e ∈ T, u ∈ e.1) :
    (H.usedColorsOn S c u).card + T.card ≤ Fintype.card V - 1 := by
  classical
  let I := S.filter fun e ↦ u ∈ e.1
  have hI : I.card + T.card = (I ∪ T).card :=
    (card_union_of_disjoint (hST.mono_left (filter_subset _ _))).symm
  have hsub : (I ∪ T : Finset H) ⊆ (H.incidentEdges u).toFinset := by
    intro e he
    apply Set.mem_toFinset.mpr
    rcases mem_union.mp he with he | he
    · exact (mem_filter.mp he).2
    · exact hTu e he
  have hcard : I.card + T.card ≤ (H.incidentEdges u).ncard := by
    rw [hI, Set.ncard_eq_toFinset_card']
    exact card_le_card hsub
  have hinc := H.incidentEdges_ncard_le_div_of_min_size hlinear u 2 (by norm_num) hmin
  norm_num only [Nat.reduceSub, Nat.div_one] at hinc
  have hused : (H.usedColorsOn S c u).card ≤ I.card := card_image_le
  omega

#print axioms used_colors_add_star_card_le
#print axioms card_blocked_indices_le_cover

end Erdos19.SetHypergraph
