import Mathlib
import ErdosProblems.Erdos550.TauFineComponentIndexing

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Vertex-to-component maps and bundled indexed τ-fine data

This is the final quotient-to-finite-batch interface for the tree partition.
Every nonseed vertex receives an index in `NonseedComponent`; membership in the
indexed component is characterized exactly, internal edges preserve the index,
and seed attachments are transported to this finite indexing.  The concluding
theorem chooses the separator and returns all size, mass, attachment, and edge
classification facts in one package.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The finite shrub-component index of a nonseed vertex. -/
noncomputable def nonseedComponentOf
    (T : SimpleGraph α) (S : Finset α) (v : α) (hv : v ∉ S) :
    NonseedComponent T S :=
  ⟨seedComponent T S v, by
    unfold nonseedComponents
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩⟩

@[simp] lemma nonseedComponentOf_val
    (T : SimpleGraph α) (S : Finset α) (v : α) (hv : v ∉ S) :
    (nonseedComponentOf T S v hv).1 = seedComponent T S v := rfl

lemma mem_component_of_nonseed
    (T : SimpleGraph α) (S : Finset α) (v : α) (hv : v ∉ S) :
    v ∈ componentNonseedVertices T S (nonseedComponentOf T S v hv).1 := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hv, mem_seedComponent_supp _ _ _ ⟩

lemma mem_indexed_component_iff
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) (v : α) :
    v ∈ componentNonseedVertices T S c.1 ↔
      ∃ hv : v ∉ S, nonseedComponentOf T S v hv = c := by
  refine' ⟨ fun h => _, fun ⟨ hv, h ⟩ => _ ⟩;
  · unfold componentNonseedVertices at h; simp_all +decide [ Finset.mem_filter ] ;
    exact Subtype.ext h.2;
  · exact h ▸ mem_component_of_nonseed T S v hv

lemma nonseedComponentOf_eq_iff
    (T : SimpleGraph α) (S : Finset α) {v w : α}
    (hv : v ∉ S) (hw : w ∉ S) :
    nonseedComponentOf T S v hv = nonseedComponentOf T S w hw ↔
      seedComponent T S v = seedComponent T S w := by
  exact ⟨ fun h => congr_arg Subtype.val h, fun h => Subtype.ext h ⟩

lemma nonseedComponentOf_eq_of_adj
    (T : SimpleGraph α) (S : Finset α) {v w : α}
    (hvw : T.Adj v w) (hv : v ∉ S) (hw : w ∉ S) :
    nonseedComponentOf T S v hv = nonseedComponentOf T S w hw := by
  convert! nonseedComponentOf_eq_iff T S hv hw |>.2 ( seedComponent_eq_of_adj_of_nonseed T S hvw hv hw )

lemma seed_attaches_to_nonseedComponentOf
    (T : SimpleGraph α) (S : Finset α) {s v : α}
    (hsv : T.Adj s v) (hs : s ∈ S) (hv : v ∉ S) :
    s ∈ componentSeeds T S (nonseedComponentOf T S v hv).1 := by
  convert! left_seed_recorded_of_adj T S hs hsv using 1

lemma component_attachment_witness
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) {s : α}
    (hs : s ∈ componentSeeds T S c.1) :
    ∃ v ∈ componentNonseedVertices T S c.1, T.Adj s v := by
  obtain ⟨ v, hv, hv' ⟩ := Finset.mem_filter.mp hs |>.2;
  refine' ⟨ v, _, hv' ⟩;
  convert! hv using 1;
  exact componentNonseedVertices_eq_supp T S c

/-
Exact edge classification using the finite component index.
-/
theorem tauFine_indexed_edge_classification
    (T : SimpleGraph α) (S : Finset α) {a b : α} (hab : T.Adj a b) :
    (a ∈ S ∧ b ∈ S) ∨
    (∃ ha : a ∉ S, ∃ hb : b ∉ S,
      nonseedComponentOf T S a ha = nonseedComponentOf T S b hb) ∨
    (∃ _ha : a ∈ S, ∃ hb : b ∉ S,
      a ∈ componentSeeds T S (nonseedComponentOf T S b hb).1) ∨
    (∃ ha : a ∉ S, ∃ _hb : b ∈ S,
      b ∈ componentSeeds T S (nonseedComponentOf T S a ha).1) := by
  convert! tauFine_edge_classification T S hab using 1;
  simp +decide [ nonseedComponentOf_eq_iff ];
  grind

/-
Fully bundled finite-batch form of the τ-fine decomposition.
-/
theorem tree_tau_fine_indexed_data
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 1 / τ ∧
      (∀ c : NonseedComponent T S,
        ((componentNonseedVertices T S c.1).card : ℝ)
          ≤ τ * Fintype.card α) ∧
      (∀ c : NonseedComponent T S,
        (componentSeeds T S c.1).card ≤ Nat.floor (1 / τ)) ∧
      (∑ c : NonseedComponent T S,
        (componentNonseedVertices T S c.1).card)
          = Fintype.card α - S.card ∧
      Finset.univ.biUnion (fun c : NonseedComponent T S =>
        componentNonseedVertices T S c.1) = Finset.univ \ S ∧
      Set.Pairwise (Set.univ : Set (NonseedComponent T S))
        (fun c d => Disjoint (componentNonseedVertices T S c.1)
          (componentNonseedVertices T S d.1)) ∧
      (∀ ⦃a b : α⦄, T.Adj a b →
        (a ∈ S ∧ b ∈ S) ∨
        (∃ ha : a ∉ S, ∃ hb : b ∉ S,
          nonseedComponentOf T S a ha = nonseedComponentOf T S b hb) ∨
        (∃ _ha : a ∈ S, ∃ hb : b ∉ S,
          a ∈ componentSeeds T S (nonseedComponentOf T S b hb).1) ∨
        (∃ ha : a ∉ S, ∃ _hb : b ∈ S,
          b ∈ componentSeeds T S (nonseedComponentOf T S a ha).1)) := by
  obtain ⟨S, hS⟩ := tree_tau_fine_with_attachments T hT τ hτ hn;
  refine' ⟨ S, hS.1, _, _, _, _, _ ⟩;
  · convert! nonseed_component_size_bound T S _ hS.2.1 using 1;
  · exact fun c => hS.2.2 c.1;
  · convert! sum_componentNonseedVertices_card T S using 1;
  · convert! biUnion_componentNonseedVertices T S using 1;
  · exact ⟨ componentNonseedVertices_pairwise_disjoint T S, fun a b hab => by simpa using! tauFine_indexed_edge_classification T S hab ⟩

end Erdos550
