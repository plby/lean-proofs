import ErdosProblems.Erdos1105.Basic
import ErdosProblems.Erdos767.EGApi

/-!
# Finite graph disintegration

The `d`-core is the largest induced subgraph of minimum degree greater than
`d`. Vertices outside it can be deleted one at a time at cost at most `d`
edges each. These are the counting tools for Kopylov's disintegration method.
-/

namespace Erdos1105

open SimpleGraph Finset

noncomputable def degreeWithin {V : Type*} (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ := by
  classical
  exact (S.filter (G.Adj v)).card

lemma degreeWithin_mono {V : Type*} (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) (v : V) :
    degreeWithin G S v ≤ degreeWithin G T v := by
  classical
  exact card_le_card (filter_subset_filter _ hST)

lemma degreeWithin_le_of_neighbors_mem {V : Type*} (G : SimpleGraph V)
    (S T : Finset V) (v : V) (h : ∀ w ∈ S, G.Adj v w → w ∈ T) :
    degreeWithin G S v ≤ degreeWithin G T v := by
  classical
  apply card_le_card
  intro w hw
  exact mem_filter.mpr ⟨h w (mem_filter.mp hw).1 (mem_filter.mp hw).2, (mem_filter.mp hw).2⟩

noncomputable def vertexCore {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Finset V := by
  classical
  exact ((univ : Finset (Finset V)).filter
    (fun S ↦ ∀ v ∈ S, d < degreeWithin G S v)).biUnion id

theorem subset_vertexCore {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) {S : Finset V}
    (hS : ∀ v ∈ S, d < degreeWithin G S v) : S ⊆ vertexCore G d := by
  classical
  intro v hv
  exact mem_biUnion.mpr ⟨S, mem_filter.mpr ⟨mem_univ _, hS⟩, hv⟩

theorem vertexCore_degree {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    {v : V} (hv : v ∈ vertexCore G d) : d < degreeWithin G (vertexCore G d) v := by
  classical
  obtain ⟨S, hS, hvS⟩ := mem_biUnion.mp hv
  have hmin := (mem_filter.mp hS).2
  exact (hmin v hvS).trans_le (degreeWithin_mono G (subset_vertexCore G d hmin) v)

theorem exists_low_degree_outside_core {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    {S : Finset V} (hsub : vertexCore G d ⊆ S) (hne : S ≠ vertexCore G d) :
    ∃ v ∈ S, v ∉ vertexCore G d ∧ degreeWithin G S v ≤ d := by
  classical
  by_contra h
  push Not at h
  apply hne
  apply Subset.antisymm ?_ hsub
  apply subset_vertexCore
  intro v hv
  by_cases hvc : v ∈ vertexCore G d
  · exact (vertexCore_degree G d hvc).trans_le (degreeWithin_mono G hsub v)
  · exact h v hv hvc

/-- Deleting one vertex removes precisely its incident edges inside the set. -/
theorem edgesInside_erase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {v : V} (hv : v ∈ S) :
    (E767EGApi.edgesInside G S).card =
      (E767EGApi.edgesInside G (S.erase v)).card + degreeWithin G S v := by
  classical
  let N := S.filter (G.Adj v)
  have heq : E767EGApi.edgesInside G S = E767EGApi.edgesInside G (S.erase v) ∪
      N.image (fun w ↦ s(v, w)) := by
    ext e
    simp only [E767EGApi.edgesInside, mem_filter, mem_union, mem_image]
    constructor
    · rintro ⟨he, hS⟩
      by_cases hve : v ∈ e
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
        apply Or.inr
        refine ⟨w, mem_filter.mpr ⟨?_, by simpa using he⟩, rfl⟩
        exact hS (by simp)
      · apply Or.inl
        refine ⟨he, ?_⟩
        intro w hw
        refine mem_erase.mpr ⟨?_, hS hw⟩
        intro hwv
        subst w
        exact hve (by simpa using hw)
    · rintro (⟨he, hS⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨he, hS.trans (erase_subset _ _)⟩
      · have hwS := (mem_filter.mp hw).1
        have hvw := (mem_filter.mp hw).2
        refine ⟨by simpa using hvw, ?_⟩
        intro x hx
        have hx : x = v ∨ x = w := by simpa using hx
        rcases hx with rfl | rfl
        · exact hv
        · exact hwS
  have hdisj : Disjoint (E767EGApi.edgesInside G (S.erase v)) (N.image fun w ↦ s(v, w)) := by
    rw [Finset.disjoint_left]
    intro e he heN
    obtain ⟨w, _, rfl⟩ := mem_image.mp heN
    have hsubset := (mem_filter.mp he).2
    have hv' : v ∈ S.erase v := hsubset (by simp)
    exact (mem_erase.mp hv').1 rfl
  rw [heq, card_union_of_disjoint hdisj, card_image_of_injective]
  · simp only [degreeWithin, Nat.add_left_cancel_iff]
    apply congrArg Finset.card
    ext w
    simp [N]
  · intro a b hab
    rcases Sym2.eq_iff.mp hab with h | h
    · exact h.2
    · exact h.2.trans h.1

theorem edgesInside_le_core_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (S : Finset V) (hsub : vertexCore G d ⊆ S) :
    (E767EGApi.edgesInside G S).card ≤ (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * (S.card - (vertexCore G d).card) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases heq : S = vertexCore G d
    · simp [heq]
    · obtain ⟨v, hv, hvc, hdeg⟩ := exists_low_degree_outside_core G d hsub heq
      have hsub' : vertexCore G d ⊆ S.erase v := by
        intro w hw
        exact mem_erase.mpr ⟨fun h ↦ hvc (h ▸ hw), hsub hw⟩
      have hlt : (S.erase v).card < m := by
        rw [card_erase_of_mem hv, ← hcard]
        exact Nat.sub_lt (card_pos.mpr ⟨v, hv⟩) (by omega)
      have hind := ih (S.erase v).card hlt (S.erase v) hsub' rfl
      rw [← hcard]
      rw [edgesInside_erase G hv]
      have hc := card_le_card hsub'
      rw [card_erase_of_mem hv] at hc hind
      have hdiff : S.card - (vertexCore G d).card =
          (S.card - 1 - (vertexCore G d).card) + 1 := by
        have hpos := card_pos.mpr ⟨v, hv⟩
        omega
      rw [hdiff, Nat.mul_add, Nat.mul_one]
      omega

theorem edgesInside_le_choose {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (E767EGApi.edgesInside G S).card ≤ S.card.choose 2 := by
  rw [E767EGApi.card_edgesInside]
  simpa using (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two

theorem edges_le_core_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    G.edgeFinset.card ≤ (vertexCore G d).card.choose 2 +
      d * (Fintype.card V - (vertexCore G d).card) := by
  classical
  have h := edgesInside_le_core_add G d univ (subset_univ _)
  have heq : E767EGApi.edgesInside G univ = G.edgeFinset := by
    simp [E767EGApi.edgesInside]
  rw [heq, card_univ] at h
  exact h.trans (Nat.add_le_add_right (edgesInside_le_choose G (vertexCore G d)) _)

/-- The usual sharp edge bound for a graph with empty `d`-core. -/
theorem edgesInside_le_of_core_empty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hempty : vertexCore G d = ∅)
    (S : Finset V) :
    (E767EGApi.edgesInside G S).card ≤ d.choose 2 + d * (S.card - d) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases hsmall : m ≤ d
    · have hbound : (E767EGApi.edgesInside G S).card ≤ d.choose 2 :=
        (edgesInside_le_choose G S).trans (Nat.choose_le_choose 2 (by omega))
      exact hbound.trans (Nat.le_add_right _ _)
    · have hsub : vertexCore G d ⊆ S := by simp [hempty]
      have hne : S ≠ vertexCore G d := by
        intro h
        rw [h, hempty, card_empty] at hcard
        omega
      obtain ⟨v, hv, _, hdeg⟩ := exists_low_degree_outside_core G d hsub hne
      have hlt : (S.erase v).card < m := by
        rw [card_erase_of_mem hv, ← hcard]
        exact Nat.sub_lt (card_pos.mpr ⟨v, hv⟩) (by omega)
      have hind := ih _ hlt (S.erase v) rfl
      rw [← hcard, edgesInside_erase G hv]
      rw [card_erase_of_mem hv] at hind
      have hdiff : S.card - d = S.card - 1 - d + 1 := by omega
      rw [hdiff, Nat.mul_add, Nat.mul_one]
      omega

theorem edges_le_of_core_empty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hempty : vertexCore G d = ∅) :
    G.edgeFinset.card ≤ d.choose 2 + d * (Fintype.card V - d) := by
  simpa [E767EGApi.edgesInside] using edgesInside_le_of_core_empty G d hempty univ

end Erdos1105

#print axioms Erdos1105.edgesInside_le_core_add
#print axioms Erdos1105.edges_le_of_core_empty
