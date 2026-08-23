import ErdosProblems.Erdos1105.Disintegration

namespace Erdos1105

open SimpleGraph Finset

lemma degreeWithin_le_card_sub_one {V : Type*} (G : SimpleGraph V)
    {S : Finset V} {v : V} (hv : v ∈ S) : degreeWithin G S v ≤ S.card - 1 := by
  classical
  have hsub : S.filter (G.Adj v) ⊆ S.erase v := by
    intro w hw
    exact mem_erase.mpr ⟨(mem_filter.mp hw).2.ne.symm, (mem_filter.mp hw).1⟩
  simpa [degreeWithin, card_erase_of_mem hv] using card_le_card hsub

lemma degreeWithin_eq_card_of_all_adj {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (v : V) (h : ∀ w ∈ S, G.Adj v w) :
    degreeWithin G S v = S.card := by
  classical
  apply congrArg Finset.card
  exact filter_eq_self.mpr h

lemma degreeWithin_clique {V : Type*} (G : SimpleGraph V)
    {S : Finset V} (hS : G.IsClique (S : Set V)) {v : V} (hv : v ∈ S) :
    degreeWithin G S v = S.card - 1 := by
  classical
  have heq : S.filter (G.Adj v) = S.erase v := by
    ext w
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hw, hadj⟩
      exact ⟨hadj.ne.symm, hw⟩
    · rintro ⟨hne, hw⟩
      exact ⟨hw, hS hv hw hne.symm⟩
  simpa only [degreeWithin, card_erase_of_mem hv] using congrArg Finset.card heq

lemma vertexCore_antitone {V : Type*} [Fintype V] (G : SimpleGraph V)
    {a d : ℕ} (had : a ≤ d) : vertexCore G d ⊆ vertexCore G a := by
  apply subset_vertexCore
  intro v hv
  exact had.trans_lt (vertexCore_degree G d hv)

lemma vertexCore_card_lower {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) (hne : (vertexCore G d).Nonempty) : d + 2 ≤ (vertexCore G d).card := by
  obtain ⟨v, hv⟩ := hne
  have h := (vertexCore_degree G d hv).trans_le (degreeWithin_le_card_sub_one G hv)
  omega

/-- A vertex complete to a nonempty core is itself in that core. -/
lemma mem_vertexCore_of_all_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) (hne : (vertexCore G d).Nonempty) {v : V}
    (hadj : ∀ w ∈ vertexCore G d, G.Adj v w) : v ∈ vertexCore G d := by
  classical
  have hmin : ∀ w ∈ insert v (vertexCore G d),
      d < degreeWithin G (insert v (vertexCore G d)) w := by
    intro w hw
    rcases mem_insert.mp hw with heq | hw
    · subst w
      have hdeg := degreeWithin_eq_card_of_all_adj G (vertexCore G d) v hadj
      have hcard := vertexCore_card_lower G d hne
      have hm := degreeWithin_mono G (subset_insert v (vertexCore G d)) v
      omega
    · exact (vertexCore_degree G d hw).trans_le
        (degreeWithin_mono G (subset_insert v (vertexCore G d)) w)
  exact subset_vertexCore G d hmin (mem_insert_self _ _)

lemma universal_mem_vertexCore {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) (hne : (vertexCore G d).Nonempty) {u : V} (hu : G.IsUniversal u) :
    u ∈ vertexCore G d := by
  by_contra hunot
  apply hunot
  apply mem_vertexCore_of_all_adj G d hne
  intro w hw
  exact hu (fun h ↦ hunot (h ▸ hw))

end Erdos1105
