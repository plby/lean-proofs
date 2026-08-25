/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The exact-order part of the Thomas--Wollan minimal-pair argument. -/

import ErdosProblems.Erdos717.NoRigid
import ErdosProblems.Erdos717.FullArms

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A path separator can be oriented as a separation with all sources on
the left and all targets on the right.  Unlike the usual proper-separation
form, this statement permits source and target vertices to belong to the
separator. -/
theorem exists_separation_of_path_separator_with_sides
    {G : SimpleGraph V} {A B S : Set V}
    (hsep : Erdos599.Countable.Separates G A B S) :
    ∃ s : Erdos718.Separation G,
      A ⊆ (s.left : Set V) ∧ B ⊆ (s.right : Set V) ∧
        s.separator.card = S.ncard := by
  classical
  let H := Erdos599.Countable.outsideGraph G S
  let R : Finset V := Finset.univ.filter fun v =>
    ∃ a ∈ A, a ∉ S ∧ H.Reachable a v
  have source_left (a : V) (ha : a ∈ A) : a ∈ S.toFinset ∪ R := by
    by_cases haS : a ∈ S
    · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr haS)
    · apply Finset.mem_union_right
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, haS, SimpleGraph.Reachable.refl a⟩
  have target_right (b : V) (hb : b ∈ B) :
      b ∈ S.toFinset ∪ (Finset.univ \ R) := by
    by_cases hbS : b ∈ S
    · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr hbS)
    · apply Finset.mem_union_right
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ b, ?_⟩
      intro hbR
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hbR
      rcases hbR with ⟨a, ha, haS, hab⟩
      rcases hab.exists_isPath with ⟨q, hq⟩
      let qG := q.mapLe (Erdos599.Countable.outsideGraph_le G S)
      rcases hsep a ha b hb qG (hq.mapLe _) with ⟨x, hxqG, hxS⟩
      have hxq : x ∈ q.support := by
        simpa [qG, Walk.support_mapLe_eq_support] using hxqG
      exact (Erdos599.Countable.Walk.vertex_not_mem_of_outsideGraph q haS hxq) hxS
  let s : Erdos718.Separation G := {
    left := S.toFinset ∪ R
    right := S.toFinset ∪ (Finset.univ \ R)
    cover := by
      ext v
      simp only [Finset.mem_union, Set.mem_toFinset, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      tauto
    not_adj := by
      intro a b haL haR hbR hbL hab
      have haS : a ∉ S := by
        intro haS
        exact haR (Finset.mem_union_left _ (Set.mem_toFinset.mpr haS))
      have haReach : a ∈ R := by
        rcases Finset.mem_union.mp haL with haSin | haRin
        · exact (haS (Set.mem_toFinset.mp haSin)).elim
        · exact haRin
      have hbS : b ∉ S := by
        intro hbS
        exact hbL (Finset.mem_union_left _ (Set.mem_toFinset.mpr hbS))
      have hbNotReach : b ∉ R := by
        intro hbReach
        exact hbL (Finset.mem_union_right _ hbReach)
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at haReach
      rcases haReach with ⟨a₀, ha₀, ha₀S, ha₀a⟩
      have habH : H.Adj a b := ⟨hab, haS, hbS⟩
      apply hbNotReach
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a₀, ha₀, ha₀S, ha₀a.trans habH.reachable⟩
  }
  refine ⟨s, ?_, ?_, ?_⟩
  · exact fun a ha => source_left a ha
  · exact fun b hb => target_right b hb
  · rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp only [Erdos718.Separation.separator, s, Finset.mem_inter,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.mem_toFinset]
    tauto

/-- A separation separates arbitrary sets placed on its two (possibly
overlapping) sides. -/
theorem separation_separator_separates_of_subsets
    {G : SimpleGraph V} (s : Erdos718.Separation G)
    {A B : Set V} (hA : A ⊆ (s.left : Set V))
    (hB : B ⊆ (s.right : Set V)) :
    Erdos599.Countable.Separates G A B (s.separator : Set V) := by
  intro a ha b hb p _hp
  have haL := hA ha
  have hbR := hB hb
  by_cases haR : a ∈ s.right
  · exact ⟨a, p.start_mem_support,
      Finset.mem_inter.mpr ⟨haL, haR⟩⟩
  by_cases hbL : b ∈ s.left
  · exact ⟨b, p.end_mem_support,
      Finset.mem_inter.mpr ⟨hbL, hbR⟩⟩
  · exact s.walk_meets_separator p
      (Finset.mem_sdiff.mpr ⟨haL, haR⟩)
      (Finset.mem_sdiff.mpr ⟨hbR, hbL⟩)

/-- A separation of the induced left graph is a separation of the left
torso when the completed old separator lies wholly on its right side. -/
def separationInduceLeftToTorso {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.left : Set V)))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.right) :
    Erdos718.Separation (leftTorso s) where
  left := t.left
  right := t.right
  cover := t.cover
  not_adj := by
    intro a b haL haR hbR hbL hab
    rcases hab with hab | hab
    · exact t.not_adj haL haR hbR hbL hab
    · exact haR (hseparator a hab.1)

@[simp] lemma separationInduceLeftToTorso_left {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.left : Set V)))
    (hseparator) :
    (separationInduceLeftToTorso s t hseparator).left = t.left := rfl

@[simp] lemma separationInduceLeftToTorso_right {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.left : Set V)))
    (hseparator) :
    (separationInduceLeftToTorso s t hseparator).right = t.right := rfl

@[simp] lemma separationInduceLeftToTorso_separator {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.left : Set V)))
    (hseparator) :
    (separationInduceLeftToTorso s t hseparator).separator =
      t.separator := rfl

/-- A set spanning all possible non-loop edges is linked. -/
theorem isLinkedSet_of_pairwise_adj {G : SimpleGraph V} {S : Set V}
    (hadj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) :
    Erdos718.IsLinkedSet G S := by
  intro I _ terminal hterminal
  have hedge (i : I) : G.Adj (terminal (.inl i)) (terminal (.inr i)) := by
    apply hadj _ (hterminal ⟨.inl i, rfl⟩)
      _ (hterminal ⟨.inr i, rfl⟩)
    intro h
    exact Sum.inl_ne_inr (terminal.injective h)
  let p (i : I) : G.Walk (terminal (.inl i)) (terminal (.inr i)) :=
    .cons (hedge i) .nil
  refine ⟨{
    path := p
    isPath := fun i => by simp [p]
    avoids := fun i => by
      rw [Set.disjoint_left]
      intro x hx _hxS
      rcases hx with ⟨hxs, hxL, hxR⟩
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hxs
      exact hxs.elim hxL hxR
    disjoint := ?_
  }⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  change x ∈ (p i).support at hxi
  change x ∈ (p j).support at hxj
  simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hxi hxj
  rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
  · exact hij (Sum.inl.inj (terminal.injective (hxi.symm.trans hxj)))
  · exact Sum.inl_ne_inr (terminal.injective (hxi.symm.trans hxj))
  · exact Sum.inr_ne_inl (terminal.injective (hxi.symm.trans hxj))
  · exact hij (Sum.inr.inj (terminal.injective (hxi.symm.trans hxj)))

end ThomasWollanMassed
end Erdos717
