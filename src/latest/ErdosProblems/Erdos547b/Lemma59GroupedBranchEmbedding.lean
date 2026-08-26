/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59BranchRootSelector

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59FullOnline
open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
universe u v

namespace GroupedBranches

variable {m : ℕ}

def deepOrder (F : OrderedRootedForest m) : ℕ :=
  ∑ i, (F.size i - 1)

/-- Non-root demand assigned to one matching edge. -/
def groupDeep {K : Type*} [DecidableEq K]
    (F : OrderedRootedForest m) (group : Fin m → K) (k : K) : ℕ :=
  ∑ i, if group i = k then F.size i - 1 else 0

/-- Permute canonical tree colors so color `1` uses the selected endpoint. -/
def orientTo (s : Fin 2) : Fin 2 ≃ Fin 2 :=
  if s = 1 then Equiv.refl _ else Equiv.swap 0 1

@[simp] theorem orientTo_one (s : Fin 2) : orientTo s 1 = s := by
  rcases OrderedRootedForest.fin_two_eq_zero_or_one s with rfl | rfl <;>
    simp [orientTo]

theorem groupDeep_tail_add_head
    {K : Type*} [DecidableEq K] {m : ℕ}
    (F : OrderedRootedForest (m + 1)) (group : Fin (m + 1) → K) (k : K) :
    groupDeep F.tail (fun i => group i.succ) k +
        (if group 0 = k then F.size 0 - 1 else 0) = groupDeep F group k := by
  simp [groupDeep, OrderedRootedForest.tail, Fin.sum_univ_succ, add_comm]

/-- Assigned-pair prescribed-root embedding. Many branches may share a pair;
the reserve for each pair is its total non-root demand plus one, rather than
the global forest order. -/
theorem exists_embedding_in_grouped_candidates_oriented
    {K : Type u} [DecidableEq K]
    {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (group : Fin m → K) (orient : Fin m → (Fin 2 ≃ Fin 2))
    (rootImage : Fin m → B)
    (candidate : K → Fin 2 → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i k c, rootImage i ∉ candidate k c)
    (hdisjoint : ∀ k l, k ≠ l →
      Disjoint (candidate k 0 ∪ candidate k 1)
        (candidate l 0 ∪ candidate l 1))
    (hrootDegree : ∀ i, groupDeep F group (group i) + 1 ≤
      #{w ∈ candidate (group i) (orient i 1) | G.Adj (rootImage i) w})
    (hcross : ∀ k c d, c ≠ d → ∀ z ∈ candidate k c,
      groupDeep F group k + 1 ≤ #{w ∈ candidate k d | G.Adj z w}) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i →
        E.copy i a ∈ candidate (group i)
          (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a)) := by
  classical
  induction m generalizing candidate with
  | zero =>
      let copies : ∀ i : Fin 0, (F.tree i).Copy G := fun i => Fin.elim0 i
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) => copies z.1 z.2) := by
        rintro ⟨i, _⟩
        exact Fin.elim0 i
      let E : F.Embedding G := ⟨copies, hinjective⟩
      exact ⟨E, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
      let Ftail : OrderedRootedForest m := F.tail
      let groupTail : Fin m → K := fun i => group i.succ
      let orientTail : Fin m → (Fin 2 ≃ Fin 2) := fun i => orient i.succ
      let rootImageTail : Fin m → B := fun i => rootImage i.succ
      have hheadPos : 0 < F.size 0 := by
        have := (F.root 0).isLt
        omega
      have hhead_le : F.size 0 ≤ groupDeep F group (group 0) + 1 := by
        rw [← groupDeep_tail_add_head F group (group 0)]
        simp
        omega
      obtain ⟨fhead, hfheadRoot, hfheadMem⟩ :=
        exists_rooted_tree_copy (F.tree 0) G (F.isTree 0) (F.root 0)
          (fun c => candidate (group 0) (orient 0 c)) (rootImage 0) (by
            simpa using hhead_le.trans (hrootDegree 0)) (by
            intro c d hcd z hz
            have hc := hcross (group 0) (orient 0 c) (orient 0 d)
              ((orient 0).injective.ne hcd) z hz
            simpa using hhead_le.trans hc)
      let nonroots : Finset (Fin (F.size 0)) :=
        Finset.univ.erase (F.root 0)
      let used : Finset B := nonroots.image fhead
      have hnonrootsCard : #nonroots = F.size 0 - 1 := by simp [nonroots]
      have husedCard : #used = F.size 0 - 1 := by
        rw [show #used = #nonroots by
          exact card_image_iff.mpr fun _ _ _ _ h => fhead.injective h]
        exact hnonrootsCard
      let candidateTail : K → Fin 2 → Finset B := fun k c =>
        if k = group 0 then candidate k c \ used else candidate k c
      have htailRootInjective : Function.Injective rootImageTail := by
        intro i j hij
        exact Fin.succ_inj.mp (hrootInjective hij)
      have htailRootOutside : ∀ i k c, rootImageTail i ∉ candidateTail k c := by
        intro i k c hi
        by_cases hk : k = group 0
        · exact hrootOutside i.succ k c (Finset.mem_sdiff.mp (by
            simpa [candidateTail, hk] using hi)).1
        · exact hrootOutside i.succ k c (by simpa [candidateTail, hk] using hi)
      have htailDisjoint : ∀ k l, k ≠ l →
          Disjoint (candidateTail k 0 ∪ candidateTail k 1)
            (candidateTail l 0 ∪ candidateTail l 1) := by
        intro k l hkl
        apply (hdisjoint k l hkl).mono
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact Finset.mem_union_left _ (by
              by_cases hk : k = group 0
              · exact (Finset.mem_sdiff.mp (by simpa [candidateTail, hk] using hz)).1
              · simpa [candidateTail, hk] using hz)
          · exact Finset.mem_union_right _ (by
              by_cases hk : k = group 0
              · exact (Finset.mem_sdiff.mp (by simpa [candidateTail, hk] using hz)).1
              · simpa [candidateTail, hk] using hz)
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact Finset.mem_union_left _ (by
              by_cases hl : l = group 0
              · exact (Finset.mem_sdiff.mp (by simpa [candidateTail, hl] using hz)).1
              · simpa [candidateTail, hl] using hz)
          · exact Finset.mem_union_right _ (by
              by_cases hl : l = group 0
              · exact (Finset.mem_sdiff.mp (by simpa [candidateTail, hl] using hz)).1
              · simpa [candidateTail, hl] using hz)
      have htailRootDegree : ∀ i,
          groupDeep Ftail groupTail (groupTail i) + 1 ≤
            #{w ∈ candidateTail (groupTail i) (orientTail i 1) |
              G.Adj (rootImageTail i) w} := by
        intro i
        by_cases hg : groupTail i = group 0
        · have hdeg : groupDeep Ftail groupTail (groupTail i) + 1 + #used ≤
              #((candidate (groupTail i) (orientTail i 1)).filter
                (G.Adj (rootImageTail i))) := by
            have heq := groupDeep_tail_add_head F group (groupTail i)
            rw [if_pos hg.symm] at heq
            have horig := hrootDegree i.succ
            change groupDeep F group (groupTail i) + 1 ≤
              #((candidate (groupTail i) (orientTail i 1)).filter
                (G.Adj (rootImageTail i))) at horig
            change groupDeep F.tail (fun k => group k.succ) (groupTail i) + 1 +
              #used ≤ #((candidate (groupTail i) (orientTail i 1)).filter
                (G.Adj (rootImageTail i)))
            rw [husedCard]
            omega
          simpa [candidateTail, hg] using
            card_neighbors_cleaned_ge G
              (candidate (groupTail i) (orientTail i 1)) used
              (rootImageTail i) (groupDeep Ftail groupTail (groupTail i) + 1) hdeg
        · have heq := groupDeep_tail_add_head F group (groupTail i)
          rw [if_neg (fun h => hg h.symm), add_zero] at heq
          have horig := hrootDegree i.succ
          change groupDeep F group (groupTail i) + 1 ≤
            #((candidate (groupTail i) (orientTail i 1)).filter
              (G.Adj (rootImageTail i))) at horig
          rw [← heq] at horig
          simpa [candidateTail, hg] using horig
      have htailCross : ∀ k c d, c ≠ d → ∀ z ∈ candidateTail k c,
          groupDeep Ftail groupTail k + 1 ≤
            #{w ∈ candidateTail k d | G.Adj z w} := by
        intro k c d hcd z hz
        by_cases hk : k = group 0
        · have hdeg : groupDeep Ftail groupTail k + 1 + #used ≤
              #((candidate k d).filter (G.Adj z)) := by
            have heq := groupDeep_tail_add_head F group k
            rw [if_pos hk.symm] at heq
            have horig := hcross k c d hcd z
              (Finset.mem_sdiff.mp (by simpa [candidateTail, hk] using hz)).1
            change groupDeep F group k + 1 ≤
              #((candidate k d).filter (G.Adj z)) at horig
            change groupDeep F.tail (fun i => group i.succ) k + 1 + #used ≤
              #((candidate k d).filter (G.Adj z))
            rw [husedCard]
            omega
          simpa [candidateTail, hk] using
            card_neighbors_cleaned_ge G (candidate k d) used z
              (groupDeep Ftail groupTail k + 1) hdeg
        · have heq := groupDeep_tail_add_head F group k
          rw [if_neg (fun h => hk h.symm), add_zero] at heq
          have horig := hcross k c d hcd z
            (by simpa [candidateTail, hk] using hz)
          rw [← heq] at horig
          simpa [candidateTail, hk] using horig
      obtain ⟨Etail, hEtailRoot, hEtailMem⟩ :=
        ih Ftail groupTail orientTail rootImageTail candidateTail htailRootInjective
          htailRootOutside htailDisjoint htailRootDegree htailCross
      have hheadTailDisjoint : ∀ a i c, fhead a ≠ Etail.copy i c := by
        intro a i c hac
        by_cases hcroot : c = Ftail.root i
        · by_cases haroot : a = F.root 0
          · have htailRoot : Etail.copy i c = rootImage i.succ := by
              rw [hcroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            have himage : rootImage 0 = rootImage i.succ := by
              rw [← hfheadRoot, ← haroot, ← htailRoot]
              exact hac
            have hindex : (0 : Fin (m + 1)) = i.succ := hrootInjective himage
            have := congrArg Fin.val hindex
            simp at this
          · have hamem := hfheadMem a haroot
            apply hrootOutside i.succ (group 0)
              (orient 0 ((F.isTree 0).coloringTwoOfVert (F.root 0) a))
            have htailRoot : Etail.copy i c = rootImage i.succ := by
              rw [hcroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            rw [← htailRoot, ← hac]
            exact hamem
        · have hcmem := hEtailMem i c hcroot
          by_cases hg : groupTail i = group 0
          · have hcUnused : Etail.copy i c ∉ used :=
              (Finset.mem_sdiff.mp (by simpa [candidateTail, hg] using hcmem)).2
            by_cases haroot : a = F.root 0
            · apply hrootOutside 0 (groupTail i)
                (orientTail i ((Ftail.isTree i).coloringTwoOfVert (Ftail.root i) c))
              rw [← hfheadRoot, ← haroot, hac]
              exact (Finset.mem_sdiff.mp (by simpa [candidateTail, hg] using hcmem)).1
            · apply hcUnused
              exact Finset.mem_image.mpr
                ⟨a, Finset.mem_erase.mpr ⟨haroot, Finset.mem_univ a⟩, hac⟩
          · by_cases haroot : a = F.root 0
            · apply hrootOutside 0 (groupTail i)
                (orientTail i ((Ftail.isTree i).coloringTwoOfVert (Ftail.root i) c))
              rw [← hfheadRoot, ← haroot, hac]
              simpa [candidateTail, hg] using hcmem
            · have hamem := hfheadMem a haroot
              have hother := by simpa [candidateTail, hg] using hcmem
              have hd := hdisjoint (group 0) (groupTail i) (fun h => hg h.symm)
              have haUnion : fhead a ∈ candidate (group 0) 0 ∪ candidate (group 0) 1 := by
                rcases OrderedRootedForest.fin_two_eq_zero_or_one
                    (orient 0 ((F.isTree 0).coloringTwoOfVert (F.root 0) a)) with h0 | h1
                · exact Finset.mem_union_left _ (h0 ▸ hamem)
                · exact Finset.mem_union_right _ (h1 ▸ hamem)
              have hcUnion : Etail.copy i c ∈
                  candidate (groupTail i) 0 ∪ candidate (groupTail i) 1 := by
                rcases OrderedRootedForest.fin_two_eq_zero_or_one
                    (orientTail i ((Ftail.isTree i).coloringTwoOfVert (Ftail.root i) c)) with h0 | h1
                · exact Finset.mem_union_left _ (h0 ▸ hother)
                · exact Finset.mem_union_right _ (h1 ▸ hother)
              exact (Finset.disjoint_left.mp hd) haUnion (hac ▸ hcUnion)
      let copies : ∀ i, (F.tree i).Copy G :=
        Fin.cases fhead (fun i => Etail.copy i)
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) => copies z.1 z.2) := by
        rintro ⟨i, a⟩ ⟨k, c⟩ hac
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · have : a = c := fhead.injective hac
            subst c
            rfl
          · exact False.elim (hheadTailDisjoint a k c hac)
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · exact False.elim (hheadTailDisjoint c i a hac.symm)
          · have htail : (⟨i, a⟩ : Σ i, Fin (Ftail.size i)) = ⟨k, c⟩ := by
              apply Etail.injective
              exact hac
            cases htail
            rfl
      let E : F.Embedding G := ⟨copies, hinjective⟩
      refine ⟨E, ?_, ?_⟩
      · intro i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · exact hfheadRoot
        · exact hEtailRoot i
      · intro i a ha
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · exact hfheadMem a ha
        · have ha' : a ≠ Ftail.root i := ha
          have hm := hEtailMem i a ha'
          change Etail.copy i a ∈ candidateTail (group i.succ)
            (orient i.succ ((F.isTree i.succ).coloringTwoOfVert (F.root i.succ) a)) at hm
          change Etail.copy i a ∈ candidate (group i.succ)
            (orient i.succ ((F.isTree i.succ).coloringTwoOfVert (F.root i.succ) a))
          by_cases hg : groupTail i = group 0
          · exact (Finset.mem_sdiff.mp (by
              simpa [candidateTail, groupTail, hg] using hm)).1
          · simpa [candidateTail, groupTail, hg] using hm

end GroupedBranches
end Erdos547b.ZhaoLemma59FullOnline

#print axioms Erdos547b.ZhaoLemma59FullOnline.GroupedBranches.exists_embedding_in_grouped_candidates_oriented
