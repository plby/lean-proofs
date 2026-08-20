/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The iterative nearly-complete-subset lemma. -/

import ErdosProblems.Erdos717.ShortPathReservoir

open Function Set
open SimpleGraph

namespace Erdos717

/-- Ordered nonedges inside a finite vertex set. -/
def missingOrderedPairs {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : Finset (V × V) :=
  (A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ ¬G.Adj p.1 p.2

/-- Nonneighbours of `v` inside `A`, excluding `v` itself. -/
def nonNeighborFinset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) : Finset V :=
  A.filter fun w => w ≠ v ∧ ¬G.Adj v w

theorem sum_card_nonNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ∑ v ∈ A, (nonNeighborFinset G A v).card =
      (missingOrderedPairs G A).card := by
  classical
  simp only [nonNeighborFinset, missingOrderedPairs,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hvw : w ≠ v ∧ ¬G.Adj v w
  · have hvw' : v ≠ w ∧ ¬G.Adj v w := ⟨Ne.symm hvw.1, hvw.2⟩
    simp [hvw, hvw']
  · have hvw' : ¬(v ≠ w ∧ ¬G.Adj v w) := by
      intro h
      exact hvw ⟨h.1.symm, h.2⟩
    simp [hvw, hvw']

/-- A convenient local form of an independence-number bound. -/
def IndepBoundOn {V : Type*} (G : SimpleGraph V) (A : Finset V) (a : ℕ) : Prop :=
  ∀ I : Finset V, I ⊆ A → G.IsIndepSet I → I.card ≤ a

theorem indepBoundOn_of_indepNum_le
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {A : Finset V} {a : ℕ} (h : G.indepNum ≤ a) :
    IndepBoundOn G A a := by
  intro I _hIA hI
  exact hI.card_le_indepNum.trans h

private theorem pair_independent_of_missing
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (huv : u ≠ v) (hn : ¬G.Adj u v) :
    G.IsIndepSet ({u, v} : Finset V) := by
  rw [G.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · exact hn
  · exact fun h => hn h.symm
  · exact (hxy rfl).elim

private theorem insert_independent_of_nonNeighbors
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {A I : Finset V} {v : V}
    (hI : G.IsIndepSet I) (hIA : I ⊆ nonNeighborFinset G A v) :
    G.IsIndepSet (↑({v} ∪ I) : Set V) := by
  rw [G.isIndepSet_iff]
  intro x hx y hy hxy
  change x ∈ ({v} ∪ I : Finset V) at hx
  change y ∈ ({v} ∪ I : Finset V) at hy
  simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact (Finset.mem_filter.mp (hIA hy)).2.2
  · rcases hy with rfl | hy
    · exact fun h => (Finset.mem_filter.mp (hIA hx)).2.2 h.symm
    · exact (G.isIndepSet_iff.mp hI) hx hy hxy

/-- Division-free form of the nearly-complete-set lemma.  If independent
sets in `A` have size at most `k+1`, then after at most `k` successive
nonneighbourhood restrictions one reaches `T` with few ordered missing
pairs, losing a factor at most `R` at each restriction. -/
theorem exists_nearly_complete_subset_aux
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (R k : ℕ) (hR : 1 ≤ R)
    (hind : IndepBoundOn G A (k + 1)) :
    ∃ T : Finset V,
      T ⊆ A ∧ A.card ≤ R ^ k * T.card ∧
      R * (missingOrderedPairs G T).card ≤ T.card * T.card := by
  classical
  induction k generalizing A with
  | zero =>
      have hmissing : missingOrderedPairs G A = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨p, hp⟩ := hne
        have hp' := Finset.mem_filter.mp hp
        have hpA := Finset.mem_product.mp hp'.1
        have hpair := pair_independent_of_missing hp'.2.1 hp'.2.2
        have hcard := hind {p.1, p.2} (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpA.1
          · exact hpA.2) hpair
        have hpne := hp'.2.1
        have : ({p.1, p.2} : Finset V).card = 2 := by simp [hpne]
        omega
      refine ⟨A, Finset.Subset.rfl, ?_, ?_⟩
      · simp
      · rw [hmissing]
        simp
  | succ k ih =>
      by_cases hsparse :
          R * (missingOrderedPairs G A).card ≤ A.card * A.card
      · refine ⟨A, Finset.Subset.rfl, ?_, hsparse⟩
        have hpow : 1 ≤ R ^ (k + 1) := one_le_pow₀ hR
        nlinarith
      · have hex : ∃ v ∈ A,
            A.card < R * (nonNeighborFinset G A v).card := by
          by_contra! hnone
          have hsum : R * (missingOrderedPairs G A).card ≤ A.card * A.card := by
            rw [← sum_card_nonNeighborFinset]
            calc
              R * (∑ v ∈ A, (nonNeighborFinset G A v).card) =
                  ∑ v ∈ A, R * (nonNeighborFinset G A v).card := by
                rw [Finset.mul_sum]
              _ ≤ ∑ _v ∈ A, A.card := by
                apply Finset.sum_le_sum
                intro v hv
                exact hnone v hv
              _ = A.card * A.card := by simp
          exact hsparse hsum
        obtain ⟨v, hvA, hvlarge⟩ := hex
        let B := nonNeighborFinset G A v
        have hBsub : B ⊆ A := Finset.filter_subset _ _
        have hvNotB : v ∉ B := by simp [B, nonNeighborFinset]
        have hindB : IndepBoundOn G B (k + 1) := by
          intro I hIB hI
          have hinsert := insert_independent_of_nonNeighbors hI hIB
          have hinsertSub : ({v} ∪ I : Finset V) ⊆ A := by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_singleton] at hx
            rcases hx with rfl | hx
            · exact hvA
            · exact hBsub (hIB hx)
          have hcard := hind ({v} ∪ I) hinsertSub hinsert
          rw [Finset.card_union_of_disjoint] at hcard
          · simp only [Finset.card_singleton] at hcard
            omega
          · exact Finset.disjoint_left.mpr fun _ hxv hxI =>
              hvNotB (hIB (Finset.mem_singleton.mp hxv ▸ hxI))
        obtain ⟨T, hTB, hBT, hTsparse⟩ := ih B hindB
        refine ⟨T, hTB.trans hBsub, ?_, hTsparse⟩
        calc
          A.card ≤ R * B.card := hvlarge.le
          _ ≤ R * (R ^ k * T.card) := Nat.mul_le_mul_left R hBT
          _ = R ^ (k + 1) * T.card := by ring

/-- The same lemma stated directly from the graph's independence number. -/
theorem exists_nearly_complete_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (R a : ℕ) (hR : 1 ≤ R) (ha : 1 ≤ a)
    (hind : G.indepNum ≤ a) :
    ∃ T : Finset V,
      T ⊆ A ∧ A.card ≤ R ^ (a - 1) * T.card ∧
      R * (missingOrderedPairs G T).card ≤ T.card * T.card := by
  have haeq : a - 1 + 1 = a := by omega
  apply exists_nearly_complete_subset_aux G A R (a - 1) hR
  rw [haeq]
  exact indepBoundOn_of_indepNum_le hind

end Erdos717
