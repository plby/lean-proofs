import ErdosProblems.Erdos547.Potential
import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Counting fresh two-step embedding choices

The escape condition supplies many first vertices, each of which has many
second vertices outside a prescribed neighbourhood. Removing the used set
twice gives a quadratic lower bound on the number of useful ordered pairs.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def pairChoices (used : Finset V) (u : V) : Finset (V × V) := by
  classical
  exact (((G.neighborFinset u) \ used) ×ˢ Finset.univ).filter
    fun p ↦ G.Adj p.1 p.2 ∧ p.2 ∉ used

theorem mem_pairChoices (used : Finset V) (u z w : V) :
    (z, w) ∈ pairChoices G used u ↔ G.Adj u z ∧ z ∉ used ∧ G.Adj z w ∧ w ∉ used := by
  classical
  simp [pairChoices, and_assoc]

theorem card_pairChoices_le (used : Finset V) (u : V) :
    (pairChoices G used u).card ≤ (Fintype.card V) ^ 2 := by
  have h := Finset.card_le_univ (pairChoices G used u)
  simpa [Fintype.card_prod, pow_two] using h

open scoped Classical in
theorem card_pairChoices_outside (used : Finset V) (u x : V) :
    ((pairChoices G used u).filter fun p ↦ ¬ G.Adj x p.2).card =
      ∑ z ∈ G.neighborFinset u \ used, ((G.neighborFinset z \ G.neighborFinset x) \ used).card := by
  classical
  have hcard {A B : Finset V} (p : V → V → Prop) :
      ((A ×ˢ B).filter fun q ↦ p q.1 q.2).card = ∑ z ∈ A, (B.filter (p z)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  unfold pairChoices
  rw [Finset.filter_filter]
  trans ∑ z ∈ G.neighborFinset u \ used,
    (Finset.univ.filter fun w ↦ (G.Adj z w ∧ w ∉ used) ∧ ¬ G.Adj x w).card
  · convert hcard (A := G.neighborFinset u \ used) (B := Finset.univ)
      (fun z w ↦ (G.Adj z w ∧ w ∉ used) ∧ ¬ G.Adj x w) using 1
    · congr 1
      ext q
      simp
    · apply Finset.sum_congr (by ext z; simp)
      intro z _
      congr 1
      ext w
      simp
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  ext w
  simp [and_left_comm, and_comm]

open scoped Classical in
/-- The escape condition leaves at least `(k - |used|)^2` useful ordered
pairs, including the exact losses from excluding previously used vertices. -/
theorem card_pairChoices_outside_lower (used : Finset V) (u x : V) (k : ℕ)
    (hescape : k ≤ ((G.neighborFinset u).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card) :
    (k - used.card) ^ 2 ≤ ((pairChoices G used u).filter fun p ↦ ¬ G.Adj x p.2).card := by
  classical
  let Z := (G.neighborFinset u).filter
    fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card
  let A := Z \ used
  have hAsub : A ⊆ G.neighborFinset u \ used := by
    intro z hz
    obtain ⟨hzZ, hzu⟩ := Finset.mem_sdiff.mp hz
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hzZ).1, hzu⟩
  have hAcard : k - used.card ≤ A.card := by
    have hle : (Z ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
    have heq := Finset.card_sdiff_add_card_inter Z used
    change k ≤ Z.card at hescape
    dsimp [A]
    omega
  have hrow (z : V) (hz : z ∈ A) :
      k - used.card ≤ ((G.neighborFinset z \ G.neighborFinset x) \ used).card := by
    have hzZ : z ∈ Z := (Finset.mem_sdiff.mp hz).1
    have hdeg := (Finset.mem_filter.mp hzZ).2
    have hle : ((G.neighborFinset z \ G.neighborFinset x) ∩ used).card ≤ used.card :=
      Finset.card_le_card Finset.inter_subset_right
    have heq := Finset.card_sdiff_add_card_inter (G.neighborFinset z \ G.neighborFinset x) used
    omega
  rw [card_pairChoices_outside]
  calc
    (k - used.card) ^ 2 = (k - used.card) * (k - used.card) := pow_two _
    _ ≤ A.card * (k - used.card) := Nat.mul_le_mul_right _ hAcard
    _ = ∑ _z ∈ A, (k - used.card) := by simp [mul_comm]
    _ ≤ ∑ z ∈ A, ((G.neighborFinset z \ G.neighborFinset x) \ used).card :=
      Finset.sum_le_sum hrow
    _ ≤ _ := Finset.sum_le_sum_of_subset hAsub

theorem pairChoices_nonempty (used : Finset V) (u : V) (hu : u ∈ used)
    (hmin : used.card + 1 ≤ G.minDegree) : (pairChoices G used u).Nonempty := by
  classical
  have huDegree : used.card ≤ G.degree u := by
    have h := G.minDegree_le_degree u
    omega
  obtain ⟨z, huz, hz⟩ := exists_unused_neighbor used u hu huDegree
  have hzDegree : (insert z used).card ≤ G.degree z := by
    rw [Finset.card_insert_of_notMem hz]
    exact hmin.trans (G.minDegree_le_degree z)
  obtain ⟨w, hzw, hw⟩ := exists_unused_neighbor (insert z used) z (by simp) hzDegree
  refine ⟨(z, w), (mem_pairChoices G used u z w).mpr ⟨huz, hz, hzw, ?_⟩⟩
  exact fun h ↦ hw (Finset.mem_insert_of_mem h)

open scoped Classical in
/-- Choose a fresh host pair that contracts the nonneighbour potential by
the precise proportion obtained from the escape count. -/
theorem exists_pair_exposure_contraction (used : Finset V) (u : V) (hu : u ∈ used)
    (hmin : used.card + 1 ≤ G.minDegree) (indices : Finset V) (k : ℕ)
    (hescape : ∀ x ∈ indices, k ≤ ((G.neighborFinset u).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card) :
    ∃ q ∈ pairChoices G used u,
      exposurePotential indices
        (fun x ↦ ((insert q.2 (insert q.1 used)).filter fun w ↦ ¬ G.Adj x w).card) ≤
      (1 - (((k - used.card : ℕ) : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2) / 2) *
        exposurePotential indices (fun x ↦ (used.filter fun w ↦ ¬ G.Adj x w).card) := by
  classical
  let p : ℝ := ((k - used.card : ℕ) : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hnreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hden : (Fintype.card V : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hnreal)
  have hproportion (x : V) (hx : x ∈ indices) : p * (pairChoices G used u).card ≤
      ((pairChoices G used u).filter fun q ↦ ¬ G.Adj x q.2).card := by
    have hupper : ((pairChoices G used u).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      exact_mod_cast card_pairChoices_le G used u
    have hlower : ((k - used.card : ℕ) : ℝ) ^ 2 ≤
        ((pairChoices G used u).filter fun q ↦ ¬ G.Adj x q.2).card := by
      exact_mod_cast card_pairChoices_outside_lower G used u x k (hescape x hx)
    calc
      _ ≤ p * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hupper hp
      _ = ((k - used.card : ℕ) : ℝ) ^ 2 := div_mul_cancel₀ _ hden
      _ ≤ _ := hlower
  apply exists_choice_exposure_contraction indices (pairChoices G used u)
    (pairChoices_nonempty G used u hu hmin)
    (fun x ↦ (used.filter fun w ↦ ¬ G.Adj x w).card)
    (fun q x ↦ ((insert q.2 (insert q.1 used)).filter fun w ↦ ¬ G.Adj x w).card)
    (fun x q ↦ ¬ G.Adj x q.2) p (by
      intro x hx
      convert hproportion x hx using 1
      congr 2
      ext q
      simp)
  · intro q _ x _
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwu, hxw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwu), hxw⟩
  · intro q hq x _ hgood
    have hqspec := (mem_pairChoices G used u q.1 q.2).mp hq
    have hnot : q.2 ∉ used.filter (fun w ↦ ¬ G.Adj x w) := by
      intro h
      exact hqspec.2.2.2 (Finset.mem_filter.mp h).1
    have hsub : insert q.2 (used.filter fun w ↦ ¬ G.Adj x w) ⊆
        (insert q.2 (insert q.1 used)).filter (fun w ↦ ¬ G.Adj x w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with hw | hw
      · subst w
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hgood⟩
      · obtain ⟨hwu, hxw⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwu), hxw⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hcard
    exact hcard

end Erdos547

#print axioms Erdos547.card_pairChoices_outside_lower
#print axioms Erdos547.exists_pair_exposure_contraction
