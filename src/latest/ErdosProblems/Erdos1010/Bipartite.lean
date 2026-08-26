import Mathlib

/-! # Finite bipartite missing-edge bookkeeping

A bipartite edge is represented by its ordered pair of endpoints. The
ordering records the two sides, not an orientation of the original graph.
-/

open Finset

namespace Erdos1010.Bipartite

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

def leftDegree (M : Finset (A × B)) (a : A) : ℕ :=
  (M.filter fun e ↦ e.1 = a).card

def rightDegree (M : Finset (A × B)) (b : B) : ℕ :=
  (M.filter fun e ↦ e.2 = b).card

def eraseLeft (M : Finset (A × B)) (a : A) : Finset (A × B) :=
  M.filter fun e ↦ e.1 ≠ a

def transpose (M : Finset (A × B)) : Finset (B × A) :=
  M.map (Equiv.prodComm A B).toEmbedding

lemma card_transpose (M : Finset (A × B)) : (transpose M).card = M.card := by
  simp [transpose]

lemma leftDegree_transpose (M : Finset (A × B)) (b : B) :
    leftDegree (transpose M) b = rightDegree M b := by
  simp [leftDegree, rightDegree, transpose, filter_map, Function.comp_def]
  rfl

lemma rightDegree_transpose (M : Finset (A × B)) (a : A) :
    rightDegree (transpose M) a = leftDegree M a := by
  simp [leftDegree, rightDegree, transpose, filter_map, Function.comp_def]
  rfl

lemma leftDegree_le_card (M : Finset (A × B)) (a : A) : leftDegree M a ≤ M.card :=
  card_le_card (filter_subset _ _)

lemma rightDegree_le_card (M : Finset (A × B)) (b : B) : rightDegree M b ≤ M.card :=
  card_le_card (filter_subset _ _)

lemma sum_leftDegree (M : Finset (A × B)) (s : Finset A) :
    (∑ a ∈ s, leftDegree M a) = (M.filter fun e ↦ e.1 ∈ s).card :=
  sum_card_fiberwise_eq_card_filter M s Prod.fst

lemma sum_rightDegree (M : Finset (A × B)) (s : Finset B) :
    (∑ b ∈ s, rightDegree M b) = (M.filter fun e ↦ e.2 ∈ s).card :=
  sum_card_fiberwise_eq_card_filter M s Prod.snd

lemma sum_leftDegree_univ [Fintype A] (M : Finset (A × B)) :
    ∑ a, leftDegree M a = M.card := by simp [sum_leftDegree]

lemma sum_rightDegree_univ [Fintype B] (M : Finset (A × B)) :
    ∑ b, rightDegree M b = M.card := by simp [sum_rightDegree]

lemma leftDegree_add_card_eraseLeft (M : Finset (A × B)) (a : A) :
    leftDegree M a + (eraseLeft M a).card = M.card :=
  card_filter_add_card_filter_not _

lemma leftDegree_eraseLeft_self (M : Finset (A × B)) (a : A) :
    leftDegree (eraseLeft M a) a = 0 := by
  simp [leftDegree, eraseLeft, filter_filter]

lemma leftDegree_eraseLeft_of_ne (M : Finset (A × B)) {a u : A} (h : a ≠ u) :
    leftDegree (eraseLeft M u) a = leftDegree M a := by
  unfold leftDegree eraseLeft
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · exact fun he ↦ ⟨he.1.1, he.2⟩
  · rintro ⟨he, hea⟩
    exact ⟨⟨he, fun heu ↦ h (hea.symm.trans heu)⟩, hea⟩

lemma rightDegree_eraseLeft (M : Finset (A × B)) (u : A) (b : B) :
    rightDegree M b = (if (u, b) ∈ M then 1 else 0) + rightDegree (eraseLeft M u) b := by
  have hsplit := card_filter_add_card_filter_not
    (s := M.filter fun e ↦ e.2 = b) (fun e ↦ e.1 = u)
  have hsingle : ((M.filter fun e ↦ e.2 = b).filter fun e ↦ e.1 = u) =
      if (u, b) ∈ M then {(u, b)} else ∅ := by
    ext e
    by_cases h : (u, b) ∈ M <;> simp [h, Prod.ext_iff] <;> aesop
  have hres : ((M.filter fun e ↦ e.2 = b).filter fun e ↦ e.1 ≠ u) =
      (eraseLeft M u).filter fun e ↦ e.2 = b := by
    ext e
    simp [eraseLeft, and_left_comm, and_comm]
  rw [hsingle, hres] at hsplit
  by_cases h : (u, b) ∈ M <;> simpa [rightDegree, h] using hsplit.symm

lemma degree_sums_le_card_add_cross (M : Finset (A × B)) (s : Finset A) (t : Finset B) :
    (∑ a ∈ s, leftDegree M a) + (∑ b ∈ t, rightDegree M b) ≤
      M.card + (M.filter fun e ↦ e.1 ∈ s ∧ e.2 ∈ t).card := by
  rw [sum_leftDegree, sum_rightDegree]
  have h := card_union_add_card_inter (M.filter fun e ↦ e.1 ∈ s)
    (M.filter fun e ↦ e.2 ∈ t)
  have hi : (M.filter fun e ↦ e.1 ∈ s) ∩ (M.filter fun e ↦ e.2 ∈ t) =
      M.filter fun e ↦ e.1 ∈ s ∧ e.2 ∈ t := by ext e; simp only [mem_inter, mem_filter]; tauto
  have hu : (M.filter fun e ↦ e.1 ∈ s) ∪ (M.filter fun e ↦ e.2 ∈ t) ⊆ M :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  rw [hi] at h
  have hc := card_le_card hu
  omega

lemma cross_card_le (M : Finset (A × B)) (s : Finset A) (t : Finset B) :
    (M.filter fun e ↦ e.1 ∈ s ∧ e.2 ∈ t).card ≤ s.card * t.card := by
  rw [← card_product]
  apply card_le_card
  intro e he
  exact mem_product.mpr (mem_filter.mp he).2

lemma degree_sums_le_card_add_product (M : Finset (A × B)) (s : Finset A) (t : Finset B) :
    (∑ a ∈ s, leftDegree M a) + (∑ b ∈ t, rightDegree M b) ≤ M.card + s.card * t.card :=
  (degree_sums_le_card_add_cross M s t).trans (Nat.add_le_add_left (cross_card_le M s t) _)

lemma eraseLeft_eq_empty_of_star (M : Finset (A × B)) (u : A)
    (hu : leftDegree M u = M.card) : eraseLeft M u = ∅ := by
  apply card_eq_zero.mp
  have := leftDegree_add_card_eraseLeft M u
  omega

lemma leftDegree_of_star (M : Finset (A × B)) (u a : A)
    (hu : leftDegree M u = M.card) : leftDegree M a = if a = u then M.card else 0 := by
  by_cases ha : a = u
  · simpa [ha] using hu
  · rw [if_neg ha, ← leftDegree_eraseLeft_of_ne M ha, eraseLeft_eq_empty_of_star M u hu]
    simp [leftDegree]

lemma rightDegree_of_star (M : Finset (A × B)) (u : A) (b : B)
    (hu : leftDegree M u = M.card) : rightDegree M b = if (u, b) ∈ M then 1 else 0 := by
  rw [rightDegree_eraseLeft M u b, eraseLeft_eq_empty_of_star M u hu]
  simp [rightDegree]

lemma card_right_neighbors [Fintype B] (M : Finset (A × B)) (u : A) :
    (univ.filter fun b ↦ (u, b) ∈ M).card = leftDegree M u := by
  unfold leftDegree
  apply card_bij (fun b _ ↦ (u, b))
  · intro b hb
    exact mem_filter.mpr ⟨(mem_filter.mp hb).2, rfl⟩
  · intro b hb c hc h
    exact Prod.mk.inj h |>.2
  · intro e he
    obtain ⟨he, heu⟩ := mem_filter.mp he
    refine ⟨e.2, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · simpa [← heu] using he
    · exact Prod.ext heu.symm rfl

lemma leftDegree_le_one_of_right_star (M : Finset (A × B)) (v : B)
    (hv : rightDegree M v = M.card) (a : A) : leftDegree M a ≤ 1 := by
  have ht : leftDegree (transpose M) v = (transpose M).card := by
    rwa [leftDegree_transpose, card_transpose]
  have hd := rightDegree_of_star (transpose M) v a ht
  rw [rightDegree_transpose] at hd
  split_ifs at hd <;> omega

lemma double_hubs_residual_star (M : Finset (A × B)) (u : A) (v : B)
    (h : leftDegree M u + rightDegree M v = M.card + 1) :
    (u, v) ∈ M ∧ rightDegree (eraseLeft M u) v = (eraseLeft M u).card := by
  have he := leftDegree_add_card_eraseLeft M u
  have hd := rightDegree_eraseLeft M u v
  have hle := rightDegree_le_card (eraseLeft M u) v
  by_cases huv : (u, v) ∈ M
  · simp only [if_pos huv] at hd
    exact ⟨huv, by omega⟩
  · simp only [if_neg huv] at hd
    omega

lemma double_hubs_left_le_one (M : Finset (A × B)) (u : A) (v : B)
    (h : leftDegree M u + rightDegree M v = M.card + 1) (a : A) (ha : a ≠ u) :
    leftDegree M a ≤ 1 := by
  rw [← leftDegree_eraseLeft_of_ne M ha]
  exact leftDegree_le_one_of_right_star (eraseLeft M u) v (double_hubs_residual_star M u v h).2 a

lemma double_hubs_right_le_one (M : Finset (A × B)) (u : A) (v : B)
    (h : leftDegree M u + rightDegree M v = M.card + 1) (b : B) (hb : b ≠ v) :
    rightDegree M b ≤ 1 := by
  have ht : leftDegree (transpose M) v + rightDegree (transpose M) u = (transpose M).card + 1 := by
    simpa [leftDegree_transpose, rightDegree_transpose, card_transpose, add_comm] using h
  simpa [leftDegree_transpose] using double_hubs_left_le_one (transpose M) v u ht b hb

lemma exists_max_degree [Fintype A] [Fintype B] (M : Finset (A × B)) (hM : M.Nonempty) :
    ∃ k : ℕ, 0 < k ∧ (∀ a, leftDegree M a ≤ k) ∧ (∀ b, rightDegree M b ≤ k) ∧
      ((∃ a, leftDegree M a = k) ∨ ∃ b, rightDegree M b = k) := by
  obtain ⟨⟨a, b⟩, hab⟩ := hM
  let f : A ⊕ B → ℕ := Sum.elim (leftDegree M) (rightDegree M)
  obtain ⟨u, hu, hmax⟩ := (univ : Finset (A ⊕ B)).exists_max_image f
    ⟨Sum.inl a, mem_univ _⟩
  have hpos : 0 < leftDegree M a := by
    apply card_pos.mpr
    exact ⟨(a, b), mem_filter.mpr ⟨hab, rfl⟩⟩
  refine ⟨f u, lt_of_lt_of_le hpos (hmax (Sum.inl a) (mem_univ _)),
    (fun a ↦ hmax (Sum.inl a) (mem_univ _)),
    (fun b ↦ hmax (Sum.inr b) (mem_univ _)), ?_⟩
  cases u with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr b => exact Or.inr ⟨b, rfl⟩

lemma leftDegree_pos_of_mem (M : Finset (A × B)) {a : A} {b : B} (hab : (a, b) ∈ M) :
    0 < leftDegree M a := card_pos.mpr ⟨(a, b), mem_filter.mpr ⟨hab, rfl⟩⟩

lemma rightDegree_pos_of_mem (M : Finset (A × B)) {a : A} {b : B} (hab : (a, b) ∈ M) :
    0 < rightDegree M b := card_pos.mpr ⟨(a, b), mem_filter.mpr ⟨hab, rfl⟩⟩

lemma exists_two_right_neighbors [Fintype B] (M : Finset (A × B)) (a : A)
    (ha : 2 ≤ leftDegree M a) : ∃ b c, b ≠ c ∧ (a, b) ∈ M ∧ (a, c) ∈ M := by
  have hcard : 1 < (univ.filter fun b ↦ (a, b) ∈ M).card := by rw [card_right_neighbors]; omega
  obtain ⟨b, hb, c, hc, hbc⟩ := one_lt_card.mp hcard
  exact ⟨b, c, hbc, (mem_filter.mp hb).2, (mem_filter.mp hc).2⟩

lemma degree_sums_equality_cover (M : Finset (A × B)) (s : Finset A) (t : Finset B)
    (h : (∑ a ∈ s, leftDegree M a) + (∑ b ∈ t, rightDegree M b) =
      M.card + s.card * t.card) : ∀ e ∈ M, e.1 ∈ s ∨ e.2 ∈ t := by
  rw [sum_leftDegree, sum_rightDegree] at h
  let L := M.filter fun e ↦ e.1 ∈ s
  let R := M.filter fun e ↦ e.2 ∈ t
  have hsum := card_union_add_card_inter L R
  have hinter : L ∩ R ⊆ s ×ˢ t := by
    intro e he
    exact mem_product.mpr ⟨(mem_filter.mp (mem_inter.mp he).1).2,
      (mem_filter.mp (mem_inter.mp he).2).2⟩
  have hcross : (L ∩ R).card ≤ s.card * t.card := by
    simpa only [card_product] using card_le_card hinter
  have hsub : L ∪ R ⊆ M := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard : M.card ≤ (L ∪ R).card := by dsimp [L, R] at hsum hcross ⊢; omega
  have heq : L ∪ R = M := eq_of_subset_of_card_le hsub hcard
  intro e he
  rw [← heq] at he
  rcases mem_union.mp he with he | he
  · exact Or.inl (mem_filter.mp he).2
  · exact Or.inr (mem_filter.mp he).2

lemma exists_right_neighbor_outside [Fintype B] (M : Finset (A × B)) (a : A) (t : Finset B)
    (h : t.card < leftDegree M a) : ∃ b, (a, b) ∈ M ∧ b ∉ t := by
  have hn : ¬ (univ.filter fun b ↦ (a, b) ∈ M) ⊆ t := by
    intro hsub
    have hc := card_le_card hsub
    rw [card_right_neighbors] at hc
    omega
  obtain ⟨b, hb, hbt⟩ := not_subset.mp hn
  exact ⟨b, (mem_filter.mp hb).2, hbt⟩

lemma exists_edge_left_outside (M : Finset (A × B)) (s : Finset A)
    (h : (∑ a ∈ s, leftDegree M a) < M.card) : ∃ e ∈ M, e.1 ∉ s := by
  have hs := card_filter_add_card_filter_not (s := M) (fun e ↦ e.1 ∈ s)
  rw [← sum_leftDegree] at hs
  have hp : 0 < (M.filter fun e ↦ e.1 ∉ s).card := by omega
  obtain ⟨e, he⟩ := card_pos.mp hp
  exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩

lemma card_left_neighbors [Fintype A] (M : Finset (A × B)) (b : B) :
    (univ.filter fun a ↦ (a, b) ∈ M).card = rightDegree M b := by
  unfold rightDegree
  apply card_bij (fun a _ ↦ (a, b))
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).2, rfl⟩
  · intro a ha c hc h
    exact Prod.mk.inj h |>.1
  · intro e he
    obtain ⟨he, heb⟩ := mem_filter.mp he
    refine ⟨e.1, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · simpa [← heb] using he
    · exact Prod.ext rfl heb.symm

end Erdos1010.Bipartite
