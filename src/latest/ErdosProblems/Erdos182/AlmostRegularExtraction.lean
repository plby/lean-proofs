import ErdosProblems.Erdos182.AlmostRegularThinning

/-!
# Almost-regular extraction for Erdős Problem 182

This file packages Janzer--Sudakov Lemma 3.5.  The two inputs are the
four-almost-biregular roof extraction and the alteration lemma.  The small
deterministic argument at the end deletes vertices of degree below one
quarter of the retained right degree.
-/

namespace Erdos182

open Finset
open scoped BigOperators

noncomputable section

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Remove all edges incident with one left vertex. -/
def eraseLeft (G : BipartiteGraph A B) (a : A) : BipartiteGraph A B :=
  ⟨fun a' b ↦ G.Adj a' b ∧ a' ≠ a⟩

/-- Remove all edges incident with one right vertex. -/
def eraseRight (G : BipartiteGraph A B) (b : B) : BipartiteGraph A B :=
  ⟨fun a b' ↦ G.Adj a b' ∧ b' ≠ b⟩

@[simp] theorem eraseLeft_adj (G : BipartiteGraph A B) (a a' : A) (b : B) :
    (G.eraseLeft a).Adj a' b ↔ G.Adj a' b ∧ a' ≠ a := Iff.rfl

@[simp] theorem eraseRight_adj (G : BipartiteGraph A B) (b b' : B) (a : A) :
    (G.eraseRight b).Adj a b' ↔ G.Adj a b' ∧ b' ≠ b := Iff.rfl

theorem eraseLeft_le (G : BipartiteGraph A B) (a : A) : G.eraseLeft a ≤ G := by
  intro a' b h
  exact h.1

theorem eraseRight_le (G : BipartiteGraph A B) (b : B) : G.eraseRight b ≤ G := by
  intro a b' h
  exact h.1

@[simp] theorem leftDegree_eraseLeft (G : BipartiteGraph A B) (a a' : A) :
    (G.eraseLeft a).leftDegree a' = if a' = a then 0 else G.leftDegree a' := by
  classical
  by_cases h : a' = a
  · subst a'
    simp [leftDegree, rightNeighbors]
  · simp [leftDegree, rightNeighbors, h]

@[simp] theorem rightDegree_eraseRight (G : BipartiteGraph A B) (b b' : B) :
    (G.eraseRight b).rightDegree b' = if b' = b then 0 else G.rightDegree b' := by
  classical
  by_cases h : b' = b
  · subst b'
    simp [rightDegree, leftNeighbors]
  · simp [rightDegree, leftNeighbors, h]

theorem edgeCount_eraseLeft (G : BipartiteGraph A B) (a : A) :
    (G.eraseLeft a).edgeCount = G.edgeCount - G.leftDegree a := by
  classical
  rw [edgeCount_eq_sum_leftDegree, edgeCount_eq_sum_leftDegree]
  simp only [leftDegree_eraseLeft]
  have hdecomp := Finset.sum_erase_add Finset.univ G.leftDegree
    (Finset.mem_univ a)
  calc
    (∑ x, if x = a then 0 else G.leftDegree x) =
        ∑ x ∈ (Finset.univ.erase a), G.leftDegree x := by
      rw [← Finset.sum_erase_add Finset.univ
        (fun x ↦ if x = a then 0 else G.leftDegree x) (Finset.mem_univ a)]
      simp only [ite_self, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      simp [(Finset.mem_erase.mp hx).1]
    _ = (∑ x, G.leftDegree x) - G.leftDegree a := by omega

theorem edgeCount_eraseRight (G : BipartiteGraph A B) (b : B) :
    (G.eraseRight b).edgeCount = G.edgeCount - G.rightDegree b := by
  classical
  unfold edgeCount
  simp only [rightDegree_eraseRight]
  have hdecomp := Finset.sum_erase_add Finset.univ G.rightDegree
    (Finset.mem_univ b)
  calc
    (∑ x, if x = b then 0 else G.rightDegree x) =
        ∑ x ∈ (Finset.univ.erase b), G.rightDegree x := by
      rw [← Finset.sum_erase_add Finset.univ
        (fun x ↦ if x = b then 0 else G.rightDegree x) (Finset.mem_univ b)]
      simp only [ite_self, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      simp [(Finset.mem_erase.mp hx).1]
    _ = (∑ x, G.rightDegree x) - G.rightDegree b := by omega

theorem supportCard_eq_support (G : BipartiteGraph A B) :
    G.supportCard = G.supportLeft.card + G.supportRight.card := by
  rfl

@[simp] theorem supportLeft_eraseLeft (G : BipartiteGraph A B) (a : A) :
    (G.eraseLeft a).supportLeft = G.supportLeft.erase a := by
  classical
  ext a'
  by_cases h : a' = a
  · subst a'
    simp [mem_supportLeft]
  · simp [mem_supportLeft, h]

@[simp] theorem supportRight_eraseRight (G : BipartiteGraph A B) (b : B) :
    (G.eraseRight b).supportRight = G.supportRight.erase b := by
  classical
  ext b'
  by_cases h : b' = b
  · subst b'
    simp [mem_supportRight]
  · simp [mem_supportRight, h]

theorem supportRight_eraseLeft_subset (G : BipartiteGraph A B) (a : A) :
    (G.eraseLeft a).supportRight ⊆ G.supportRight := by
  intro b hb
  rw [mem_supportRight] at hb ⊢
  exact hb.trans_le (rightDegree_mono (eraseLeft_le G a) b)

theorem supportLeft_eraseRight_subset (G : BipartiteGraph A B) (b : B) :
    (G.eraseRight b).supportLeft ⊆ G.supportLeft := by
  intro a ha
  rw [mem_supportLeft] at ha ⊢
  exact ha.trans_le (leftDegree_mono (eraseRight_le G b) a)

theorem supportCard_eraseLeft_le_sub_one (G : BipartiteGraph A B) (a : A)
    (ha : 0 < G.leftDegree a) :
    (G.eraseLeft a).supportCard ≤ G.supportCard - 1 := by
  classical
  rw [supportCard_eq_support, supportCard_eq_support, supportLeft_eraseLeft]
  have hamem : a ∈ G.supportLeft := by simpa [mem_supportLeft] using ha
  have hleftpos : 0 < G.supportLeft.card := Finset.card_pos.mpr ⟨a, hamem⟩
  have hright := Finset.card_le_card (supportRight_eraseLeft_subset G a)
  calc
    (G.supportLeft.erase a).card + (G.eraseLeft a).supportRight.card ≤
        (G.supportLeft.erase a).card + G.supportRight.card :=
      Nat.add_le_add_left hright _
    _ = (G.supportLeft.card - 1) + G.supportRight.card := by
      rw [Finset.card_erase_of_mem hamem]
    _ = G.supportLeft.card + G.supportRight.card - 1 := by omega

theorem supportCard_eraseRight_le_sub_one (G : BipartiteGraph A B) (b : B)
    (hb : 0 < G.rightDegree b) :
    (G.eraseRight b).supportCard ≤ G.supportCard - 1 := by
  classical
  rw [supportCard_eq_support, supportCard_eq_support, supportRight_eraseRight]
  have hbmem : b ∈ G.supportRight := by simpa [mem_supportRight] using hb
  have hrightpos : 0 < G.supportRight.card := Finset.card_pos.mpr ⟨b, hbmem⟩
  have hleft := Finset.card_le_card (supportLeft_eraseRight_subset G b)
  calc
    (G.eraseRight b).supportLeft.card + (G.supportRight.erase b).card ≤
        G.supportLeft.card + (G.supportRight.erase b).card :=
      Nat.add_le_add_right hleft _
    _ = G.supportLeft.card + (G.supportRight.card - 1) := by
      rw [Finset.card_erase_of_mem hbmem]
    _ = G.supportLeft.card + G.supportRight.card - 1 := by omega

theorem one_le_supportCard_of_vertexDegree_pos (G : BipartiteGraph A B)
    {v : A ⊕ B} (hv : 0 < G.vertexDegree v) : 1 ≤ G.supportCard := by
  cases v with
  | inl a =>
      rw [supportCard_eq_support]
      have : a ∈ G.supportLeft := by simpa [vertexDegree, mem_supportLeft] using hv
      have := Finset.card_pos.mpr ⟨a, this⟩
      omega
  | inr b =>
      rw [supportCard_eq_support]
      have : b ∈ G.supportRight := by simpa [vertexDegree, mem_supportRight] using hv
      have := Finset.card_pos.mpr ⟨b, this⟩
      omega

/-- The bipartite graph consisting of exactly one prescribed edge. -/
def singletonEdge (a : A) (b : B) : BipartiteGraph A B :=
  ⟨fun a' b' ↦ a' = a ∧ b' = b⟩

theorem singletonEdge_le {G : BipartiteGraph A B} {a : A} {b : B}
    (hab : G.Adj a b) : singletonEdge a b ≤ G := by
  intro a' b' h
  rcases h with ⟨rfl, rfl⟩
  exact hab

@[simp] theorem leftDegree_singletonEdge (a a' : A) (b : B) :
    (singletonEdge a b).leftDegree a' = if a' = a then 1 else 0 := by
  classical
  by_cases h : a' = a
  · subst a'
    simp only [if_pos]
    unfold leftDegree rightNeighbors
    simp only [singletonEdge, true_and]
    change (Finset.univ.filter fun b' ↦ b' = b).card = 1
    rw [show Finset.univ.filter (fun b' ↦ b' = b) = {b} by ext; simp]
    simp
  · simp [singletonEdge, leftDegree, rightNeighbors, h]

@[simp] theorem rightDegree_singletonEdge (a : A) (b b' : B) :
    (singletonEdge a b).rightDegree b' = if b' = b then 1 else 0 := by
  classical
  by_cases h : b' = b
  · subst b'
    simp only [if_pos]
    unfold rightDegree leftNeighbors
    simp only [singletonEdge, and_true]
    change (Finset.univ.filter fun a' ↦ a' = a).card = 1
    rw [show Finset.univ.filter (fun a' ↦ a' = a) = {a} by ext; simp]
    simp
  · simp [singletonEdge, rightDegree, leftNeighbors, h]

@[simp] theorem edgeCount_singletonEdge (a : A) (b : B) :
    (singletonEdge a b).edgeCount = 1 := by
  classical
  unfold edgeCount
  simp

@[simp] theorem supportCard_singletonEdge (a : A) (b : B) :
    (singletonEdge a b).supportCard = 2 := by
  classical
  rw [supportCard_eq_support]
  have hleft : (singletonEdge a b).supportLeft = {a} := by
    ext a'
    rw [mem_supportLeft, leftDegree_singletonEdge]
    by_cases h : a' = a <;> simp [h]
  have hright : (singletonEdge a b).supportRight = {b} := by
    ext b'
    rw [mem_supportRight, rightDegree_singletonEdge]
    by_cases h : b' = b <;> simp [h]
  rw [hleft, hright]
  simp

theorem singletonEdge_vertexDegree_le_one (a : A) (b : B) (v : A ⊕ B) :
    (singletonEdge a b).vertexDegree v ≤ 1 := by
  cases v <;> simp [vertexDegree] <;> split <;> omega

theorem singletonEdge_isAlmostRegular (a : A) (b : B) :
    (singletonEdge a b).IsAlmostRegular 64 := by
  refine ⟨by simp, ?_⟩
  intro u v hv
  have hu := singletonEdge_vertexDegree_le_one a b u
  omega

/-- From average degree at least `d/2`, retain a nonempty subgraph of the
same average-degree quality whose every non-isolated vertex has degree at
least `d/4`.  The proof chooses an admissible subgraph with minimum support;
this is the finite form of the usual iterative deletion argument. -/
theorem exists_minDegree_subgraph
    (G : BipartiteGraph A B) {d : ℕ} (hG : 0 < G.edgeCount)
    (havg : G.HasAverageDegreeAtLeastHalf d) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧ 0 < H.edgeCount ∧
      H.HasAverageDegreeAtLeastHalf d ∧
      ∀ v : A ⊕ B, 0 < H.vertexDegree v → d ≤ 4 * H.vertexDegree v := by
  classical
  let candidates : Finset (BipartiteGraph A B) :=
    Finset.univ.filter fun H ↦
      H ≤ G ∧ 0 < H.edgeCount ∧ H.HasAverageDegreeAtLeastHalf d
  have hGmem : G ∈ candidates := by
    simp [candidates, hG, havg]
  obtain ⟨H, hHmem, hminimal⟩ :=
    Finset.exists_min_image candidates supportCard ⟨G, hGmem⟩
  have hH : H ≤ G ∧ 0 < H.edgeCount ∧ H.HasAverageDegreeAtLeastHalf d := by
    simpa [candidates] using hHmem
  refine ⟨H, hH.1, hH.2.1, hH.2.2, ?_⟩
  intro v hv
  by_contra hlow
  have hfour : 4 * H.vertexDegree v < d := by omega
  have hsupp : 1 ≤ H.supportCard := one_le_supportCard_of_vertexDegree_pos H hv
  have hde : H.vertexDegree v < H.edgeCount := by
    have hdle : d ≤ 4 * H.edgeCount := by
      exact le_trans (Nat.le_mul_of_pos_right d hsupp) hH.2.2
    omega
  cases v with
  | inl a =>
      let K := H.eraseLeft a
      have hKedge : 0 < K.edgeCount := by
        change 0 < (H.eraseLeft a).edgeCount
        rw [edgeCount_eraseLeft]
        simpa [vertexDegree] using Nat.sub_pos_of_lt hde
      have hKsupport : K.supportCard ≤ H.supportCard - 1 := by
        exact supportCard_eraseLeft_le_sub_one H a (by simpa [vertexDegree] using hv)
      have hsplit : d * (H.supportCard - 1) + d = d * H.supportCard := by
        calc
          d * (H.supportCard - 1) + d =
              d * ((H.supportCard - 1) + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
          _ = d * H.supportCard := by congr 1; omega
      have hKavg : K.HasAverageDegreeAtLeastHalf d := by
        unfold HasAverageDegreeAtLeastHalf
        change d * (H.eraseLeft a).supportCard ≤ 4 * (H.eraseLeft a).edgeCount
        calc
          d * (H.eraseLeft a).supportCard ≤ d * (H.supportCard - 1) :=
            Nat.mul_le_mul_left d hKsupport
          _ ≤ 4 * (H.eraseLeft a).edgeCount := by
            rw [edgeCount_eraseLeft]
            have hdeg : H.leftDegree a = H.vertexDegree (Sum.inl a) := rfl
            rw [hdeg]
            have hpre :
                d * (H.supportCard - 1) + 4 * H.vertexDegree (Sum.inl a) <
                  4 * H.edgeCount := by
              calc
                _ < d * (H.supportCard - 1) + d :=
                  Nat.add_lt_add_left hfour _
                _ = d * H.supportCard := hsplit
                _ ≤ 4 * H.edgeCount := hH.2.2
            have hsub :
                4 * (H.edgeCount - H.vertexDegree (Sum.inl a)) +
                    4 * H.vertexDegree (Sum.inl a) = 4 * H.edgeCount := by
              rw [← Nat.mul_add]
              congr 1
              omega
            have hpre_le := hpre.le
            omega
      have hKmem : K ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(eraseLeft_le H a).trans hH.1, hKedge, hKavg⟩
      have := hminimal K hKmem
      omega

  | inr b =>
      let K := H.eraseRight b
      have hKedge : 0 < K.edgeCount := by
        change 0 < (H.eraseRight b).edgeCount
        rw [edgeCount_eraseRight]
        simpa [vertexDegree] using Nat.sub_pos_of_lt hde
      have hKsupport : K.supportCard ≤ H.supportCard - 1 := by
        exact supportCard_eraseRight_le_sub_one H b (by simpa [vertexDegree] using hv)
      have hsplit : d * (H.supportCard - 1) + d = d * H.supportCard := by
        calc
          d * (H.supportCard - 1) + d =
              d * ((H.supportCard - 1) + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
          _ = d * H.supportCard := by congr 1; omega
      have hKavg : K.HasAverageDegreeAtLeastHalf d := by
        unfold HasAverageDegreeAtLeastHalf
        change d * (H.eraseRight b).supportCard ≤ 4 * (H.eraseRight b).edgeCount
        calc
          d * (H.eraseRight b).supportCard ≤ d * (H.supportCard - 1) :=
            Nat.mul_le_mul_left d hKsupport
          _ ≤ 4 * (H.eraseRight b).edgeCount := by
            rw [edgeCount_eraseRight]
            have hdeg : H.rightDegree b = H.vertexDegree (Sum.inr b) := rfl
            rw [hdeg]
            have hpre :
                d * (H.supportCard - 1) + 4 * H.vertexDegree (Sum.inr b) <
                  4 * H.edgeCount := by
              calc
                _ < d * (H.supportCard - 1) + d :=
                  Nat.add_lt_add_left hfour _
                _ = d * H.supportCard := hsplit
                _ ≤ 4 * H.edgeCount := hH.2.2
            have hsub :
                4 * (H.edgeCount - H.vertexDegree (Sum.inr b)) +
                    4 * H.vertexDegree (Sum.inr b) = 4 * H.edgeCount := by
              rw [← Nat.mul_add]
              congr 1
              omega
            have hpre_le := hpre.le
            omega
      have hKmem : K ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(eraseRight_le H b).trans hH.1, hKedge, hKavg⟩
      have := hminimal K hKmem
      omega

/-- The graph-theoretic core of JS Lemma 3.5.  Once the roof extraction
produces a four-almost-biregular graph of right degree `d`, alteration and
minimum-degree pruning give a `64`-almost-regular graph. -/
theorem exists_almostRegular_subgraph_of_scale
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {L δ d ℓ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hpow : L * δ ≤ 2 ^ (δ / (d - 1)))
    (hδd : δ ≤ 8 * ℓ * d) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧ H.IsAlmostRegular 64 ∧
      δ * H.supportCard ≤ 32 * ℓ * H.edgeCount := by
  classical
  obtain ⟨F, A₁, B₁, hFG, hF⟩ :=
    exists_four_almostBiregular_subgraph G A₀ B₀ L δ d hG hd hdδ hpow
  obtain ⟨T, hTF, hTedge, hTavg, hTmax⟩ :=
    exists_randomly_thinned hF (by norm_num : 0 < 4) (by omega : 0 < d)
  obtain ⟨H, hHT, hHedge, hHavg, hHmin⟩ :=
    exists_minDegree_subgraph T hTedge hTavg
  have hdegree_mono : ∀ v : A ⊕ B, H.vertexDegree v ≤ T.vertexDegree v := by
    intro v
    cases v with
    | inl a => exact leftDegree_mono hHT a
    | inr b => exact rightDegree_mono hHT b
  have hHalmost : H.IsAlmostRegular 64 := by
    refine ⟨hHedge, ?_⟩
    intro u v hv
    have huT := (hdegree_mono u).trans (hTmax u)
    have hvmin := hHmin v hv
    omega
  refine ⟨H, hHT.trans (hTF.trans hFG), hHalmost, ?_⟩
  calc
    δ * H.supportCard ≤ (8 * ℓ * d) * H.supportCard :=
      Nat.mul_le_mul_right H.supportCard hδd
    _ = 8 * ℓ * (d * H.supportCard) := by ring
    _ ≤ 8 * ℓ * (4 * H.edgeCount) :=
      Nat.mul_le_mul_left (8 * ℓ) hHavg
    _ = 32 * ℓ * H.edgeCount := by ring

/-- Janzer--Sudakov Lemma 3.5, in the integer form used by the iteration.

The logarithmic loss is written with `Nat.log2 L + 1`, so the statement is
valid without a separate convention at `L = 1`.  The small-degree branch is
a single edge; in the other branch we use
`d = δ / (4 * (Nat.log2 L + 1))` in the roof lemma. -/
theorem exists_almostRegular_subgraph
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {L δ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hδ : 2 ≤ δ) (hδL : δ ≤ L) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧ H.IsAlmostRegular 64 ∧
      δ * H.supportCard ≤
        32 * (Nat.log2 L + 1) * H.edgeCount := by
  classical
  let ℓ := Nat.log2 L + 1
  have hℓ : 0 < ℓ := by simp [ℓ]
  by_cases hsmall : δ ≤ 16 * ℓ
  · obtain ⟨b, hb⟩ := hG.2.2.1
    have hbdeg : G.rightDegree b = δ := hG.2.2.2.1 b hb
    have hbpos : 0 < G.rightDegree b := by omega
    rw [rightDegree, Finset.card_pos] at hbpos
    obtain ⟨a, ha⟩ := hbpos
    have hab : G.Adj a b := (mem_leftNeighbors G a b).mp ha
    refine ⟨singletonEdge a b, singletonEdge_le hab,
      singletonEdge_isAlmostRegular a b, ?_⟩
    simp only [supportCard_singletonEdge, edgeCount_singletonEdge]
    dsimp [ℓ] at hsmall ⊢
    omega
  · let d := δ / (4 * ℓ)
    have hden : 0 < 4 * ℓ := by positivity
    have hd : 2 ≤ d := by
      apply (Nat.le_div_iff_mul_le hden).2
      dsimp [ℓ] at hsmall ⊢
      omega
    have hdδ : d ≤ δ := by
      exact (Nat.div_le_self δ (4 * ℓ)).trans le_rfl
    have hδd : δ ≤ 8 * ℓ * d := by
      have hlt : δ < (d + 1) * (4 * ℓ) := by
        apply (Nat.div_lt_iff_lt_mul hden).mp
        dsimp [d]
        exact Nat.lt_succ_self _
      have hdenle : 4 * ℓ ≤ (4 * ℓ) * d := by
        simpa using Nat.mul_le_mul_left (4 * ℓ) (show 1 ≤ d by omega)
      calc
        δ ≤ (d + 1) * (4 * ℓ) := hlt.le
        _ = (4 * ℓ) * d + 4 * ℓ := by ring
        _ ≤ (4 * ℓ) * d + (4 * ℓ) * d :=
          Nat.add_le_add_left hdenle _
        _ = 8 * ℓ * d := by ring
    have hLpow : L ≤ 2 ^ ℓ := by
      have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
      exact (by simpa [ℓ, Nat.log2_eq_log_two] using hlt.le)
    have hδpow : δ ≤ 2 ^ ℓ := hδL.trans hLpow
    have hprod : L * δ ≤ 2 ^ (2 * ℓ) := by
      calc
        L * δ ≤ (2 ^ ℓ) * (2 ^ ℓ) := Nat.mul_le_mul hLpow hδpow
        _ = 2 ^ (ℓ + ℓ) := (pow_add 2 ℓ ℓ).symm
        _ = 2 ^ (2 * ℓ) := by congr 1 <;> omega
    have hdsub : 0 < d - 1 := by omega
    have hexp : 2 * ℓ ≤ δ / (d - 1) := by
      apply (Nat.le_div_iff_mul_le hdsub).2
      calc
        (2 * ℓ) * (d - 1) ≤ (4 * ℓ) * d := by
          exact Nat.mul_le_mul (by omega) (Nat.sub_le d 1)
        _ ≤ δ := by
          simpa [d, Nat.mul_comm] using Nat.div_mul_le_self δ (4 * ℓ)
    have hpowmono : 2 ^ (2 * ℓ) ≤ 2 ^ (δ / (d - 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    have hpow : L * δ ≤ 2 ^ (δ / (d - 1)) := hprod.trans hpowmono
    simpa [ℓ] using
      (exists_almostRegular_subgraph_of_scale hG hd hdδ hpow hδd)

end BipartiteGraph

end


end Erdos182
