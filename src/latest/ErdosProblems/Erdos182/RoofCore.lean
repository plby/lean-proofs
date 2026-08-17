import Mathlib

/-!
# Roofs in finite bipartite graphs

This file contains the finite Hall-theoretic ``roof'' lemma used in the
Pyber--Rödl--Szemerédi almost-biregular extraction argument.  We use a
two-sorted bipartite graph, so that all cardinality bookkeeping stays on the
two parts and no disjointness side condition is needed.
-/

namespace Erdos182

open Finset Function
open scoped BigOperators

/-- A finite bipartite graph with left vertex type `A` and right vertex type `B`. -/
structure BipartiteGraph (A B : Type*) where
  Adj : A → B → Prop

namespace BipartiteGraph

variable {A B : Type*}

@[ext]
theorem ext {G H : BipartiteGraph A B} (h : ∀ a b, G.Adj a b ↔ H.Adj a b) : G = H := by
  cases G with
  | mk g =>
    cases H with
    | mk h' =>
      congr
      funext a b
      exact propext (h a b)

/-- On finite vertex types, a bipartite graph is equivalently a Boolean adjacency table. -/
noncomputable def boolTableEquiv [Fintype A] [Fintype B] :
    (A → B → Bool) ≃ BipartiteGraph A B := by
  classical
  exact
    { toFun := fun f ↦ ⟨fun a b ↦ f a b = true⟩
      invFun := fun G a b ↦ if G.Adj a b then true else false
      left_inv := fun f ↦ by
        funext a b
        cases h : f a b <;> simp [h]
      right_inv := fun G ↦ by
        ext a b
        simp }

noncomputable instance [Fintype A] [Fintype B] : Fintype (BipartiteGraph A B) :=
  by
    letI : Fintype (A → B → Bool) := Fintype.ofFinite _
    exact Fintype.ofEquiv (A → B → Bool) boolTableEquiv

instance : PartialOrder (BipartiteGraph A B) where
  le G H := ∀ ⦃a b⦄, G.Adj a b → H.Adj a b
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ _ _ h := h₂ (h₁ h)
  le_antisymm G H hGH hHG := by
    apply ext
    exact fun a b ↦ ⟨@hGH a b, @hHG a b⟩

@[simp]
theorem le_def {G H : BipartiteGraph A B} : G ≤ H ↔ ∀ ⦃a b⦄, G.Adj a b → H.Adj a b :=
  Iff.rfl

instance : Bot (BipartiteGraph A B) := ⟨⟨fun _ _ ↦ False⟩⟩

instance : Max (BipartiteGraph A B) :=
  ⟨fun G H ↦ ⟨fun a b ↦ G.Adj a b ∨ H.Adj a b⟩⟩

instance : SDiff (BipartiteGraph A B) :=
  ⟨fun G H ↦ ⟨fun a b ↦ G.Adj a b ∧ ¬ H.Adj a b⟩⟩

@[simp] theorem bot_adj (a : A) (b : B) : (⊥ : BipartiteGraph A B).Adj a b ↔ False :=
  Iff.rfl

@[simp] theorem max_adj (G H : BipartiteGraph A B) (a : A) (b : B) :
    (G ⊔ H).Adj a b ↔ G.Adj a b ∨ H.Adj a b := Iff.rfl

@[simp] theorem sdiff_adj (G H : BipartiteGraph A B) (a : A) (b : B) :
    (G \ H).Adj a b ↔ G.Adj a b ∧ ¬ H.Adj a b := Iff.rfl

variable [Fintype A] [Fintype B]

/-- The left neighbors of a right vertex. -/
noncomputable def leftNeighbors (G : BipartiteGraph A B) (b : B) : Finset A :=
  by classical exact Finset.univ.filter fun a ↦ G.Adj a b

/-- The right neighbors of a left vertex. -/
noncomputable def rightNeighbors (G : BipartiteGraph A B) (a : A) : Finset B :=
  by classical exact Finset.univ.filter fun b ↦ G.Adj a b

/-- Degree of a vertex in the left part. -/
noncomputable def leftDegree (G : BipartiteGraph A B) (a : A) : ℕ :=
  (G.rightNeighbors a).card

/-- Degree of a vertex in the right part. -/
noncomputable def rightDegree (G : BipartiteGraph A B) (b : B) : ℕ :=
  (G.leftNeighbors b).card

/-- The number of edges, counted from the right part. -/
noncomputable def edgeCount (G : BipartiteGraph A B) : ℕ :=
  ∑ b, G.rightDegree b

@[simp]
theorem mem_leftNeighbors (G : BipartiteGraph A B) (a : A) (b : B) :
    a ∈ G.leftNeighbors b ↔ G.Adj a b := by
  simp [leftNeighbors]

@[simp]
theorem mem_rightNeighbors (G : BipartiteGraph A B) (a : A) (b : B) :
    b ∈ G.rightNeighbors a ↔ G.Adj a b := by
  simp [rightNeighbors]

theorem edgeCount_eq_sum_leftDegree (G : BipartiteGraph A B) :
    G.edgeCount = ∑ a, G.leftDegree a := by
  classical
  simpa only [edgeCount, rightDegree, leftDegree, leftNeighbors, rightNeighbors,
      Finset.card_filter] using
    (Finset.sum_comm (s := (Finset.univ : Finset B)) (t := (Finset.univ : Finset A))
      (f := fun b a ↦ if G.Adj a b then 1 else 0))

/-- Left vertices incident with at least one edge. -/
noncomputable def supportLeft (G : BipartiteGraph A B) : Finset A :=
  by classical exact Finset.univ.filter fun a ↦ 0 < G.leftDegree a

/-- Right vertices incident with at least one edge. -/
noncomputable def supportRight (G : BipartiteGraph A B) : Finset B :=
  by classical exact Finset.univ.filter fun b ↦ 0 < G.rightDegree b

@[simp] theorem mem_supportLeft (G : BipartiteGraph A B) (a : A) :
    a ∈ G.supportLeft ↔ 0 < G.leftDegree a := by
  simp [supportLeft]

@[simp] theorem mem_supportRight (G : BipartiteGraph A B) (b : B) :
    b ∈ G.supportRight ↔ 0 < G.rightDegree b := by
  simp [supportRight]

theorem adj_mem_supportLeft (G : BipartiteGraph A B) {a : A} {b : B} (h : G.Adj a b) :
    a ∈ G.supportLeft := by
  rw [mem_supportLeft, leftDegree, Finset.card_pos]
  exact ⟨b, G.mem_rightNeighbors a b |>.mpr h⟩

theorem adj_mem_supportRight (G : BipartiteGraph A B) {a : A} {b : B} (h : G.Adj a b) :
    b ∈ G.supportRight := by
  rw [mem_supportRight, rightDegree, Finset.card_pos]
  exact ⟨a, G.mem_leftNeighbors a b |>.mpr h⟩

/-- `G` has no edges outside the displayed finite vertex sets. -/
def SupportedOn (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) : Prop :=
  ∀ ⦃a b⦄, G.Adj a b → a ∈ A₀ ∧ b ∈ B₀

theorem supportedOn_support (G : BipartiteGraph A B) :
    G.SupportedOn G.supportLeft G.supportRight := by
  intro a b hab
  exact ⟨G.adj_mem_supportLeft hab, G.adj_mem_supportRight hab⟩

/-- Every displayed right vertex has the same degree. -/
def IsRightRegularOn (G : BipartiteGraph A B) (B₀ : Finset B) (d : ℕ) : Prop :=
  ∀ b ∈ B₀, G.rightDegree b = d

/-- A half-regular subgraph, with all active vertices explicitly recorded. -/
def IsHalfRegularSubgraphOf (H G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (d : ℕ) : Prop :=
  H ≤ G ∧ H.SupportedOn A₀ B₀ ∧ B₀.Nonempty ∧ H.IsRightRegularOn B₀ d

/-- The integer form of `(L,d)`-almost-biregularity.

The usual left density is `edgeCount / |A₀|`; cross multiplication avoids
introducing rationals into the extraction lemma.
-/
def IsAlmostBiregularOn (G : BipartiteGraph A B) (A₀ : Finset A)
    (B₀ : Finset B) (L d : ℕ) : Prop :=
  G.SupportedOn A₀ B₀ ∧ A₀.Nonempty ∧ B₀.Nonempty ∧ G.IsRightRegularOn B₀ d ∧
    d * A₀.card ≤ G.edgeCount ∧
    ∀ a ∈ A₀, G.leftDegree a * A₀.card ≤ L * G.edgeCount

theorem edgeCount_eq_card_mul_of_rightRegularOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {d : ℕ} (hs : G.SupportedOn A₀ B₀)
    (hr : G.IsRightRegularOn B₀ d) : G.edgeCount = B₀.card * d := by
  classical
  have hout : ∀ b ∈ (Finset.univ : Finset B), b ∉ B₀ → G.rightDegree b = 0 := by
    intro b _ hb
    rw [rightDegree, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨a, ha⟩
    exact hb (hs ((G.mem_leftNeighbors a b).mp ha)).2
  calc
    G.edgeCount = ∑ b ∈ (Finset.univ : Finset B), G.rightDegree b := by
      simp [edgeCount]
    _ = ∑ b ∈ B₀, G.rightDegree b :=
      (Finset.sum_subset (Finset.subset_univ B₀) hout).symm
    _ = ∑ _b ∈ B₀, d := by
      apply Finset.sum_congr rfl
      exact hr
    _ = B₀.card * d := by simp

theorem supportLeft_subset_of_supportedOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} (hs : G.SupportedOn A₀ B₀) :
    G.supportLeft ⊆ A₀ := by
  intro a ha
  rw [mem_supportLeft, leftDegree, Finset.card_pos] at ha
  obtain ⟨b, hb⟩ := ha
  exact (hs ((G.mem_rightNeighbors a b).mp hb)).1

theorem supportRight_eq_of_supportedOn_isRightRegularOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {d : ℕ} (hs : G.SupportedOn A₀ B₀)
    (hr : G.IsRightRegularOn B₀ d) (hd : 0 < d) : G.supportRight = B₀ := by
  classical
  ext b
  constructor
  · intro hb
    rw [mem_supportRight, rightDegree, Finset.card_pos] at hb
    obtain ⟨a, ha⟩ := hb
    exact (hs ((G.mem_leftNeighbors a b).mp ha)).2
  · intro hb
    rw [mem_supportRight, hr b hb]
    exact hd

/-- The neighborhood in `A` of a finite set of right vertices. -/
noncomputable def neighborhood (G : BipartiteGraph A B) (X : Finset B) : Finset A :=
  by classical exact X.biUnion G.leftNeighbors

@[simp]
theorem mem_neighborhood (G : BipartiteGraph A B) (X : Finset B) (a : A) :
    a ∈ G.neighborhood X ↔ ∃ b ∈ X, G.Adj a b := by
  simp [neighborhood]

/-- Delete all edges at right vertices outside `X`. -/
def restrictRight (G : BipartiteGraph A B) (X : Finset B) : BipartiteGraph A B where
  Adj a b := G.Adj a b ∧ b ∈ X

@[simp] theorem restrictRight_adj (G : BipartiteGraph A B) (X : Finset B) (a : A) (b : B) :
    (G.restrictRight X).Adj a b ↔ G.Adj a b ∧ b ∈ X := Iff.rfl

theorem restrictRight_le (G : BipartiteGraph A B) (X : Finset B) :
    G.restrictRight X ≤ G := by
  intro a b h
  exact h.1

theorem leftNeighbors_restrictRight_of_mem (G : BipartiteGraph A B)
    {X : Finset B} {b : B} (hb : b ∈ X) :
    (G.restrictRight X).leftNeighbors b = G.leftNeighbors b := by
  classical
  ext a
  simp [hb]

theorem leftNeighbors_restrictRight_of_not_mem (G : BipartiteGraph A B)
    {X : Finset B} {b : B} (hb : b ∉ X) :
    (G.restrictRight X).leftNeighbors b = ∅ := by
  classical
  ext a
  simp [hb]

theorem rightDegree_restrictRight_of_mem (G : BipartiteGraph A B)
    {X : Finset B} {b : B} (hb : b ∈ X) :
    (G.restrictRight X).rightDegree b = G.rightDegree b := by
  unfold rightDegree
  rw [leftNeighbors_restrictRight_of_mem G hb]

theorem rightDegree_restrictRight_of_not_mem (G : BipartiteGraph A B)
    {X : Finset B} {b : B} (hb : b ∉ X) :
    (G.restrictRight X).rightDegree b = 0 := by
  rw [rightDegree, leftNeighbors_restrictRight_of_not_mem G hb]
  simp

theorem supportLeft_restrictRight (G : BipartiteGraph A B) (X : Finset B) :
    (G.restrictRight X).supportLeft = G.neighborhood X := by
  classical
  ext a
  rw [mem_supportLeft, mem_neighborhood]
  constructor
  · intro h
    rw [leftDegree, Finset.card_pos] at h
    obtain ⟨b, hb⟩ := h
    rw [mem_rightNeighbors] at hb
    exact ⟨b, hb.2, hb.1⟩
  · rintro ⟨b, hbX, hab⟩
    rw [leftDegree, Finset.card_pos]
    exact ⟨b, by simp [hab, hbX]⟩

theorem supportRight_restrictRight (G : BipartiteGraph A B) (X : Finset B)
    (hpos : ∀ b ∈ X, 0 < G.rightDegree b) :
    (G.restrictRight X).supportRight = X := by
  classical
  ext b
  by_cases hb : b ∈ X
  · simp [mem_supportRight, hb, rightDegree_restrictRight_of_mem, hpos b hb]
  · simp [mem_supportRight, hb, rightDegree_restrictRight_of_not_mem]

/-- A graph is half-regular when all its non-isolated right vertices have
the same positive degree. -/
def IsHalfRegular (G : BipartiteGraph A B) (d : ℕ) : Prop :=
  G.supportRight.Nonempty ∧ ∀ b ∈ G.supportRight, G.rightDegree b = d

theorem isHalfRegular_of_supportedOn_isRightRegularOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {d : ℕ} (hs : G.SupportedOn A₀ B₀)
    (hne : B₀.Nonempty) (hr : G.IsRightRegularOn B₀ d) (hd : 0 < d) :
    G.IsHalfRegular d := by
  have hsupp := supportRight_eq_of_supportedOn_isRightRegularOn hs hr hd
  constructor
  · rw [hsupp]
    exact hne
  · intro b hb
    rw [hsupp] at hb
    exact hr b hb

/-- The right-to-left vertex ratio of the non-isolated parts. -/
noncomputable def supportRatio (G : BipartiteGraph A B) : ℚ :=
  (G.supportRight.card : ℚ) / (G.supportLeft.card : ℚ)

/-- Choose exactly `r` neighbors at each displayed right vertex. -/
noncomputable def selectedNeighbors (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) (b : B) : Finset A := by
  classical
  by_cases hb : b ∈ B₀
  · exact Classical.choose (Finset.exists_subset_card_eq (h b hb))
  · exact ∅

theorem selectedNeighbors_subset (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) (b : B) :
    G.selectedNeighbors B₀ r h b ⊆ G.leftNeighbors b := by
  classical
  unfold selectedNeighbors
  split
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq (h b ‹b ∈ B₀›))).1
  · exact Finset.empty_subset _

theorem card_selectedNeighbors_of_mem (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) {b : B} (hb : b ∈ B₀) :
    (G.selectedNeighbors B₀ r h b).card = r := by
  classical
  unfold selectedNeighbors
  split
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq (h b hb))).2
  · contradiction

theorem selectedNeighbors_eq_empty_of_not_mem (G : BipartiteGraph A B)
    (B₀ : Finset B) (r : ℕ) (h : ∀ b ∈ B₀, r ≤ G.rightDegree b)
    {b : B} (hb : b ∉ B₀) : G.selectedNeighbors B₀ r h b = ∅ := by
  classical
  unfold selectedNeighbors
  simp [hb]

/-- The canonical subgraph retaining exactly `r` arbitrary incident edges
at each vertex of `B₀`. -/
noncomputable def trimRightDegree (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) : BipartiteGraph A B where
  Adj a b := a ∈ G.selectedNeighbors B₀ r h b

@[simp] theorem trimRightDegree_adj (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) (a : A) (b : B) :
    (G.trimRightDegree B₀ r h).Adj a b ↔ a ∈ G.selectedNeighbors B₀ r h b := Iff.rfl

theorem trimRightDegree_le (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) : G.trimRightDegree B₀ r h ≤ G := by
  intro a b hab
  rw [← G.mem_leftNeighbors a b]
  exact G.selectedNeighbors_subset B₀ r h b hab

theorem rightDegree_trimRightDegree_of_mem (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) {b : B} (hb : b ∈ B₀) :
    (G.trimRightDegree B₀ r h).rightDegree b = r := by
  classical
  rw [rightDegree]
  have heq : (G.trimRightDegree B₀ r h).leftNeighbors b =
      G.selectedNeighbors B₀ r h b := by
    ext a
    simp
  rw [heq, G.card_selectedNeighbors_of_mem B₀ r h hb]

theorem rightDegree_trimRightDegree_of_not_mem (G : BipartiteGraph A B)
    (B₀ : Finset B) (r : ℕ) (h : ∀ b ∈ B₀, r ≤ G.rightDegree b)
    {b : B} (hb : b ∉ B₀) : (G.trimRightDegree B₀ r h).rightDegree b = 0 := by
  classical
  rw [rightDegree]
  have heq : (G.trimRightDegree B₀ r h).leftNeighbors b = ∅ := by
    ext a
    simp [G.selectedNeighbors_eq_empty_of_not_mem B₀ r h hb]
  simp [heq]

theorem supportRight_trimRightDegree (G : BipartiteGraph A B) (B₀ : Finset B) (r : ℕ)
    (h : ∀ b ∈ B₀, r ≤ G.rightDegree b) (hr : 0 < r) :
    (G.trimRightDegree B₀ r h).supportRight = B₀ := by
  classical
  ext b
  by_cases hb : b ∈ B₀
  · simp [mem_supportRight, hb, G.rightDegree_trimRightDegree_of_mem B₀ r h hb, hr]
  · simp [mem_supportRight, hb, G.rightDegree_trimRightDegree_of_not_mem B₀ r h hb]

theorem isHalfRegular_trimRightDegree {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    (G.trimRightDegree G.supportRight r
      (fun b hb ↦ hrδ.trans_eq (hG.2 b hb).symm)).IsHalfRegular r := by
  let hdeg : ∀ b ∈ G.supportRight, r ≤ G.rightDegree b :=
    fun b hb ↦ hrδ.trans_eq (hG.2 b hb).symm
  have hsupp := G.supportRight_trimRightDegree G.supportRight r hdeg hr
  refine ⟨?_, ?_⟩
  · rw [hsupp]
    exact hG.1
  · intro b hb
    rw [hsupp] at hb
    exact G.rightDegree_trimRightDegree_of_mem G.supportRight r hdeg hb

/-- All half-regular subgraphs of `G` with right degree `r`. -/
noncomputable def halfRegularSubgraphs (G : BipartiteGraph A B) (r : ℕ) :
    Finset (BipartiteGraph A B) := by
  classical
  exact Finset.univ.filter fun H ↦ H ≤ G ∧ H.IsHalfRegular r

@[simp] theorem mem_halfRegularSubgraphs (G H : BipartiteGraph A B) (r : ℕ) :
    H ∈ G.halfRegularSubgraphs r ↔ H ≤ G ∧ H.IsHalfRegular r := by
  classical
  simp [halfRegularSubgraphs]

theorem halfRegularSubgraphs_nonempty {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    (G.halfRegularSubgraphs r).Nonempty := by
  let hdeg : ∀ b ∈ G.supportRight, r ≤ G.rightDegree b :=
    fun b hb ↦ hrδ.trans_eq (hG.2 b hb).symm
  let H := G.trimRightDegree G.supportRight r hdeg
  refine ⟨H, (G.mem_halfRegularSubgraphs H r).mpr ⟨?_, ?_⟩⟩
  · exact G.trimRightDegree_le G.supportRight r hdeg
  · exact isHalfRegular_trimRightDegree hG hr hrδ

/-- A half-regular subgraph maximizing the ratio of its two non-isolated
parts exists because the ambient graph is finite. -/
theorem exists_maximal_halfRegular {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ∃ H ∈ G.halfRegularSubgraphs r,
      ∀ K ∈ G.halfRegularSubgraphs r, K.supportRatio ≤ H.supportRatio := by
  classical
  exact Finset.exists_max_image _ _ (halfRegularSubgraphs_nonempty hG hr hrδ)

theorem supportLeft_nonempty_of_isHalfRegular {G : BipartiteGraph A B} {r : ℕ}
    (hG : G.IsHalfRegular r) (hr : 0 < r) : G.supportLeft.Nonempty := by
  obtain ⟨b, hb⟩ := hG.1
  have hdeg : 0 < G.rightDegree b := (hG.2 b hb).symm ▸ hr
  rw [rightDegree, Finset.card_pos] at hdeg
  obtain ⟨a, ha⟩ := hdeg
  exact ⟨a, G.adj_mem_supportLeft ((G.mem_leftNeighbors a b).mp ha)⟩

theorem supportRatio_pos_of_isHalfRegular {G : BipartiteGraph A B} {r : ℕ}
    (hG : G.IsHalfRegular r) (hr : 0 < r) : 0 < G.supportRatio := by
  rw [supportRatio]
  apply div_pos
  · exact_mod_cast hG.1.card_pos
  · exact_mod_cast (supportLeft_nonempty_of_isHalfRegular hG hr).card_pos

theorem supportLeft_mono {G H : BipartiteGraph A B} (h : H ≤ G) :
    H.supportLeft ⊆ G.supportLeft := by
  intro a ha
  rw [mem_supportLeft] at ha ⊢
  rw [leftDegree, Finset.card_pos] at ha ⊢
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, G.mem_rightNeighbors a b |>.mpr (h (H.mem_rightNeighbors a b |>.mp hb))⟩

theorem supportRight_mono {G H : BipartiteGraph A B} (h : H ≤ G) :
    H.supportRight ⊆ G.supportRight := by
  intro b hb
  rw [mem_supportRight] at hb ⊢
  rw [rightDegree, Finset.card_pos] at hb ⊢
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, G.mem_leftNeighbors a b |>.mpr (h (H.mem_leftNeighbors a b |>.mp ha))⟩

theorem leftDegree_mono {G H : BipartiteGraph A B} (h : H ≤ G) (a : A) :
    H.leftDegree a ≤ G.leftDegree a := by
  apply Finset.card_le_card
  intro b hb
  rw [mem_rightNeighbors] at hb ⊢
  exact h hb

theorem rightDegree_mono {G H : BipartiteGraph A B} (h : H ≤ G) (b : B) :
    H.rightDegree b ≤ G.rightDegree b := by
  apply Finset.card_le_card
  intro a ha
  rw [mem_leftNeighbors] at ha ⊢
  exact h ha

theorem edgeCount_eq_sum_supportLeft (G : BipartiteGraph A B) :
    G.edgeCount = ∑ a ∈ G.supportLeft, G.leftDegree a := by
  rw [G.edgeCount_eq_sum_leftDegree]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  rw [mem_supportLeft] at ha
  omega

theorem edgeCount_eq_card_supportRight_mul_of_isHalfRegular
    {G : BipartiteGraph A B} {r : ℕ} (hG : G.IsHalfRegular r) :
    G.edgeCount = G.supportRight.card * r :=
  edgeCount_eq_card_mul_of_rightRegularOn G.supportedOn_support hG.2

/-- Nonnegative rational version of `supportRatio`, used for finite suprema. -/
noncomputable def supportRatioNN (G : BipartiteGraph A B) : NNRat :=
  (G.supportRight.card : NNRat) / (G.supportLeft.card : NNRat)

/-- The largest support ratio among the degree-`r` half-regular subgraphs. -/
noncomputable def maxSupportRatio (G : BipartiteGraph A B) (r : ℕ) : NNRat := by
  classical
  exact (G.halfRegularSubgraphs r).sup supportRatioNN

theorem supportRatioNN_le_maxSupportRatio {G H : BipartiteGraph A B} {r : ℕ}
    (hHG : H ≤ G) (hH : H.IsHalfRegular r) :
    H.supportRatioNN ≤ G.maxSupportRatio r := by
  classical
  apply Finset.le_sup
  exact (G.mem_halfRegularSubgraphs H r).mpr ⟨hHG, hH⟩

theorem supportRatioNN_le_trimRightDegree {H : BipartiteGraph A B} {r s : ℕ}
    (hH : H.IsHalfRegular s) (hr : 0 < r) (hrs : r ≤ s) :
    H.supportRatioNN ≤
      (H.trimRightDegree H.supportRight r
        (fun b hb ↦ hrs.trans_eq (hH.2 b hb).symm)).supportRatioNN := by
  let hdeg : ∀ b ∈ H.supportRight, r ≤ H.rightDegree b :=
    fun b hb ↦ hrs.trans_eq (hH.2 b hb).symm
  let K := H.trimRightDegree H.supportRight r hdeg
  have hsuppR : K.supportRight = H.supportRight :=
    H.supportRight_trimRightDegree H.supportRight r hdeg hr
  have hsuppL : K.supportLeft ⊆ H.supportLeft :=
    supportLeft_mono (H.trimRightDegree_le H.supportRight r hdeg)
  rw [supportRatioNN, supportRatioNN, hsuppR]
  have hden : (K.supportLeft.card : NNRat) ≤ H.supportLeft.card := by
    exact_mod_cast Finset.card_le_card hsuppL
  have hdenpos : 0 < (K.supportLeft.card : NNRat) := by
    exact_mod_cast (supportLeft_nonempty_of_isHalfRegular
      (isHalfRegular_trimRightDegree hH hr hrs) hr).card_pos
  gcongr

/-- Decreasing the prescribed right degree can only increase the optimal
support ratio. -/
theorem maxSupportRatio_antitone_degree {G : BipartiteGraph A B} {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s) :
    G.maxSupportRatio s ≤ G.maxSupportRatio r := by
  classical
  apply Finset.sup_le
  intro H hHmem
  have hH := (G.mem_halfRegularSubgraphs H s).mp hHmem
  let hdeg : ∀ b ∈ H.supportRight, r ≤ H.rightDegree b :=
    fun b hb ↦ hrs.trans_eq (hH.2.2 b hb).symm
  let K := H.trimRightDegree H.supportRight r hdeg
  calc
    H.supportRatioNN ≤ K.supportRatioNN :=
      supportRatioNN_le_trimRightDegree hH.2 hr hrs
    _ ≤ G.maxSupportRatio r := supportRatioNN_le_maxSupportRatio
      (le_trans (H.trimRightDegree_le H.supportRight r hdeg) hH.1)
      (isHalfRegular_trimRightDegree hH.2 hr hrs)

theorem support_card_cross_bound_of_one_halfRegular
    {G H : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {L δ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ) (hHG : H ≤ G)
    (hH : H.IsHalfRegular 1) :
    H.supportRight.card * A₀.card ≤
      L * δ * B₀.card * H.supportLeft.card := by
  rcases hG with ⟨hs, _hA, _hB, hreg, _hdens, hmax⟩
  have hedgeG : G.edgeCount = B₀.card * δ :=
    edgeCount_eq_card_mul_of_rightRegularOn hs hreg
  have hpoint : ∀ a ∈ H.supportLeft,
      H.leftDegree a * A₀.card ≤ L * (B₀.card * δ) := by
    intro a ha
    have haG : a ∈ G.supportLeft := supportLeft_mono hHG ha
    have haA : a ∈ A₀ := supportLeft_subset_of_supportedOn hs haG
    calc
      H.leftDegree a * A₀.card ≤ G.leftDegree a * A₀.card := by
        gcongr
        exact leftDegree_mono hHG a
      _ ≤ L * G.edgeCount := hmax a haA
      _ = L * (B₀.card * δ) := by rw [hedgeG]
  have hsum :
      ∑ a ∈ H.supportLeft, H.leftDegree a * A₀.card ≤
        ∑ _a ∈ H.supportLeft, L * (B₀.card * δ) :=
    Finset.sum_le_sum fun a (ha : a ∈ H.supportLeft) ↦ hpoint a ha
  have hedgeH : H.edgeCount = H.supportRight.card := by
    simpa using edgeCount_eq_card_supportRight_mul_of_isHalfRegular hH
  rw [← Finset.sum_mul, ← H.edgeCount_eq_sum_supportLeft, hedgeH] at hsum
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

theorem maxSupportRatio_one_le_displayed_bound
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {L δ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ) :
    G.maxSupportRatio 1 ≤
      (L * δ : NNRat) * ((B₀.card : NNRat) / (A₀.card : NNRat)) := by
  classical
  apply Finset.sup_le
  intro H hHmem
  have hH := (G.mem_halfRegularSubgraphs H 1).mp hHmem
  have hcross := support_card_cross_bound_of_one_halfRegular hG hH.1 hH.2
  have hdenH : 0 < (H.supportLeft.card : NNRat) := by
    exact_mod_cast (supportLeft_nonempty_of_isHalfRegular hH.2 (by omega)).card_pos
  have hdenA : 0 < (A₀.card : NNRat) := by
    exact_mod_cast hG.2.1.card_pos
  rw [supportRatioNN, ← mul_div_assoc]
  apply (div_le_div_iff₀ hdenH hdenA).2
  exact_mod_cast hcross

theorem displayedRatio_le_maxSupportRatio
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {L δ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ) (hδ : 0 < δ) :
    (B₀.card : NNRat) / (A₀.card : NNRat) ≤ G.maxSupportRatio δ := by
  have hhalf : G.IsHalfRegular δ :=
    isHalfRegular_of_supportedOn_isRightRegularOn hG.1 hG.2.2.1 hG.2.2.2.1 hδ
  have hsuppR : G.supportRight = B₀ :=
    supportRight_eq_of_supportedOn_isRightRegularOn hG.1 hG.2.2.2.1 hδ
  have hsuppL : G.supportLeft ⊆ A₀ := supportLeft_subset_of_supportedOn hG.1
  calc
    (B₀.card : NNRat) / A₀.card ≤
        (G.supportRight.card : NNRat) / G.supportLeft.card := by
      rw [hsuppR]
      have hden : (G.supportLeft.card : NNRat) ≤ A₀.card := by
        exact_mod_cast Finset.card_le_card hsuppL
      have hpos : 0 < (G.supportLeft.card : NNRat) := by
        exact_mod_cast (supportLeft_nonempty_of_isHalfRegular hhalf hδ).card_pos
      gcongr
    _ = G.supportRatioNN := by rfl
    _ ≤ G.maxSupportRatio δ := supportRatioNN_le_maxSupportRatio le_rfl hhalf

theorem maxSupportRatio_endpoint_bound
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {L δ : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L δ) (hδ : 0 < δ) :
    G.maxSupportRatio 1 ≤ (L * δ : NNRat) * G.maxSupportRatio δ := by
  calc
    G.maxSupportRatio 1 ≤
        (L * δ : NNRat) * ((B₀.card : NNRat) / (A₀.card : NNRat)) :=
      maxSupportRatio_one_le_displayed_bound hG
    _ ≤ (L * δ : NNRat) * G.maxSupportRatio δ := by
      gcongr
      exact displayedRatio_le_maxSupportRatio hG hδ

/-- A roof chooses one incident edge above every right vertex. -/
structure Roof (G : BipartiteGraph A B) where
  choice : B → A
  adj_choice : ∀ b, G.Adj (choice b) b

/-- The load placed by a roof on a left vertex. -/
noncomputable def Roof.load {G : BipartiteGraph A B} (R : G.Roof) (a : A) : ℕ :=
  by classical exact (Finset.univ.filter fun b ↦ R.choice b = a).card

/-- A roof of maximum load at most `q`. -/
def HasRoofLoadAtMost (G : BipartiteGraph A B) (q : ℕ) : Prop :=
  ∃ R : G.Roof, ∀ a, R.load a ≤ q

theorem card_le_mul_card_neighborhood_of_roof {G : BipartiteGraph A B} {q : ℕ}
    (h : G.HasRoofLoadAtMost q) (X : Finset B) :
    X.card ≤ q * (G.neighborhood X).card := by
  classical
  obtain ⟨R, hR⟩ := h
  calc
    X.card = ∑ a ∈ G.neighborhood X, (X.filter fun b ↦ R.choice b = a).card := by
      rw [← card_biUnion]
      · congr 1
        ext b
        simp only [mem_biUnion, mem_neighborhood, mem_filter]
        constructor
        · intro hb
          exact ⟨R.choice b, ⟨b, hb, R.adj_choice b⟩, hb, rfl⟩
        · rintro ⟨a, _, hb, _⟩
          exact hb
      · intro a _ a' _ haa'
        show Disjoint (X.filter fun b ↦ R.choice b = a)
          (X.filter fun b ↦ R.choice b = a')
        rw [Finset.disjoint_left]
        intro b hb hb'
        exact haa' ((mem_filter.mp hb).2.symm.trans (mem_filter.mp hb').2)
    _ ≤ ∑ _a ∈ G.neighborhood X, q := by
      gcongr with a ha
      exact (card_le_card (filter_subset_filter _ (Finset.subset_univ X))).trans (by
        simpa [Roof.load] using hR a)
    _ = q * (G.neighborhood X).card := by simp [Nat.mul_comm]

/-- Hall's theorem in the cloned left part: the neighborhood inequalities are
exactly the criterion for a roof with load at most `q`. -/
theorem hasRoofLoadAtMost_iff (G : BipartiteGraph A B) (q : ℕ) :
    G.HasRoofLoadAtMost q ↔
      ∀ X : Finset B, X.card ≤ q * (G.neighborhood X).card := by
  classical
  constructor
  · intro h X
    exact card_le_mul_card_neighborhood_of_roof h X
  · intro h
    let t : B → Finset (A × Fin q) := fun b ↦
      (G.leftNeighbors b).product Finset.univ
    have hHall : ∀ X : Finset B, X.card ≤ (X.biUnion t).card := by
      intro X
      calc
        X.card ≤ q * (G.neighborhood X).card := h X
        _ = (X.biUnion t).card := by
          have heq : X.biUnion t = (G.neighborhood X).product Finset.univ := by
            ext z
            simp [t, neighborhood]
          rw [heq]
          simp [Finset.card_product, Nat.mul_comm]
    obtain ⟨f, hf_inj, hf_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
    let R : G.Roof :=
      { choice := fun b ↦ (f b).1
        adj_choice := fun b ↦ by
          have := hf_mem b
          simpa [t] using this }
    refine ⟨R, fun a ↦ ?_⟩
    let e : (Finset.univ.filter fun b ↦ R.choice b = a) ↪ Fin q :=
      { toFun := fun b ↦ (f b).2
        inj' := by
          intro b b' heq
          apply Subtype.ext
          apply hf_inj
          apply Prod.ext
          · exact (mem_filter.mp b.property).2.trans (mem_filter.mp b'.property).2.symm
          · exact heq }
    change (Finset.univ.filter fun b ↦ R.choice b = a).card ≤ q
    rw [← Fintype.card_coe]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective

/-! ## The block-pigeonhole step in PRS extraction -/

private lemma exists_adjacent_le_three_of_endpoint
    (b : ℕ → ℚ) (n t : ℕ) (_hn : 0 < n) (hb0 : 0 < b 0)
    (hpow : (2 : ℚ) ^ t < (3 : ℚ) ^ n)
    (hend : b n ≤ (2 : ℚ) ^ t * b 0) :
    ∃ j < n, b (j + 1) ≤ 3 * b j := by
  by_contra! hbad
  have hgrowth : ∀ k ≤ n, (3 : ℚ) ^ k * b 0 ≤ b k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          (3 : ℚ) ^ (k + 1) * b 0 = 3 * ((3 : ℚ) ^ k * b 0) := by ring
          _ ≤ 3 * b k := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
          _ ≤ b (k + 1) := (hbad k (by omega)).le
  have hstrict : (2 : ℚ) ^ t * b 0 < (3 : ℚ) ^ n * b 0 :=
    mul_lt_mul_of_pos_right hpow hb0
  exact (not_lt_of_ge hend) (hstrict.trans_le (hgrowth n le_rfl))

private lemma two_pow_lt_three_pow_pred (t : ℕ) (ht : 3 ≤ t) :
    (2 : ℚ) ^ t < (3 : ℚ) ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [show t + 1 - 1 = t by omega]
      calc
        (2 : ℚ) ^ (t + 1) = 2 ^ t * 2 := by rw [pow_succ]
        _ < 3 ^ (t - 1) * 2 := mul_lt_mul_of_pos_right ih (by norm_num)
        _ < 3 ^ (t - 1) * 3 :=
          mul_lt_mul_of_pos_left (by norm_num) (pow_pos (by norm_num) _)
        _ = 3 ^ ((t - 1) + 1) := (pow_succ (3 : ℚ) (t - 1)).symm
        _ = 3 ^ t := by rw [Nat.sub_add_cancel (by omega)]

/-- The exact integer-endpoint pigeonhole used in JS Lemma 3.6.

For `q_j = j(d-1)`, one of the usable consecutive ratios is at most
three.  When `(d-1) ∣ δ` there are only `t-1` usable ratios, which is why
the proof uses `2^t < 3^(t-1)`.
-/
theorem exists_controlled_block
    (a : ℕ → ℚ) (δ d t : ℕ)
    (hd : 2 ≤ d) (ht_def : t = δ / (d - 1)) (ht : 3 ≤ t)
    (hpos : ∀ i < δ, 0 < a i) (hmono : Monotone a)
    (hend : a (δ - 1) ≤ (2 : ℚ) ^ t * a 0) :
    ∃ j, (j + 1) * (d - 1) ≤ δ - 1 ∧
      a ((j + 1) * (d - 1)) ≤ 3 * a (j * (d - 1)) := by
  have hstep : 0 < d - 1 := by omega
  have hδ : 0 < δ := by
    by_contra h
    have hzero : δ = 0 := Nat.eq_zero_of_not_pos h
    subst δ
    simp at ht_def
    omega
  have ha0 : 0 < a 0 := hpos 0 hδ
  by_cases hdiv : δ = t * (d - 1)
  · have hn : 0 < t - 1 := by omega
    have hlast : (t - 1) * (d - 1) ≤ δ - 1 := by
      have hsum : (t - 1) * (d - 1) + (d - 1) = δ := by
        calc
          (t - 1) * (d - 1) + (d - 1) = ((t - 1) + 1) * (d - 1) := by
            rw [Nat.add_mul, one_mul]
          _ = t * (d - 1) := by congr 1; omega
          _ = δ := hdiv.symm
      omega
    have hchain_end : a ((t - 1) * (d - 1)) ≤ (2 : ℚ) ^ t * a 0 :=
      (hmono hlast).trans hend
    obtain ⟨j, hj, hratio⟩ := exists_adjacent_le_three_of_endpoint
      (fun j ↦ a (j * (d - 1))) (t - 1) t hn (by simpa using ha0)
      (two_pow_lt_three_pow_pred t ht) (by simpa using hchain_end)
    refine ⟨j, ?_, ?_⟩
    · have hindex : (j + 1) * (d - 1) ≤ (t - 1) * (d - 1) := by
        gcongr
        omega
      exact hindex.trans hlast
    · simpa using hratio
  · have hquot : t * (d - 1) ≤ δ := by
      rw [ht_def]
      exact Nat.div_mul_le_self δ (d - 1)
    have hlast : t * (d - 1) ≤ δ - 1 := by omega
    have hchain_end : a (t * (d - 1)) ≤ (2 : ℚ) ^ t * a 0 :=
      (hmono hlast).trans hend
    have hpow : (2 : ℚ) ^ t < (3 : ℚ) ^ t :=
      pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    obtain ⟨j, hj, hratio⟩ := exists_adjacent_le_three_of_endpoint
      (fun j ↦ a (j * (d - 1))) t t (by omega) (by simpa using ha0) hpow
      (by simpa using hchain_end)
    refine ⟨j, ?_, ?_⟩
    · have hindex : (j + 1) * (d - 1) ≤ t * (d - 1) := by
        gcongr
        omega
      exact hindex.trans hlast
    · simpa using hratio

end BipartiteGraph
end Erdos182
/-
variable {A B : Type*} [Fintype A] [Fintype B]

private theorem supportRatioNN_eq_supportRatio (G : BipartiteGraph A B) :
    (G.supportRatioNN : ℚ) = G.supportRatio := by
  rfl

private theorem maxSupportRatio_pos {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    0 < G.maxSupportRatio r := by
  let hdeg : ∀ b ∈ G.supportRight, r ≤ G.rightDegree b :=
    fun b hb => hrδ.trans_eq (hG.2 b hb).symm
  let H := G.trimRightDegree G.supportRight r hdeg
  have hHreg : H.IsHalfRegular r := isHalfRegular_trimRightDegree hG hr hrδ
  have hHle : H ≤ G := G.trimRightDegree_le G.supportRight r hdeg
  exact (supportRatio_pos_of_isHalfRegular hHreg hr :
    0 < (H.supportRatioNN : ℚ)).trans_le (by
      exact_mod_cast supportRatioNN_le_maxSupportRatio hHle hHreg)

private theorem maxSupportRatio_clipped_monotone (G : BipartiteGraph A B)
    (δ : ℕ) (hδ : 0 < δ) :
    Monotone (fun i => G.maxSupportRatio (δ - min i (δ - 1))) := by
  intro i j hij
  apply maxSupportRatio_antitone_degree
  · omega
  · omega

private def restrictRightType (G : BipartiteGraph A B) (S : Finset B) :
    BipartiteGraph A S where
  Adj a b := G.Adj a b.1

private def extendRightType {S : Finset B} (H : BipartiteGraph A S) :
    BipartiteGraph A B where
  Adj a b := ∃ hb : b ∈ S, H.Adj a ⟨b, hb⟩

private def subtypeEmbedding (S : Finset B) : S ↪ B :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] private theorem rightDegree_restrictRightType
    (G : BipartiteGraph A B) (S : Finset B) (b : S) :
    (restrictRightType G S).rightDegree b = G.rightDegree b.1 := by
  simp [rightDegree, leftNeighbors, restrictRightType]
  rfl

private theorem extendRightType_le {G : BipartiteGraph A B} {S : Finset B}
    {H : BipartiteGraph A S} (hH : H ≤ restrictRightType G S) :
    extendRightType H ≤ G := by
  intro a b hab
  obtain ⟨hb, hab⟩ := hab
  exact hH hab

private theorem leftNeighbors_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (b : B) :
    (extendRightType H).leftNeighbors b =
      if hb : b ∈ S then H.leftNeighbors ⟨b, hb⟩ else ∅ := by
  classical
  ext a
  by_cases hb : b ∈ S
  · rw [dif_pos hb]
    simp only [mem_leftNeighbors, extendRightType]
    constructor
    · rintro ⟨hb', ha⟩
      simpa only [Subsingleton.elim hb' hb] using ha
    · intro ha
      exact ⟨hb, ha⟩
  · rw [dif_neg hb]
    simp only [mem_leftNeighbors, extendRightType, not_false_eq_true, Finset.notMem_empty]
    constructor
    · rintro ⟨hb', _⟩
      exact (hb hb').elim
    · intro h
      exact h.elim

private theorem rightDegree_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (b : B) :
    (extendRightType H).rightDegree b =
      if hb : b ∈ S then H.rightDegree ⟨b, hb⟩ else 0 := by
  rw [rightDegree, leftNeighbors_extendRightType]
  split <;> simp [rightDegree]

private theorem rightNeighbors_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (a : A) :
    (extendRightType H).rightNeighbors a =
      (H.rightNeighbors a).map (subtypeEmbedding S) := by
  classical
  ext b
  simp only [mem_rightNeighbors, extendRightType, Finset.mem_map]
  constructor
  · rintro ⟨hb, hab⟩
    exact ⟨⟨b, hb⟩, by simpa using hab, rfl⟩
  · rintro ⟨⟨b', hbmem⟩, hb', rfl⟩
    exact ⟨hbmem, hb'⟩

@[simp] private theorem leftDegree_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (a : A) :
    (extendRightType H).leftDegree a = H.leftDegree a := by
  rw [leftDegree, rightNeighbors_extendRightType, Finset.card_map]
  rfl

private theorem supportLeft_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportLeft = H.supportLeft := by
  ext a
  simp [mem_supportLeft]

private theorem supportRight_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportRight =
      H.supportRight.map (subtypeEmbedding S) := by
  classical
  ext b
  by_cases hb : b ∈ S
  · simp only [mem_supportRight, rightDegree_extendRightType, hb, dite_true,
      Finset.mem_map]
    constructor
    · intro hpos
      exact ⟨⟨b, hb⟩, by simpa [mem_supportRight] using hpos, rfl⟩
    · rintro ⟨b', hb', heq⟩
      have hsub : b' = ⟨b, hb⟩ := Subtype.ext heq
      rw [← hsub]
      simpa [mem_supportRight] using hb'
  · simp only [mem_supportRight, rightDegree_extendRightType, hb, dite_false,
      Finset.mem_map]
    constructor
    · omega
    · rintro ⟨b', _, heq⟩
      exact (hb (heq ▸ b'.property)).elim

private theorem supportRatioNN_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportRatioNN = H.supportRatioNN := by
  rw [supportRatioNN, supportRatioNN, supportLeft_extendRightType,
    supportRight_extendRightType, Finset.card_map]

private theorem restrictRightType_le {G K : BipartiteGraph A B} {S : Finset B}
    (hKG : K ≤ G) : restrictRightType K S ≤ restrictRightType G S := by
  intro a b hab
  exact hKG hab

private theorem extend_restrict_supportRight (G : BipartiteGraph A B) :
    extendRightType (restrictRightType G G.supportRight) = G := by
  ext a b
  constructor
  · rintro ⟨_, hab⟩
    exact hab
  · intro hab
    exact ⟨G.adj_mem_supportRight hab, hab⟩

private theorem extendRightType_mono {S : Finset B}
    {H K : BipartiteGraph A S} (hHK : H ≤ K) :
    extendRightType H ≤ extendRightType K := by
  intro a b hab
  obtain ⟨hb, hab⟩ := hab
  exact ⟨hb, hHK hab⟩

private theorem isHalfRegular_extendRightType {S : Finset B}
    {H : BipartiteGraph A S} {r : ℕ} (hH : H.IsHalfRegular r) :
    (extendRightType H).IsHalfRegular r := by
  rw [IsHalfRegular, supportRight_extendRightType]
  constructor
  · obtain ⟨b, hb⟩ := hH.1
    exact ⟨subtypeEmbedding S b, Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  · intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    rw [rightDegree_extendRightType]
    split
    · rename_i hmem
      have heq : (⟨(subtypeEmbedding S) b', hmem⟩ : S) = b' := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact hH.2 b' hb'
    · rename_i hnot
      exact (hnot b'.property).elim

private def Roof.graph {G : BipartiteGraph A B} (R : G.Roof) :
    BipartiteGraph A B where
  Adj a b := R.choice b = a

@[simp] private theorem Roof.graph_adj {G : BipartiteGraph A B}
    (R : G.Roof) (a : A) (b : B) :
    R.graph.Adj a b ↔ R.choice b = a := Iff.rfl

private theorem Roof.graph_le {G : BipartiteGraph A B} (R : G.Roof) :
    R.graph ≤ G := by
  intro a b hab
  rw [← hab]
  exact R.adj_choice b

@[simp] private theorem Roof.rightDegree_graph {G : BipartiteGraph A B}
    (R : G.Roof) (b : B) : R.graph.rightDegree b = 1 := by
  classical
  rw [rightDegree]
  have heq : R.graph.leftNeighbors b = {R.choice b} := by
    ext a
    simp [leftNeighbors, eq_comm]
  simp [heq]

@[simp] private theorem Roof.leftDegree_graph {G : BipartiteGraph A B}
    (R : G.Roof) (a : A) : R.graph.leftDegree a = R.load a := by
  classical
  simp [leftDegree, rightNeighbors, Roof.load, Roof.graph, eq_comm]

@[simp] private theorem rightDegree_sdiff_roof {G : BipartiteGraph A B}
    (R : G.Roof) (b : B) : (G \ R.graph).rightDegree b = G.rightDegree b - 1 := by
  classical
  have heq :
      Finset.univ.filter (fun a => G.Adj a b ∧ ¬R.choice b = a) =
        (G.leftNeighbors b).erase (R.choice b) := by
    ext a
    simp [leftNeighbors, eq_comm, and_comm]
  simp only [rightDegree, leftNeighbors, sdiff_adj, Roof.graph_adj]
  rw [heq, card_erase_of_mem
    ((mem_leftNeighbors G (R.choice b) b).mpr (R.adj_choice b))]
  congr 2

private theorem sdiff_roof_le {G : BipartiteGraph A B} (R : G.Roof) :
    G \ R.graph ≤ G := by
  intro a b hab
  exact hab.1

private theorem rightDegree_sup_roof_of_le_sdiff {G H : BipartiteGraph A B}
    (R : G.Roof) (hH : H ≤ G \ R.graph) (b : B) :
    (R.graph ⊔ H).rightDegree b = H.rightDegree b + 1 := by
  classical
  have hnot : R.choice b ∉ H.leftNeighbors b := by
    intro hb
    have hh := hH ((mem_leftNeighbors H (R.choice b) b).mp hb)
    exact hh.2 rfl
  rw [rightDegree]
  have heq : (R.graph ⊔ H).leftNeighbors b =
      insert (R.choice b) (H.leftNeighbors b) := by
    ext a
    simp [leftNeighbors, Roof.graph, eq_comm]
  rw [heq, card_insert_of_notMem hnot]
  rfl

private theorem leftDegree_sup_roof_le {G H : BipartiteGraph A B}
    (R : G.Roof) (a : A) :
    (R.graph ⊔ H).leftDegree a ≤ R.load a + H.leftDegree a := by
  classical
  rw [leftDegree]
  have hsub : (R.graph ⊔ H).rightNeighbors a ⊆
      R.graph.rightNeighbors a ∪ H.rightNeighbors a := by
    intro b hb
    simpa [rightNeighbors] using hb
  calc
    ((R.graph ⊔ H).rightNeighbors a).card ≤
        (R.graph.rightNeighbors a ∪ H.rightNeighbors a).card := card_le_card hsub
    _ ≤ (R.graph.rightNeighbors a).card + (H.rightNeighbors a).card := card_union_le _ _
    _ = R.load a + H.leftDegree a := by
      rw [← Roof.leftDegree_graph]
      rfl

private theorem exists_regular_of_bounded_roofs (G : BipartiteGraph A B)
    (r d q : ℕ) (hreg : ∀ b, G.rightDegree b = r + d)
    (hroof : ∀ (K : BipartiteGraph A B), K ≤ G → ∀ s,
      r + 1 ≤ s → (∀ b, K.rightDegree b = s) → K.HasRoofLoadAtMost q) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧ ∀ a, H.leftDegree a ≤ d * q := by
  induction d generalizing G with
  | zero =>
      refine ⟨⊥, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim
      · intro b
        simp [rightDegree, leftNeighbors]
      · intro a
        simp [leftDegree, rightNeighbors]
  | succ d ih =>
      have hdegmin : r + 1 ≤ r + (d + 1) := by omega
      obtain ⟨R, hRload⟩ := hroof G le_rfl (r + (d + 1)) hdegmin (by
        intro b
        simpa [Nat.add_assoc] using hreg b)
      let K : BipartiteGraph A B := G \ R.graph
      have hKle : K ≤ G := sdiff_roof_le R
      have hKreg : ∀ b, K.rightDegree b = r + d := by
        intro b
        rw [show K.rightDegree b = G.rightDegree b - 1 by
          simp [K, rightDegree_sdiff_roof], hreg b]
        omega
      have hKroof : ∀ (J : BipartiteGraph A B), J ≤ K → ∀ s,
          r + 1 ≤ s → (∀ b, J.rightDegree b = s) → J.HasRoofLoadAtMost q := by
        intro J hJK s hrs hJreg
        exact hroof J (hJK.trans hKle) s hrs hJreg
      obtain ⟨H, hHK, hHreg, hHmax⟩ := ih K hKreg hKroof
      refine ⟨R.graph ⊔ H, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim (fun h => R.graph_le h) (fun h => hKle (hHK h))
      · intro b
        rw [rightDegree_sup_roof_of_le_sdiff R hHK b, hHreg b]
      · intro a
        calc
          (R.graph ⊔ H).leftDegree a ≤ R.load a + H.leftDegree a :=
            leftDegree_sup_roof_le R a
          _ ≤ q + d * q := Nat.add_le_add (hRload a) (hHmax a)
          _ = (d + 1) * q := by ring

private theorem hasRoofLoadAtMost_ceil_maxSupportRatio
    {G : BipartiteGraph A B} {S : Finset B} {K : BipartiteGraph A S}
    {r s : ℕ} (hKG : extendRightType K ≤ G) (hr : 0 < r) (hrs : r ≤ s)
    (hs : 0 < s) (hreg : ∀ b, K.rightDegree b = s) :
    K.HasRoofLoadAtMost (Nat.ceil (G.maxSupportRatio r)) := by
  classical
  rw [hasRoofLoadAtMost_iff]
  intro X
  by_cases hX : X.Nonempty
  · let J := K.restrictRight X
    have hJR : J.supportRight = X := by
      apply supportRight_restrictRight
      intro b hb
      rw [hreg b]
      exact hs
    have hJL : J.supportLeft = K.neighborhood X := supportLeft_restrictRight K X
    have hJhalf : J.IsHalfRegular s := by
      constructor
      · rw [hJR]
        exact hX
      · intro b hb
        rw [hJR] at hb
        rw [rightDegree_restrictRight_of_mem K hb, hreg b]
    have hJG : extendRightType J ≤ G :=
      (extendRightType_mono (restrictRight_le K X)).trans hKG
    have hratio : (extendRightType J).supportRatioNN ≤ G.maxSupportRatio r :=
      (supportRatioNN_le_maxSupportRatio hJG (isHalfRegular_extendRightType hJhalf)).trans
        (maxSupportRatio_antitone_degree hr hrs)
    have hratio_eq : (extendRightType J).supportRatioNN =
        (X.card : NNRat) / (K.neighborhood X).card := by
      rw [supportRatioNN_extendRightType, supportRatioNN, hJR, hJL]
    have hNpos : 0 < (K.neighborhood X).card := by
      rw [← hJL]
      exact (supportLeft_nonempty_of_isHalfRegular hJhalf hs).card_pos
    have hfrac : (X.card : NNRat) / (K.neighborhood X).card ≤
        (Nat.ceil (G.maxSupportRatio r) : NNRat) := by
      rw [← hratio_eq]
      exact hratio.trans (Nat.le_ceil _)
    rw [div_le_iff₀ (by exact_mod_cast hNpos)] at hfrac
    exact_mod_cast hfrac
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hX, Finset.card_empty, zero_le]

private theorem exists_four_almostBiregular_of_small_quotient
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {L δ d : ℕ} (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1)))
    (ht : δ / (d - 1) ≤ 2) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  classical
  obtain ⟨hs, hA, hB, hr, hdense, hmax⟩ := hG
  have hδ : 0 < δ := by omega
  let hdeg : ∀ b ∈ B₀, d ≤ G.rightDegree b :=
    fun b hb => hdδ.trans_eq (hr b hb).symm
  let H := G.trimRightDegree B₀ d hdeg
  have hHG : H ≤ G := G.trimRightDegree_le B₀ d hdeg
  have hHs : H.SupportedOn A₀ B₀ := by
    intro a b hab
    exact hs (hHG hab)
  have hHr : H.IsRightRegularOn B₀ d := by
    intro b hb
    exact G.rightDegree_trimRightDegree_of_mem B₀ d hdeg hb
  have hedgeG : G.edgeCount = B₀.card * δ :=
    edgeCount_eq_card_mul_of_rightRegularOn hs hr
  have hedgeH : H.edgeCount = B₀.card * d :=
    edgeCount_eq_card_mul_of_rightRegularOn hHs hHr
  have hAB : A₀.card ≤ B₀.card := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_comm, hedgeG] using hdense) hδ
  have hpow4 : 2 ^ (δ / (d - 1)) ≤ 4 := by
    interval_cases δ / (d - 1) <;> norm_num
  refine ⟨H, A₀, B₀, hHG, hHs, hA, hB, hHr, ?_, ?_⟩
  · rw [hedgeH]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hAB
  · intro a ha
    calc
      H.leftDegree a * A₀.card ≤ G.leftDegree a * A₀.card := by
        gcongr
        exact leftDegree_mono hHG a
      _ ≤ L * G.edgeCount := hmax a ha
      _ = (L * δ) * B₀.card := by rw [hedgeG]; ring
      _ ≤ (2 ^ (δ / (d - 1))) * B₀.card := Nat.mul_le_mul_right _ hscale
      _ ≤ 4 * B₀.card := Nat.mul_le_mul_right _ hpow4
      _ ≤ 4 * (B₀.card * d) := by
        gcongr
        simpa using Nat.mul_le_mul_left B₀.card (show 1 ≤ d by omega)
      _ = 4 * H.edgeCount := by rw [hedgeH]

private theorem exists_eq_maxSupportRatio {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ∃ K : BipartiteGraph A B, K ≤ G ∧ K.IsHalfRegular r ∧
      K.supportRatioNN = G.maxSupportRatio r := by
  classical
  obtain ⟨K, hKmem, hKmax⟩ := exists_maximal_halfRegular hG hr hrδ
  obtain ⟨hKG, hKhalf⟩ := (G.mem_halfRegularSubgraphs K r).mp hKmem
  have hupper : G.maxSupportRatio r ≤ K.supportRatioNN := by
    apply Finset.sup_le
    intro J hJmem
    have hj := hKmax J hJmem
    have hjq : (J.supportRatioNN : ℚ) ≤ (K.supportRatioNN : ℚ) := by
      simpa only [supportRatioNN_eq_supportRatio] using hj
    exact_mod_cast hjq
  exact ⟨K, hKG, hKhalf,
    le_antisymm (supportRatioNN_le_maxSupportRatio hKG hKhalf) hupper⟩

private theorem ceil_le_four_of_le_three {x y : NNRat}
    (hy : 1 ≤ y) (hxy : x ≤ 3 * y) : (Nat.ceil x : NNRat) ≤ 4 * y := by
  calc
    (Nat.ceil x : NNRat) ≤ x + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ x by positivity)).le
    _ ≤ 3 * y + 1 := by simpa [add_comm] using add_le_add_right hxy 1
    _ ≤ 3 * y + y := by
      simpa [add_comm] using add_le_add_left hy (3 * y)
    _ = 4 * y := by ring

private theorem exists_four_almostBiregular_of_large_quotient
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (L δ d : ℕ) (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1)))
    (htlarge : 3 ≤ δ / (d - 1)) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  classical
  let t := δ / (d - 1)
  have ht3 : 3 ≤ t := by simpa [t] using htlarge
  have hδ : 0 < δ := by omega
  have hhalf : G.IsHalfRegular δ :=
    isHalfRegular_of_supportedOn_isRightRegularOn hG.1 hG.2.2.1 hG.2.2.2.1 hδ
  let a : ℕ → ℚ := fun i =>
    (G.maxSupportRatio (δ - min i (δ - 1)) : ℚ)
  have hapos : ∀ i < δ, 0 < a i := by
    intro i hi
    have hp := maxSupportRatio_pos hhalf (show 0 < δ - min i (δ - 1) by omega)
      (show δ - min i (δ - 1) ≤ δ by omega)
    exact_mod_cast hp
  have hamono : Monotone a := by
    intro i j hij
    exact_mod_cast maxSupportRatio_clipped_monotone G δ hδ hij
  have haend : a (δ - 1) ≤ (2 : ℚ) ^ t * a 0 := by
    have hendNN := maxSupportRatio_endpoint_bound hG hδ
    have hendQ : (G.maxSupportRatio 1 : ℚ) ≤
        (L * δ : ℚ) * (G.maxSupportRatio δ : ℚ) := by
      exact_mod_cast hendNN
    have hscaleQ : (L * δ : ℚ) ≤ (2 : ℚ) ^ t := by
      exact_mod_cast (show L * δ ≤ 2 ^ t by simpa [t] using hscale)
    have hmain : (G.maxSupportRatio 1 : ℚ) ≤
        (2 : ℚ) ^ t * (G.maxSupportRatio δ : ℚ) :=
      hendQ.trans (mul_le_mul_of_nonneg_right hscaleQ (by positivity))
    dsimp [a]
    rw [min_self, show δ - (δ - 1) = 1 by omega]
    simpa using hmain
  obtain ⟨j, hj, hjratio⟩ :=
    exists_controlled_block a δ d t hd rfl ht3 hapos hamono haend
  let q₀ := j * (d - 1)
  let q₁ := (j + 1) * (d - 1)
  have hq₁ : q₁ ≤ δ - 1 := by simpa [q₁] using hj
  have hq₀ : q₀ ≤ δ - 1 := by
    have hq₀q₁ : q₀ ≤ q₁ := by
      dsimp [q₀, q₁]
      gcongr
      omega
    exact hq₀q₁.trans hq₁
  have hqeq : q₁ = q₀ + (d - 1) := by
    simp [q₀, q₁, Nat.add_mul]
  let s₀ := δ - q₀
  let r₀ := δ - q₀ - d
  have hs₀ : 0 < s₀ := by dsimp [s₀]; omega
  have hs₀δ : s₀ ≤ δ := Nat.sub_le _ _
  have hr₀ : 0 < r₀ + 1 := by omega
  have hrs : r₀ + d = s₀ := by dsimp [r₀, s₀]; omega
  have hrlevel : r₀ + 1 = δ - q₁ := by dsimp [r₀]; omega
  have hratio : (G.maxSupportRatio (δ - q₁) : ℚ) ≤
      3 * (G.maxSupportRatio (δ - q₀) : ℚ) := by
    simpa [a, q₀, q₁, Nat.min_eq_left hq₀, Nat.min_eq_left hq₁] using hjratio
  obtain ⟨K, hKG, hKhalf, hKratio⟩ :=
    exists_eq_maxSupportRatio hhalf hs₀ hs₀δ
  let S := K.supportRight
  let K' : BipartiteGraph A S := restrictRightType K S
  have hK'G : extendRightType K' ≤ G := by
    rw [show extendRightType K' = K by simpa [K', S] using extend_restrict_supportRight K]
    exact hKG
  have hK'reg : ∀ b, K'.rightDegree b = r₀ + d := by
    intro b
    rw [rightDegree_restrictRightType, hKhalf.2 b b.property, hrs]
  let q := Nat.ceil (G.maxSupportRatio (r₀ + 1))
  have hroof : ∀ (J : BipartiteGraph A S), J ≤ K' → ∀ s,
      r₀ + 1 ≤ s → (∀ b, J.rightDegree b = s) → J.HasRoofLoadAtMost q := by
    intro J hJK s hrs' hJreg
    apply hasRoofLoadAtMost_ceil_maxSupportRatio
        ((extendRightType_mono hJK).trans hK'G) hr₀ hrs' (by omega) hJreg
  obtain ⟨P, hPK, hPreg, hPmax⟩ :=
    exists_regular_of_bounded_roofs K' r₀ d q hK'reg hroof
  let H := extendRightType P
  have hHK : H ≤ K := by
    rw [← extend_restrict_supportRight K]
    exact extendRightType_mono hPK
  have hHG : H ≤ G := hHK.trans hKG
  have hHs : H.SupportedOn K.supportLeft K.supportRight := by
    intro x y hxy
    exact ⟨K.adj_mem_supportLeft (hHK hxy), K.adj_mem_supportRight (hHK hxy)⟩
  have hHr : H.IsRightRegularOn K.supportRight d := by
    intro b hb
    rw [rightDegree_extendRightType]
    split
    · rename_i hb'
      have heq : (⟨b, hb'⟩ : K.supportRight) = ⟨b, hb⟩ := Subtype.ext rfl
      rw [heq]
      exact hPreg ⟨b, hb⟩
    · contradiction
  have hBne : K.supportRight.Nonempty := hKhalf.1
  have hAne : K.supportLeft.Nonempty :=
    supportLeft_nonempty_of_isHalfRegular hKhalf hs₀
  have hedgeH : H.edgeCount = K.supportRight.card * d :=
    edgeCount_eq_card_mul_of_rightRegularOn hHs hHr
  have hedgeG : G.edgeCount = B₀.card * δ :=
    edgeCount_eq_card_mul_of_rightRegularOn hG.1 hG.2.2.2.1
  have hA₀B₀ : A₀.card ≤ B₀.card := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_comm, hedgeG] using hG.2.2.2.2.1) hδ
  have hdisplay : (1 : NNRat) ≤
      (B₀.card : NNRat) / (A₀.card : NNRat) := by
    rw [le_div_iff₀ (by exact_mod_cast hG.2.1.card_pos)]
    norm_num
    exact_mod_cast hA₀B₀
  have hone : (1 : NNRat) ≤ K.supportRatioNN := by
    calc
      (1 : NNRat) ≤ (B₀.card : NNRat) / (A₀.card : NNRat) := hdisplay
      _ ≤ G.maxSupportRatio δ := displayedRatio_le_maxSupportRatio hG hδ
      _ ≤ G.maxSupportRatio s₀ := maxSupportRatio_antitone_degree hs₀ hs₀δ
      _ = K.supportRatioNN := hKratio.symm
  have hAB : K.supportLeft.card ≤ K.supportRight.card := by
    rw [supportRatioNN] at hone
    have hcross := (le_div_iff₀ (by exact_mod_cast hAne.card_pos)).mp hone
    norm_num at hcross
    exact_mod_cast hcross
  have hratioNN : G.maxSupportRatio (r₀ + 1) ≤
      3 * K.supportRatioNN := by
    have hq : (G.maxSupportRatio (r₀ + 1) : ℚ) ≤
        3 * (K.supportRatioNN : ℚ) := by
      rw [hrlevel, hKratio]
      simpa [s₀] using hratio
    exact_mod_cast hq
  have hqbound : (q : NNRat) ≤ 4 * K.supportRatioNN := by
    exact ceil_le_four_of_le_three hone hratioNN
  have hqcross : q * K.supportLeft.card ≤ 4 * K.supportRight.card := by
    have hqNN : (q : NNRat) * K.supportLeft.card ≤
        4 * K.supportRight.card := by
      rw [supportRatioNN] at hqbound
      have hden : 0 < (K.supportLeft.card : NNRat) := by
        exact_mod_cast hAne.card_pos
      apply (le_div_iff₀ hden).mp
      simpa [mul_div_assoc] using hqbound
    exact_mod_cast hqNN
  refine ⟨H, K.supportLeft, K.supportRight, hHG,
    hHs, hAne, hBne, hHr, ?_, ?_⟩
  · rw [hedgeH]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hAB
  · intro x hx
    calc
      H.leftDegree x * K.supportLeft.card =
          P.leftDegree x * K.supportLeft.card := by
            rw [show H.leftDegree x = P.leftDegree x by simp [H]]
      _ ≤ (d * q) * K.supportLeft.card :=
        Nat.mul_le_mul_right _ (hPmax x)
      _ = d * (q * K.supportLeft.card) := by ring
      _ ≤ d * (4 * K.supportRight.card) := Nat.mul_le_mul_left d hqcross
      _ = 4 * (K.supportRight.card * d) := by ring
      _ = 4 * H.edgeCount := by rw [hedgeH]

/-- The roof extraction of Janzer--Sudakov Lemma 3.6. -/
theorem exists_four_almostBiregular_subgraph
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (L δ d : ℕ) (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1))) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  by_cases ht : δ / (d - 1) ≤ 2
  · exact exists_four_almostBiregular_of_small_quotient hG hd hdδ hscale ht
  · exact exists_four_almostBiregular_of_large_quotient G A₀ B₀ L δ d
      hG hd hdδ hscale (by omega)


end BipartiteGraph

end Erdos182
-/
