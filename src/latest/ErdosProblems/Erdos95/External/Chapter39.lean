/-
This file incorporates the finite sign-vector and Ky Fan infrastructure from
`xiangyazi24/proof_in_the_book` (commit `8ccc127c6c0109fa30ac61541420101376b24482`),
with small compatibility repairs for Lean/Mathlib v4.33.0.
-/

import Mathlib

/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and formalizes Matoušek's finite reduction from a too-small Kneser
coloring to a Tucker-labeling counterexample.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The remaining upstream gap is now the finite Ky Fan boundary-parity count,
formalized in two equivalent ways: `KyFanPrefixParityStatement` says that the
positive-first alternating signed-permutation prefix chains are odd, while
`KyFanPrefixModFourStatement` says that both orientations together have
cardinality `2 mod 4`.  This file proves the Matoušek construction from a
hypothetical `(n - 2*k + 1)`-coloring of `KG(n,k)` to a Tucker counterexample,
proves low-dimensional Tucker cases, packages them into an unconditional
low-dimensional Lovász theorem, proves the one-dimensional Ky Fan prefix-parity
count and the vacuous two-dimensional Ky Fan prefix-parity case, and proves
either Ky Fan parity frontier implies
`TuckerLemmaStatement → chapter39`.
-/

namespace ProofsInTheBook.Chapter39

/-- Vertices of the Kneser graph `KG(n,k)`: the `k`-subsets of `[n]`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance (n k : ℕ) : Fintype (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

instance (n k : ℕ) : DecidableEq (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

/-- The Kneser graph: vertices are `k`-subsets, adjacent when disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj a b := a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

theorem kneserGraph_adj_iff {n k : ℕ} (a b : KneserVertex n k) :
    (kneserGraph n k).Adj a b ↔
      a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n)) :=
  Iff.rfl

/-- Symmetry of Kneser adjacency, exposed as a named theorem
(`SimpleGraph.Adj.symm` already provides this generically). -/
theorem kneserGraph_adj_symm {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) : (kneserGraph n k).Adj b a :=
  h.symm

/-- Kneser adjacency is irreflexive: no vertex is adjacent to itself. -/
@[simp]
theorem kneserGraph_not_adj_self {n k : ℕ} (a : KneserVertex n k) :
    ¬ (kneserGraph n k).Adj a a := by
  intro h
  exact h.1 rfl

/-- An adjacency in `kneserGraph n k` forces the underlying subsets to be
disjoint (the constructive form of the second conjunct). -/
theorem disjoint_of_kneserGraph_adj {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) :
    Disjoint (a : Finset (Fin n)) (b : Finset (Fin n)) := h.2

/-- An adjacency in `kneserGraph n k` forces the two vertices to be distinct. -/
theorem ne_of_kneserGraph_adj {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) : a ≠ b := h.1

/--
Any coloring of a Kneser graph assigns different colors to disjoint
`k`-subsets.
-/
theorem kneser_coloring_separates_disjoint {n k q : ℕ}
    (C : (kneserGraph n k).Coloring (Fin q)) {a b : KneserVertex n k}
    (hne : a ≠ b) (hdisj : Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))) :
    C a ≠ C b := by
  exact C.valid ⟨hne, hdisj⟩

/--
The first finite-counting layer in the Kneser graph proof: `KG(n,k)` has
`n choose k` vertices.
-/
theorem kneserVertex_card (n k : ℕ) :
    Fintype.card (KneserVertex n k) = n.choose k := by
  rw [Fintype.card_subtype]
  have hset :
      ({s | s.card = k} : Finset (Finset (Fin n))) =
        Finset.powersetCard k Finset.univ := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The Kneser graph has at least one vertex when `k ≤ n`. -/
theorem kneserVertex_nonempty_of_le {n k : ℕ} (h : k ≤ n) :
    Nonempty (KneserVertex n k) := by
  rw [← Fintype.card_pos_iff, kneserVertex_card]
  exact Nat.choose_pos h

/-- The Kneser graph has no vertices when `k > n`. -/
theorem kneserGraph_no_vertices_of_lt {n k : ℕ} (h : n < k) :
    IsEmpty (KneserVertex n k) := by
  rw [← Fintype.card_eq_zero_iff, kneserVertex_card]
  exact Nat.choose_eq_zero_of_lt h

/-- The Kneser graph has no edges when `2k > n` (no two disjoint k-subsets fit). -/
theorem kneserGraph_no_adj_of_lt {n k : ℕ} (_hk : 1 ≤ k) (h : n < 2 * k)
    (a b : KneserVertex n k) :
    ¬ (kneserGraph n k).Adj a b := by
  intro ⟨_, hdisj⟩
  have hcard : (↑a ∪ ↑b : Finset (Fin n)).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hdisj, a.2, b.2, two_mul]
  have hle : (↑a ∪ ↑b : Finset (Fin n)).card ≤ Fintype.card (Fin n) :=
    (↑a ∪ ↑b : Finset (Fin n)).card_le_univ
  rw [Fintype.card_fin] at hle
  omega

/-- For `k = 0`, the Kneser graph has exactly one vertex (the empty set). -/
theorem kneserVertex_card_zero (n : ℕ) :
    Fintype.card (KneserVertex n 0) = 1 := by
  rw [kneserVertex_card, Nat.choose_zero_right]

/-- For `k = n`, the Kneser graph has exactly one vertex (the full set `[n]`). -/
theorem kneserVertex_card_eq_one_of_eq (n : ℕ) :
    Fintype.card (KneserVertex n n) = 1 := by
  rw [kneserVertex_card, Nat.choose_self]

/-- For `k = 0`, the Kneser graph has no edges (only one vertex). -/
theorem kneserGraph_zero_no_adj (n : ℕ) (a b : KneserVertex n 0) :
    ¬ (kneserGraph n 0).Adj a b := by
  intro h
  apply h.1
  have ha : (a.1 : Finset (Fin n)) = ∅ := Finset.card_eq_zero.mp a.2
  have hb : (b.1 : Finset (Fin n)) = ∅ := Finset.card_eq_zero.mp b.2
  exact Subtype.ext (ha.trans hb.symm)

/-- KG(n, 0) is the empty graph (zero edges). -/
theorem kneserGraph_zero_eq_bot (n : ℕ) :
    kneserGraph n 0 = (⊥ : SimpleGraph (KneserVertex n 0)) := by
  ext a b
  simp only [SimpleGraph.bot_adj]
  refine ⟨fun h => kneserGraph_zero_no_adj n a b h, fun h => ?_⟩
  exact (h.elim : (kneserGraph n 0).Adj a b)

/-- KG(n, 1) is the complete graph on n vertices, as a SimpleGraph equality. -/
theorem kneserGraph_one_eq_completeGraph (n : ℕ) :
    kneserGraph n 1 = SimpleGraph.completeGraph (KneserVertex n 1) := by
  ext a b
  rw [kneserGraph_adj_iff]
  simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj, ne_eq]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have ha_card : (a.1 : Finset (Fin n)).card = 1 := a.2
    have hb_card : (b.1 : Finset (Fin n)).card = 1 := b.2
    have ha_eq : (a.1 : Finset (Fin n)) = {x} := by
      rcases Finset.card_eq_one.mp ha_card with ⟨y, hy⟩
      rw [hy] at hxa
      rw [Finset.mem_singleton] at hxa
      rw [hy, hxa]
    have hb_eq : (b.1 : Finset (Fin n)) = {x} := by
      rcases Finset.card_eq_one.mp hb_card with ⟨y, hy⟩
      rw [hy] at hxb
      rw [Finset.mem_singleton] at hxb
      rw [hy, hxb]
    exact h (Subtype.ext (ha_eq.trans hb_eq.symm))

/-- For `k = 1`, the Kneser graph is the complete graph: any two distinct
singleton vertices are adjacent.  (KG(n, 1) ≅ K_n.) -/
theorem kneserGraph_one_adj_of_ne (n : ℕ) (a b : KneserVertex n 1) (h_ne : a ≠ b) :
    (kneserGraph n 1).Adj a b := by
  refine ⟨h_ne, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxa hxb
  -- Both a.1 and b.1 are singletons (card = 1), so x ∈ a.1 ∧ x ∈ b.1 forces a.1 = b.1.
  have ha_card : (a.1 : Finset (Fin n)).card = 1 := a.2
  have hb_card : (b.1 : Finset (Fin n)).card = 1 := b.2
  have ha_eq : (a.1 : Finset (Fin n)) = {x} := by
    rcases Finset.card_eq_one.mp ha_card with ⟨y, hy⟩
    rw [hy] at hxa
    rw [Finset.mem_singleton] at hxa
    rw [hy, hxa]
  have hb_eq : (b.1 : Finset (Fin n)) = {x} := by
    rcases Finset.card_eq_one.mp hb_card with ⟨y, hy⟩
    rw [hy] at hxb
    rw [Finset.mem_singleton] at hxb
    rw [hy, hxb]
  exact h_ne (Subtype.ext (ha_eq.trans hb_eq.symm))

/-- When `2k ≤ n`, the Kneser graph has at least one edge — there exist two
disjoint k-subsets. -/
theorem kneserGraph_exists_adj_of_two_mul_le {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ a b : KneserVertex n k, (kneserGraph n k).Adj a b := by
  -- Build two explicit disjoint k-subsets: {0,...,k-1} and {k,...,2k-1}.
  let A : Finset (Fin n) := (Finset.Ico 0 k).attachFin (fun m hm => by
    rw [Finset.mem_Ico] at hm; omega)
  let B : Finset (Fin n) := (Finset.Ico k (2 * k)).attachFin (fun m hm => by
    rw [Finset.mem_Ico] at hm; omega)
  have hA_card : A.card = k := by
    simp [A, Finset.card_attachFin, Nat.Ico_eq_range']
  have hB_card : B.card = k := by
    simp [B, Finset.card_attachFin, Nat.Ico_eq_range', two_mul]
  refine ⟨⟨A, hA_card⟩, ⟨B, hB_card⟩, ?_, ?_⟩
  · intro h_eq
    have h_eq_set : A = B := by
      have := Subtype.ext_iff.mp h_eq
      simpa using this
    -- 0 ∈ A but 0 ∉ B (since the smallest element of B is k ≥ 1).
    have h0_A : (⟨0, by omega⟩ : Fin n) ∈ A := by
      simp [A, Finset.mem_attachFin]; omega
    have h0_B : (⟨0, by omega⟩ : Fin n) ∉ B := by
      simp [B, Finset.mem_attachFin, Finset.mem_Ico]
    rw [h_eq_set] at h0_A
    exact h0_B h0_A
  · rw [Finset.disjoint_left]
    intro x hxA hxB
    simp [A, B, Finset.mem_attachFin, Finset.mem_Ico] at hxA hxB
    omega

/--
The minimum element of a k-subset (well-defined since k ≥ 1).
-/
noncomputable def KneserVertex.min' {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : Fin n :=
  S.1.min' (by rw [Finset.nonempty_iff_ne_empty]; intro h; have := S.2; simp [h] at this; omega)

/--
The Kneser coloring by minimum element: color each k-subset by its minimum
when that minimum is ≤ n-2k, otherwise assign the default color n-2k+1.
-/
noncomputable def kneserColorNat {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : ℕ :=
  let m := (KneserVertex.min' hk S).val
  if m ≤ n - 2 * k then m else n - 2 * k + 1

theorem kneserColorNat_lt {n k : ℕ} (_hk : 1 ≤ k) (_h2k : 2 * k ≤ n)
    (S : KneserVertex n k) : kneserColorNat _hk S < n - 2 * k + 2 := by
  unfold kneserColorNat
  simp only
  by_cases h : (KneserVertex.min' _hk S).val ≤ n - 2 * k
  · simp [h]
    omega
  · simp [h]

noncomputable def kneserColor {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    KneserVertex n k → Fin (n - 2 * k + 2) :=
  fun S => ⟨kneserColorNat hk S, kneserColorNat_lt hk h2k S⟩

private theorem kneserColor_proper {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (a b : KneserVertex n k) (hadj : (kneserGraph n k).Adj a b) :
    kneserColor hk hn a ≠ kneserColor hk hn b := by
  intro heq
  have hdisj : Disjoint a.1 b.1 := hadj.2
  have hma_mem : KneserVertex.min' hk a ∈ a.1 := Finset.min'_mem _ _
  have hmb_mem : KneserVertex.min' hk b ∈ b.1 := Finset.min'_mem _ _
  have hne_min : (KneserVertex.min' hk a).val ≠ (KneserVertex.min' hk b).val := by
    intro h
    exact Finset.disjoint_left.mp hdisj hma_mem (by rwa [Fin.ext_iff.mpr h])
  simp only [kneserColor, Fin.mk.injEq] at heq
  unfold kneserColorNat at heq
  by_cases ha : (KneserVertex.min' hk a).val ≤ n - 2 * k <;>
    by_cases hb : (KneserVertex.min' hk b).val ≤ n - 2 * k <;>
    simp only [ha, hb, ite_true, ite_false] at heq
  · exact hne_min heq
  · omega
  · omega
  · have ha_neg := ha; have hb_neg := hb
    have ha_sub : ∀ x ∈ (↑a : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact ha_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hb_sub : ∀ x ∈ (↑b : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact hb_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hcard_union : ((↑a : Finset (Fin n)) ∪ ↑b).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj]
      have := a.2; have := b.2; omega
    have hsub : (↑a : Finset (Fin n)) ∪ ↑b ⊆ Finset.univ.filter fun i : Fin n => n - 2 * k < i.val := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rcases Finset.mem_union.mp hx with h | h
        · exact ha_sub x h
        · exact hb_sub x h⟩
    have hle := Finset.card_le_card hsub
    have hfilt_le : (Finset.univ.filter fun i : Fin n => n - 2 * k < i.val).card +
        (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card = n := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => n - 2 * k < i.val)
      simp at this; omega
    have hlow : (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card ≥ n - 2 * k + 1 := by
      have : ∀ j : Fin (n - 2 * k + 1), (⟨j.val, by omega⟩ : Fin n) ∈
          Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k := by
        intro j; simp; omega
      calc _ ≥ Fintype.card (Fin (n - 2 * k + 1)) := by
            exact Finset.card_le_card_of_injOn (fun j => ⟨j.val, by omega⟩)
              (fun j _ => this j) (fun a _ b _ h => by simp [Fin.ext_iff] at h; exact Fin.ext h)
        _ = n - 2 * k + 1 := Fintype.card_fin _
    omega

theorem kneser_chromatic_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  ⟨kneserColor hk hn, kneserColor_proper hk hn⟩

/-! ### Tucker-lemma route for the hard lower bound -/

/-- A sign vector in `{−1,0,1}^n`, represented by its positive and negative supports. -/
structure SignedSubset (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  disjoint : Disjoint pos neg

namespace SignedSubset

/-- Antipodal sign vector: swap positive and negative supports. -/
def antipode {n : ℕ} (X : SignedSubset n) : SignedSubset n where
  pos := X.neg
  neg := X.pos
  disjoint := X.disjoint.symm

/-- The sign vector is not the origin. -/
def Nonzero {n : ℕ} (X : SignedSubset n) : Prop :=
  X.pos.Nonempty ∨ X.neg.Nonempty

theorem antipode_nonzero {n : ℕ} (X : SignedSubset n) :
    X.antipode.Nonzero ↔ X.Nonzero := by
  simp [Nonzero, antipode, or_comm]

/-- Total support size of a sign vector. -/
def card {n : ℕ} (X : SignedSubset n) : ℕ :=
  X.pos.card + X.neg.card

theorem card_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.card = X.card := by
  simp [card, antipode, Nat.add_comm]

theorem card_pos_of_nonzero {n : ℕ} {X : SignedSubset n} (hX : X.Nonzero) :
    0 < X.card := by
  rcases hX with hpos | hneg
  · simp [card, Finset.card_pos.2 hpos]
  · simp [card, Finset.card_pos.2 hneg]

/-- The unsigned support of a sign vector. -/
def support {n : ℕ} (X : SignedSubset n) : Finset (Fin n) :=
  X.pos ∪ X.neg

theorem support_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.support = X.support := by
  ext i
  simp [support, antipode, or_comm]

theorem support_nonempty_iff_nonzero {n : ℕ} (X : SignedSubset n) :
    X.support.Nonempty ↔ X.Nonzero := by
  simp [support, Nonzero]

/-- The largest coordinate in the support of a nonzero sign vector. -/
noncomputable def maxSupport {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Fin n :=
  X.support.max' ((support_nonempty_iff_nonzero X).mpr hX)

theorem maxSupport_mem_support {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.maxSupport hX ∈ X.support := by
  exact Finset.max'_mem _ _

theorem maxSupport_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupport h₁ = X.maxSupport h₂ := by
  unfold maxSupport
  congr

theorem maxSupport_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupport ((antipode_nonzero X).mpr hX) = X.maxSupport hX := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.antipode.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'

/-- The sign of the largest supported coordinate, used in Matoušek's small-support labels. -/
noncomputable def maxSupportPositive {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Bool :=
  decide (X.maxSupport hX ∈ X.pos)

theorem maxSupportPositive_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupportPositive h₁ = X.maxSupportPositive h₂ := by
  unfold maxSupportPositive
  rw [maxSupport_congr_proof X h₁ h₂]

theorem maxSupportPositive_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupportPositive ((antipode_nonzero X).mpr hX) =
      !(X.maxSupportPositive hX) := by
  unfold maxSupportPositive
  rw [maxSupport_antipode]
  change decide (X.maxSupport hX ∈ X.neg) = !decide (X.maxSupport hX ∈ X.pos)
  by_cases hpos : X.maxSupport hX ∈ X.pos
  · have hnotneg : X.maxSupport hX ∉ X.neg := by
      intro hneg
      exact (Finset.disjoint_left.mp X.disjoint) hpos hneg
    simp [hpos, hnotneg]
  · have hneg : X.maxSupport hX ∈ X.neg := by
      have hmem := X.maxSupport_mem_support hX
      exact (Finset.mem_union.mp hmem).resolve_left hpos
    simp [hpos, hneg]

/-- The face order on the cross-polytope boundary, by support inclusion. -/
def Le {n : ℕ} (X Y : SignedSubset n) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

/-- Select the positive or negative support of a sign vector. -/
def side {n : ℕ} (X : SignedSubset n) (positive : Bool) : Finset (Fin n) :=
  if positive then X.pos else X.neg

@[simp]
theorem side_true {n : ℕ} (X : SignedSubset n) : X.side true = X.pos := by
  simp [side]

@[simp]
theorem side_false {n : ℕ} (X : SignedSubset n) : X.side false = X.neg := by
  simp [side]

theorem side_antipode_not {n : ℕ} (X : SignedSubset n) (positive : Bool) :
    X.antipode.side (!positive) = X.side positive := by
  cases positive <;> simp [side, antipode]

theorem side_disjoint_of_le_not {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (positive : Bool) :
    Disjoint (X.side positive) (Y.side (!positive)) := by
  cases positive
  · simp [side]
    exact Disjoint.mono hXY.2 (fun _ h => h) Y.disjoint.symm
  · simp [side]
    exact Disjoint.mono hXY.1 (fun _ h => h) Y.disjoint

theorem eq_of_le_card_eq {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hcard : X.card = Y.card) : X = Y := by
  have hpos_le : X.pos.card ≤ Y.pos.card := Finset.card_le_card hXY.1
  have hneg_le : X.neg.card ≤ Y.neg.card := Finset.card_le_card hXY.2
  have hsum : X.pos.card + X.neg.card = Y.pos.card + Y.neg.card := by
    simpa [card] using hcard
  have hpos_ge : Y.pos.card ≤ X.pos.card := by omega
  have hneg_ge : Y.neg.card ≤ X.neg.card := by omega
  have hpos_eq : X.pos = Y.pos := Finset.eq_of_subset_of_card_le hXY.1 hpos_ge
  have hneg_eq : X.neg = Y.neg := Finset.eq_of_subset_of_card_le hXY.2 hneg_ge
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos_eq hneg_eq
          subst ypos
          subst yneg
          simp

end SignedSubset

/-- Nonzero sign vectors, i.e. vertices/faces of the deleted origin sign complex. -/
abbrev NonzeroSignedSubset (n : ℕ) :=
  {X : SignedSubset n // X.Nonzero}

namespace NonzeroSignedSubset

/-- Antipodal map on nonzero sign vectors. -/
def antipode {n : ℕ} (X : NonzeroSignedSubset n) : NonzeroSignedSubset n :=
  ⟨X.1.antipode, (SignedSubset.antipode_nonzero X.1).mpr X.2⟩

end NonzeroSignedSubset

/-- A signed label `±i`, with `i : Fin m`. -/
structure SignedLabel (m : ℕ) where
  positive : Bool
  index : Fin m
  deriving DecidableEq, Repr

namespace SignedLabel

/-- Negating a signed label flips its sign and keeps its index. -/
def neg {m : ℕ} (L : SignedLabel m) : SignedLabel m where
  positive := !L.positive
  index := L.index

theorem ext {m : ℕ} {L M : SignedLabel m}
    (hpositive : L.positive = M.positive) (hindex : L.index = M.index) : L = M := by
  cases L
  cases M
  simp at hpositive hindex
  subst hpositive
  subst hindex
  rfl

end SignedLabel

/-- `k`-subsets contained in a fixed finite support. -/
abbrev KneserVertexIn (n k : ℕ) (support : Finset (Fin n)) : Type :=
  {A : KneserVertex n k // (A.1 : Finset (Fin n)) ⊆ support}

instance (n k : ℕ) (support : Finset (Fin n)) :
    Fintype (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

instance (n k : ℕ) (support : Finset (Fin n)) :
    DecidableEq (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

theorem KneserVertexIn.nonempty_of_le_card {n k : ℕ} {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    Nonempty (KneserVertexIn n k support) := by
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨⟨⟨A, hAcard⟩, hAsub⟩⟩

/-- The set of colors used on `k`-subsets contained in a support. -/
noncomputable def colorsInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) : Finset (Fin q) :=
  Finset.univ.image fun A : KneserVertexIn n k support => C A.1

theorem colorsInSupport_nonempty {n k q : ℕ} (C : KneserVertex n k → Fin q)
    {support : Finset (Fin n)} (hcard : k ≤ support.card) :
    (colorsInSupport C support).Nonempty := by
  classical
  obtain ⟨A⟩ := KneserVertexIn.nonempty_of_le_card (n := n) (k := k) hcard
  exact ⟨C A.1, by simp [colorsInSupport]⟩

/-- The minimum color appearing on a `k`-subset contained in `support`. -/
noncomputable def minColorInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) (hcard : k ≤ support.card) : Fin q :=
  (colorsInSupport C support).min' (colorsInSupport_nonempty C hcard)

theorem exists_kneserVertexIn_color_eq_minColorInSupport {n k q : ℕ}
    (C : KneserVertex n k → Fin q) {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    ∃ A : KneserVertexIn n k support, C A.1 = minColorInSupport C support hcard := by
  classical
  have hmem :
      minColorInSupport C support hcard ∈ colorsInSupport C support :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨A, _hA, hAeq⟩
  exact ⟨A, hAeq⟩

@[simp]
theorem minColorInSupport_congr_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (support : Finset (Fin n))
    (h₁ h₂ : k ≤ support.card) :
    minColorInSupport C support h₁ = minColorInSupport C support h₂ := by
  unfold minColorInSupport
  congr

/--
Key finite step in Matoušek's Tucker reduction: if two disjoint supports both
contain a `k`-subset, then a proper Kneser coloring gives different minimum
colors on the two supports.
-/
theorem minColorInSupport_ne_of_disjoint {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by
  classical
  obtain ⟨A, hAcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hleft
  obtain ⟨B, hBcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hright
  have hABdisj : Disjoint (A.1.1 : Finset (Fin n)) (B.1.1 : Finset (Fin n)) :=
    Disjoint.mono A.2 B.2 hdisj
  have hABne : A.1 ≠ B.1 := by
    intro h
    have hself : Disjoint (A.1.1 : Finset (Fin n)) (A.1.1 : Finset (Fin n)) := by
      simpa [h] using hABdisj
    have hempty : (A.1.1 : Finset (Fin n)) = ∅ := by
      exact (Finset.disjoint_self_iff_empty _).mp hself
    have hzero : (A.1.1 : Finset (Fin n)).card = 0 := by simp [hempty]
    have hAcard : (A.1.1 : Finset (Fin n)).card = k := A.1.2
    omega
  intro hmin
  exact hC A.1 B.1 ⟨hABne, hABdisj⟩ (hAcolor.trans (hmin.trans hBcolor.symm))

/--
Small-support part of Matoušek's labeling: a nonzero sign vector with total
support at most `2k - 2` receives label index `|X| - 1`.
-/
def matousekSmallSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    Fin (n - 1) :=
  ⟨X.card - 1, by
    have hpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
    omega⟩

/-- Full small-support signed label in Matoušek's construction. -/
noncomputable def matousekSmallSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    SignedLabel (n - 1) where
  positive := X.maxSupportPositive hX
  index := matousekSmallSupportIndex hk hn X hX hsmall

theorem matousekSmallSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall) =
      (matousekSmallSupportLabel hk hn X hX hsmall).neg := by
  change SignedLabel.mk
      (X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX))
      (matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall)) =
    SignedLabel.mk (!(X.maxSupportPositive hX)) (matousekSmallSupportIndex hk hn X hX hsmall)
  have hpositive :
      X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX) =
        !(X.maxSupportPositive hX) :=
    SignedSubset.maxSupportPositive_antipode X hX
  have hindex :
      matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
          (by simpa [SignedSubset.card_antipode] using hsmall) =
        matousekSmallSupportIndex hk hn X hX hsmall := by
    apply Fin.ext
    simp [matousekSmallSupportIndex, SignedSubset.card_antipode]
  exact SignedLabel.ext hpositive hindex

theorem matousekSmallSupportIndex_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportIndex hk hn X hX₁ hsmall₁ =
      matousekSmallSupportIndex hk hn X hX₂ hsmall₂ := by
  apply Fin.ext
  simp [matousekSmallSupportIndex]

theorem matousekSmallSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X hX₁ hsmall₁ =
      matousekSmallSupportLabel hk hn X hX₂ hsmall₂ := by
  apply SignedLabel.ext
  · exact SignedSubset.maxSupportPositive_congr_proof X hX₁ hX₂
  · exact matousekSmallSupportIndex_congr_proof hk hn X hX₁ hX₂ hsmall₁ hsmall₂

theorem matousekSmallSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero)
    (hXsmall : X.card ≤ 2 * k - 2) (hYsmall : Y.card ≤ 2 * k - 2)
    (hXY : SignedSubset.Le X Y) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcard : X.card = Y.card := by
    simp [matousekSmallSupportIndex] at hindex_val
    omega
  have hXYeq : X = Y := SignedSubset.eq_of_le_card_eq hXY hcard
  subst Y
  have hpositive := congrArg SignedLabel.positive hcomp
  simp [matousekSmallSupportLabel, SignedLabel.neg] at hpositive

/--
Large-support color labels occupy the range `2k - 2, …, n - 2`, obtained by
adding the color value to the offset `2k - 2`.
-/
def matousekLargeSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (color : Fin (n - 2 * k + 1)) : Fin (n - 1) :=
  ⟨2 * k - 2 + color.val, by
    have hcolor := color.isLt
    omega⟩

/-- If a sign vector has support at least `2k - 1`, then one side has a `k`-subset. -/
theorem signedSubset_large_support_has_k_side {n k : ℕ} {X : SignedSubset n}
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ X.pos.card ∨ k ≤ X.neg.card := by
  by_contra h
  push Not at h
  simp [SignedSubset.card] at hlarge
  omega

theorem decide_lt_swap_eq_not {α : Type*} [LinearOrder α] [DecidableRel ((· < ·) : α → α → Prop)]
    {a b : α} (hne : a ≠ b) : decide (b < a) = !decide (a < b) := by
  by_cases hab : a < b
  · have hba : ¬ b < a := not_lt_of_ge hab.le
    simp [hab, hba]
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hne.symm
    simp [hab, hba]

/--
Large-support side choice in Matoušek's construction: use the side whose
contained `k`-subsets have smaller minimum color, breaking one-sided cases by
choosing the only side that contains a `k`-subset.
-/
noncomputable def matousekLargeSupportPositive {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (_hlarge : 2 * k - 1 ≤ X.card) : Bool :=
  if hpos : k ≤ X.pos.card then
    if hneg : k ≤ X.neg.card then
      decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg)
    else true
  else false

@[simp]
theorem matousekLargeSupportPositive_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X hlarge₁ =
      matousekLargeSupportPositive C X hlarge₂ := by
  rfl

theorem matousekLargeSupportPositive_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ (X.side (matousekLargeSupportPositive C X hlarge)).card := by
  unfold matousekLargeSupportPositive
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · by_cases hlt : minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg
      · simp [hpos, hneg, hlt]
      · simp [hpos, hneg, hlt]
    · simp [hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [hpos, hneg]

theorem matousekLargeSupportPositive_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      !(matousekLargeSupportPositive C X hlarge) := by
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · have hne :
          minColorInSupport C X.pos hpos ≠ minColorInSupport C X.neg hneg :=
        minColorInSupport_ne_of_disjoint hk C hC X.disjoint hpos hneg
      have hswap :
          decide (minColorInSupport C X.neg hneg < minColorInSupport C X.pos hpos) =
            !decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg) :=
        decide_lt_swap_eq_not hne
      simpa [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg] using hswap
    · simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]

/-- The minimum color on the selected large-support side. -/
noncomputable def matousekLargeSupportColor {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : Fin q :=
  minColorInSupport C (X.side (matousekLargeSupportPositive C X hlarge))
    (matousekLargeSupportPositive_card C X hlarge)

theorem matousekLargeSupportColor_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X hlarge₁ =
      matousekLargeSupportColor C X hlarge₂ := by
  simp [matousekLargeSupportColor]

theorem matousekLargeSupportColor_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      matousekLargeSupportColor C X hlarge := by
  have hpositive := matousekLargeSupportPositive_antipode hk C hC X hlarge
  simp [matousekLargeSupportColor, hpositive, SignedSubset.side_antipode_not]

/-- Full large-support signed label in Matoušek's construction. -/
noncomputable def matousekLargeSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : SignedLabel (n - 1) where
  positive := matousekLargeSupportPositive C X hlarge
  index := matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge)

theorem matousekLargeSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X hlarge₁ =
      matousekLargeSupportLabel hk hn C X hlarge₂ := by
  apply SignedLabel.ext
  · exact matousekLargeSupportPositive_congr_proof C X hlarge₁ hlarge₂
  · apply Fin.ext
    simp [matousekLargeSupportLabel, matousekLargeSupportIndex,
      matousekLargeSupportColor_congr_proof C X hlarge₁ hlarge₂]

theorem matousekLargeSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      (matousekLargeSupportLabel hk hn C X hlarge).neg := by
  change SignedLabel.mk
      (matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge))
      (matousekLargeSupportIndex hk hn
        (matousekLargeSupportColor C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge))) =
    SignedLabel.mk (!(matousekLargeSupportPositive C X hlarge))
      (matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge))
  have hpositive :
      matousekLargeSupportPositive C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge) =
        !(matousekLargeSupportPositive C X hlarge) :=
    matousekLargeSupportPositive_antipode hk C hC X hlarge
  have hindex :
      matousekLargeSupportIndex hk hn
          (matousekLargeSupportColor C X.antipode
            (by simpa [SignedSubset.card_antipode] using hlarge)) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge) := by
    rw [matousekLargeSupportColor_antipode hk C hC X hlarge]
  exact SignedLabel.ext hpositive hindex

theorem matousekLargeSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card) (hYlarge : 2 * k - 1 ≤ Y.card)
    (hXY : SignedSubset.Le X Y) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hpositive :
      matousekLargeSupportPositive C X hXlarge =
        !(matousekLargeSupportPositive C Y hYlarge) := by
    have := congrArg SignedLabel.positive hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hcolor : matousekLargeSupportColor C X hXlarge =
      matousekLargeSupportColor C Y hYlarge := by
    apply Fin.ext
    have hindex_val := congrArg Fin.val hindex
    simp [matousekLargeSupportIndex] at hindex_val
    omega
  have hdisj :
      Disjoint
        (X.side (matousekLargeSupportPositive C X hXlarge))
        (Y.side (matousekLargeSupportPositive C Y hYlarge)) := by
    cases hYpos : matousekLargeSupportPositive C Y hYlarge
    · have hXpos : matousekLargeSupportPositive C X hXlarge = true := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY true
    · have hXpos : matousekLargeSupportPositive C X hXlarge = false := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY false
  have hmin_ne :
      minColorInSupport C
          (X.side (matousekLargeSupportPositive C X hXlarge))
          (matousekLargeSupportPositive_card C X hXlarge) ≠
        minColorInSupport C
          (Y.side (matousekLargeSupportPositive C Y hYlarge))
          (matousekLargeSupportPositive_card C Y hYlarge) :=
    minColorInSupport_ne_of_disjoint hk C hC hdisj
      (matousekLargeSupportPositive_card C X hXlarge)
      (matousekLargeSupportPositive_card C Y hYlarge)
  exact hmin_ne (by simpa [matousekLargeSupportColor] using hcolor)

theorem matousekSmallSupportLabel_ne_neg_large {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hX : X.Nonzero) (hXsmall : X.card ≤ 2 * k - 2)
    (hYlarge : 2 * k - 1 ≤ Y.card) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hcolor := (matousekLargeSupportColor C Y hYlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega

theorem matousekLargeSupportLabel_ne_neg_small {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card)
    (hY : Y.Nonzero) (hYsmall : Y.card ≤ 2 * k - 2) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcolor := (matousekLargeSupportColor C X hXlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega

/--
In a proper Kneser coloring, if both signs of a signed support contain
`k`-subsets, the minimum colors on the two sides are different.
-/
theorem minColorInSignedSubset_pos_ne_neg {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n)
    (hpos : k ≤ X.pos.card) (hneg : k ≤ X.neg.card) :
    minColorInSupport C X.pos hpos ≠ minColorInSupport C X.neg hneg :=
  minColorInSupport_ne_of_disjoint hk C hC X.disjoint hpos hneg

/-- Matoušek's sign-vector label produced by a hypothetical too-small coloring. -/
noncomputable def matousekTuckerLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) :
    NonzeroSignedSubset n → SignedLabel (n - 1) :=
  fun X =>
    if hsmall : X.1.card ≤ 2 * k - 2 then
      matousekSmallSupportLabel hk hn X.1 X.2 hsmall
    else
      matousekLargeSupportLabel hk hn C X.1 (by omega)

theorem matousekTuckerLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : NonzeroSignedSubset n) :
    matousekTuckerLabel hk hn C X.antipode = (matousekTuckerLabel hk hn C X).neg := by
  unfold matousekTuckerLabel
  by_cases hsmall : X.1.card ≤ 2 * k - 2
  · have hsmall_ant : X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_pos hsmall, dif_pos hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekSmallSupportLabel_congr_proof hk hn X.1.antipode] using
      matousekSmallSupportLabel_antipode hk hn X.1 X.2 hsmall
  · have hlarge : 2 * k - 1 ≤ X.1.card := by omega
    have hsmall_ant : ¬ X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_neg hsmall, dif_neg hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekLargeSupportLabel_congr_proof hk hn C X.1,
      matousekLargeSupportLabel_congr_proof hk hn C X.1.antipode] using
      matousekLargeSupportLabel_antipode hk hn C hC X.1 hlarge

theorem matousekTuckerLabel_no_complementary {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X Y : NonzeroSignedSubset n) :
    SignedSubset.Le X.1 Y.1 →
      matousekTuckerLabel hk hn C X ≠ (matousekTuckerLabel hk hn C Y).neg := by
  intro hXY
  unfold matousekTuckerLabel
  by_cases hXsmall : X.1.card ≤ 2 * k - 2
  · by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall] using
        matousekSmallSupportLabel_ne_neg_of_le hk hn X.2 Y.2 hXsmall hYsmall hXY
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekSmallSupportLabel_ne_neg_large hk hn C X.2 hXsmall hYlarge
  · have hXlarge : 2 * k - 1 ≤ X.1.card := by omega
    by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1] using
        matousekLargeSupportLabel_ne_neg_small hk hn C hXlarge Y.2 hYsmall
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1,
        matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekLargeSupportLabel_ne_neg_of_le hk hn C hC hXlarge hYlarge hXY

/--
Tucker's lemma in the octahedral/sign-vector form needed for the Matoušek
proof of Lovász's theorem.  The remaining proof obligation is supplied by the
finer `KyFanPrefixParityStatement` below.
-/
def TuckerLemmaStatement (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, label X.antipode = (label X).neg) →
      ∃ X Y : NonzeroSignedSubset n,
        SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg

theorem not_nonzeroSignedSubset_zero (X : NonzeroSignedSubset 0) : False := by
  rcases X with ⟨X, hX⟩
  have hpos : X.pos = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _hx
    exact Fin.elim0 x
  have hneg : X.neg = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _hx
    exact Fin.elim0 x
  simp [SignedSubset.Nonzero, hpos, hneg] at hX

theorem not_tuckerLemmaStatement_zero : ¬ TuckerLemmaStatement 0 := by
  intro htucker
  let label : NonzeroSignedSubset 0 → SignedLabel (0 - 1) :=
    fun X => False.elim (not_nonzeroSignedSubset_zero X)
  have hantipodal : ∀ X, label X.antipode = (label X).neg := by
    intro X
    exact False.elim (not_nonzeroSignedSubset_zero X)
  obtain ⟨X, _Y, _hXY, _hcomp⟩ := htucker label hantipodal
  exact not_nonzeroSignedSubset_zero X

/-- A sign-vector labeling has no complementary comparable pair. -/
def NoComplementaryComparableLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Prop :=
  ∀ X Y : NonzeroSignedSubset n,
    SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

theorem positive_eq_of_le_of_same_index_of_no_complement {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset n}
    (hXY : SignedSubset.Le X.1 Y.1)
    (hindex : (label X).index = (label Y).index) :
    (label X).positive = (label Y).positive := by
  by_contra hne
  have hbool : (label X).positive = !((label Y).positive) := by
    cases hx : (label X).positive <;> cases hy : (label Y).positive <;>
      simp [hx, hy] at hne ⊢
  exact hno X Y hXY (SignedLabel.ext hbool (by simpa [SignedLabel.neg] using hindex))

/--
Ky Fan's alternating-chain form for the sign-vector/cross-polytope complex.
Under an antipodal labeling with no complementary comparable pair, there is a
chain of `n` sign-vector faces whose absolute label indices are strictly
increasing.

The missing proof is the standard finite parity count of alternating maximal
chains in the barycentric subdivision of the cross-polytope boundary.
-/
def KyFanAlternatingChainStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ chain : Fin n → NonzeroSignedSubset n,
          (∀ i j, i < j → SignedSubset.Le (chain i).1 (chain j).1) ∧
            StrictMono fun i => (label (chain i)).index

theorem not_strictMono_fin_pred (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ f : Fin n → Fin (n - 1), StrictMono f := by
  rintro ⟨f, hf⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hij' : i = j
    · exact hij'
    · have hlt_or_gt : i < j ∨ j < i := lt_or_gt_of_ne hij'
      rcases hlt_or_gt with hlt | hgt
      · exact (ne_of_lt (hf hlt) hij).elim
      · exact (ne_of_gt (hf hgt) hij).elim
  have hcard := Fintype.card_le_of_injective f hinj
  simp [Fintype.card_fin] at hcard
  omega

theorem not_strictMono_fin_of_lt {n m : ℕ} (hmn : m < n) :
    ¬ ∃ f : Fin n → Fin m, StrictMono f := by
  rintro ⟨f, hf⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hij' : i = j
    · exact hij'
    · have hlt_or_gt : i < j ∨ j < i := lt_or_gt_of_ne hij'
      rcases hlt_or_gt with hlt | hgt
      · exact (ne_of_lt (hf hlt) hij).elim
      · exact (ne_of_gt (hf hgt) hij).elim
  have hcard := Fintype.card_le_of_injective f hinj
  simp [Fintype.card_fin] at hcard
  omega

theorem tuckerLemmaStatement_of_kyFan {n : ℕ} (hn : 1 ≤ n)
    (hfan : KyFanAlternatingChainStatement n (n - 1)) :
    TuckerLemmaStatement n := by
  intro label hantipodal
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨chain, _hchain, hstrict⟩ := hfan label hantipodal hno
  exact not_strictMono_fin_pred n hn ⟨fun i => (label (chain i)).index, hstrict⟩

/--
A signed permutation, i.e. a maximal chain in the face lattice of the
cross-polytope boundary: reveal the coordinates in `order`, with the prescribed
sign at each coordinate.
-/
structure SignedPermutation (n : ℕ) where
  order : Equiv.Perm (Fin n)
  positive : Fin n → Bool
  deriving DecidableEq

def signedPermutationEquiv (n : ℕ) :
    SignedPermutation n ≃ Equiv.Perm (Fin n) × (Fin n → Bool) where
  toFun P := (P.order, P.positive)
  invFun data := { order := data.1, positive := data.2 }
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro data
    cases data
    rfl

noncomputable instance (n : ℕ) : Fintype (SignedPermutation n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n) × (Fin n → Bool)) (signedPermutationEquiv n).symm

namespace SignedPermutation

/-- Antipodal signed permutation: keep the order and flip every sign. -/
def antipode {n : ℕ} (P : SignedPermutation n) : SignedPermutation n where
  order := P.order
  positive := fun i => !P.positive i

theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro P
  cases P
  simp [antipode]

theorem antipode_ne_self {n : ℕ} (hn : 0 < n) (P : SignedPermutation n) :
    P.antipode ≠ P := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hfun := congrArg SignedPermutation.positive h
  have hi := congrFun hfun i
  simp [antipode] at hi

/-- Positive coordinates in the `i`th prefix face of a signed permutation. -/
def prefixPos {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ P.positive (P.order.symm x)

/-- Negative coordinates in the `i`th prefix face of a signed permutation. -/
def prefixNeg {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ !P.positive (P.order.symm x)

theorem prefix_disjoint {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    Disjoint (P.prefixPos i) (P.prefixNeg i) := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  simp [prefixPos, prefixNeg] at hxpos hxneg
  cases h : P.positive (P.order.symm x) <;> simp [h] at hxpos hxneg

theorem prefixPos_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixPos i = P.prefixNeg i := by
  ext x
  simp [antipode, prefixPos, prefixNeg]

theorem prefixNeg_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixNeg i = P.prefixPos i := by
  ext x
  simp [antipode, prefixPos, prefixNeg]

/-- The `i`th prefix face as a sign vector. -/
def prefixSignedSubset {n : ℕ} (P : SignedPermutation n) (i : Fin n) : SignedSubset n where
  pos := P.prefixPos i
  neg := P.prefixNeg i
  disjoint := P.prefix_disjoint i

theorem prefix_nonzero {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).Nonzero := by
  let x : Fin n := P.order i
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hsymm : P.order.symm x = i := by simp [x]
  have hle : P.order.symm x ≤ i := le_of_eq hsymm
  by_cases hpos : P.positive (P.order.symm x) = true
  · left
    exact ⟨x, by simp [prefixSignedSubset, prefixPos, hxuniv, hle, hpos]⟩
  · right
    exact ⟨x, by simp [prefixSignedSubset, prefixNeg, hxuniv, hle, hpos]⟩

/-- The maximal chain associated to a signed permutation. -/
def prefixChain {n : ℕ} (P : SignedPermutation n) (i : Fin n) : NonzeroSignedSubset n :=
  ⟨P.prefixSignedSubset i, P.prefix_nonzero i⟩

theorem prefixSignedSubset_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixSignedSubset i = (P.prefixSignedSubset i).antipode := by
  cases P with
  | mk order positive =>
      simp [antipode, prefixSignedSubset, prefixPos, prefixNeg, SignedSubset.antipode]

theorem prefixChain_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixChain i = (P.prefixChain i).antipode := by
  apply Subtype.ext
  exact P.prefixSignedSubset_antipode i

theorem prefixChain_le {n : ℕ} (P : SignedPermutation n) {i j : Fin n} (hij : i ≤ j) :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 := by
  constructor
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixPos] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixNeg] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩

theorem prefixChain_strictly_ordered {n : ℕ} (P : SignedPermutation n) :
    ∀ i j, i < j → SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 := by
  intro i j hij
  exact P.prefixChain_le hij.le

end SignedPermutation

/--
The explicit maximal-chain version of the Ky Fan frontier.  It is the standard
odd-count statement specialized to signed permutations/prefix chains.
-/
def KyFanPrefixChainStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ P : SignedPermutation n,
          StrictMono fun i => (label (P.prefixChain i)).index

theorem kyFanAlternatingChainStatement_of_prefix {n m : ℕ}
    (hprefix : KyFanPrefixChainStatement n m) :
    KyFanAlternatingChainStatement n m := by
  intro label hantipodal hno
  obtain ⟨P, hstrict⟩ := hprefix label hantipodal hno
  exact ⟨P.prefixChain, P.prefixChain_strictly_ordered, hstrict⟩

theorem tuckerLemmaStatement_of_kyFanPrefix {n : ℕ} (hn : 1 ≤ n)
    (hprefix : KyFanPrefixChainStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFan hn (kyFanAlternatingChainStatement_of_prefix hprefix)

theorem label_prefixChain_antipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) (i : Fin n) :
    label (P.antipode.prefixChain i) = (label (P.prefixChain i)).neg := by
  rw [SignedPermutation.prefixChain_antipode]
  exact hantipodal (P.prefixChain i)

theorem prefix_strictMono_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    (StrictMono fun i => (label (P.antipode.prefixChain i)).index) ↔
      StrictMono fun i => (label (P.prefixChain i)).index := by
  simp [label_prefixChain_antipode label hantipodal P, SignedLabel.neg]

/-- Signed permutations whose prefix labels have strictly increasing indices. -/
noncomputable def strictPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => StrictMono fun i => (label (P.prefixChain i)).index

/--
Positive-first alternating prefix labels: the absolute label indices strictly
increase, and the signs alternate `+,-,+,-,...` along the prefix chain.
-/
def PositiveAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = decide (Even i.val)

/-- Negative-first alternating prefix labels, the antipodal partner of the positive-first version. -/
def NegativeAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = !decide (Even i.val)

theorem positiveAlternatingPrefixLabels_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P.antipode ↔
      NegativeAlternatingPrefixLabels label P := by
  constructor
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mp h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i] at hsign
    simpa [NegativeAlternatingPrefixLabels, PositiveAlternatingPrefixLabels, SignedLabel.neg]
      using hsign
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mpr h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i]
    simp [SignedLabel.neg, hsign]

theorem positive_negative_alternating_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P →
      NegativeAlternatingPrefixLabels label P → False := by
  intro hpos hneg
  let i : Fin n := ⟨0, hn⟩
  have hp := hpos.2 i
  have hn' := hneg.2 i
  simp [i] at hp hn'
  rw [hp] at hn'
  simp at hn'

/-- Signed permutations whose prefix labels are positive-first alternating. -/
noncomputable def positiveAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => PositiveAlternatingPrefixLabels label P

/-- Signed permutations whose prefix labels are negative-first alternating. -/
noncomputable def negativeAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => NegativeAlternatingPrefixLabels label P

theorem positiveAlternatingPrefixLabelChains_card_eq_negative {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (positiveAlternatingPrefixLabelChains label).card =
      (negativeAlternatingPrefixLabelChains label).card := by
  classical
  refine Finset.card_bij (fun P _ => SignedPermutation.antipode P) ?mem ?inj ?surj
  · intro P hP
    have hpos : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    have hneg : NegativeAlternatingPrefixLabels label P.antipode := by
      have hiff := positiveAlternatingPrefixLabels_antipode_iff label hantipodal P.antipode
      have hpos' : PositiveAlternatingPrefixLabels label P.antipode.antipode := by
        simpa [SignedPermutation.antipode_involutive P] using hpos
      exact hiff.mp hpos'
    simpa [negativeAlternatingPrefixLabelChains] using hneg
  · intro P hP Q hQ hPQ
    have h := congrArg SignedPermutation.antipode hPQ
    simpa [SignedPermutation.antipode_involutive P, SignedPermutation.antipode_involutive Q] using h
  · intro Q hQ
    have hneg : NegativeAlternatingPrefixLabels label Q := by
      simpa [negativeAlternatingPrefixLabelChains] using hQ
    refine ⟨Q.antipode, ?_, ?_⟩
    · have hpos : PositiveAlternatingPrefixLabels label Q.antipode := by
        exact (positiveAlternatingPrefixLabels_antipode_iff label hantipodal Q).mpr hneg
      simpa [positiveAlternatingPrefixLabelChains] using hpos
    · exact SignedPermutation.antipode_involutive Q

theorem positive_negativeAlternatingPrefixLabelChains_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    Disjoint (positiveAlternatingPrefixLabelChains label)
      (negativeAlternatingPrefixLabelChains label) := by
  classical
  rw [Finset.disjoint_left]
  intro P hpos hneg
  exact positive_negative_alternating_disjoint hn label P
    (by simpa [positiveAlternatingPrefixLabelChains] using hpos)
    (by simpa [negativeAlternatingPrefixLabelChains] using hneg)

/-- Positive- or negative-first alternating prefix-label chains. -/
noncomputable def alternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  positiveAlternatingPrefixLabelChains label ∪ negativeAlternatingPrefixLabelChains label

theorem alternatingPrefixLabelChains_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (alternatingPrefixLabelChains label).card =
      2 * (positiveAlternatingPrefixLabelChains label).card := by
  classical
  rw [alternatingPrefixLabelChains,
    Finset.card_union_of_disjoint (positive_negativeAlternatingPrefixLabelChains_disjoint hn label),
    positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  omega

/--
Equivalent mod-four form of the Ky Fan prefix-chain frontier: after both
orientations are counted, the number of alternating maximal chains is `2`
modulo `4`.
-/
def KyFanPrefixModFourStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ r, (alternatingPrefixLabelChains label).card = 4 * r + 2

/--
The exact finite parity statement still missing from Mathlib for this chapter:
under an antipodal labeling with no complementary comparable pair, the number
of positive-first alternating signed-permutation prefix chains is odd.  This is
the standard Ky Fan odd-count statement specialized to the cross-polytope
face-poset model.
-/
def KyFanPrefixParityStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (positiveAlternatingPrefixLabelChains label).card

/-- In dimension one, every signed-permutation prefix chain is alternating
in exactly one of the two possible first signs. -/
theorem alternatingPrefixLabelChains_card_one
    (label : NonzeroSignedSubset 1 → SignedLabel 0) :
    (alternatingPrefixLabelChains label).card = 2 := by
  classical
  have huniv : alternatingPrefixLabelChains label = (Finset.univ : Finset (SignedPermutation 1)) := by
    ext P
    simp only [Finset.mem_univ, iff_true]
    change P ∈ positiveAlternatingPrefixLabelChains label ∪
      negativeAlternatingPrefixLabelChains label
    rw [Finset.mem_union]
    have hstrict : StrictMono fun i : Fin 1 => (label (P.prefixChain i)).index := by
      intro a b hab
      fin_cases a
      fin_cases b
      omega
    cases h : (label (P.prefixChain 0)).positive
    · right
      have hneg : NegativeAlternatingPrefixLabels label P := by
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      simpa only [negativeAlternatingPrefixLabelChains, Finset.mem_filter,
        Finset.mem_univ, true_and] using hneg
    · left
      have hpos : PositiveAlternatingPrefixLabels label P := by
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      simpa only [positiveAlternatingPrefixLabelChains, Finset.mem_filter,
        Finset.mem_univ, true_and] using hpos
  rw [huniv]
  calc
    (Finset.univ : Finset (SignedPermutation 1)).card =
        Fintype.card (SignedPermutation 1) := by
      simp
    _ = Fintype.card (Equiv.Perm (Fin 1) × (Fin 1 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 1)
    _ = 2 := by simp

/-- The Ky Fan prefix-parity frontier is fully discharged in dimension one. -/
theorem kyFanPrefixParityStatement_one : KyFanPrefixParityStatement 1 0 := by
  intro label hantipodal _hno
  have halt := alternatingPrefixLabelChains_card_one label
  have htwice := alternatingPrefixLabelChains_card (n := 1) (m := 0) (by omega) label hantipodal
  rw [halt] at htwice
  have hpos : (positiveAlternatingPrefixLabelChains label).card = 1 := by
    omega
  rw [hpos]
  exact odd_one

theorem kyFanPrefixParityStatement_iff_modFour {n m : ℕ} (hn : 0 < n) :
    KyFanPrefixParityStatement n m ↔ KyFanPrefixModFourStatement n m := by
  constructor
  · intro hparity label hantipodal hno
    rcases hparity label hantipodal hno with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [alternatingPrefixLabelChains_card hn label hantipodal, hr]
    omega
  · intro hmodFour label hantipodal hno
    obtain ⟨r, hcard⟩ := hmodFour label hantipodal hno
    have htwo := alternatingPrefixLabelChains_card hn label hantipodal
    refine ⟨r, ?_⟩
    omega

theorem kyFanPrefixChainStatement_of_parity {n m : ℕ}
    (hparity : KyFanPrefixParityStatement n m) :
    KyFanPrefixChainStatement n m := by
  intro label hantipodal hno
  have hodd := hparity label hantipodal hno
  have hpos : 0 < (positiveAlternatingPrefixLabelChains label).card := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  exact ⟨P, (by
    have hP' : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    exact hP'.1)⟩

theorem exists_complementaryComparable_of_kyFanPrefixParity_of_lt {n m : ℕ}
    (hmn : m < n) (hparity : KyFanPrefixParityStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg := by
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨P, hstrict⟩ := kyFanPrefixChainStatement_of_parity hparity label hantipodal hno
  exact not_strictMono_fin_of_lt hmn ⟨fun i => (label (P.prefixChain i)).index, hstrict⟩

theorem not_noComplementaryComparableLabels_of_kyFanPrefixParity_of_lt {n m : ℕ}
    (hmn : m < n) (hparity : KyFanPrefixParityStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label := by
  intro hno
  obtain ⟨P, hstrict⟩ := kyFanPrefixChainStatement_of_parity hparity label hantipodal hno
  exact not_strictMono_fin_of_lt hmn ⟨fun i => (label (P.prefixChain i)).index, hstrict⟩

theorem exists_complementaryComparable_of_kyFanPrefixModFour_of_lt {n m : ℕ}
    (hmn : m < n) (hmodFour : KyFanPrefixModFourStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg :=
  exists_complementaryComparable_of_kyFanPrefixParity_of_lt hmn
    ((kyFanPrefixParityStatement_iff_modFour (Nat.zero_lt_of_lt hmn)).mpr hmodFour)
    label hantipodal

theorem not_noComplementaryComparableLabels_of_kyFanPrefixModFour_of_lt {n m : ℕ}
    (hmn : m < n) (hmodFour : KyFanPrefixModFourStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label :=
  not_noComplementaryComparableLabels_of_kyFanPrefixParity_of_lt hmn
    ((kyFanPrefixParityStatement_iff_modFour (Nat.zero_lt_of_lt hmn)).mpr hmodFour)
    label hantipodal

/-! ### Endpoint-count form of the remaining Ky Fan parity frontier -/

theorem even_card_of_fixedPointFree_involutive {α : Type*} [Fintype α]
    (e : α ≃ α) (hinv : Function.Involutive e) (hfree : ∀ x : α, e x ≠ x) :
    Even (Fintype.card α) := by
  classical
  let p : Equiv.Perm α := e
  have hp2 : p ^ 2 = 1 := by
    ext x
    exact hinv x
  have hsupp : p.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support]
    exact hfree x
  have htwo : 2 ∣ Fintype.card α := by
    simpa [hsupp] using Equiv.Perm.two_dvd_card_support (σ := p) hp2
  exact even_iff_two_dvd.mpr htwo

/--
The numerical core of the Prescott-Su/Fan path count: if paths come in
antipodal pairs, every path has two endpoints, and the endpoints are exactly
the two base endpoints plus equally many positive and negative top endpoints,
then the positive top endpoints are odd.
-/
theorem odd_positive_endpoints_of_antipodal_path_count
    (positive negative pathCount : ℕ)
    (hneg : negative = positive)
    (hpath_even : Even pathCount)
    (hendpoints : 2 + positive + negative = 2 * pathCount) :
    Odd positive := by
  rcases hpath_even with ⟨r, hr⟩
  rw [Nat.odd_iff]
  omega

theorem sigma_endpoint_card_eq_two_mul_paths
    {Path : Type*} [Fintype Path]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2) :
    Fintype.card (Σ p : Path, Endpoint p) = 2 * Fintype.card Path := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ p : Path, Fintype.card (Endpoint p)) = ∑ _p : Path, 2 := by
      exact Finset.sum_congr rfl fun p _ => htwo p
    _ = 2 * Fintype.card Path := by
      simp [mul_comm]

theorem endpoint_card_eq_base_add_positive_add_negative
    {Endpoint Base Positive Negative : Type*}
    [Fintype Endpoint] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (classify : Endpoint ≃ Base ⊕ (Positive ⊕ Negative)) :
    Fintype.card Endpoint =
      Fintype.card Base + Fintype.card Positive + Fintype.card Negative := by
  have hcard := Fintype.card_congr classify
  rw [hcard]
  simp [Fintype.card_sum]
  omega

theorem endpoint_count_eq_two_mul_paths_of_endpoint_equiv
    {Path Base Positive Negative : Type*}
    [Fintype Path] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative))
    (hbase : Fintype.card Base = 2) :
    2 + Fintype.card Positive + Fintype.card Negative = 2 * Fintype.card Path := by
  have hpath := sigma_endpoint_card_eq_two_mul_paths Endpoint htwo
  have hclass := endpoint_card_eq_base_add_positive_add_negative classify
  rw [hbase] at hclass
  omega

theorem odd_card_positive_endpoints_of_path_endpoint_equiv
    {Path Base Positive Negative : Type*}
    [Fintype Path] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative))
    (hbase : Fintype.card Base = 2)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  exact odd_positive_endpoints_of_antipodal_path_count
    (Fintype.card Positive) (Fintype.card Negative) (Fintype.card Path)
    hneg
    (even_card_of_fixedPointFree_involutive pathAntipode hinv hfree)
    (endpoint_count_eq_two_mul_paths_of_endpoint_equiv Endpoint htwo classify hbase)

abbrev PositivePrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  {P : SignedPermutation n // P ∈ positiveAlternatingPrefixLabelChains label}

abbrev NegativePrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  {P : SignedPermutation n // P ∈ negativeAlternatingPrefixLabelChains label}

/--
Packaged endpoint data for the Prescott-Su/Fan path proof.  The only
remaining combinatorial construction is to instantiate this structure for the
octahedral flag graph of a concrete Tucker labeling.
-/
structure PathEndpointDecomposition (Positive Negative : Type) [Fintype Positive]
    [Fintype Negative] where
  Path : Type
  Base : Type
  Endpoint : Path → Type
  instPath : Fintype Path
  instBase : Fintype Base
  instEndpoint : ∀ p : Path, Fintype (Endpoint p)
  pathAntipode : Path ≃ Path
  pathAntipode_involutive : Function.Involutive pathAntipode
  pathAntipode_fixedPointFree : ∀ p : Path, pathAntipode p ≠ p
  endpoint_card_two : ∀ p : Path, Fintype.card (Endpoint p) = 2
  classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative)
  base_card : Fintype.card Base = 2

namespace PathEndpointDecomposition

theorem positive_card_odd {Positive Negative : Type} [Fintype Positive] [Fintype Negative]
    (D : PathEndpointDecomposition Positive Negative)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  letI := D.instPath
  letI := D.instBase
  letI : ∀ p : D.Path, Fintype (D.Endpoint p) := D.instEndpoint
  exact odd_card_positive_endpoints_of_path_endpoint_equiv
    D.Endpoint D.pathAntipode D.pathAntipode_involutive D.pathAntipode_fixedPointFree
    D.endpoint_card_two D.classify D.base_card hneg

end PathEndpointDecomposition

abbrev KyFanPrefixPathEndpointDecomposition {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  PathEndpointDecomposition (PositivePrefixChainType label) (NegativePrefixChainType label)

/--
Ky Fan prefix parity follows from the structured endpoint decomposition.  This
is now the concrete finite-combinatorics frontier for the general Tucker
lemma: build the path graph and endpoint classifier.
-/
theorem kyFanPrefixParity_of_pathEndpointDecomposition {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (D : KyFanPrefixPathEndpointDecomposition label) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  have hneg :
      Fintype.card (NegativePrefixChainType label) =
        Fintype.card (PositivePrefixChainType label) := by
    simp [PositivePrefixChainType, NegativePrefixChainType,
      positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd := D.positive_card_odd hneg
  simpa [PositivePrefixChainType] using hodd

def KyFanPrefixPathEndpointDecompositionStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanPrefixPathEndpointDecomposition label)

theorem kyFanPrefixParityStatement_of_pathEndpointDecomposition {n m : ℕ}
    (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m) :
    KyFanPrefixParityStatement n m := by
  intro label hantipodal hno
  rcases hpaths label hantipodal hno with ⟨D⟩
  exact kyFanPrefixParity_of_pathEndpointDecomposition label hantipodal D

theorem exists_complementaryComparable_of_pathEndpointDecomposition_of_lt {n m : ℕ}
    (hmn : m < n) (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg :=
  exists_complementaryComparable_of_kyFanPrefixParity_of_lt hmn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths) label hantipodal

theorem not_noComplementaryComparableLabels_of_pathEndpointDecomposition_of_lt {n m : ℕ}
    (hmn : m < n) (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label :=
  not_noComplementaryComparableLabels_of_kyFanPrefixParity_of_lt hmn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths) label hantipodal

theorem tuckerLemmaStatement_of_kyFanPrefixParity {n : ℕ} (hn : 1 ≤ n)
    (hparity : KyFanPrefixParityStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefix hn (kyFanPrefixChainStatement_of_parity hparity)

/-- The one-dimensional Tucker case also follows through the Ky Fan prefix
parity pipeline, not only by the direct ad-hoc proof below. -/
theorem tuckerLemmaStatement_one_of_kyFanPrefixParity : TuckerLemmaStatement 1 :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega) kyFanPrefixParityStatement_one

theorem tuckerLemmaStatement_of_kyFanPrefixModFour {n : ℕ} (hn : 1 ≤ n)
    (hmodFour : KyFanPrefixModFourStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefixParity hn
    ((kyFanPrefixParityStatement_iff_modFour (n := n) (m := n - 1) (by omega)).mpr hmodFour)

theorem tuckerLemmaStatement_one : TuckerLemmaStatement 1 := by
  intro label _
  let z : Fin 1 := ⟨0, by omega⟩
  let X : NonzeroSignedSubset 1 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  exact Fin.elim0 (label X).index

theorem tuckerLemmaStatement_two : TuckerLemmaStatement 2 := by
  classical
  intro label hantipodal
  by_contra hnone
  have hno :
      ∀ X Y : NonzeroSignedSubset 2,
        SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  have hsame :
      ∀ {X Y : NonzeroSignedSubset 2},
        SignedSubset.Le X.1 Y.1 → (label X).positive = (label Y).positive := by
    intro X Y hXY
    by_contra hne
    have hbool : (label X).positive = !((label Y).positive) := by
      cases hx : (label X).positive <;> cases hy : (label Y).positive <;>
        simp [hx, hy] at hne ⊢
    have hindex : (label X).index = ((label Y).neg).index := by
      simp [SignedLabel.neg]
      exact Subsingleton.elim _ _
    exact hno X Y hXY (SignedLabel.ext hbool hindex)
  let z : Fin 2 := ⟨0, by omega⟩
  let o : Fin 2 := ⟨1, by omega⟩
  let P0 : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let P1 : NonzeroSignedSubset 2 :=
    ⟨{ pos := {o}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let N1 : NonzeroSignedSubset 2 := P1.antipode
  let PP : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z, o}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let PN : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z}, neg := {o}, disjoint := by
        simp [z, o] },
      by simp [SignedSubset.Nonzero]⟩
  have hP0PP : (label P0).positive = (label PP).positive :=
    hsame (X := P0) (Y := PP) (by simp [SignedSubset.Le, P0, PP])
  have hP1PP : (label P1).positive = (label PP).positive :=
    hsame (X := P1) (Y := PP) (by simp [SignedSubset.Le, P1, PP])
  have hP0PN : (label P0).positive = (label PN).positive :=
    hsame (X := P0) (Y := PN) (by simp [SignedSubset.Le, P0, PN])
  have hN1PN : (label N1).positive = (label PN).positive :=
    hsame (X := N1) (Y := PN) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, N1, P1, PN])
  have hP0P1 : (label P0).positive = (label P1).positive :=
    hP0PP.trans hP1PP.symm
  have hP0N1 : (label P0).positive = (label N1).positive :=
    hP0PN.trans hN1PN.symm
  have hN1neg : (label N1).positive = !((label P1).positive) := by
    have := congrArg SignedLabel.positive (hantipodal P1)
    simpa [N1, SignedLabel.neg] using this
  have hself : (label P1).positive = !((label P1).positive) := by
    exact hP0P1.symm.trans (hP0N1.trans hN1neg)
  cases (label P1).positive <;> simp at hself

/-- Tucker's lemma is unconditional in the low dimensions already proved here. -/
theorem tuckerLemmaStatement_le_two {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 2) :
    TuckerLemmaStatement n := by
  interval_cases n
  · exact tuckerLemmaStatement_one
  · exact tuckerLemmaStatement_two

/--
The two-dimensional Ky Fan prefix-parity statement is discharged by the direct
two-dimensional Tucker proof above: the `NoComplementaryComparableLabels`
hypothesis is already impossible.
-/
theorem kyFanPrefixParityStatement_two : KyFanPrefixParityStatement 2 1 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_two label hantipodal
  exact False.elim (hno X Y hXY hcomp)

theorem tuckerLemmaStatement_two_of_kyFanPrefixParity : TuckerLemmaStatement 2 :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega) kyFanPrefixParityStatement_two

/-- The path-endpoint frontier is vacuous in dimension one: the
`NoComplementaryComparableLabels` hypothesis contradicts the direct
one-dimensional Tucker proof. -/
theorem kyFanPrefixPathEndpointDecompositionStatement_one :
    KyFanPrefixPathEndpointDecompositionStatement 1 0 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_one label hantipodal
  exact False.elim (hno X Y hXY hcomp)

/-- The path-endpoint frontier is also vacuous in dimension two by the direct
two-dimensional Tucker proof. -/
theorem kyFanPrefixPathEndpointDecompositionStatement_two :
    KyFanPrefixPathEndpointDecompositionStatement 2 1 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_two label hantipodal
  exact False.elim (hno X Y hXY hcomp)

theorem kyFanPrefixPathEndpointDecompositionStatement_le_two {n : ℕ}
    (hnpos : 1 ≤ n) (hnle : n ≤ 2) :
    KyFanPrefixPathEndpointDecompositionStatement n (n - 1) := by
  interval_cases n
  · exact kyFanPrefixPathEndpointDecompositionStatement_one
  · exact kyFanPrefixPathEndpointDecompositionStatement_two

/--
Matoušek's bridge from a too-small Kneser coloring to a Tucker counterexample:
given a proper `(n - 2*k + 1)`-coloring, construct an antipodal sign-vector
labeling with no complementary comparable pair.
-/
def KneserColoringProducesTuckerCounterexample (n k : ℕ) : Prop :=
  ∀ C : KneserVertex n k → Fin (n - 2 * k + 1),
    (∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) →
      ∃ label : NonzeroSignedSubset n → SignedLabel (n - 1),
        (∀ X, label X.antipode = (label X).neg) ∧
          ∀ X Y : NonzeroSignedSubset n,
            SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

theorem kneserColoringProducesTuckerCounterexample_of_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    KneserColoringProducesTuckerCounterexample n k := by
  intro C hC
  refine ⟨matousekTuckerLabel hk hn C, ?_, ?_⟩
  · intro X
    exact matousekTuckerLabel_antipode hk hn C hC X
  · intro X Y hXY
    exact matousekTuckerLabel_no_complementary hk hn C hC X Y hXY

/--
If Tucker's lemma and Matoušek's coloring-to-labeling bridge are available,
the hard Kneser lower bound follows immediately.
-/
theorem kneser_chromatic_lower_bound_from_tucker (n k : ℕ)
    (htucker : TuckerLemmaStatement n)
    (hbridge : KneserColoringProducesTuckerCounterexample n k) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  obtain ⟨label, hantipodal, hno_complementary⟩ := hbridge C hC
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker label hantipodal
  exact hno_complementary X Y hXY hcomp

theorem kneser_chromatic_lower_bound_from_tucker_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  kneser_chromatic_lower_bound_from_tucker n k htucker
    (kneserColoringProducesTuckerCounterexample_of_matousek n k hk hn)

/-- The hard lower bound is elementary for `k = 1`: `KG(n,1)` is complete,
so a proper coloring must inject `n` singleton vertices into the color set. -/
theorem kneser_chromatic_lower_bound_one (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 1),
      ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  have hC_inj : Function.Injective C := by
    intro a b hCab
    by_contra hne
    exact hC a b (kneserGraph_one_adj_of_ne n a b hne) hCab
  have hcard := Fintype.card_le_of_injective C hC_inj
  rw [kneserVertex_card, Nat.choose_one_right, Fintype.card_fin] at hcard
  omega

/-- The lower bound is also unconditional on the boundary `n = 2k`: the
target color type has one element, while the graph has an edge. -/
theorem kneser_chromatic_lower_bound_two_mul (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 1),
      ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  obtain ⟨a, b, hadj⟩ :=
    kneserGraph_exists_adj_of_two_mul_le (n := 2 * k) (k := k) hk (by omega)
  have hfin1 : C a = C b := by
    ext
    omega
  exact hC a b hadj hfin1

/-- Unconditional Chapter 39 for singleton vertices: `KG(n,1)` is the complete
graph on `n` vertices, so it has the expected lower and upper coloring bounds. -/
theorem chapter39_one (n : ℕ) (hn : 2 ≤ n) :
    (∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 2),
        ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 1),
        ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n 1 (by omega) (by omega)
  · exact kneser_chromatic_lower_bound_one n hn

/-- Unconditional Chapter 39 on the boundary `n = 2k`. -/
theorem chapter39_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 2),
        ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 1),
        ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound (2 * k) k hk (by omega)
  · exact kneser_chromatic_lower_bound_two_mul k hk

/-- Unconditional Chapter 39 whenever the Kneser graph has singleton vertices. -/
theorem chapter39_of_k_eq_one {n k : ℕ} (hk_eq : k = 1) (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  subst k
  exact chapter39_one n (by omega)

/-- Unconditional Chapter 39 on the boundary `n = 2k`, in the general theorem's parameters. -/
theorem chapter39_of_two_mul_eq {n k : ℕ} (hk : 1 ≤ k) (hn_eq : n = 2 * k) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  subst n
  exact chapter39_two_mul k hk

/--
Chapter 39 (Lovász's theorem on Kneser graph chromatic number, conditional on
the discrete Tucker lemma): the upper bound is explicit, and the lower bound
is derived from Tucker's lemma via the formalized Matoušek labeling above.

Remaining gap to an unconditional theorem in Mathlib: prove
`TuckerLemmaStatement`.
-/
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n k hk hn
  · exact kneser_chromatic_lower_bound_from_tucker_matousek n k hk hn htucker

/--
Unconditional low-dimensional Chapter 39.  Under the theorem's ordinary
hypotheses, `n ≤ 2` leaves only the already-proved Tucker dimensions, so the
conditional Tucker assumption in `chapter39` is discharged here.
-/
theorem chapter39_low_dim {n k : ℕ} (hnle : n ≤ 2) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemmaStatement_le_two (by omega) hnle)

/--
The same Chapter 39 conclusion from Ky Fan's alternating-chain form.  The
smaller frontier below is the signed-permutation positive-first parity count,
which implies this alternating-chain form.
-/
theorem chapter39_of_kyFan {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hfan : KyFanAlternatingChainStatement n (n - 1)) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemmaStatement_of_kyFan (by omega) hfan)

/--
Chapter 39 from the exact signed-permutation parity count.  This is the
smallest remaining combinatorial frontier in this file.
-/
theorem chapter39_of_kyFanPrefixParity {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hparity : KyFanPrefixParityStatement n (n - 1)) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemmaStatement_of_kyFanPrefixParity (by omega) hparity)

/--
The same conclusion from the equivalent mod-four Ky Fan count.  This is often
the form produced directly by the standard boundary-parity proof.
-/
theorem chapter39_of_kyFanPrefixModFour {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hmodFour : KyFanPrefixModFourStatement n (n - 1)) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemmaStatement_of_kyFanPrefixModFour (by omega) hmodFour)

/--
Chapter 39 from the concrete Prescott-Su/Fan path endpoint decomposition.
This is a tighter frontier than the abstract parity statement: the remaining
work is to construct the finite path decomposition for the octahedral labeling.
-/
theorem chapter39_of_kyFanPrefixPathEndpointDecomposition {n k : ℕ}
    (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hpaths : KyFanPrefixPathEndpointDecompositionStatement n (n - 1)) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39_of_kyFanPrefixParity hk hn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths)

end ProofsInTheBook.Chapter39
