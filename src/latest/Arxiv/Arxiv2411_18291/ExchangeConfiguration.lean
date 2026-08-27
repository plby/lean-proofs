import Arxiv.Arxiv2411_18291.ExchangeIteration

/-!
# The full clique exchange configuration

Lemma `lem:OO` in arXiv:2411.18291, including the two true decompositions,
all distinguished cliques, pairwise disjoint private sets, the frame
admissibility condition, and the explicit bound on the number of edges.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

/-- The distinguished negative clique family in the exchange lemma. Its
cardinality and single-edge intersections ensure it has exactly one member
for each edge of the positive base clique. -/
def IsExchangeFamily (S : ExchangeSystem V q r) (A : Finset (Block V q)) : Prop :=
  A ⊆ S.negative ∧
  A.card = q.choose r ∧
  (∀ e ∈ cliqueEdges r S.base, ∃ Q ∈ A,
    cliqueEdges r Q ∩ cliqueEdges r S.base = {e}) ∧
  (A : Set (Block V q)).Pairwise (fun Q R =>
    Disjoint (Q.val \ S.base.val) (R.val \ S.base.val)) ∧
  (∀ e ∈ S.graph,
    e.val ∩ (S.base.val ∪ A.biUnion Subtype.val) ⊆ S.base.val ∨
      ∃ Q ∈ A, e.val ∩ (S.base.val ∪ A.biUnion Subtype.val) ⊆ Q.val)

/-- Positive cliques meet the distinguished frame in at most one of its
negative pieces. The stronger invariant prevents reuse of far partners. -/
def IsPositiveFrameLocal (S : ExchangeSystem V q r) (A : Finset (Block V q)) : Prop :=
  ∀ Q ∈ S.positive,
    Q.val ∩ (S.base.val ∪ A.biUnion Subtype.val) ⊆ S.base.val ∨
      ∃ N ∈ A, Q.val ∩ (S.base.val ∪ A.biUnion Subtype.val) ⊆ N.val

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem prepared_isExchangeFamily (S : ExchangeSystem V q r) (B : Block W q)
    (f : W ↪ V) (hB : S.base = mapBlock f B)
    (P : PreparedFamily S.graph S.negative S.base (cliqueEdges r B) (fun e => mapBlock f e)) :
    IsExchangeFamily S ((cliqueEdges r B).image P.clique) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
    exact P.clique_mem i hi
  · have hinj : Set.InjOn P.clique (cliqueEdges r B : Set (Block W r)) := by
      intro i hi j hj h
      have h' := congrArg (fun Q : Block V q => Q.val ∩ S.base.val) h
      rw [P.clique_inter_base hi, P.clique_inter_base hj] at h'
      exact mapBlock_injective f (Subtype.ext h')
    rw [card_image_of_injOn hinj, card_cliqueEdges]
  · intro e he
    rw [hB, ← map_cliqueEdges] at he
    obtain ⟨i, hi, hmap⟩ := (mem_mapGraph f (cliqueEdges r B) e).mp he
    refine ⟨P.clique i, mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    simpa only [hmap] using P.clique_edge_inter hi
  · intro Q hQ R hR hQR
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hR
    exact P.private_pairwise hi hj (fun hij => hQR (congrArg P.clique hij))
  · intro e he
    rw [image_biUnion]
    rcases P.admissible he with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨P.clique i, mem_image.mpr ⟨i, hi, rfl⟩, h⟩

theorem prepared_isPositiveFrameLocal (S : ExchangeSystem V q r) (B : Block W q)
    (f : W ↪ V)
    (P : PreparedFamily S.graph S.negative S.base (cliqueEdges r B) (fun e => mapBlock f e))
    (hP : P.Protects S.positive) :
    IsPositiveFrameLocal S ((cliqueEdges r B).image P.clique) := by
  intro Q hQ
  rw [image_biUnion]
  rcases hP.frame_local hQ with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨P.clique i, mem_image.mpr ⟨i, hi, rfl⟩, h⟩

/-- **Clique exchange lemma** (`lem:OO`): an unconditional finite
construction with the paper's quantitative edge bound. -/
theorem exists_clique_exchange (q r : ℕ) (hr : 0 < r) (hqr : r < q) :
    ∃ T : FiniteExchangeSystem q r, ∃ A : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2 ∧
      IsExchangeFamily T.system A := by
  obtain ⟨p, hp, _, _, hseed⟩ := exists_prime_exchange_seed q r hqr
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, _, hEbound⟩ := hseed
  obtain ⟨T, f, hB, ⟨P, _⟩, hcard, _⟩ :=
    exists_prepared_subfamily E hr hqr (cliqueEdges r E.positiveClique) Subset.rfl
  refine ⟨T, (cliqueEdges r E.positiveClique).image P.clique, ?_,
    prepared_isExchangeFamily T.system E.positiveClique f hB P⟩
  have hk : 1 ≤ q.choose r := Nat.choose_pos hqr.le
  calc
    T.system.graph.card ≤ (2 * q.choose r + 1) * E.graph.card := by
      simpa only [card_cliqueEdges] using hcard
    _ ≤ (2 * q.choose r + 1) * ((2 * q) ^ r * q.choose r) :=
      Nat.mul_le_mul_left _ hEbound
    _ ≤ (3 * q.choose r) * ((2 * q) ^ r * q.choose r) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

/-- The exchange construction with opposite-clique intersection and positive
frame locality. It uses a degree-`r` translation in the seed and preserves
positive protection through the attachments, with the same edge bound. -/
theorem exists_local_crossSimple_clique_exchange_with_vertex_bound
    (q r : ℕ) (hr : 0 < r) (hqr : r < q) :
    ∃ T : FiniteExchangeSystem q r, ∃ A : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2 ∧
      IsExchangeFamily T.system A ∧ IsCrossSimple r T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A ∧
      Fintype.card T.Vertex ≤ 6 * q ^ 2 * q.choose r := by
  obtain ⟨p, hp, _, hpq, hseed⟩ := exists_prime_crossSimple_exchange_seed q r hqr
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, _, hEbound, hEcross⟩ := hseed
  obtain ⟨T, f, hB, ⟨P, hP⟩, hcard, hcross, hvertices⟩ :=
    exists_prepared_subfamily_with_vertex_bound E hr hqr
      (cliqueEdges r E.positiveClique) Subset.rfl
  have hk : 1 ≤ q.choose r := Nat.choose_pos hqr.le
  refine ⟨T, (cliqueEdges r E.positiveClique).image P.clique, ?_,
    prepared_isExchangeFamily T.system E.positiveClique f hB P, hcross hEcross,
    prepared_isPositiveFrameLocal T.system E.positiveClique f P hP, ?_⟩
  · calc
      T.system.graph.card ≤ (2 * q.choose r + 1) * E.graph.card := by
        simpa only [card_cliqueEdges] using hcard
      _ ≤ (2 * q.choose r + 1) * ((2 * q) ^ r * q.choose r) :=
        Nat.mul_le_mul_left _ hEbound
      _ ≤ (3 * q.choose r) * ((2 * q) ^ r * q.choose r) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  · calc
      Fintype.card T.Vertex ≤ (2 * q.choose r + 1) * (q * p) := by
        simpa only [card_cliqueEdges, Fintype.card_prod, Fintype.card_fin,
          ZMod.card] using hvertices
      _ ≤ (3 * q.choose r) * (q * (2 * q)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left q hpq)
      _ = _ := by ring

/-- The original local exchange interface follows from the construction that
also keeps track of every vertex introduced by its attachments. -/
theorem exists_local_crossSimple_clique_exchange (q r : ℕ) (hr : 0 < r) (hqr : r < q) :
    ∃ T : FiniteExchangeSystem q r, ∃ A : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2 ∧
      IsExchangeFamily T.system A ∧ IsCrossSimple r T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A := by
  obtain ⟨T, A, hc, hA, hs, hl, _⟩ :=
    exists_local_crossSimple_clique_exchange_with_vertex_bound q r hr hqr
  exact ⟨T, A, hc, hA, hs, hl⟩

/-- The earlier exchange interface follows from the stronger local construction. -/
theorem exists_crossSimple_clique_exchange (q r : ℕ) (hr : 0 < r) (hqr : r < q) :
    ∃ T : FiniteExchangeSystem q r, ∃ A : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2 ∧
      IsExchangeFamily T.system A ∧ IsCrossSimple r T.system.positive T.system.negative := by
  obtain ⟨T, A, hcard, hA, hcross, _⟩ := exists_local_crossSimple_clique_exchange q r hr hqr
  exact ⟨T, A, hcard, hA, hcross⟩

end Arxiv2411_18291
