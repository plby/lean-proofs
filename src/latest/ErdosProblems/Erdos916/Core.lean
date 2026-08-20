/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 916.
https://www.erdosproblems.com/916

Informal author:
- C. Thomassen

Formal authors:
- OpenAI Codex
-/

import Mathlib

/-!
# Erdős Problem 916

Every finite simple graph on `n ≥ 4` vertices with `2 * n - 2` edges contains a cycle and
a vertex outside the cycle adjacent to at least three distinct vertices of the cycle.

The configuration is called a special `K₄`-subdivision, or `K₄ᵀ`, in the literature.  We
represent its rim by a `SimpleGraph.Walk.IsCycle`; taking a finset of its support removes the
single repetition at the base point of the closed walk.
-/

open scoped Sym2

namespace Erdos916

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A cycle together with a vertex outside it adjacent to at least three cycle vertices. -/
def HasWheelWitness (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (a : V) (p : G.Walk a a) (x : V),
    p.IsCycle ∧ x ∉ p.support ∧
      3 ≤ (G.neighborFinset x ∩ p.support.toFinset).card

namespace HasWheelWitness

/-- The witness proposition is independent of the chosen decidability procedure. -/
theorem decidableRel_iff (G : SimpleGraph V)
    (d₁ d₂ : DecidableRel G.Adj) :
    @HasWheelWitness V _ _ G d₁ ↔ @HasWheelWitness V _ _ G d₂ := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

/-- A wheel witness persists when edges are added to a graph on the same vertex type. -/
theorem mono {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (hH : HasWheelWitness H) : HasWheelWitness G := by
  rcases hH with ⟨a, p, x, hp, hxp, hcard⟩
  refine ⟨a, p.mapLe hHG, x, hp.mapLe hHG, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hxp
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]
    apply hcard.trans
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset] at hy ⊢
    exact ⟨hHG hy.1, hy.2⟩

variable {W : Type v} [Fintype W] [DecidableEq W]

/-- A wheel witness transports along an induced graph embedding. -/
theorem mapEmbedding {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ↪g H) (hG : HasWheelWitness G) : HasWheelWitness H := by
  rcases hG with ⟨a, p, x, hp, hxp, hcard⟩
  let q : H.Walk (f a) (f a) := p.map f.toHom
  have hq : q.IsCycle := hp.map f.injective
  have hxq : f x ∉ q.support := by
    intro hx
    simp only [q, SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, hyp, hyx⟩ := List.mem_map.mp hx
    exact hxp (f.injective hyx ▸ hyp)
  refine ⟨f a, q, f x, hq, hxq, ?_⟩
  have htwo : 2 < (G.neighborFinset x ∩ p.support.toFinset).card := by
    omega
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have map_mem (y : V) (hy : y ∈ G.neighborFinset x ∩ p.support.toFinset) :
      f y ∈ H.neighborFinset (f x) ∩ q.support.toFinset := by
    rw [Finset.mem_inter] at hy ⊢
    constructor
    · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact f.map_adj_iff.mpr hy.1
    · rw [List.mem_toFinset] at hy ⊢
      simp only [q, SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨y, hy.2, rfl⟩
  have hthree :
      2 < (H.neighborFinset (f x) ∩ q.support.toFinset).card := by
    apply Finset.two_lt_card_iff.mpr
    exact ⟨f y₁, f y₂, f y₃, map_mem y₁ hy₁, map_mem y₂ hy₂,
      map_mem y₃ hy₃, f.injective.ne hy₁₂, f.injective.ne hy₁₃,
      f.injective.ne hy₂₃⟩
  omega

/-- A wheel witness transports along any injective graph homomorphism.  Unlike
`mapEmbedding`, the target need not reflect nonedges; this is the form needed
to lift a witness from a spanning subgraph of an induced graph. -/
theorem mapHomOfInjective {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G →g H) (hf : Function.Injective f)
    (hG : HasWheelWitness G) : HasWheelWitness H := by
  rcases hG with ⟨a, p, x, hp, hxp, hcard⟩
  let q : H.Walk (f a) (f a) := p.map f
  have hq : q.IsCycle := hp.map hf
  have hxq : f x ∉ q.support := by
    intro hx
    simp only [q, SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, hyp, hyx⟩ := List.mem_map.mp hx
    exact hxp (hf hyx ▸ hyp)
  refine ⟨f a, q, f x, hq, hxq, ?_⟩
  have htwo : 2 < (G.neighborFinset x ∩ p.support.toFinset).card := by
    omega
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have map_mem (y : V)
      (hy : y ∈ G.neighborFinset x ∩ p.support.toFinset) :
      f y ∈ H.neighborFinset (f x) ∩ q.support.toFinset := by
    rw [Finset.mem_inter] at hy ⊢
    constructor
    · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact f.map_adj hy.1
    · rw [List.mem_toFinset] at hy ⊢
      simp only [q, SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨y, hy.2, rfl⟩
  have hthree :
      2 < (H.neighborFinset (f x) ∩ q.support.toFinset).card := by
    apply Finset.two_lt_card_iff.mpr
    exact ⟨f y₁, f y₂, f y₃, map_mem y₁ hy₁, map_mem y₂ hy₂,
      map_mem y₃ hy₃, hf.ne hy₁₂, hf.ne hy₁₃, hf.ne hy₂₃⟩
  omega

/-- A wheel in an induced subgraph is also a wheel in the ambient graph. -/
theorem induce {G : SimpleGraph V} [DecidableRel G.Adj] (S : Set V)
    [DecidablePred (· ∈ S)] (hS : HasWheelWitness (G.induce S)) :
    HasWheelWitness G :=
  mapEmbedding (SimpleGraph.Embedding.induce S) hS

end HasWheelWitness

/-! ## The four-vertex base case -/

/-- Four embedded vertices in a complete graph give a triangle and a hub. -/
theorem hasWheelWitness_top_of_embedding [DecidableRel (⊤ : SimpleGraph V).Adj]
    (f : Fin 4 ↪ V) : HasWheelWitness (⊤ : SimpleGraph V) := by
  let a := f 0
  let b := f 1
  let c := f 2
  let x := f 3
  have hab : (⊤ : SimpleGraph V).Adj a b := by
    simp [a, b, f.injective.ne]
  have hbc : (⊤ : SimpleGraph V).Adj b c := by
    simp [b, c, f.injective.ne]
  have hca : (⊤ : SimpleGraph V).Adj c a := by
    simp [c, a, f.injective.ne]
  let p : (⊤ : SimpleGraph V).Walk a a :=
    .cons hab (.cons hbc (.cons hca .nil))
  have hp : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    constructor
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [p, a, b, c]
    constructor
    · simp [p]
    · simp [p, a, b, c]
  refine ⟨a, p, x, hp, ?_, ?_⟩
  · simp [p, x, a, b, c]
  · have ha : a ∈ (⊤ : SimpleGraph V).neighborFinset x ∩ p.support.toFinset := by
      simp [p, x, a, b, c]
    have hb : b ∈ (⊤ : SimpleGraph V).neighborFinset x ∩ p.support.toFinset := by
      simp [p, x, a, b, c]
    have hc : c ∈ (⊤ : SimpleGraph V).neighborFinset x ∩ p.support.toFinset := by
      simp [p, x, a, b, c]
    have hneab : a ≠ b := f.injective.ne (by decide)
    have hneac : a ≠ c := f.injective.ne (by decide)
    have hnebc : b ≠ c := f.injective.ne (by decide)
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨a, b, c, ha, hb, hc, hneab, hneac, hnebc⟩
    omega

/-- Every complete graph on at least four vertices has a wheel witness. -/
theorem hasWheelWitness_top (hn : 4 ≤ Fintype.card V) :
    HasWheelWitness (⊤ : SimpleGraph V) := by
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card V := by
    simpa using hn
  obtain ⟨f : Fin 4 ↪ V⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact hasWheelWitness_top_of_embedding f

/-! ## Elementary vertex-deletion facts -/

/-- Deleting a vertex adjacent to `v` lowers the degree of `v` by exactly one. -/
theorem degree_deleteIncidenceSet_of_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {v x : V} (hvx : G.Adj v x) :
    (G.deleteIncidenceSet x).degree v = G.degree v - 1 := by
  have hneighbors :
      (G.deleteIncidenceSet x).neighborFinset v = (G.neighborFinset v).erase x := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteIncidenceSet_adj,
      Finset.mem_erase]
    constructor
    · rintro ⟨hvw, -, hwx⟩
      exact ⟨hwx, hvw⟩
    · rintro ⟨hwx, hvw⟩
      exact ⟨hvw, hvx.ne, hwx⟩
  rw [← G.card_neighborFinset_eq_degree,
    ← (G.deleteIncidenceSet x).card_neighborFinset_eq_degree, hneighbors,
    Finset.card_erase_of_mem]
  rw [SimpleGraph.mem_neighborFinset]
  exact hvx

/-- Deleting a different non-neighbor of `v` does not change the degree of `v`. -/
theorem degree_deleteIncidenceSet_of_not_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {v x : V} (hvx : ¬G.Adj v x) (hvx_ne : v ≠ x) :
    (G.deleteIncidenceSet x).degree v = G.degree v := by
  have hneighbors :
      (G.deleteIncidenceSet x).neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · exact fun h ↦ h.1
    · intro hvw
      exact ⟨hvw, hvx_ne, fun hwx ↦ hvx (hwx ▸ hvw)⟩
  rw [← G.card_neighborFinset_eq_degree,
    ← (G.deleteIncidenceSet x).card_neighborFinset_eq_degree, hneighbors]

/-! ## The induced `K₂,₃` reduction certificate -/

/-- The first two vertices in the three-element part of `K₂,₃`. -/
def firstTwo : Fin 2 ↪ Fin 3 :=
  Fin.castLEEmb (by omega)

/-- The four degree-three indices in a Thomassen--Toft `K₂,₃` reduction. -/
private def fourIndex : Fin 2 ⊕ Fin 2 ↪ Fin 2 ⊕ Fin 3 where
  toFun
    | .inl i => .inl i
    | .inr j => .inr (firstTwo j)
  inj' := by
    intro i j hij
    cases i <;> cases j
    · simp only [Sum.inl.injEq] at hij ⊢
      exact hij
    · simp at hij
    · simp at hij
    · simp only [Sum.inr.injEq] at hij ⊢
      exact firstTwo.injective hij

/--
The local reduction supplied by Thomassen--Toft: an induced `K₂,₃` in which both vertices
of the two-element part and the first two vertices of the three-element part have degree three.

Using a graph embedding makes both injectivity and the fact that the five vertices induce exactly
`K₂,₃` part of the certificate.
-/
structure K23Reduction (G : SimpleGraph V) [DecidableRel G.Adj] where
  copy : completeBipartiteGraph (Fin 2) (Fin 3) ↪g G
  degree_left : ∀ i : Fin 2, G.degree (copy (.inl i)) = 3
  degree_right : ∀ j : Fin 2, G.degree (copy (.inr (firstTwo j))) = 3

namespace K23Reduction

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A vertex in the two-element part. -/
abbrev a (R : K23Reduction G) (i : Fin 2) : V := R.copy (.inl i)

/-- A vertex in the three-element part. -/
abbrev b (R : K23Reduction G) (j : Fin 3) : V := R.copy (.inr j)

/-- The four degree-three vertices, as an embedding into the ambient vertex type. -/
def deletedEmbedding (R : K23Reduction G) : Fin 2 ⊕ Fin 2 ↪ V :=
  fourIndex.trans R.copy.toEmbedding

@[simp]
theorem deletedEmbedding_inl (R : K23Reduction G) (i : Fin 2) :
    R.deletedEmbedding (.inl i) = R.a i := rfl

@[simp]
theorem deletedEmbedding_inr (R : K23Reduction G) (j : Fin 2) :
    R.deletedEmbedding (.inr j) = R.b (firstTwo j) := rfl

@[simp]
theorem degree_deletedEmbedding_inl (R : K23Reduction G) (i : Fin 2) :
    G.degree (R.deletedEmbedding (.inl i)) = 3 := by
  change G.degree (R.copy (.inl i)) = 3
  exact R.degree_left i

@[simp]
theorem degree_deletedEmbedding_inr (R : K23Reduction G) (j : Fin 2) :
    G.degree (R.deletedEmbedding (.inr j)) = 3 := by
  change G.degree (R.copy (.inr (firstTwo j))) = 3
  exact R.degree_right j

/-- The four degree-three vertices deleted in the density induction. -/
def deletedFour (R : K23Reduction G) : Finset V :=
  Finset.univ.map R.deletedEmbedding

@[simp]
theorem card_deletedFour (R : K23Reduction G) : R.deletedFour.card = 4 := by
  simp [deletedFour]

@[simp]
theorem mem_deletedFour_iff (R : K23Reduction G) (x : V) :
    x ∈ R.deletedFour ↔ ∃ i : Fin 2 ⊕ Fin 2, R.deletedEmbedding i = x := by
  simp [deletedFour]

@[simp]
theorem a_mem_deletedFour (R : K23Reduction G) (i : Fin 2) :
    R.a i ∈ R.deletedFour := by
  rw [mem_deletedFour_iff]
  exact ⟨.inl i, rfl⟩

@[simp]
theorem b_firstTwo_mem_deletedFour (R : K23Reduction G) (j : Fin 2) :
    R.b (firstTwo j) ∈ R.deletedFour := by
  rw [mem_deletedFour_iff]
  exact ⟨.inr j, rfl⟩

/-- All five displayed vertices of a reduction are distinct. -/
theorem vertex_injective (R : K23Reduction G) : Function.Injective R.copy :=
  R.copy.injective

/-- Every left vertex is adjacent to every right vertex. -/
theorem adj_a_b (R : K23Reduction G) (i : Fin 2) (j : Fin 3) :
    G.Adj (R.a i) (R.b j) := by
  exact R.copy.map_adj_iff.mpr (by simp)

/-- No two vertices in the two-element part are adjacent. -/
theorem not_adj_a_a (R : K23Reduction G) (i j : Fin 2) :
    ¬G.Adj (R.a i) (R.a j) := by
  intro h
  have h' := R.copy.map_adj_iff.mp h
  simpa using h'

/-- No two vertices in the three-element part are adjacent. -/
theorem not_adj_b_b (R : K23Reduction G) (i j : Fin 3) :
    ¬G.Adj (R.b i) (R.b j) := by
  intro h
  have h' := R.copy.map_adj_iff.mp h
  simpa using h'

/-- The sum of the degrees of the four deleted vertices is twelve. -/
theorem sum_degree_deletedFour (R : K23Reduction G) :
    ∑ x ∈ R.deletedFour, G.degree x = 12 := by
  rw [deletedFour, Finset.sum_map]
  change ∑ i : Fin 2 ⊕ Fin 2, G.degree (R.deletedEmbedding i) = 12
  rw [Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, degree_deletedEmbedding_inl,
    degree_deletedEmbedding_inr]
  norm_num

/-- A reduction necessarily displays five different vertices. -/
theorem five_le_card (R : K23Reduction G) : 5 ≤ Fintype.card V := by
  have hcard : Fintype.card (Fin 2 ⊕ Fin 3) ≤ Fintype.card V :=
    Fintype.card_le_of_injective R.copy R.copy.injective
  simpa using hcard

end K23Reduction

end Erdos916
