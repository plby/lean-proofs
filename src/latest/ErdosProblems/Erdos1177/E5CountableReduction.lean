-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5IntersectionCycle
import ErdosProblems.Erdos1177.E5ObstructionGrid

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Countable-core reductions for the Hajnal--Komjáth theorem

This module reduces the remaining infinitary E5 assertion to a theorem about
countable linear triple systems whose finite weak chromatic numbers are
unbounded.  The reduction is useful because every uncountably chromatic triple
system contains many pairwise disjoint countable subhypergraphs of exactly this
kind.
-/

open Cardinal

namespace Erdos1177

universe u

variable {W : Type u}

/-
Triple-system structure passes to a subfamily of edges.
-/
theorem isTripleSystem_of_edges_subset (H : Hypergraph W) (htri : H.IsTripleSystem)
    (A : Set (Set W)) (hA : A ⊆ H.edges) :
    (⟨A⟩ : Hypergraph W).IsTripleSystem := by
  intro e he; specialize htri e; aesop;

/-
Linearity passes to a subfamily of edges.
-/
theorem linear_of_edges_subset (H : Hypergraph W) (hlin : H.Linear)
    (A : Set (Set W)) (hA : A ⊆ H.edges) :
    (⟨A⟩ : Hypergraph W).Linear := by
  intro e he f hf b hb;
  grind +suggestions

/-
A finite-system embedding into an edge subfamily is also an embedding into
its ambient hypergraph.
-/
theorem FTS.embeds_of_edges_subset {F : FTS} (H : Hypergraph W)
    (A : Set (Set W)) (hA : A ⊆ H.edges)
    (hemb : F.Embeds (⟨A⟩ : Hypergraph W)) : F.Embeds H := by
  obtain ⟨ f, hf ⟩ := hemb;
  exact ⟨ f, hf.1, fun e he => hA <| hf.2 e he ⟩

/-- A clean loose cycle in a subhypergraph is a clean loose cycle in the
ambient hypergraph. -/
def CleanLoose7EdgeCycle.ofEdgesSubset (H : Hypergraph W) (A : Set (Set W))
    (hA : A ⊆ H.edges) (c : CleanLoose7EdgeCycle (⟨A⟩ : Hypergraph W)) :
    CleanLoose7EdgeCycle H where
  core := c.core
  edge := c.edge
  core_injective := c.core_injective
  edge_mem := fun i => hA (c.edge_mem i)
  left_mem := c.left_mem
  right_mem := c.right_mem
  core_mem_iff := c.core_mem_iff
  inter_subset_core := c.inter_subset_core

/-- The countable-core formulation with the conclusion already stated as an
embedding. -/
def E5CountableEmbeddingPrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    looseCycle7.Embeds (⟨A⟩ : Hypergraph W)

/-
It is enough to prove E5 for countable edge families with unbounded finite
weak chromatic number.
-/
theorem e5_HK_loose7_of_countable_embedding_principle
    (hp : E5CountableEmbeddingPrinciple.{u}) : E5_HK_loose7.{u} := by
  intro H hH Hlin Huc;
  intro huc
  obtain ⟨A, hA⟩ := exists_exactly_countably_chromatic_subhypergraph_avoid hH Hlin huc (hS := Set.countable_empty) (hB := Set.countable_empty);
  have := hp hH A Hlin Huc hA.1 hA.2.1 hA.2.2.2.2; exact FTS.embeds_of_edges_subset _ _ hA.2.1 this;

/-- A clean-cycle version of the countable-core principle. -/
def E5CountableCleanCyclePrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    Nonempty (CleanLoose7EdgeCycle (⟨A⟩ : Hypergraph W))

/-
The clean-cycle countable-core principle implies E5.
-/
theorem e5_HK_loose7_of_countable_cleanCycle_principle
    (hp : E5CountableCleanCyclePrinciple.{u}) : E5_HK_loose7.{u} := by
  intro H htri hlin huc;
  have := @exists_exactly_countably_chromatic_subhypergraph_avoid H htri hlin;
  intro huc
  obtain ⟨A, hA_countable, hA_subset, hA_avoid, hA_colorable⟩ := this huc (Set.countable_empty) (Set.countable_empty);
  obtain ⟨c, hc⟩ := hp htri A hlin ‹_› hA_countable hA_subset (fun k hk => hA_colorable.right k hk);
  convert! looseCycle7_embeds_of_cleanEdgeCycle htri hlin ( CleanLoose7EdgeCycle.ofEdgesSubset htri A hA_subset ⟨ c, hc, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption ⟩ ) using 1

/-- An edge-intersection-graph version of the countable-core principle. -/
def E5CountableIntersectionCyclePrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    Nonempty (InducedEdgeIntersectionSevenCycle (⟨A⟩ : Hypergraph W))

/-
Producing an induced seven-cycle in every countable unbounded-chromatic
core suffices for the full Hajnal--Komjáth conclusion.
-/
theorem e5_HK_loose7_of_countable_intersectionCycle_principle
    (hp : E5CountableIntersectionCyclePrinciple.{u}) : E5_HK_loose7.{u} := by
  apply e5_HK_loose7_of_countable_cleanCycle_principle;
  intro W H A htri hlin hA hA' hA'';
  obtain ⟨c⟩ := hp H A htri hlin hA hA' hA'';
  exact ⟨ c.toClean ⟨ A ⟩ ( linear_of_edges_subset H hlin A hA' ) ⟩

/-
A stronger avoidance form: after prescribing countably many forbidden
vertices and host edges, there is still a countable exactly-countably-chromatic
core containing a loose seven-cycle.
-/
theorem exists_countable_core_with_loose7_avoid
    (hp : E5CountableEmbeddingPrinciple.{u})
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : Set (Set W),
      A.Countable ∧ A ⊆ H.edges ∧
      (∀ e ∈ A, e ∉ B ∧ e ⊆ Sᶜ) ∧
      (⟨A⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
      (∀ k : ℕ, 0 < k →
        ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) ∧
      looseCycle7.Embeds (⟨A⟩ : Hypergraph W) := by
  -- Apply the theorem `exists_exactly_countably_chromatic_subhypergraph_avoid` to obtain a countable subset `A` of `H.edges` that avoids `S` and `B` and is exactly countably chromatic.
  obtain ⟨A, hA_countable, hA_subset, hA_avoid, hA_colorable, hA_unbounded⟩ := Erdos1177.exists_exactly_countably_chromatic_subhypergraph_avoid (H := H) htri huc hS hB;
  refine' ⟨ A, hA_countable, hA_subset, hA_avoid, hA_colorable, hA_unbounded, _ ⟩;
  convert! hp ⟨ A ⟩ A ( isTripleSystem_of_edges_subset H htri A hA_subset ) ( linear_of_edges_subset H hlin A hA_subset ) hA_countable ( Set.Subset.refl _ ) hA_unbounded using 1

/-
Under the countable principle, an uncountably chromatic linear host has
countably many pairwise vertex-disjoint countable cores, each containing a
loose seven-cycle and having unbounded finite weak chromatic number.
-/
theorem exists_disjoint_countable_cores_with_loose7
    (hp : E5CountableEmbeddingPrinciple.{u})
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ r, (A r).Countable ∧ A r ⊆ H.edges ∧
        (∀ e ∈ A r, e ⊆ Sᶜ) ∧
        (⟨A r⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
        (∀ k, 0 < k → ¬ ∃ c : W → Fin k,
          (⟨A r⟩ : Hypergraph W).ProperColoring c) ∧
        looseCycle7.Embeds (⟨A r⟩ : Hypergraph W)) ∧
      (∀ ⦃r s⦄, r ≠ s →
        Disjoint (⋃ e ∈ A r, e) (⋃ e ∈ A s, e)) := by
  obtain ⟨A, hA⟩ := exists_disjoint_linear_exactly_countably_chromatic_family H htri hlin huc hS;
  refine' ⟨ A, _, hA.2 ⟩;
  intro r
  obtain ⟨hA_countable, hA_subset, hA_avoid, hA_triple, hA_linear, hA_colorable, hA_unbounded⟩ := hA.left r
  exact ⟨hA_countable, hA_subset, hA_avoid, hA_colorable, hA_unbounded, hp _ _ hA_triple hA_linear hA_countable (by
  exact Set.Subset.rfl) (by
  exact hA_unbounded)⟩

end Erdos1177
