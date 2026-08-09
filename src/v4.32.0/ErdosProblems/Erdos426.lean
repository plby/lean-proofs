/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 426.
https://www.erdosproblems.com/forum/thread/426

Informal authors:
- Domagoj Bradač
- Micha Christoph

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/426#post-5643
- https://www.erdosproblems.com/forum/thread/426#post-5775
- https://gist.githubusercontent.com/LorenzoLuccioli/7c10c6803e56a3271ca6ebfc9cfb89ad/raw/9aa347c235591c53684d9ac06050c18b183aea23/Erdos426.lean
- https://gist.githubusercontent.com/LorenzoLuccioli/6740274ef8c8bd77a6c966887a72b198/raw/656e1c8330a75a6fd003efef2a8bcae1966482df/Erdos426.lean
-/
import Mathlib

namespace Erdos426

set_option linter.style.setOption false
-- The generated counting and switching sections need extended heartbeat and
-- recursion budgets.
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.longLine false
-- Local generated proof budgets below exceed the style threshold but are scoped
-- where possible.
set_option linter.style.maxHeartbeats false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

/-! ==================================================================
    Core Definitions and Burnside Machinery
    (originally MainDefs.lean)
    ================================================================== -/

open Finset Function SimpleGraph

attribute [local instance] Classical.propDecidable

/-!
# Core Definitions and Burnside Machinery for Unique Subgraphs

Extracted from Main.lean to break the circular dependency with PolyaWright.lean.
Contains all definitions, basic properties, the group action, and Burnside-related
theorems needed by both Main.lean and PolyaWright.lean.
-/

namespace UniqueSubgraphs

/-! ## Core Definitions -/

/-! ### Isomorphism of graphs -/

/-- The isomorphism equivalence relation on SimpleGraph (Fin n). -/
instance graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G₁ G₂ := Nonempty (G₁.Iso G₂)
  iseqv := {
    refl := fun _ => ⟨Iso.refl⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

/-- The number of isomorphism classes of graphs on Fin n. -/
def numIsoClasses (n : ℕ) : ℕ :=
  Fintype.card (Quotient (graphIsoSetoid n))

/-! ### Paper's normalization constant -/

/-- The normalization constant 2^{n choose 2} / n! from the paper.
    This is the asymptotic count of unlabeled graphs on n vertices (Pólya's theorem). -/
def paperDenom (n : ℕ) : ℝ :=
  (2 ^ n.choose 2 : ℝ) / (Nat.factorial n : ℝ)

theorem paperDenom_pos {n : ℕ} : 0 < paperDenom n := by
  apply div_pos
  · positivity
  · exact Nat.cast_pos.mpr (Nat.factorial_pos n)

/-! ### Unique Subgraphs via SimpleGraph.Subgraph -/

/-- A spanning subgraph of H corresponding to a graph G ≤ H. -/
def spanningSubgraphOf {n : ℕ} {H : SimpleGraph (Fin n)} {G : SimpleGraph (Fin n)}
    (hle : G ≤ H) : H.Subgraph where
  verts := Set.univ
  Adj := G.Adj
  adj_sub ha := hle ha
  edge_vert _ := Set.mem_univ _
  symm := G.symm

/-- G is a **unique subgraph** of H if there is exactly one spanning subgraph of H
    that is isomorphic to G (as an abstract graph). -/
def IsUniqueSubgraph {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! S : H.Subgraph, S.IsSpanning ∧ Nonempty (S.spanningCoe.Iso G)

/-- Equivalent characterization using the lattice order. -/
def IsUniqueSubgraph' {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! G' : SimpleGraph (Fin n), G' ≤ H ∧ Nonempty (G.Iso G')

theorem isUniqueSubgraph_iff {n : ℕ} (G H : SimpleGraph (Fin n)) :
    IsUniqueSubgraph G H ↔ IsUniqueSubgraph' G H := by
  constructor <;> intro h;
  · obtain ⟨ S, hS₁, hS₂ ⟩ := h;
    refine ⟨ S.spanningCoe, ?_, ?_ ⟩ <;> norm_num +zetaDelta at *;
    · exact ⟨ S.spanningCoe_le, hS₁.2.map ( fun f => f.symm ) ⟩;
    · intro y hy a; specialize hS₂ ( spanningSubgraphOf hy ) ?_ ?_ <;> simp_all +decide [ SimpleGraph.Subgraph.IsSpanning ] ;
      · exact fun v => Set.mem_univ v;
      · exact a.symm;
      · ext v w; aesop;
  · obtain ⟨ G', hG', hG'' ⟩ := h;
    refine ⟨ spanningSubgraphOf hG'.1, ?_, ?_ ⟩ <;> simp +decide;
    · refine ⟨ ?_, ?_ ⟩;
      · exact Subgraph.isSpanning_iff.mpr rfl;
      · refine ⟨ hG'.2.some.symm ⟩;
    · intro y hy a;
      have := hG'' ( y.spanningCoe ) ⟨ by
        exact Subgraph.spanningCoe_le y, ⟨ a.symm ⟩ ⟩
      generalize_proofs at *;
      unfold spanningSubgraphOf; aesop;

theorem isUniqueSubgraph_iso_invariant {n : ℕ} {G₁ G₂ H : SimpleGraph (Fin n)}
    (hi : Nonempty (G₁.Iso G₂)) :
    IsUniqueSubgraph G₁ H ↔ IsUniqueSubgraph G₂ H := by
  constructor;
  · rintro ⟨ S, ⟨ hS₁, hS₂ ⟩, hS₃ ⟩;
    refine ⟨ S, ⟨ hS₁, ?_ ⟩, ?_ ⟩;
    · exact ⟨ hS₂.some.trans hi.some ⟩;
    · intro y hy;
      obtain ⟨ f ⟩ := hy.2;
      exact hS₃ y ⟨ hy.1, ⟨ f.trans hi.some.symm ⟩ ⟩;
  · rintro ⟨ S, hS₁, hS₂ ⟩;
    refine ⟨ S, ?_, ?_ ⟩;
    · exact ⟨ hS₁.1, ⟨ hS₁.2.some.trans hi.some.symm ⟩ ⟩;
    · rintro T ⟨ hT₁, ⟨ f ⟩ ⟩;
      exact hS₂ T ⟨ hT₁, ⟨ f.trans hi.some ⟩ ⟩

/-! ### The function f(H) -/

/-- The set of isomorphism classes that are unique subgraphs of H. -/
def uniqueSubgraphClasses {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Quotient (graphIsoSetoid n)) :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsUniqueSubgraph G H)).image
    (Quotient.mk (graphIsoSetoid n))

/-- f(H): the fraction of isomorphism classes that appear as unique subgraphs of H,
    normalized by the paper's denominator 2^{n choose 2} / n!. -/
def fH {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  ((uniqueSubgraphClasses H).card : ℝ) / paperDenom n

/-- f(n): the maximum of f(H) over all n-vertex graphs H. -/
def fSeq (n : ℕ) : ℝ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup' ⟨⊥, mem_univ _⟩ fH

/-! ### Embeddings (auxiliary, used in proofs) -/

/-- An embedding of G into H is a permutation φ of Fin n
    such that every edge of G maps to an edge of H under φ. -/
def IsEmbedding {n : ℕ} (G H : SimpleGraph (Fin n)) (φ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → H.Adj (φ u) (φ v)

/-- The set of all embeddings of G into H. -/
def embeddingFinset {n : ℕ} (G H : SimpleGraph (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (IsEmbedding G H)

/-- The number of embeddings of G into H. -/
def numEmbeddings {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ :=
  (embeddingFinset G H).card

/-- G uniquely embeds into H: there is exactly one embedding (permutation). -/
def UniquelyEmbeds {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  numEmbeddings G H = 1

/-- The automorphism set of G. -/
def autFinset {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun φ => ∀ u v : Fin n, G.Adj u v ↔ G.Adj (φ u) (φ v))

/-- The number of labelled graphs G on Fin n that uniquely embed into H. -/
def numUniquelyEmbedding {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H)).card

/-- The probability that a uniformly random labelled graph uniquely embeds into H. -/
def probUniqueEmb {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  (numUniquelyEmbedding H : ℝ) / (2 ^ (n.choose 2) : ℝ)

/-! ## Basic Properties -/

theorem id_mem_autFinset {n : ℕ} (G : SimpleGraph (Fin n)) :
    (1 : Equiv.Perm (Fin n)) ∈ autFinset G := by
  simp [autFinset]

theorem id_mem_embeddingFinset {n : ℕ} {G H : SimpleGraph (Fin n)}
    (h : ∀ u v, G.Adj u v → H.Adj u v) :
    (1 : Equiv.Perm (Fin n)) ∈ embeddingFinset G H := by
  simp only [embeddingFinset, IsEmbedding, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun u v huv => h u v huv

theorem autFinset_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    (autFinset G).Nonempty :=
  ⟨_, id_mem_autFinset G⟩

theorem probUniqueEmb_nonneg {n : ℕ} (H : SimpleGraph (Fin n)) :
    0 ≤ probUniqueEmb H := by
  apply div_nonneg <;> positivity

theorem probUniqueEmb_le_one {n : ℕ} (H : SimpleGraph (Fin n)) :
    probUniqueEmb H ≤ 1 := by
  have h_card_le : numUniquelyEmbedding H ≤ 2 ^ (n.choose 2) := by
    let S : Finset (SimpleGraph (Fin n)) := Finset.image ( fun s : Finset ( Sym2 ( Fin n ) ) =>
      SimpleGraph.fromEdgeSet ( s.filter fun e => ¬e.IsDiag ) ) ( Finset.powerset (
        Finset.univ.filter fun e => ¬e.IsDiag ) );
    refine le_trans ( Finset.card_le_card (t := S) ?_ ) ?_;
    · intro G hG;
      simp +zetaDelta at *;
      refine ⟨ Finset.filter ( fun e => e ∈ G.edgeSet ) ( Finset.univ.filter fun e => ¬e.IsDiag ), ?_, ?_ ⟩ <;> aesop;
    · refine Finset.card_image_le.trans ?_;
      rw [ show Finset.filter ( fun e => ¬e.IsDiag ) Finset.univ = Finset.univ \ Finset.image ( fun i => Sym2.mk i i ) Finset.univ from ?_, Finset.card_powerset, Finset.card_sdiff ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
      · rw [ Sym2.card ];
        simp +arith +decide [ Nat.choose_succ_succ ];
      · ext ⟨ i, j ⟩ ; aesop;
  exact div_le_one_of_le₀ ( mod_cast h_card_le ) ( by positivity )

theorem fH_nonneg {n : ℕ} (H : SimpleGraph (Fin n)) : 0 ≤ fH H := by
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact le_of_lt paperDenom_pos

theorem fSeq_nonneg (n : ℕ) : 0 ≤ fSeq n := by
  unfold fSeq
  exact le_trans (fH_nonneg ⊥) (Finset.le_sup' _ (mem_univ _))

theorem every_perm_embeds_into_top {n : ℕ} (G : SimpleGraph (Fin n))
    (φ : Equiv.Perm (Fin n)) : IsEmbedding G ⊤ φ := by
  intro u v huv
  rw [SimpleGraph.top_adj]
  exact fun h => (G.ne_of_adj huv) (φ.injective h)

theorem embeddingFinset_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    embeddingFinset G ⊤ = Finset.univ := by
  ext φ
  simp [embeddingFinset, every_perm_embeds_into_top G φ]

theorem numEmbeddings_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    numEmbeddings G ⊤ = Nat.factorial n := by
  simp [numEmbeddings, embeddingFinset_top, Fintype.card_perm]

theorem not_uniquelyEmbeds_top {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    ¬ UniquelyEmbeds G ⊤ := by
  unfold UniquelyEmbeds
  rw [numEmbeddings_top]
  have : 2 ≤ n.factorial := le_trans (by norm_num : 2 ≤ Nat.factorial 2) (Nat.factorial_le hn)
  omega

/-! ## Group Action of Perm on SimpleGraph

We define the action of Perm(Fin n) on SimpleGraph(Fin n) by relabeling vertices.
The orbits are isomorphism classes, and the stabilizer of G is Aut(G).
This connects to Burnside's lemma from Mathlib. -/

/-- The action of Perm(Fin n) on SimpleGraph(Fin n):
    (σ • G).Adj u v ↔ G.Adj (σ⁻¹ u) (σ⁻¹ v). -/
instance permGraphMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  smul σ G := {
    Adj := fun u v => G.Adj (σ⁻¹ u) (σ⁻¹ v)
    symm.symm _ _ h := G.adj_symm h
    loopless := ⟨fun v h => G.loopless.irrefl (σ⁻¹ v) h⟩
  }
  one_smul G := by
    ext u v
    change G.Adj ((1 : Equiv.Perm (Fin n))⁻¹ u) ((1 : Equiv.Perm (Fin n))⁻¹ v) ↔ _
    simp
  mul_smul σ τ G := by
    ext u v
    change G.Adj ((σ * τ)⁻¹ u) ((σ * τ)⁻¹ v) ↔ G.Adj (τ⁻¹ (σ⁻¹ u)) (τ⁻¹ (σ⁻¹ v))
    simp [mul_inv_rev, Equiv.Perm.mul_apply]

@[simp] theorem smul_adj {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (u v : Fin n) : (σ • G).Adj u v ↔ G.Adj (σ⁻¹ u) (σ⁻¹ v) := Iff.rfl

/-! ### Connecting MulAction to autFinset and graphIsoSetoid -/

/-
The orbit relation for the Perm action on SimpleGraph equals
    the graph isomorphism equivalence relation.
-/
theorem orbitRel_eq_graphIsoSetoid (n : ℕ) :
    MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) = graphIsoSetoid n := by
  ext G H;
  constructor;
  · rintro ⟨ σ, rfl ⟩;
    refine ⟨ ?_, ?_ ⟩;
    exacts [ σ⁻¹, by simp +decide [ SimpleGraph.adj_comm ] ];
  · rintro ⟨ f ⟩;
    use f.toEquiv.symm;
    ext u v; simp +decide [ f.map_adj_iff ] ;

/-
σ fixes G under the action iff σ⁻¹ is an automorphism of G.
-/
theorem mem_fixedBy_iff_inv_mem_autFinset {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) :
    G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ ↔ σ⁻¹ ∈ autFinset G := by
  simp +decide [ MulAction.mem_fixedBy, autFinset ];
  constructor;
  · intro h u v; replace h := congr_arg ( fun G => G.Adj u v ) h; aesop;
  · intro h; ext u v; simp +decide [ h u v, SimpleGraph.adj_comm ] ;

/-
autFinset is closed under inversion.
-/
theorem autFinset_inv_mem {n : ℕ} {G : SimpleGraph (Fin n)} {σ : Equiv.Perm (Fin n)}
    (h : σ ∈ autFinset G) : σ⁻¹ ∈ autFinset G := by
  unfold autFinset at *;
  simp +zetaDelta at *;
  grind

/-
σ fixes G iff σ is an automorphism.
-/
theorem mem_fixedBy_iff_mem_autFinset {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) :
    G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ ↔ σ ∈ autFinset G := by
  constructor;
  · intro h;
    convert autFinset_inv_mem _;
    · exact inv_eq_iff_eq_inv.mp rfl
    · exact (mem_fixedBy_iff_inv_mem_autFinset σ G).mp h;
  · grind +suggestions

/-
The number of orbits of Perm on SimpleGraph equals numIsoClasses.
-/
theorem card_orbits_eq_numIsoClasses (n : ℕ) :
    Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)))) =
    numIsoClasses n := by
  have h_orbitRel_eq_graphIsoSetoid : MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) = graphIsoSetoid n := by
    exact orbitRel_eq_graphIsoSetoid n;
  rw [ h_orbitRel_eq_graphIsoSetoid ];
  rfl

/-
Burnside's lemma applied to this action:
    Σ_σ |Fix(σ)| = numIsoClasses(n) * n!
-/
theorem burnside_applied (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) =
    numIsoClasses n * Nat.factorial n := by
  convert MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ( Equiv.Perm ( Fin n ) ) ( SimpleGraph ( Fin n ) ) using 1;
  rw [ card_orbits_eq_numIsoClasses, Fintype.card_perm ];
  norm_num

/-
Double counting: Σ_σ |Fix(σ)| = Σ_G |Aut(G)|
-/
theorem sum_fixedBy_eq_sum_autFinset (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ)).card =
    ∑ G : SimpleGraph (Fin n), (autFinset G).card := by
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ];
  congr! 2;
  convert Finset.card_filter ( fun σ : Equiv.Perm ( Fin n ) => σ ∈ autFinset _ ) Finset.univ using 2;
  any_goals exact ‹SimpleGraph ( Fin n ) ›;
  · rw [ Finset.card_filter ];
    congr! 2;
    expose_names; exact mem_fixedBy_iff_mem_autFinset x_1 x;
  · simp +decide [ Fintype.card_subtype ]

/-
Combined: Σ_G |Aut(G)| = numIsoClasses(n) * n!
-/
theorem sum_autFinset_eq (n : ℕ) :
    (∑ G : SimpleGraph (Fin n), (autFinset G).card : ℕ) =
    numIsoClasses n * Nat.factorial n := by
  convert burnside_applied n;
  convert sum_fixedBy_eq_sum_autFinset n |> Eq.symm using 1;
  simp +decide [ Fintype.card_subtype ]

/-
The number of graphs with non-trivial automorphisms is bounded.
-/
theorem nontrivial_aut_bound (n : ℕ) :
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      (autFinset G).card ≠ 1)).card : ℝ) ≤
    (numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) - (2 ^ n.choose 2 : ℝ) := by
  have h_aut_bound : (∑ G : SimpleGraph (Fin n), (autFinset G).card : ℝ) = (numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) := by
    exact_mod_cast sum_autFinset_eq n;
  have h_card_SimpleGraph : (Fintype.card (SimpleGraph (Fin n)) : ℝ) = 2 ^ (Nat.choose n 2) := by
    rw [ Fintype.card_eq_nat_card ];
    have h_card_simpleGraph : Fintype.card (SimpleGraph (Fin n)) = Finset.card (Finset.powerset (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2))) := by
      refine Finset.card_bij (fun G _ => Finset.filter ( fun e => G.Adj e.1 e.2 ) ( Finset.univ.filter ( fun e : Fin n × Fin n => e.1 < e.2 ) )) ?_ ?_ ?_;
      · grind +splitImp;
      · intro G₁ _ G₂ _ h; ext u v; by_cases hu : u < v <;> by_cases hv : v < u <;> simp_all +decide [ Finset.ext_iff ] ;
        · simpa [ SimpleGraph.adj_comm ] using h v u hv;
        · simp_all +decide [ le_antisymm hv hu ];
      · intro b hb;
        refine ⟨ SimpleGraph.mk fun u v => u < v ∧ ( u, v ) ∈ b ∨ v < u ∧ ( v, u ) ∈ b, ?_, ?_ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
        grind;
    rw [ Nat.card_eq_fintype_card, h_card_simpleGraph, Finset.card_powerset ];
    rw [ show Finset.filter ( fun e : Fin n × Fin n => e.1 < e.2 ) Finset.univ = Finset.biUnion ( Finset.univ : Finset ( Fin n ) ) fun i => Finset.image ( fun j => ( i, j ) ) ( Finset.Ioi i ) from ?_, Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ fun x y hxy => by injection hxy ] ; norm_num [ Nat.choose_two_right ];
      convert Finset.sum_range_id n using 1;
      rw [ ← Finset.sum_range_reflect, Finset.sum_range ];
    · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
    · ext ⟨i, j⟩; simp [Finset.mem_biUnion, Finset.mem_image];
  have h_card_aut_bound : (∑ G : SimpleGraph (Fin n), (if (autFinset G).card = 1 then 1 else (autFinset G).card) : ℝ) ≥ (∑ G : SimpleGraph (Fin n), (if (autFinset G).card = 1 then 1 else 2)) := by
    gcongr;
    split_ifs <;> norm_cast ; linarith [ show Finset.card ( autFinset ‹_› ) ≥ 2 from Finset.one_lt_card.2 <| by obtain ⟨ σ, hσ ⟩ := autFinset_nonempty ‹_› ; obtain ⟨ τ, hτ ⟩ := Finset.exists_mem_ne ( show 1 < Finset.card ( autFinset ‹_› ) from lt_of_le_of_ne ( Finset.card_pos.2 ⟨ σ, hσ ⟩ ) <| Ne.symm <| by aesop ) σ; use σ, hσ, τ, hτ.1; aesop ];
  have h_card_aut_bound : (∑ G : SimpleGraph (Fin n), (if (autFinset G).card = 1 then 1 else (autFinset G).card) : ℝ) = (∑ G : SimpleGraph (Fin n), (autFinset G).card : ℝ) := by
    exact Finset.sum_congr rfl fun x hx => by aesop;
  simp_all +decide [ Finset.sum_ite ];
  linarith [ show ( Finset.card ( Finset.filter ( fun x : SimpleGraph ( Fin n ) => # ( autFinset x ) = 1 ) Finset.univ ) : ℝ ) + Finset.card ( Finset.filter ( fun x : SimpleGraph ( Fin n ) => ¬# ( autFinset x ) = 1 ) Finset.univ ) = Fintype.card ( SimpleGraph ( Fin n ) ) from mod_cast by rw [ Finset.card_filter_add_card_filter_not ] ; simp +decide ]

/-
Fintype.card (SimpleGraph (Fin n)) = 2^(n choose 2)
-/
theorem card_simpleGraph (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  have h_bij : Fintype.card (SimpleGraph (Fin n)) = Fintype.card {s : Finset (Fin n × Fin n) | ∀ x y, (x, y) ∈ s → x < y} := by
    refine Fintype.card_congr ?_;
    refine Equiv.ofBijective ( fun G => ⟨ Finset.filter ( fun p => G.Adj p.1 p.2 ) ( Finset.univ.filter fun p => p.1 < p.2 ), ?_ ⟩ ) ⟨ ?_, ?_ ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    · aesop;
    · intro G₁ G₂ h; ext u v; by_cases hu : u < v <;> by_cases hv : v < u <;> simp_all +decide [ Finset.ext_iff, SimpleGraph.adj_comm ] ;
      · simpa [ SimpleGraph.adj_comm ] using h v u hv;
      · simp_all +decide [ le_antisymm hv hu ];
    · intro a ha;
      refine ⟨ SimpleGraph.mk fun x y => x < y ∧ ( x, y ) ∈ a ∨ y < x ∧ ( y, x ) ∈ a, ?_ ⟩;
      grind;
  -- The number of subsets of the set of pairs (x, y) with x < y is 2^(n choose 2).
  have h_subsets : Fintype.card {s : Finset (Fin n × Fin n) | ∀ x y, (x, y) ∈ s → x < y} = 2 ^ (Finset.card (Finset.filter (fun p => p.1 < p.2) (Finset.univ : Finset (Fin n × Fin n)))) := by
    rw [ Fintype.card_of_subtype ];
    case s => exact Finset.powerset ( Finset.filter ( fun p => p.1 < p.2 ) ( Finset.univ : Finset ( Fin n × Fin n ) ) );
    · rw [ Finset.card_powerset ];
    · grind;
  convert h_bij.trans h_subsets using 2;
  rw [ Nat.choose_two_right, Finset.card_filter ];
  erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite ];
  rw [ ← Finset.sum_range_id ];
  simp +decide [ Finset.filter_lt_eq_Ioi ];
  rw [ ← Finset.sum_range_reflect, Finset.sum_range ]

end UniqueSubgraphs

/-! ==================================================================
    Helper Lemmas (EdgeSlot, graph encoding, low-degree set)
    (originally Helpers.lean)
    ================================================================== -/

/-!
# Helper Lemmas for Unique Subgraphs Are Rare

Sorry-free infrastructure supporting the proof of `per_perm_switch_bound`
and `reduction_to_dense` in the main formalization.
-/

open Finset Function SimpleGraph

namespace UniqueSubgraphs

/-! ## Graph ↔ Bool Bijection

The canonical bijection `SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool)`,
encoding each graph by its edge indicator function on ordered pairs `(i,j)` with `i < j`.
-/

/-- The set of "edge slots": pairs (i,j) with i < j in Fin n.
    These represent potential edges in a simple graph on Fin n. -/
def EdgeSlot (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

instance edgeSlotFintype (n : ℕ) : Fintype (EdgeSlot n) := Subtype.fintype _
instance edgeSlotDecidableEq (n : ℕ) : DecidableEq (EdgeSlot n) := Subtype.instDecidableEq

/-- The cardinality of edge slots equals n choose 2. -/
theorem card_edgeSlot (n : ℕ) : Fintype.card (EdgeSlot n) = n.choose 2 := by
  have h_comb : Finset.card (Finset.filter (fun p => p.1 < p.2) (Finset.univ : Finset (Fin n × Fin n))) = Nat.choose n 2 := by
    rw [ Nat.choose_two_right, Finset.card_filter ]
    convert Finset.sum_range_id n using 1
    erw [ Finset.sum_product ]
    simp +decide [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ]
    rw [ ← Finset.sum_range_reflect, Finset.sum_range ]
  change Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2
  rw [Fintype.card_subtype]
  exact h_comb

/-- Encode a simple graph as a Boolean function on edge slots. -/
def graphEncode {n : ℕ} (G : SimpleGraph (Fin n)) : EdgeSlot n → Bool :=
  fun ⟨⟨i, j⟩, _⟩ => decide (G.Adj i j)

/-- Decode a Boolean function on edge slots into a simple graph. -/
def graphDecode {n : ℕ} (f : EdgeSlot n → Bool) : SimpleGraph (Fin n) where
  Adj i j :=
    if h : i < j then f ⟨⟨i, j⟩, h⟩ = true
    else if h' : j < i then f ⟨⟨j, i⟩, h'⟩ = true
    else False
  symm.symm i j hij := by
    show (if h : j < i then _ else if h' : i < j then _ else _)
    by_cases h1 : i < j <;> by_cases h2 : j < i <;> simp_all; omega
  loopless := by
    constructor; intro i
    show ¬ (if h : i < i then _ else if h' : i < i then _ else _)
    simp

/-- The graph encoding is a bijection between SimpleGraph (Fin n) and (EdgeSlot n → Bool). -/
def graphEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool) where
  toFun := graphEncode
  invFun := graphDecode
  left_inv G := by
    ext i j
    simp only [graphEncode, graphDecode]
    by_cases h1 : i < j
    · simp [h1, decide_eq_true_eq]
    · by_cases h2 : j < i
      · simp [h1, h2, decide_eq_true_eq, G.adj_comm]
      · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hij; simp [SimpleGraph.irrefl]
  right_inv f := by
    ext ⟨⟨i, j⟩, h⟩
    simp only [graphEncode, graphDecode, h, dite_true]
    simp

/-- The graph encoding composed with a Fin equivalence. -/
noncomputable def graphEquivBool (n : ℕ) :
    SimpleGraph (Fin n) ≃ (Fin (Fintype.card (EdgeSlot n)) → Bool) :=
  (graphEquiv n).trans (Equiv.arrowCongr (Fintype.equivFin (EdgeSlot n)) (Equiv.refl Bool))

/-- Key property: the encoding preserves the uniform counting measure.
    Since graphEquiv is a bijection, #{G : P(G)} = #{x : P(graphDecode x)}. -/
theorem graphEquiv_card_filter {n : ℕ} (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
    (Finset.univ.filter (fun x : EdgeSlot n → Bool => P (graphDecode x))).card := by
  apply Finset.card_bij (fun G _ => graphEncode G)
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    have : graphDecode (graphEncode G) = G := (graphEquiv n).left_inv G
    rw [this]; exact hG
  · intro _ _ _ _ h; exact (graphEquiv n).injective h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact ⟨graphDecode f, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hf,
      (graphEquiv n).right_inv f⟩

/-! ## Low-Degree Set Infrastructure -/

/-
In a graph with at most C*n edges, at least n/2 vertices have degree ≤ 4*C.
    Proof: by the handshaking lemma, Σ deg(v) = 2*e ≤ 2*C*n. At most n/2 vertices
    can have degree > 4*C (otherwise the sum exceeds n/2 * 4*C + 0 = 2*C*n).
-/
lemma low_degree_set_large {n : ℕ} (C : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.edgeFinset.card ≤ C * n) :
    n / 2 ≤ (Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 * C)).card := by
  have h_sum_degrees : ∑ v : Fin n, G.degree v ≤ 2 * C * n := by
    rw [ SimpleGraph.sum_degrees_eq_twice_card_edges ] ; linarith;
  -- Let $H$ be the set of high-degree vertices, i.e., vertices with degree greater than $4C$.
  set H := Finset.filter (fun v => G.degree v > 4 * C) (Finset.univ : Finset (Fin n)) with hH_def;
  -- Then $|H| * (4C + 1) \leq \sum_{v \in H} \deg(v) \leq \sum_{v} \deg(v) \leq 2Cn$.
  have h_card_H : H.card * (4 * C + 1) ≤ 2 * C * n := by
    exact le_trans ( by simpa using Finset.sum_le_sum fun v ( hv : v ∈ H ) => Nat.succ_le_of_lt <| Finset.mem_filter.mp hv |>.2 ) ( h_sum_degrees.trans' <| Finset.sum_le_sum_of_subset <| Finset.filter_subset _ _ );
  rw [ show ( Finset.filter ( fun v => G.degree v ≤ 4 * C ) Finset.univ ) = Finset.univ \ H by ext; aesop, Finset.card_sdiff ] ; norm_num;
  exact Nat.le_sub_of_add_le ( by nlinarith [ Nat.div_mul_le_self n 2 ] )

/-! ## Switch Condition Properties -/

/-- The paper's switch condition. -/
def IsIdSwitch' {n : ℕ} (Hc G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  (∀ w : Fin n, Hc.Adj u w → ¬Hc.Adj v w → G.Adj v w) ∧
  (∀ w : Fin n, Hc.Adj v w → ¬Hc.Adj u w → G.Adj u w)

/-
IsIdSwitch is always False for adjacent pairs because it requires a self-loop.
    If Hc.Adj u v, then v ∈ N_Hc(u) and ¬Hc.Adj v v (no self-loops),
    so the first conjunct requires G.Adj v v, which is always False.
-/
lemma isIdSwitch_false_of_adj {n : ℕ} {Hc G : SimpleGraph (Fin n)} {u v : Fin n}
    (hadj : Hc.Adj u v) : ¬IsIdSwitch' Hc G u v := by
  intro h; unfold IsIdSwitch' at h; specialize h; have := h.1 v; simp_all +decide [ SimpleGraph.adj_comm ] ;

/-
IsIdSwitch is vacuously True for non-adjacent vertices with identical neighborhoods.
    If N_Hc(u) = N_Hc(v) (as sets), then the asymmetric neighborhoods are both empty.
-/
lemma isIdSwitch_true_of_same_nbhd {n : ℕ} {Hc G : SimpleGraph (Fin n)} {u v : Fin n}
    (hne : u ≠ v) (hnbhd : ∀ w : Fin n, Hc.Adj u w ↔ Hc.Adj v w) :
    IsIdSwitch' Hc G u v := by
  constructor <;> intro w <;> by_cases hw : Hc.Adj u w <;> by_cases hw' : Hc.Adj v w <;> simp_all +decide

/-
If Hc has at least two vertices with the same neighborhood ("twins"),
    then the no-switch set is empty.
-/
lemma no_switch_empty_of_twins {n : ℕ} {Hc : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (h : ∀ w, Hc.Adj u w ↔ Hc.Adj v w) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ a b : Fin n, a ≠ b → ¬IsIdSwitch' Hc G a b)).card = 0 := by
  simp_all +decide [ Finset.ext_iff ];
  exact fun G => ⟨ u, v, huv, isIdSwitch_true_of_same_nbhd huv h ⟩

end UniqueSubgraphs
/-! ==================================================================
    Switch Helpers
    (originally SwitchHelpers.lean)
    ================================================================== -/

/-!
# Switch Helpers — Critical-path lemmas for per_perm_switch_bound

Sorry-free infrastructure supporting the Azuma-based switch argument
(Lemma 2.3 core) in the main formalization.

Key results:
- `asymNbhd_card_le_degree`: |N_Hc(u) \ N_Hc(v)| ≤ deg(u)
- `switch_pair_count_lower`: switch probability lower bound for a pair
- `greedy_independent_set`: extraction of independent set from bounded-degree subgraph
- `no_switch_mono`: monotonicity of the no-switch condition
- `switchCount_nonneg`, `switchCount_zero_iff`: switch count properties
- `mean_switchCount_lower`: mean switch count lower bound
-/

open Finset Function SimpleGraph

-- The generated Azuma-switch infrastructure needs a higher ambient heartbeat budget.
set_option maxHeartbeats 1600000

namespace UniqueSubgraphs

/-! ## Asymmetric Neighborhoods -/

/-- The asymmetric neighborhood of u relative to v in Hc:
    {w : Hc.Adj u w ∧ ¬Hc.Adj v w}. -/
def asymNbhd {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w)

/-- The asymmetric neighborhood has cardinality at most the degree. -/
lemma asymNbhd_card_le_degree {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) :
    (asymNbhd Hc u v).card ≤ Hc.degree u := by
  unfold asymNbhd
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [SimpleGraph.mem_neighborFinset]; exact hw.1

/-- For non-adjacent u,v, the total size of both asymmetric neighborhoods
    is at most deg(u) + deg(v). -/
lemma asymNbhd_total_le {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) :
    (asymNbhd Hc u v).card + (asymNbhd Hc v u).card ≤ Hc.degree u + Hc.degree v := by
  exact Nat.add_le_add (asymNbhd_card_le_degree Hc u v) (asymNbhd_card_le_degree Hc v u)

/-! ## Switch Condition (local copy matching Main.lean) -/

/-- The switch condition for a specific pair (u,v). -/
def IsIdSwitch {n : ℕ} (Hc G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  (∀ w : Fin n, Hc.Adj u w → ¬Hc.Adj v w → G.Adj v w) ∧
  (∀ w : Fin n, Hc.Adj v w → ¬Hc.Adj u w → G.Adj u w)

instance isIdSwitchDecidable {n : ℕ} (Hc G : SimpleGraph (Fin n)) (u v : Fin n) :
    Decidable (IsIdSwitch Hc G u v) := by
  unfold IsIdSwitch; infer_instance

/-! ## Switch Probability for a Pair -/

/-- For non-adjacent vertices u,v with degree ≤ d in Hc,
    the number of graphs G satisfying IsIdSwitch Hc G u v
    is at least 2^(n.choose 2 - 2*d). -/
lemma switch_pair_count_lower {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : u ≠ v) (hnadj : ¬Hc.Adj u v) (d : ℕ)
    (hdu : Hc.degree u ≤ d) (hdv : Hc.degree v ≤ d)
    (hdn : 2 * d ≤ n.choose 2) :
    2 ^ (n.choose 2 - 2 * d) ≤
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G u v)).card := by
  have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => (∀ w : Fin n, Hc.Adj u w → ¬Hc.Adj v w → G.Adj v w) ∧ (∀ w : Fin n, Hc.Adj v w → ¬Hc.Adj u w → G.Adj u w)) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ))) := by
    have h_edges : ∀ (S : Finset (Sym2 (Fin n))), S ⊆ Finset.univ.filter (fun e => e.IsDiag = false) → Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - S.card) := by
      intros S hS
      have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) = 2 ^ (Finset.card (Finset.univ.filter (fun e => e.IsDiag = false) \ S)) := by
        have h_edges : Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n))) = Finset.image (fun T : Finset (Sym2 (Fin n)) => SimpleGraph.fromEdgeSet (S ∪ T)) (Finset.powerset (Finset.univ.filter (fun e => e.IsDiag = false) \ S)) := by
          ext G; simp [Finset.mem_image];
          constructor;
          · intro hG; use Finset.filter ( fun e => e ∈ G.edgeSet ) ( Finset.univ.filter ( fun e => ¬e.IsDiag ) \ S ) ; simp_all +decide [ Finset.subset_iff ] ;
            ext v w; simp +decide [ SimpleGraph.fromEdgeSet ] ;
            by_cases hvw : v = w <;> by_cases h : s(v, w) ∈ S <;> simp_all +decide [ SimpleGraph.adj_comm ];
            exact (mem_edgeSet G).mp (hG s(v, w) h);
          · rintro ⟨ T, hT, rfl ⟩ e he; simp_all +decide [ Finset.subset_iff ] ;
        rw [ h_edges, Finset.card_image_of_injOn, Finset.card_powerset ];
        · simp +decide [ Finset.ext_iff ];
        · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
          intro e; replace h_eq := congr_arg ( fun f => f.edgeSet ) h_eq; simp_all +decide [ Set.ext_iff ] ;
          specialize h_eq e; replace hT := @hT e; replace hT' := @hT' e; aesop;
      rw [ h_edges, Finset.card_sdiff ];
      gcongr;
      · norm_num;
      · have h_card : Finset.card (Finset.filter (fun e => e.IsDiag = false) (Finset.univ : Finset (Sym2 (Fin n)))) = Finset.card (Finset.powersetCard 2 (Finset.univ : Finset (Fin n))) := by
          refine Finset.card_bij ( fun e he => Finset.filter ( fun x => x ∈ e ) Finset.univ ) ?_ ?_ ?_ <;> simp +decide [ Finset.mem_powersetCard ];
          · intro a ha; rw [ Finset.card_eq_two ] ;
            rcases a with ⟨ x, y ⟩ ; use x, y ; aesop;
          · simp +contextual [ Finset.ext_iff, Sym2.ext_iff ];
          · intro b hb; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb; use Sym2.mk x y ; aesop;
        aesop;
      · exact Finset.inter_subset_left;
    have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ Finset.image (fun w => Sym2.mk v w) (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) ∪ Finset.image (fun w => Sym2.mk u w) (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ), e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ))) := by
      let S : Finset (Sym2 (Fin n)) := Finset.image (fun w => Sym2.mk v w) (Finset.filter (
        fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) ∪ Finset.image (fun w => Sym2.mk u w) (
          Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ);
      refine le_trans ?_ ( h_edges S ?_ );
      · rw [ Finset.card_union_of_disjoint ];
        · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          · grind;
          · grind;
        · simp +decide [ Finset.disjoint_left, Sym2.eq ];
          rintro _ x hx₁ hx₂ rfl y hy₁ hy₂; contrapose! hnadj; aesop;
      · dsimp [S];
        simp +decide [ Finset.subset_iff ];
        rintro _ ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp +decide [ *, Sym2.eq_swap ];
        · grind;
        · rintro rfl; tauto;
    refine le_trans h_edges ?_;
    refine Finset.card_mono ?_;
    simp +contextual [ Finset.subset_iff, Sym2.forall ];
    exact fun G hG => ⟨ fun w hw₁ hw₂ => hG _ _ <| Or.inl ⟨ w, ⟨ hw₁, hw₂ ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩, fun w hw₁ hw₂ => hG _ _ <| Or.inr ⟨ w, ⟨ hw₁, hw₂ ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩ ⟩;
  have h_constrained_edges : (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ)) ≤ 2 * d := by
    simpa [asymNbhd, two_mul] using
      Nat.add_le_add ((asymNbhd_card_le_degree Hc u v).trans hdu)
        ((asymNbhd_card_le_degree Hc v u).trans hdv)
  exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_left h_constrained_edges _ ) ) h_edges

/-! ## Greedy Independent Set -/

/-- In a graph where a set S of vertices all have degree ≤ d,
    there exists an independent set of size ≥ |S| / (d+1). -/
lemma greedy_independent_set {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (d : ℕ)
    (hdeg : ∀ v ∈ S, G.degree v ≤ d) :
    ∃ I : Finset (Fin n), I ⊆ S ∧
    (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v) ∧
    S.card ≤ I.card * (d + 1) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅;
    · aesop;
    · obtain ⟨v, hv⟩ : ∃ v ∈ S, True := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty hS ) fun v hv => ⟨ v, hv, trivial ⟩;
      have := ih ( S \ ( { v } ∪ G.neighborFinset v ) ) ?_ ?_;
      · obtain ⟨ I, hI₁, hI₂, hI₃ ⟩ := this; use Insert.insert v I; simp_all +decide [ Finset.subset_iff ] ;
        rw [ Finset.card_sdiff ] at hI₃ ; simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun u hu => by have := hI₁ hu; tauto, by rw [ Finset.card_insert_of_notMem fun h => by have := hI₁ h; tauto ] ; nlinarith [ show # ( G.neighborFinset v ∩ S ) ≤ d by exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( hdeg v hv ) ] ⟩;
      · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ v, hv, by tauto ⟩;
      · grind +qlia

/-! ## Switch Count Infrastructure -/

/-- The switch indicator for a fixed pair (u,v). -/
def switchIndicator {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n)
    (G : SimpleGraph (Fin n)) : ℝ :=
  if IsIdSwitch Hc G u v then 1 else 0

/-- The switch count function: sum of switch indicators over all pairs in a set T. -/
def switchCount {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ p ∈ T.offDiag, switchIndicator Hc p.1 p.2 G

/-- switchCount is nonneg -/
lemma switchCount_nonneg {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : 0 ≤ switchCount Hc T G := by
  apply Finset.sum_nonneg
  intro p _
  unfold switchIndicator
  split <;> norm_num

/-- If the switchCount is 0, then no pair in T has a switch. -/
lemma switchCount_zero_iff_no_switch {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) :
    switchCount Hc T G = 0 ↔
    ∀ p ∈ T.offDiag, ¬IsIdSwitch Hc G p.1 p.2 := by
  unfold switchCount
  constructor
  · intro h p hp
    have hsm := Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
      unfold switchIndicator; split <;> norm_num : ∀ p ∈ T.offDiag, (0 : ℝ) ≤ switchIndicator Hc p.1 p.2 G)
    rw [hsm] at h
    have := h p hp
    unfold switchIndicator at this
    split at this <;> simp_all
  · intro h
    apply Finset.sum_eq_zero
    intro p hp
    unfold switchIndicator
    simp [h p hp]

/-- No-switch monotonicity: if all pairs fail the switch condition,
    then pairs in any subset T also fail. -/
lemma no_switch_implies_switchCount_zero {n : ℕ} (Hc G : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (h : ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v) :
    switchCount Hc T G = 0 := by
  rw [switchCount_zero_iff_no_switch]
  intro p hp
  exact h p.1 p.2 (Finset.mem_offDiag.mp hp).2.2

/-- The set of graphs with no switch for all pairs is a subset of
    the set with switchCount = 0. -/
lemma no_switch_subset_switchCount_zero {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)) ⊆
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)) := by
  intro G hG
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact no_switch_implies_switchCount_zero Hc G T hG

/-! ## Mean Switch Count Lower Bound -/

/-- Sum of switch indicators over all graphs equals the number of
    graphs satisfying the switch condition. -/
lemma sum_switchIndicator_eq_card {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) :
    ∑ G : SimpleGraph (Fin n), switchIndicator Hc u v G =
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G u v)).card : ℝ) := by
  unfold switchIndicator
  rw [← Finset.sum_boole]

/-- The total switch count summed over all graphs G equals
    the sum over pairs of the number of satisfying graphs. -/
lemma sum_switchCount_eq {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    ∑ G : SimpleGraph (Fin n), switchCount Hc T G =
    ∑ p ∈ T.offDiag,
      ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        IsIdSwitch Hc G p.1 p.2)).card : ℝ) := by
  unfold switchCount
  rw [Finset.sum_comm]
  congr 1
  ext p
  exact sum_switchIndicator_eq_card Hc p.1 p.2

/-
The mean value of the switch count over all graphs G is at least
    |T.offDiag| * 2^(N - 8C), assuming T is independent in Hc and
    all vertices of T have degree ≤ 4C in Hc.
-/
lemma mean_switchCount_lower {n : ℕ} (Hc : SimpleGraph (Fin n)) (C : ℕ)
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hn : 8 * C ≤ n.choose 2) :
    (T.offDiag.card : ℝ) * (2 : ℝ) ^ (n.choose 2 - 8 * C) ≤
    ∑ G : SimpleGraph (Fin n), switchCount Hc T G := by
  rw [ sum_switchCount_eq, mul_comm ];
  -- Apply the lemma `switch_pair_count_lower` to each pair in $T.offDiag$.
  have h_pair_count : ∀ p ∈ T.offDiag, ((Finset.univ.filter (fun G => IsIdSwitch Hc G p.1 p.2)).card : ℝ) ≥ 2 ^ (n.choose 2 - 8 * C) := by
    intros p hp
    have h_pair_count : ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G p.1 p.2)).card : ℝ) ≥ 2 ^ (n.choose 2 - 2 * (4 * C)) := by
      norm_num +zetaDelta at *;
      exact_mod_cast switch_pair_count_lower Hc p.1 p.2 hp.2.2 ( hT_indep p.1 hp.1 p.2 hp.2.1 hp.2.2 ) ( 4 * C ) ( hT_deg p.1 hp.1 ) ( hT_deg p.2 hp.2.1 ) ( by linarith );
    grind;
  simpa [ mul_comm ] using Finset.sum_le_sum h_pair_count

/-! ## Bounded Differences for switchCount through graphEquiv -/

/-- The bounded-differences constant for switchCount at edge slot e.
    For T independent in Hc:
    - If exactly one endpoint of e is in T: bound = 2·dT(non-T endpoint)
    - Otherwise (both in T or both outside T): bound = 0 -/
def switchBound {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (e : EdgeSlot n) : ℝ :=
  if e.val.1 ∈ T ∧ e.val.2 ∉ T then
    (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.2)).card)
  else if e.val.2 ∈ T ∧ e.val.1 ∉ T then
    (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.1)).card)
  else 0

/-- switchBound is nonneg. -/
lemma switchBound_nonneg {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (e : EdgeSlot n) :
    0 ≤ switchBound Hc T e := by
  unfold switchBound; split_ifs <;> positivity

/-
For T independent in Hc, switchCount Hc T composed with graphDecode
    has bounded differences through the edge-slot encoding.
    Flipping one edge slot changes switchCount by at most switchBound.
-/
lemma switchCount_bounded_diff_edgeSlot {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (e : EdgeSlot n)
    (x y : EdgeSlot n → Bool)
    (hxy : ∀ e' : EdgeSlot n, e' ≠ e → x e' = y e') :
    |switchCount Hc T (graphDecode x) -
     switchCount Hc T (graphDecode y)| ≤
    switchBound Hc T e := by
  unfold switchBound;
  split_ifs <;> simp_all +decide [ switchCount ];
  · -- Let's simplify the expression inside the absolute value.
    suffices h_simp : ∀ p ∈ T.offDiag, |switchIndicator Hc p.1 p.2 (graphDecode x) - switchIndicator Hc p.1 p.2 (graphDecode y)| ≤ if p.1 = e.val.1 ∧ Hc.Adj p.2 e.val.2 then 1 else if p.2 = e.val.1 ∧ Hc.Adj p.1 e.val.2 then 1 else 0 by
      refine le_trans ( by simpa only [ ← Finset.sum_sub_distrib ] using Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_simp ) ?_ );
      simp +decide [ Finset.sum_ite, Finset.filter_and ];
      rw [ two_mul ];
      gcongr;
      · refine le_trans ( Finset.card_le_card (t := Finset.image ( fun v => ( e.val.1, v ) ) (
          Finset.filter ( fun v => Hc.Adj v e.val.2 ) T )) ?_ ) ?_;
        · intro p hp; aesop;
        · exact Finset.card_image_le;
      · refine le_trans ( Finset.card_le_card (t := Finset.image ( fun v => ( v, e.val.1 ) ) (
          Finset.filter ( fun v => Hc.Adj v e.val.2 ) T )) ?_ ) ?_;
        · grind;
        · exact Finset.card_image_le;
    intro p hp; split_ifs <;> simp_all +decide [ switchIndicator ] ;
    · split_ifs <;> norm_num;
    · split_ifs <;> norm_num;
    · unfold IsIdSwitch; simp_all +decide [ graphDecode ] ;
      grind +revert;
  · -- The difference in switch counts is bounded by the number of pairs affected by the edge slot e.
    have h_diff_bound : |∑ p ∈ T.offDiag, (switchIndicator Hc p.1 p.2 (graphDecode x) - switchIndicator Hc p.1 p.2 (graphDecode y))| ≤ ∑ p ∈ T.offDiag, (if p.1 = e.val.2 ∧ Hc.Adj p.2 (e.val.1) then 1 else 0) + ∑ p ∈ T.offDiag, (if p.2 = e.val.2 ∧ Hc.Adj p.1 (e.val.1) then 1 else 0) := by
      rw [ ← Finset.sum_add_distrib ];
      refine le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum ?_ );
      intro p hp; split_ifs <;> simp_all +decide [ switchIndicator ] ;
      · split_ifs <;> norm_num;
      · split_ifs <;> norm_num;
      · unfold IsIdSwitch; simp_all +decide [ graphDecode ] ;
        grind;
    simp_all +decide [ Finset.sum_ite ];
    refine le_trans h_diff_bound ?_;
    rw [ two_mul ];
    gcongr;
    · have h_card_filter : Finset.card (Finset.image (fun p => p.2) (Finset.filter (fun p => p.1 = e.val.2 ∧ Hc.Adj p.2 (e.val.1)) (T.offDiag))) ≤ Finset.card (Finset.filter (fun v => Hc.Adj v (e.val.1)) T) := by
        exact Finset.card_le_card fun x hx => by aesop;
      rwa [ Finset.card_image_of_injOn ] at h_card_filter ; intro p hp q hq ; aesop;
    · refine le_trans ( Finset.card_le_card (t := Finset.image ( fun v => ( v, e.val.2 ) ) (
        Finset.filter ( fun v => Hc.Adj v e.val.1 ) T )) ?_ ) ?_;
      · intro x hx; aesop;
      · exact Finset.card_image_le;
  · rw [ sub_eq_zero, Finset.sum_congr rfl ];
    intro p hp; unfold switchIndicator; simp +decide [ graphDecode ] ;
    unfold IsIdSwitch; simp +decide [ hxy ] ;
    congr! 3;
    · congr! 3;
      · rw [ hxy ] ; aesop;
      · congr! 2;
        rw [ hxy ] ; aesop;
    · congr! 3;
      · grind +suggestions;
      · congr! 2;
        rw [ hxy ];
        rintro rfl; simp_all +decide [ SimpleGraph.adj_comm ];
        exact hT_indep _ ‹_› _ hp.2.1 ( by aesop ) ‹_›

/-! ## Tight Bounded Differences (excluding Hc-edges) -/

/-- Tight bounded-differences constant for switchCount at edge slot e.
    This refines `switchBound` by giving 0 when all of T is adjacent to
    the non-T endpoint (because flipping an Hc-edge doesn't change
    any switch indicator). -/
def switchBoundTight {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (e : EdgeSlot n) : ℝ :=
  if e.val.1 ∈ T ∧ e.val.2 ∉ T then
    if Hc.Adj e.val.1 e.val.2 then 0
    else (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.2)).card)
  else if e.val.2 ∈ T ∧ e.val.1 ∉ T then
    if Hc.Adj e.val.2 e.val.1 then 0
    else (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.1)).card)
  else 0

lemma switchBoundTight_nonneg {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (e : EdgeSlot n) :
    0 ≤ switchBoundTight Hc T e := by
  unfold switchBoundTight; split_ifs <;> positivity

/-
The tight bounded-differences result: for T independent in Hc,
    flipping one edge slot changes switchCount by at most switchBoundTight.
    This is tighter than switchBound because when Hc.Adj u w (with u ∈ T, w ∉ T),
    the switch indicators for pairs in T don't depend on G.Adj u w at all.
-/
lemma switchCount_bounded_diff_tight {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (e : EdgeSlot n)
    (x y : EdgeSlot n → Bool)
    (hxy : ∀ e' : EdgeSlot n, e' ≠ e → x e' = y e') :
    |switchCount Hc T (graphDecode x) -
     switchCount Hc T (graphDecode y)| ≤
    switchBoundTight Hc T e := by
  revert e;
  intro e he; by_cases he' : Hc.Adj e.val.1 e.val.2 <;> by_cases he'' : Hc.Adj e.val.2 e.val.1 <;> simp +decide [ he', he'', switchBoundTight ] ;
  · -- Since $Hc.Adj (e.val.1) (e.val.2)$, the switch indicators for pairs in $T$ do not depend on $G.Adj (e.val.1) (e.val.2)$.
    have h_switch_indicator_indep : ∀ u v : Fin n, u ∈ T → v ∈ T → u ≠ v → (IsIdSwitch Hc (graphDecode x) u v ↔ IsIdSwitch Hc (graphDecode y) u v) := by
      intros u v hu hv huv
      simp [IsIdSwitch, graphDecode];
      grind;
    simp +decide [ switchCount, h_switch_indicator_indep ];
    rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_eq_zero fun p hp => by unfold switchIndicator; specialize h_switch_indicator_indep p.1 p.2; aesop;
  · exact False.elim <| he'' <| he'.symm;
  · exact False.elim <| he' <| he''.symm;
  · simpa [switchBound, switchBoundTight, he', he''] using
      switchCount_bounded_diff_edgeSlot Hc T hT_indep e x y he

end UniqueSubgraphs
/-! ==================================================================
    Pruning Chain Infrastructure
    (originally PruningChain.lean)
    ================================================================== -/

/-!
# Pruning Chain Infrastructure for Claim 2.4
-/

open Finset Function SimpleGraph

namespace UniqueSubgraphs

/-- For any M > 0 and k : ℕ, eventually (n : ℝ) ≥ M * (log n)^k for natural n. -/
lemma eventually_ge_mul_log_pow (M : ℝ) (k : ℕ) (hM : M > 0) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) ≥ M * (Real.log n) ^ k := by
  have h : Filter.Tendsto (fun x : ℝ => M * (Real.log x) ^ k / x) Filter.atTop (nhds 0) := by
    have := @Real.isLittleO_pow_log_id_atTop k
    simpa [mul_div_assoc] using this.const_mul_left M |>.tendsto_div_nhds_zero
  exact Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds zero_lt_one)) |> fun ⟨N, hN⟩ ↦
    ⟨⌈N⌉₊ + 1, fun n hn ↦ by
      have := hN n (Nat.le_of_ceil_le (by linarith))
      rw [div_lt_one (by norm_cast; linarith)] at this
      exact_mod_cast this.le⟩

/-- If B' is independent and w has a neighbor in T ⊆ B', then w ∉ B'. -/
lemma pruning_vertex_not_in_indep {n : ℕ} {Hc : SimpleGraph (Fin n)}
    {B' T : Finset (Fin n)} {w : Fin n}
    (hTB : T ⊆ B')
    (hB'_indep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (hw_has_nbr : ∃ v ∈ T, Hc.Adj v w) :
    w ∉ B' := by
  obtain ⟨v, hvT, hvw⟩ := hw_has_nbr
  specialize hB'_indep v (hTB hvT) w; aesop

/-- If S ⊆ neighborFinset v, then |S| ≤ deg(v). -/
lemma card_le_degree_of_all_adj {n : ℕ} {Hc : SimpleGraph (Fin n)}
    {v : Fin n} {S : Finset (Fin n)}
    (hv_not : v ∉ S) (hadj : ∀ w ∈ S, Hc.Adj v w) :
    S.card ≤ Hc.degree v := by
  exact Finset.card_le_card fun x hx => by aesop

/-- Distinctness of pruning vertices. -/
lemma pruning_chain_vertex_ne {n : ℕ} {Hc : SimpleGraph (Fin n)}
    {T_new : Finset (Fin n)} {w_old w_new : Fin n}
    (hT_sub : ∀ v ∈ T_new, Hc.Adj v w_old)
    (hw_new_not_all : ¬∀ v ∈ T_new, Hc.Adj v w_new) :
    w_old ≠ w_new := by
  contrapose! hw_new_not_all; aesop

end UniqueSubgraphs

/-! ==================================================================
    Multi-level Pruning Chain
    (originally PruningMultiLevel.lean)
    ================================================================== -/

/-!
# Multi-level Pruning Chain for Claim 2.4 (C ≥ 1)

The paper's proof of Claim 2.4 uses an iterative multi-level pruning argument.
Starting from the independent set B', the algorithm checks whether B' is
"controlled" with a threshold τ₀. If not, it prunes to B' ∩ N(w₀) and
checks with a smaller threshold τ₁. After at most 4C levels, the chain must
terminate (by a degree contradiction), yielding a controlled (T, threshold)
pair with a good ratio bound.
-/

open Finset Function SimpleGraph

namespace UniqueSubgraphs

/-! ### Pruning threshold sequence -/

/-- The pruning threshold at level i: ⌊n / (log n)^(6^(i+1))⌋₊ -/
def pruningThresh (n : ℕ) (i : ℕ) : ℕ :=
  ⌊(n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))⌋₊

/-! ### Threshold properties -/

/-- All pruning thresholds at levels ≤ 4C are ≥ 2 for large n. -/
lemma pruningThresh_ge_two (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ i : ℕ, i ≤ 4 * C → pruningThresh n i ≥ 2 := by
  -- Use `eventually_ge_mul_log_pow` with $M = 2$ and $k = 6^{4C+1}$ to get $n₀$ such that $n \geq 2 * (\log n)^{6^{4C+1}}$ for $n \geq n₀$.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) ≥ 2 * (Real.log n) ^ (6 ^ (4 * C + 1)) := by
    convert eventually_ge_mul_log_pow 2 ( 6 ^ ( 4 * C + 1 ) ) ( by norm_num ) using 1;
  refine ⟨ n₀ + 3, fun n hn i hi => Nat.le_floor ?_ ⟩;
  rw [ le_div_iff₀ ] <;> norm_num;
  · refine le_trans ?_ ( hn₀ n ( by linarith ) );
    exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) <| pow_le_pow_right₀ ( by norm_num ) <| by linarith ) zero_le_two;
  · exact pow_pos ( Real.log_pos <| by norm_cast; linarith ) _

/-
For large n, the level-0 threshold is ≤ n/(8C+2).
-/
lemma pruningThresh_zero_le_B'_card (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ B'_card : ℕ, B'_card ≥ n / (8 * C + 2) →
    pruningThresh n 0 ≤ B'_card := by
  -- Use the lemma `eventually_ge_mul_log_pow` to find such an $n₀$.
  have h_eventually_ge_mul_log_pow : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) / (Real.log n) ^ 6 ≤ n / (8 * C + 2) := by
    have h_eventually_ge_mul_log_pow : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (Real.log n) ^ 6 ≥ 8 * C + 2 := by
      have h_log_bound : Filter.Tendsto (fun n : ℕ => (Real.log n)^6) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      exact Filter.eventually_atTop.mp ( h_log_bound.eventually_ge_atTop _ );
    exact ⟨ h_eventually_ge_mul_log_pow.choose + 1, fun n hn => by gcongr ; exact h_eventually_ge_mul_log_pow.choose_spec n ( by linarith ) ⟩;
  cases' h_eventually_ge_mul_log_pow with n₀ hn₀;
  refine ⟨ n₀ + 2, fun n hn B'_card hB'_card => ?_ ⟩ ; norm_num [ pruningThresh ] at *;
  refine Nat.le_trans ( Nat.floor_mono <| hn₀ n <| by linarith ) ?_;
  exact Nat.le_trans ( Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by linarith : 0 < ( 8 * C + 2 ) ) ] ) hB'_card

/-
Pruning thresholds are non-increasing for large n (where log n > 1).
-/
lemma pruningThresh_mono {n : ℕ} (hn : n ≥ 3) (i : ℕ) :
    pruningThresh n (i + 1) ≤ pruningThresh n i := by
  refine Nat.floor_mono ?_;
  gcongr <;> norm_num;
  · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  · exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) )

/-! ### The one-step pruning alternative -/

/-
If T ⊆ B' is not controlled with threshold τ ≥ 1, then there exists a "bad" vertex
    w outside B' that can be used to prune T.
-/
lemma not_controlled_exists_bad {n : ℕ}
    (Hc : SimpleGraph (Fin n))
    (B' T : Finset (Fin n)) (τ : ℕ) (hτ : τ ≥ 1)
    (hTB : T ⊆ B')
    (hIndep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (h_not : ¬(∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < τ)) :
    ∃ w, w ∉ B' ∧ w ∉ T ∧
    (T.filter (fun v => Hc.Adj v w)).card ≥ τ ∧
    ¬(∀ v ∈ T, Hc.Adj v w) ∧
    T.filter (fun v => Hc.Adj v w) ⊆ B' ∧
    T.filter (fun v => Hc.Adj v w) ⊂ T := by
  simp +zetaDelta at *;
  obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_not;
  refine ⟨ x, ?_, ?_, hx₃, hx₂, ?_, ?_ ⟩;
  · contrapose! hx₂;
    intro y hy; have := Finset.card_pos.mp ( by linarith ) ; obtain ⟨ z, hz ⟩ := this; specialize hIndep _ ( hTB <| Finset.mem_filter.mp hz |>.1 ) _ hx₂; aesop;
  · grind +qlia;
  · exact fun y hy => hTB <| Finset.mem_filter.mp hy |>.1;
  · grind

/-! ### The multi-level chain argument -/

/-
The multi-level pruning chain terminates within 4C levels, producing
    a controlled T with a size guarantee from the threshold sequence.
-/
-- The generated pruning-chain proof needs extra heartbeats for finite-level bookkeeping.
set_option maxHeartbeats 800000 in
lemma pruning_chain_produces_controlled {n : ℕ} (C : ℕ) (hC : C ≥ 1)
    (Hc : SimpleGraph (Fin n))
    (B' : Finset (Fin n))
    (hIndep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (hDeg : ∀ v ∈ B', Hc.degree v ≤ 4 * C)
    (τ : ℕ → ℕ)
    (hτ_ge : ∀ i, i ≤ 4 * C → τ i ≥ 2)
    (hτ_le : τ 0 ≤ B'.card)
    (hτ_mono : ∀ i, i < 4 * C → τ (i + 1) ≤ τ i) :
    ∃ (i : ℕ) (T : Finset (Fin n)),
    i ≤ 4 * C ∧
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    T.card ≥ (if i = 0 then B'.card else τ (i - 1)) ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < τ i) := by
  by_contra! h_contra;
  -- Define a recursive construction: at level ℓ (starting from 0), we have T_ℓ ⊆ B' with |T_ℓ| ≥ (if ℓ=0 then |B'| else τ(ℓ-1)), and a set W_ℓ of ℓ distinct vertices outside B', all adjacent to all of T_ℓ.
  have h_rec : ∀ k ≤ 4 * C + 1, ∃ T : Finset (Fin n), ∃ W : Finset (Fin n), T ⊆ B' ∧ W.card = k ∧ (∀ w ∈ W, w ∉ B') ∧ (∀ w ∈ W, ∀ v ∈ T, Hc.Adj v w) ∧ T.card ≥ (if k = 0 then B'.card else τ (k - 1)) := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨ B', ∅, Finset.Subset.refl _, rfl, by norm_num, by norm_num, by norm_num ⟩
    | succ k ih =>
      obtain ⟨ T, W, hT₁, hT₂, hT₃, hT₄, hT₅ ⟩ := ih ( Nat.le_of_succ_le hk );
      -- By the induction hypothesis, T is not controlled with threshold τ k.
      have h_not_controlled : ¬(∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨ (T.filter (fun v => Hc.Adj v w)).card < τ k) := by
        specialize h_contra k T ( by linarith ) hT₁ ( by
          grind ) hT₅;
        grind;
      obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := not_controlled_exists_bad Hc B' T ( τ k ) ( by linarith [ hτ_ge k ( by linarith ) ] ) hT₁ hIndep h_not_controlled;
      use T.filter (fun v => Hc.Adj v w), Insert.insert w W;
      grind;
  obtain ⟨ T, W, hT₁, hW₁, hW₂, hW₃, hT₂ ⟩ := h_rec ( 4 * C + 1 ) le_rfl;
  -- Since $W$ consists of $4C + 1$ distinct vertices outside $B'$ and each vertex in $W$ is adjacent to all vertices in $T$, the degree of any vertex in $T$ must be at least $4C + 1$.
  have h_deg_T : ∀ v ∈ T, Hc.degree v ≥ 4 * C + 1 := by
    intros v hv; exact (by
    exact hW₁ ▸ Finset.card_le_card ( show W ⊆ Hc.neighborFinset v from fun w hw => by aesop ));
  rcases T.eq_empty_or_nonempty with ( rfl | ⟨ v, hv ⟩ ) <;> simp_all +decide;
  · linarith [ hτ_ge ( 4 * C ) le_rfl ];
  · linarith [ h_deg_T v hv, hDeg v ( hT₁ hv ) ]

/-! ### Ratio bound at each level -/

/-
For large n (depending on C), at any level i ≤ 4C, the ratio
    (a - 1)² / τᵢ ≥ K · n · log n whenever a ≥ the lower bound for that level.
-/
-- The generated pruning ratio estimate needs extra heartbeats for asymptotic bounds.
set_option maxHeartbeats 1600000 in
lemma pruning_ratio_bound (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ i : ℕ, i ≤ 4 * C →
    ∀ a : ℕ, a ≥ (if i = 0 then n / (8 * C + 2) else pruningThresh n (i - 1)) →
    ((a : ℝ) - 1) ^ 2 / ((pruningThresh n i : ℝ)) ≥
      2 ^ (16 * C + 4) * (C : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  have := @UniqueSubgraphs.pruningThresh_ge_two C hC; simp_all +decide [ UniqueSubgraphs.pruningThresh ] ; (
  -- Choose n₀ so that for n ≥ n₀: (1) pruningThresh is ≥ 2, (2) a ≥ a/2 ≥ 2, (3) (log n)^3 ≥ 16·K, and (4) (log n)^5 ≥ 4·(8C+2)²·K.
  obtain ⟨n₀₁, hn₀₁⟩ := this
  obtain ⟨n₀₂, hn₀₂⟩ : ∃ n₀₂ : ℕ, ∀ n ≥ n₀₂, Real.log n ^ 3 ≥ 16 * 2 ^ (16 * C + 4) * C := by
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n ^ 3) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop _ ) |> fun ⟨ n₀₂, hn₀₂ ⟩ => ⟨ n₀₂, fun n hn => hn₀₂ n hn ⟩ ;
  obtain ⟨n₀₃, hn₀₃⟩ : ∃ n₀₃ : ℕ, ∀ n ≥ n₀₃, Real.log n ^ 5 ≥ 4 * (8 * C + 2) ^ 2 * 2 ^ (16 * C + 4) * C := by
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n ^ 5) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop _ ) |> fun ⟨ n₀₃, hn₀₃ ⟩ => ⟨ n₀₃, fun n hn => hn₀₃ n hn ⟩ ;
  obtain ⟨n₀₄, hn₀₄⟩ : ∃ n₀₄ : ℕ, ∀ n ≥ n₀₄, ∀ i ≤ 4 * C, n / (8 * C + 2) ≥ 4 := by
    exact ⟨ 4 * ( 8 * C + 2 ) + 1, fun n hn i hi => Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by linarith ⟩ ;
  use max n₀₁ (max n₀₂ (max n₀₃ n₀₄)) + 1; intros n hn i hi a ha; split_ifs at ha <;> simp_all +decide [ Nat.succ_div ] ;
  · -- For i = 0, we have a ≥ n / (8C + 2). We need to show that (a - 1)² / τ₀ ≥ K·n·log n.
    have h_case0 : (a - 1 : ℝ) ^ 2 / (n / (Real.log n) ^ 6) ≥ 2 ^ (16 * C + 4) * C * (n * Real.log n) := by
      have h_case0 : (a - 1 : ℝ) ≥ n / (2 * (8 * C + 2)) := by
        rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> try linarith;
        rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by linarith : 0 < ( 8 * C + 2 ) ), hn₀₄ n ( by linarith ) 0 ( by linarith ) ] ;
      have h_case0 : (a - 1 : ℝ) ^ 2 ≥ (n / (2 * (8 * C + 2))) ^ 2 := by
        exact pow_le_pow_left₀ ( by positivity ) h_case0 2
      have h_case0 : (n / (2 * (8 * C + 2))) ^ 2 / (n / (Real.log n) ^ 6) ≥ 2 ^ (16 * C + 4) * C * (n * Real.log n) := by
        field_simp;
        nlinarith [mul_le_mul_of_nonneg_left (hn₀₃ n (by linarith))
          (show (0 : ℝ) ≤ n * Real.log n by
            exact mul_nonneg (Nat.cast_nonneg _)
              (Real.log_nonneg (Nat.one_le_cast.mpr (by linarith))))]
      exact le_trans h_case0 (by
      gcongr);
    refine le_trans h_case0 ?_;
    by_cases h : ⌊ ( n : ℝ ) / Real.log n ^ 6⌋₊ = 0 <;> simp_all +decide [ div_eq_mul_inv ];
    · contrapose! hn₀₁;
      exact ⟨ n, by linarith, 0, by linarith, Nat.floor_lt' ( by norm_num ) |>.2 <| by simpa using h.trans_le <| by norm_num ⟩;
    · gcongr;
      exact le_trans ( by norm_num [ mul_comm ] ) ( inv_anti₀ ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr h ) <| Nat.floor_le <| by positivity );
  · -- For i ≥ 1, a ≥ pruningThresh n (i-1) = ⌊n/(log n)^(6^i)⌋₊ ≥ n/(log n)^(6^i) - 1.
    have ha_ge : (a : ℝ) ≥ (n : ℝ) / (Real.log n) ^ (6 ^ i) - 1 := by
      rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ‹_› ) ] at ha;
      exact le_trans ( sub_le_iff_le_add.mpr <| Nat.lt_floor_add_one _ |> le_of_lt ) <| mod_cast ha
    -- Thus, a ≥ n/(2·(log n)^(6^i)).
    have ha_ge_half : (a : ℝ) ≥ (n : ℝ) / (2 * (Real.log n) ^ (6 ^ i)) := by
      have ha_ge_half : (n : ℝ) / (Real.log n) ^ (6 ^ i) ≥ 2 := by
        have := hn₀₁ n ( by linarith ) ( i - 1 ) ( by omega ) ; rcases i <;> simp_all +decide [ Nat.pow_succ' ] ;
        exact le_trans ( mod_cast this ) ( Nat.floor_le ( by positivity ) )
      generalize_proofs at *; (
      ring_nf at *; linarith;)
    -- The ratio: (a-1)²/(pruningThresh n i) ≥ (a/2)²/(n/(log n)^(6^(i+1))) (for a ≥ 2).
    have h_ratio_ge : ((a - 1 : ℝ) ^ 2) / (pruningThresh n i) ≥ ((n : ℝ) / (4 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) := by
      gcongr <;> norm_num [ UniqueSubgraphs.pruningThresh ] at *;
      · grind +splitImp;
      · rcases a with ( _ | _ | a ) <;> norm_num at *;
        · grind +suggestions;
        · exact absurd ha ( not_le_of_gt ( Nat.lt_of_lt_of_le ( by norm_num ) ( hn₀₁ n ( by linarith ) ( i - 1 ) ( Nat.sub_le_of_le_add ( by linarith ) ) ) ) );
        · ring_nf at *; linarith;
      · exact Nat.floor_le ( by positivity ) |> le_trans <| by norm_num;
    generalize_proofs at *; (
    -- Simplify the right-hand side of the inequality.
    have h_simplify : ((n : ℝ) / (4 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) = (n : ℝ) * (Real.log n) ^ (4 * 6 ^ i) / 16 := by
      field_simp
      ring_nf
      generalize_proofs at *; (
      by_cases h : Real.log n = 0 <;> simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ]
      · ring_nf
        norm_cast at * ; aesop ( simp_config := { decide := true } ) ;
      · exact div_eq_iff ( pow_ne_zero _ <| pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| lt_of_le_of_ne ( Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h.1 ) <| Ne.symm h.2.1 ) |>.2 <| by ring;)
    generalize_proofs at *; (
    -- Since $4 \cdot 6^i \geq 4$ for $i \geq 1$, we have $(\log n)^{4 \cdot 6^i} \geq (\log n)^4$.
    have h_log_ge : (Real.log n) ^ (4 * 6 ^ i) ≥ (Real.log n) ^ 4 := by
      exact pow_le_pow_right₀ ( show 1 ≤ Real.log n from by have := hn₀₂ n ( by linarith ) ; nlinarith [ show ( 1 :ℝ ) ≤ 2 ^ ( 16 * C + 4 ) * C by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( mod_cast hC ), pow_two_nonneg ( Real.log n ^ 2 - 1 ) ] ) ( show 4 ≤ 4 * 6 ^ i by linarith [ pow_pos ( by decide : 0 < 6 ) i ] ) ;
    generalize_proofs at *; (
    -- Since $(\log n)^3 \geq 16 \cdot 2^{16C+4} \cdot C$, we have $(\log n)^4 \geq 16 \cdot 2^{16C+4} \cdot C \cdot \log n$.
    have h_log_fourth_ge : (Real.log n) ^ 4 ≥ 16 * 2 ^ (16 * C + 4) * C * Real.log n := by
      nlinarith only [ hn₀₂ n hn.2.1.le, Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ]
    generalize_proofs at *; (
    exact le_trans ( by nlinarith [ show ( 0 :ℝ ) ≤ n * Real.log n by positivity ] ) ( h_ratio_ge.trans' ( h_simplify.ge.trans' ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left h_log_ge <| Nat.cast_nonneg _ ) <| by positivity ) ) ) |> le_trans <| le_rfl;)))));

/-! ### Main result: combining chain and ratio -/

/-
**Claim 2.4 (C ≥ 1)**: the multi-level pruning produces a controlled (T, threshold)
    pair with a good ratio bound.
-/
theorem claim_2_4_pruning_pos_result (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) := by
  obtain ⟨ n₁, hn₁ ⟩ := pruningThresh_ge_two C hC;
  obtain ⟨ n₂, hn₂ ⟩ := pruningThresh_zero_le_B'_card C hC;
  obtain ⟨ n₃, hn₃ ⟩ := pruning_ratio_bound C hC;
  refine ⟨ n₁ + n₂ + n₃ + 3, fun n hn Hc hHc B' hB' hB'' hB''' => ?_ ⟩;
  -- Apply the multi-level pruning chain to obtain the controlled set T and threshold.
  obtain ⟨ i, T, hi₁, hi₂, hi₃, hi₄, hi₅ ⟩ := pruning_chain_produces_controlled C hC Hc B' hB' hB'' (fun i => pruningThresh n i) (fun i hi => hn₁ n (by linarith) i hi) (by
  exact hn₂ n ( by linarith ) _ hB''') (fun i hi => pruningThresh_mono (by linarith) i);
  refine ⟨ T, pruningThresh n i, hi₂, hi₃, hi₅, ?_, ?_ ⟩;
  · exact sub_pos_of_lt ( mod_cast hi₃ );
  · grind

end UniqueSubgraphs
/-! ==================================================================
    Edge Ordering Argument
    (originally EdgeOrdering.lean)
    ================================================================== -/

section EdgeOrderingSection

/-!
# Edge Ordering Argument for the z-process Sum Bound

This file proves the abstract transition bound needed for `sum_z_refined_le_one`.
-/

open Finset Function

namespace EdgeOrderingCount

variable {N : ℕ}

/-! ## Chain prefix from a permutation -/

/-- The prefix of a permutation: the set {σ(i) : i.val < m}. -/
def chainPrefix (σ : Equiv.Perm (Fin N)) (m : ℕ) : Finset (Fin N) :=
  (Finset.univ.filter (fun i : Fin N => i.val < m)).image σ

@[simp]
lemma chainPrefix_zero (σ : Equiv.Perm (Fin N)) : chainPrefix σ 0 = ∅ := by
  simp [chainPrefix]

lemma chainPrefix_card (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m ≤ N) :
    (chainPrefix σ m).card = m := by
  rw [ chainPrefix, Finset.card_image_of_injective _ σ.injective ];
  rw [ Finset.card_eq_of_bijective ];
  · use fun i hi => ⟨ i, by linarith ⟩;
  · grind;
  · aesop;
  · aesop

lemma chainPrefix_mono (σ : Equiv.Perm (Fin N)) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    chainPrefix σ m₁ ⊆ chainPrefix σ m₂ := by
  intro x hx
  simp only [chainPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, by omega, rfl⟩

@[simp]
lemma chainPrefix_full (σ : Equiv.Perm (Fin N)) : chainPrefix σ N = Finset.univ := by
  ext x
  simp only [chainPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  exact ⟨σ.symm x, (σ.symm x).isLt, by simp⟩

lemma chainPrefix_succ (σ : Equiv.Perm (Fin N)) {m : ℕ} (hm : m < N) :
    chainPrefix σ (m + 1) = insert (σ ⟨m, hm⟩) (chainPrefix σ m) := by
  ext x
  simp only [chainPrefix, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i.val = m
    · left; congr 1; exact Fin.ext h
    · right; exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨m, hm⟩, by simp, rfl⟩
    · exact ⟨i, by omega, rfl⟩

lemma chainPrefix_new_not_mem (σ : Equiv.Perm (Fin N)) {m : ℕ} (hm : m < N) :
    σ ⟨m, hm⟩ ∉ chainPrefix σ m := by
  simp only [chainPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨i, hi, h⟩
  have := σ.injective h
  subst this; simp at hi

/-! ## Counting permutations with a given prefix -/

-- The generated permutation prefix count needs extra heartbeats for factorial algebra.
set_option maxHeartbeats 800000 in
lemma perm_prefix_fiber_card (m : ℕ) (S : Finset (Fin N)) (hS : S.card = m) (hm : m ≤ N) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S)).card =
      Nat.factorial m * Nat.factorial (N - m) := by
  revert S hS hm;
  induction m generalizing N with
  | zero =>
    simp +decide [ Fintype.card_perm ]
  | succ m ih =>
    intro S hS hN
    have h_count_succ : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ (m + 1) = S} = ∑ x ∈ S, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} := by
      have h_count_succ : Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = S) Finset.univ = Finset.biUnion S (fun x => Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x) Finset.univ) := by
        ext σ; simp [chainPrefix_succ];
        constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, chainPrefix ];
        · refine ⟨ h (σ ⟨m, by linarith⟩) |>.1 ⟨ ⟨m, by linarith⟩, le_rfl, rfl ⟩,
            fun a => ⟨ fun ⟨ i, hi, hi' ⟩ => ⟨ ?_, h a |>.1 ⟨ i, hi.le, hi' ⟩ ⟩,
              fun ⟨ hi, hi' ⟩ => ?_ ⟩ ⟩;
          · intro H; have := σ.injective ( H.symm ▸ hi' ) ; aesop;
          · exact h a |>.2 hi' |> fun ⟨ i, hi, hi' ⟩ => ⟨ i, lt_of_le_of_ne hi ( by aesop ), hi' ⟩;
        · grind;
      rw [ h_count_succ, Finset.card_biUnion ];
      exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσx hσy => hxy <| by aesop;
    have h_count_erase : ∀ x ∈ S, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} = m.factorial * (N - m - 1).factorial := by
      intro x hx
      have h_count_erase : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} = Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x} / (N - m) := by
        have h_ind_step : ∀ y ∈ Finset.univ \ S.erase x, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y} = Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} := by
          intro y hy
          have h_bij : Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y) Finset.univ = Finset.image (fun σ : Equiv.Perm (Fin N) => Equiv.swap x y * σ) (Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x) Finset.univ) := by
            ext σ; simp [chainPrefix];
            constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, Equiv.swap_apply_def ];
            · grind;
            · grind;
          rw [ h_bij, Finset.card_image_of_injective _ fun σ τ h => by simpa using h ];
        have h_ind_step : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x} = ∑ y ∈ Finset.univ \ S.erase x, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y} := by
          rw [ ← Finset.card_biUnion ];
          · congr with σ ; simp +decide [ Finset.mem_biUnion ];
            intro hσ hxσ; contrapose! hxσ; simp_all +decide [ chainPrefix ] ;
            replace hσ := Finset.ext_iff.mp hσ ( σ ⟨ m, by linarith ⟩ ) ; aesop;
          · exact fun y hy z hz hyz => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hyz <| by aesop;
        rw [ h_ind_step, Finset.sum_congr rfl ‹_› ] ; simp +decide [ Finset.card_sdiff, * ];
        rw [ Nat.mul_div_cancel_left _ ( Nat.sub_pos_of_lt hN ) ];
      rw [ h_count_erase, ih ];
      · exact Nat.div_eq_of_eq_mul_left ( Nat.sub_pos_of_lt hN ) ( by rw [ mul_assoc, ← Nat.succ_pred_eq_of_pos ( Nat.sub_pos_of_lt hN ) ] ; simp +decide [ Nat.factorial_succ, mul_comm, mul_assoc, mul_left_comm ] );
      · grind;
      · grind +qlia;
    simp_all +decide [ Nat.sub_sub, Nat.factorial_succ ];
    ring

/-! ## Transition count and interval property -/

-- The generated transition-count proof needs extra heartbeats for interval cases.
set_option maxHeartbeats 800000 in
lemma transition_count_le_one
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (σ : Equiv.Perm (Fin N)) :
    ((Finset.range (N + 1)).filter (fun m =>
      P (chainPrefix σ m) ∧ (m = 0 ∨ ¬ P (chainPrefix σ (m - 1))))).card ≤ 1 := by
  rw [ Finset.card_le_one_iff ];
  grind +suggestions

/-! ## Counting identities -/

def countP (P : Finset (Fin N) → Prop) [DecidablePred P] (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin N) => S.card = m ∧ P S)).card

lemma count_perm_with_P (P : Finset (Fin N) → Prop) [DecidablePred P] (m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card =
    countP P m * Nat.factorial m * Nat.factorial (N - m) := by
  have h_card : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card = Finset.sum (Finset.univ.filter (fun S : Finset (Fin N) => S.card = m ∧ P S)) (fun S => (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S)).card) := by
    rw [ ← Finset.card_biUnion ];
    · congr with σ;
      simp +zetaDelta at *;
      exact fun _ => chainPrefix_card σ m hm;
    · exact fun x hx y hy hxy => Finset.disjoint_filter.2 fun z => by aesop;
  rw [ h_card, Finset.sum_congr rfl fun S hS ↦ perm_prefix_fiber_card m S ( by aesop ) hm ];
  simp +decide [ mul_assoc, countP ]

-- The generated paired-permutation count needs extra heartbeats for summation rewrites.
set_option maxHeartbeats 3200000 in
lemma count_perm_with_P_pair (P : Finset (Fin N) → Prop) [DecidablePred P]
    (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ N)
    (ext_val : ℕ → ℕ)
    (h_ext : ∀ (S : Finset (Fin N)), P S → S.card < N →
      ((Finset.univ : Finset (Fin N)).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
      P (chainPrefix σ m) ∧ P (chainPrefix σ (m - 1)))).card =
    countP P (m - 1) * ext_val (m - 1) * Nat.factorial (m - 1) * Nat.factorial (N - m) := by
  rcases m with ( _ | m ) <;> simp_all +decide;
  have h_fiber_size : ∀ S₀ : Finset (Fin N), S₀.card = m → P S₀ → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card = Nat.factorial m * Nat.factorial (N - m) := by
    exact fun S₀ hS₀ hP₀ => perm_prefix_fiber_card m S₀ hS₀ ( by linarith );
  have h_fiber_size_succ : ∀ S₀ : Finset (Fin N), S₀.card = m → P S₀ → ∀ e : Fin N, e ∉ S₀ → P (insert e S₀) → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card = Nat.factorial m * Nat.factorial (N - m - 1) := by
    intros S₀ hS₀ hP₀ e he hP₁
    have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
      congr 1 with σ ; simp +decide [ chainPrefix_succ, he ];
      intro hσ; rw [ chainPrefix_succ ] ; all_goals try simp +decide [ hσ, he ] ;
      · constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff ];
        intro a; specialize h a; by_cases ha : a = e <;> simp_all +decide ;
        exact fun h => he <| by obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp h; aesop;
      · grind +revert;
    have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card / (N - m) := by
      have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card = ∑ e ∈ Finset.univ \ S₀, (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
        rw [ ← Finset.card_biUnion ];
        · congr with σ ; simp +decide [ chainPrefix ];
          intro h; replace h := Finset.ext_iff.mp h ( σ ⟨ m, hm' ⟩ ) ; aesop;
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hxy <| by aesop;
      have h_fiber_size_succ : ∀ e₁ e₂ : Fin N, e₁ ∉ S₀ → e₂ ∉ S₀ → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e₁)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e₂)).card := by
        intros e₁ e₂ he₁ he₂;
        refine Finset.card_bij ( fun σ hσ => Equiv.swap e₁ e₂ * σ ) ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_univ, Equiv.swap_apply_def ];
        · intro σ hσ₁ hσ₂; simp_all +decide [ chainPrefix ] ;
          ext x; simp +decide [ Equiv.swap_apply_def, hσ₁, hσ₂ ] ;
          constructor;
          · grind;
          · intro hx;
            obtain ⟨ a, ha₁, ha₂ ⟩ := Finset.mem_image.mp ( hσ₁.symm ▸ hx ) ; use a; aesop;
        · intro b hb hb'; use Equiv.swap e₁ e₂ * b; simp_all +decide [ Equiv.swap_apply_def ] ;
          convert hb using 1;
          ext x; simp +decide [ chainPrefix ] ;
          constructor <;> rintro ⟨ a, ha, rfl ⟩ <;> use a <;> simp_all +decide [ Equiv.swap_apply_def ];
          · split_ifs <;> simp_all +decide [ chainPrefix ];
            · replace hb := Finset.ext_iff.mp hb e₁; aesop;
            · have := b.injective ( by aesop : b a = b ⟨ m, hm' ⟩ ) ; aesop;
          · split_ifs <;> simp_all +decide [ chainPrefix ];
            · replace hb := Finset.ext_iff.mp hb e₁; aesop;
            · have := b.injective ( by aesop : b a = b ⟨ m, hm' ⟩ ) ; aesop;
      rw [ ‹# { σ | chainPrefix σ m = S₀ } = ∑ e ∈ Finset.univ \ S₀, _›, Finset.sum_congr rfl fun x hx => h_fiber_size_succ x e ( by aesop ) he ] ; simp +decide [ Finset.card_sdiff, * ];
    rcases k : N - m with ( _ | k ) <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm ];
    · omega;
    · exact Nat.div_eq_of_eq_mul_left ( Nat.succ_pos _ ) ( by ring );
  have h_count : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ (m + 1)) ∧ P (chainPrefix σ m))).card = ∑ S₀ ∈ Finset.filter (fun S => S.card = m ∧ P S) (Finset.univ : Finset (Finset (Fin N))), ∑ e ∈ Finset.filter (fun e => e ∉ S₀ ∧ P (insert e S₀)) (Finset.univ : Finset (Fin N)), (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
    have h_count : Finset.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ (m + 1)) ∧ P (chainPrefix σ m)) Finset.univ = Finset.biUnion (Finset.filter (fun S => S.card = m ∧ P S) (Finset.univ : Finset (Finset (Fin N)))) (fun S₀ => Finset.biUnion (Finset.filter (fun e => e ∉ S₀ ∧ P (insert e S₀)) (Finset.univ : Finset (Fin N))) (fun e => Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e) Finset.univ)) := by
      ext σ; simp [chainPrefix_succ];
      constructor;
      · intro hσ
        use chainPrefix σ m;
        exact ⟨ ⟨ chainPrefix_card σ m hm'.le, hσ.2 ⟩, ⟨ chainPrefix_new_not_mem σ hm', by simpa [ chainPrefix_succ σ hm' ] using hσ.1 ⟩, chainPrefix_succ σ hm' ⟩;
      · rintro ⟨ S₀, ⟨ hS₀₁, hS₀₂ ⟩, ⟨ hS₀₃, hS₀₄ ⟩, hS₀₅ ⟩;
        have h_chainPrefix_m : chainPrefix σ m = S₀ := by
          have h_chainPrefix_m : chainPrefix σ (m + 1) = insert (σ ⟨m, hm'⟩) (chainPrefix σ m) := by
            exact chainPrefix_succ σ hm';
          rw [ Finset.ext_iff ] at h_chainPrefix_m;
          ext x; specialize h_chainPrefix_m x; by_cases hx : x = σ ⟨ m, hm' ⟩ <;> simp_all +decide ;
          exact chainPrefix_new_not_mem σ hm';
        grind;
    rw [ h_count, Finset.card_biUnion, Finset.sum_congr rfl ];
    · intro S₀ hS₀;
      rw [ Finset.card_biUnion ];
      intro e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
    · intros S₀ hS₀ S₁ hS₁ h_inter;
      simp_all +decide [ Finset.disjoint_left ];
      intro σ hσ₀ hσ₁ hσ₂ hσ₃ hσ₄; contrapose! h_inter; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_inter a; aesop;
  rw [ h_count ];
  rw [ Finset.sum_congr rfl fun S₀ hS₀ => Finset.sum_congr rfl fun e he => h_fiber_size_succ S₀ ( Finset.mem_filter.mp hS₀ |>.2.1 ) ( Finset.mem_filter.mp hS₀ |>.2.2 ) e ( Finset.mem_filter.mp he |>.2.1 ) ( Finset.mem_filter.mp he |>.2.2 ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul _ _ _ ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ h_ext x ( Finset.mem_filter.mp hx |>.2.2 ) ( by linarith [ Finset.mem_filter.mp hx |>.2.1, Nat.sub_add_cancel hm'.le ] ) ] ] ; simp +decide [ Nat.sub_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2.1 ] ] ; simp +decide [ countP, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

/-! ## Transition bound -/

lemma total_transitions_le_factorial
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅) :
    ∑ m ∈ Finset.range (N + 1),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
        P (chainPrefix σ m) ∧ ¬ P (chainPrefix σ (m - 1)))).card ≤
    Nat.factorial N := by
  have h_perm_bound : ∀ σ : Equiv.Perm (Fin N), (∑ m ∈ Finset.range (N + 1), if P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)) then 1 else 0) ≤ 1 := by
    intro σ;
    convert transition_count_le_one P h_interval h_empty σ using 1;
    rw [ Finset.card_filter, Finset.sum_congr rfl ] ; aesop;
  calc
    ∑ m ∈ Finset.range (N + 1),
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
          P (chainPrefix σ m) ∧ ¬ P (chainPrefix σ (m - 1)))).card
        = ∑ σ : Equiv.Perm (Fin N),
            ∑ m ∈ Finset.range (N + 1),
              if P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)) then 1 else 0 := by
          rw [show
            (∑ m ∈ Finset.range (N + 1),
              (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
                P (chainPrefix σ m) ∧ ¬ P (chainPrefix σ (m - 1)))).card) =
              ∑ m ∈ Finset.range (N + 1), ∑ σ : Equiv.Perm (Fin N),
                if P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)) then 1 else 0 by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.card_filter]]
          rw [Finset.sum_comm]
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), 1 := by
          exact Finset.sum_le_sum fun σ _ => h_perm_bound σ
    _ = Nat.factorial N := by
          simp [Fintype.card_perm]

/-! ## Main theorem -/

-- The generated transition-sum theorem needs extra heartbeats for real-valued bounds.
set_option maxHeartbeats 1600000 in
theorem transition_sum_le_one
    (R : ℕ → ℕ) (ext_val : ℕ → ℕ)
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (h_ext : ∀ (S : Finset (Fin N)), P S → S.card < N →
      ((Finset.univ : Finset (Fin N)).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card)
    (hR : ∀ m, R m = countP P m) :
    ∑ m ∈ Finset.range (N + 1),
      ((R m : ℝ) / (N.choose m : ℝ) -
       (ext_val (m - 1) : ℝ) / ((N : ℝ) - ↑m + 1) *
       ((R (m - 1) : ℝ) / (N.choose (m - 1) : ℝ))) ≤ 1 := by
  have h_total_transitions_le_factorial : ∑ m ∈ Finset.range (N + 1), ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) ≤ Nat.factorial N := by
    exact_mod_cast total_transitions_le_factorial P h_interval h_empty;
  have h_sum_eq : ∀ m ∈ Finset.range (N + 1), ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = (Nat.factorial N : ℝ) * ((R m : ℝ) / (Nat.choose N m : ℝ) - (ext_val (m - 1) : ℝ) / ((N - m + 1) : ℝ) * ((R (m - 1) : ℝ) / (Nat.choose N (m - 1) : ℝ))) := by
    intro m hm
    have h_card : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = (Nat.factorial m * Nat.factorial (N - m) : ℝ) * (R m : ℝ) - (if m = 0 then 0 else (Nat.factorial (m - 1) * Nat.factorial (N - m) : ℝ) * (ext_val (m - 1) : ℝ) * (R (m - 1) : ℝ)) := by
      have h_card : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card : ℝ) - (if m = 0 then 0 else ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ P (chainPrefix σ (m - 1)))).card : ℝ)) := by
        rcases m with ( _ | m ) <;> simp_all +decide [ Finset.filter_and ];
        rw [ eq_sub_iff_add_eq', ← Nat.cast_add ];
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with x ; by_cases hx : P ( chainPrefix x m ) <;> aesop;
        · exact Finset.disjoint_left.mpr ( by aesop );
      convert h_card using 2;
      · convert count_perm_with_P P m ( Finset.mem_range_succ_iff.mp hm ) |> Eq.symm using 1;
        rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; rw [ hR ] ; ring_nf;
      · split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        have := count_perm_with_P_pair P m ( Nat.pos_of_ne_zero ‹_› ) hm ext_val h_ext; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    split_ifs at * <;> simp_all +decide [ Nat.cast_choose, mul_sub ];
    · cases h_card <;> simp_all +decide [ Nat.factorial_ne_zero ];
    · rw [ Nat.cast_choose ];
      · field_simp [show (1 + (N : ℝ) - (m : ℝ)) ≠ 0 by linarith [show (m : ℝ) ≤ N by norm_cast]];
        rw [ show N - ( m - 1 ) = N - m + 1 by omega ];
        norm_num [ Nat.factorial_succ, Nat.cast_sub hm ];
        field_simp [show (N : ℝ) - (m : ℝ) + 1 ≠ 0 by linarith [show (m : ℝ) ≤ N by norm_cast]] at *
        ring_nf at *
      · exact Nat.sub_le_of_le_add <| by linarith;
  rw [ Finset.sum_congr rfl h_sum_eq, ← Finset.mul_sum _ _ _ ] at h_total_transitions_le_factorial ; nlinarith [ show ( N.factorial : ℝ ) > 0 by positivity ]

/-! ## Generalized version for arbitrary finite types -/

-- The generated finite-type transition theorem needs extra heartbeats for reindexing.
set_option maxHeartbeats 1600000 in
/-- Generalized transition sum bound for arbitrary finite types. -/
theorem transition_sum_le_one_gen
    {α : Type} [Fintype α] [DecidableEq α]
    (R : ℕ → ℕ) (ext_val : ℕ → ℕ)
    (P : Finset α → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset α),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (h_ext : ∀ (S : Finset α), P S → S.card < Fintype.card α →
      ((Finset.univ : Finset α).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card)
    (hR : ∀ m, R m = (Finset.univ.filter (fun S : Finset α => S.card = m ∧ P S)).card) :
    let N := Fintype.card α
    ∑ m ∈ Finset.range (N + 1),
      ((R m : ℝ) / (N.choose m : ℝ) -
       (ext_val (m - 1) : ℝ) / ((N : ℝ) - ↑m + 1) *
       ((R (m - 1) : ℝ) / (N.choose (m - 1) : ℝ))) ≤ 1 := by
  -- Define P' : Finset (Fin N) → Prop by P'(S) = P(S.map e.symm.toEmbedding).
  set N := Fintype.card α
  obtain ⟨e, he⟩ : ∃ e : α ≃ Fin N, True := by
    exact ⟨ Fintype.equivFin α, trivial ⟩;
  convert transition_sum_le_one R ext_val ( fun S => P ( S.map e.symm.toEmbedding ) ) _ _ _ _ using 1;
  · aesop;
  · aesop;
  · intro S hS hS'; specialize h_ext ( S.map e.symm.toEmbedding ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
    convert h_ext using 1
    rw [ Finset.card_filter, Finset.card_filter ]
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ]
    exact Finset.sum_congr rfl fun i _ => by simp [Equiv.apply_symm_apply]
  · intro m; rw [ hR ] ; unfold countP; simp +decide [ Finset.card_map ] ;
    refine Finset.card_bij ( fun S hS => S.map e.toEmbedding ) ?_ ?_ ?_ <;> simp +decide [ Finset.card_map ];
    · simp +contextual [ Finset.map_map, Equiv.symm_apply_apply ];
    · exact fun b hb hb' => ⟨ _, ⟨ by simpa [ Finset.card_map ] using hb, hb' ⟩, by ext x; simp +decide ⟩

end EdgeOrderingCount
end EdgeOrderingSection

/-! ==================================================================
    Pólya-Wright Theorem
    (originally PolyaWright.lean)
    ================================================================== -/

section PolyaWrightSection

/-!
# Proof of the Pólya–Wright Theorem

The proof uses Burnside's lemma and bounds the contributions from
non-identity permutations using an orbit-size argument on edges.
-/

open Finset Function SimpleGraph Filter

namespace PolyaWright

open UniqueSubgraphs

/-! ## Auxiliary: Graph ↔ Bool function on edges -/

/-- Encode a graph as a Boolean function on non-diagonal Sym2 elements. -/
def graphToFun {n : ℕ} (G : SimpleGraph (Fin n)) :
    {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool :=
  fun ⟨e, _⟩ => e.lift ⟨fun a b => decide (G.Adj a b),
    fun a b => by simp [G.adj_comm]⟩

/-- Decode a Boolean function on edges back to a graph. -/
def funToGraph {n : ℕ}
    (f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ (h : u ≠ v), f ⟨s(u, v), by rwa [Sym2.isDiag_iff_proj_eq]⟩ = true
  symm.symm u v := by
    rintro ⟨h1, h2⟩; refine ⟨h1.symm, ?_⟩
    convert h2 using 2; exact Subtype.ext (Sym2.eq_swap)
  loopless := ⟨fun v h => h.1 rfl⟩

/-- Graphs on `Fin n` are equivalent to Boolean functions on non-diagonal Sym2. -/
def graphEquivFun (n : ℕ) :
    SimpleGraph (Fin n) ≃ ({e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool) where
  toFun := graphToFun
  invFun := funToGraph
  left_inv G := by
    ext u v; simp only [funToGraph, graphToFun, Sym2.lift_mk, decide_eq_true_eq]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨G.ne_of_adj h, h⟩⟩
  right_inv f := by
    ext ⟨e, he⟩; induction e using Sym2.ind with
    | h u v =>
      simp only [graphToFun, Sym2.lift_mk, funToGraph]
      have hne : u ≠ v := by rwa [Sym2.isDiag_iff_proj_eq] at he
      simp [hne]

/-- The action of σ on non-diagonal Sym2 elements (edges). -/
def edgePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm {e : Sym2 (Fin n) // ¬ e.IsDiag} where
  toFun e := ⟨e.val.map σ, by rw [Sym2.isDiag_map σ.injective]; exact e.prop⟩
  invFun e := ⟨e.val.map σ.symm, by rw [Sym2.isDiag_map σ.symm.injective]; exact e.prop⟩
  left_inv := by intro ⟨e, he⟩; simp [Sym2.map_map]
  right_inv := by intro ⟨e, he⟩; simp [Sym2.map_map]

/-- `σ • G = G` iff `graphToFun G` is invariant under `edgePerm σ`. -/
theorem fixed_iff_invariant {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    σ • G = G ↔ ∀ e, graphToFun G (edgePerm σ e) = graphToFun G e := by
  constructor
  · intro h ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v =>
      change decide (G.Adj (σ u) (σ v)) = decide (G.Adj u v)
      congr 1; exact propext (by
        have : (σ • G).Adj (σ u) (σ v) = G.Adj (σ u) (σ v) := by rw [h]
        simp [smul_adj] at this; exact this.symm)
  · intro h
    ext u v
    simp only [smul_adj]
    by_cases huv : u = v
    · subst huv; simp
    · have hne' : σ.symm u ≠ σ.symm v := fun heq => huv (σ.symm.injective heq)
      have h' := h ⟨s(σ.symm u, σ.symm v), by rwa [Sym2.isDiag_iff_proj_eq]⟩
      change decide (G.Adj (σ (σ.symm u)) (σ (σ.symm v))) = _ at h'
      simp only [Equiv.apply_symm_apply] at h'
      rw [Equiv.Perm.inv_def]
      exact (decide_eq_decide.mp h'.symm)

/-- A σ-fixed graph corresponds to a σ-invariant Boolean edge function. -/
def fixedBy_equiv_invariant {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) ≃
    {f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool //
      ∀ e, f (edgePerm σ e) = f e} :=
  (graphEquivFun n).subtypeEquiv (fun G => by
    simp only [graphEquivFun, MulAction.mem_fixedBy]
    exact fixed_iff_invariant σ G)

/-! ## Step 1: Cardinality of SimpleGraph (Fin n) -/

/-- The number of simple graphs on `Fin n` equals `2^{n choose 2}`. -/
theorem card_simpleGraph_fin (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [card_simpleGraph]

/-- The identity contributes `2^N` to Burnside's sum. -/
theorem card_fixedBy_one (n : ℕ) :
    Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) (1 : Equiv.Perm (Fin n))) =
    2 ^ n.choose 2 := by
  rw [← card_simpleGraph_fin]
  exact Fintype.card_congr
    (Equiv.ofBijective (fun x => x.val)
      ⟨fun x y => by aesop, fun x => ⟨⟨x, by aesop⟩, rfl⟩⟩)

/-! ## Step 2: Bounding |Fix(σ)| for σ ≠ 1 -/

/-
For any permutation σ on a finite type S, the number of σ-invariant
    Boolean functions on S is at most `2^{(|S| + |Fix_S(σ)|) / 2}`.
-/
theorem card_invariant_bool_le {S : Type*} [Fintype S] [DecidableEq S]
    (σ : Equiv.Perm S) :
    Fintype.card {f : S → Bool // ∀ s, f (σ s) = f s} ≤
    2 ^ ((Fintype.card S + Fintype.card (Function.fixedPoints σ)) / 2) := by
  -- The number of orbits of σ on S is at most the number of fixed points plus half the number of non-fixed points.
  have h_orbits : (Fintype.card (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) ≤ (Fintype.card (fixedPoints σ)) + ((Fintype.card S) - (Fintype.card (fixedPoints σ))) / 2 := by
    -- Let's count the number of orbits.
    have h_orbits_card : ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) = Fintype.card S := by
      simp +decide only [card_filter, Fintype.card_eq_sum_ones];
      rw [ Finset.sum_comm ] ; aesop;
    -- Each orbit is either a fixed point or a cycle of length at least 2.
    have h_orbit_length : ∀ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) ≥ if x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S)) then 1 else 2 := by
      intro x
      by_cases hx : x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S));
      · obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact if_pos hx ▸ Finset.card_pos.mpr ⟨ y, by aesop ⟩ ;
      · obtain ⟨ y, hy ⟩ := Quotient.exists_rep x; simp_all +decide [ Quotient.eq ] ;
        refine le_trans ?_ ( Finset.card_mono <| show { y, σ y } ⊆ Finset.filter ( fun z => ⟦z⟧ = x ) Finset.univ from ?_ );
        · grind;
        · simp +decide [ ← hy, Finset.insert_subset_iff ];
          exact Quotient.sound ⟨ ⟨ σ, Subgroup.mem_zpowers σ ⟩, rfl ⟩;
    have h_orbit_length_sum : ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) ≥ ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), if x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S)) then 1 else 2 := by
      exact Finset.sum_le_sum fun x _ => h_orbit_length x;
    simp_all +decide [ Finset.sum_ite ];
    rw [ show ( Finset.filter ( fun x => ∃ a, σ a = a ∧ ⟦a⟧ = x ) Finset.univ : Finset ( Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) ) = Finset.image ( fun y => ⟦y⟧ ) ( Finset.filter ( fun y => σ y = y ) Finset.univ ) from ?_ ] at h_orbit_length_sum;
    · rw [ show ( Finset.filter ( fun x => ∀ y, σ y = y → ¬⟦y⟧ = x ) Finset.univ : Finset ( Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) ) = Finset.univ \ Finset.image ( fun y => ⟦y⟧ ) ( Finset.filter ( fun y => σ y = y ) Finset.univ ) from ?_, Finset.card_sdiff ] at h_orbit_length_sum <;> norm_num at *;
      · have h_image_le :
            #(Finset.image (fun y : S => (⟦y⟧ : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S))) ≤
              Fintype.card (Function.fixedPoints σ) := by
          simpa [Fintype.card_subtype, Function.fixedPoints, IsFixedPt] using
            (Finset.card_image_le :
              #(Finset.image (fun y : S => (⟦y⟧ : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S))) ≤
                #(Finset.filter (fun y => σ y = y) (Finset.univ : Finset S)))
        have hfix_le : Fintype.card (Function.fixedPoints σ) ≤ Fintype.card S := by
          simpa [Fintype.card_subtype, Function.fixedPoints, IsFixedPt] using
            (Finset.card_filter_le (Finset.univ : Finset S) (fun y => σ y = y))
        have hfix_eq :
            Fintype.card (Function.fixedPoints σ) =
              #(Finset.filter (fun y : S => IsFixedPt (⇑σ) y) Finset.univ) := by
          simp [Fintype.card_subtype, Function.fixedPoints]
        omega
      · ext x
        simp [Finset.mem_image]
    · ext x
      simp [Finset.mem_image]
  -- Each σ-invariant function corresponds to a function on the orbits of σ.
  have h_invariant : { f : S → Bool // ∀ s, f (σ s) = f s } ≃ (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S) → Bool) := by
    refine Equiv.ofBijective ( fun f => fun q => f.val ( Classical.choose ( Quotient.exists_rep q ) ) ) ⟨ ?_, ?_ ⟩;
    · intro f g hfg;
      ext s;
      have := Classical.choose_spec ( Quotient.exists_rep ( ⟦s⟧ : Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) );
      rw [ Quotient.eq ] at this;
      obtain ⟨ k, hk ⟩ := this;
      have h_eq : ∀ m : ℕ, f.val ((⇑σ)^[m] s) = f.val s ∧ g.val ((⇑σ)^[m] s) = g.val s := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [Function.iterate_succ_apply', f.2, g.2, ih.1, ih.2]
      obtain ⟨ m, hm ⟩ := k.2;
      have h_eq_zpow : f.val ((σ ^ m) s) = f.val s ∧ g.val ((σ ^ m) s) = g.val s := by
        have hnat := h_eq (Int.toNat (m % orderOf σ))
        have hmod_nonneg : 0 ≤ m % (orderOf σ : ℤ) :=
          Int.emod_nonneg _ (Nat.cast_ne_zero.mpr (ne_of_gt (orderOf_pos σ)))
        have hpow :
            (σ ^ (m % (orderOf σ : ℤ)) : Equiv.Perm S) =
              σ ^ Int.toNat (m % (orderOf σ : ℤ)) := by
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg hmod_nonneg]
        have hnat' :
            f.val ((σ ^ (m % orderOf σ)) s) = f.val s ∧
              g.val ((σ ^ (m % orderOf σ)) s) = g.val s := by
          simpa [hpow, Equiv.Perm.coe_pow] using hnat
        simpa [zpow_mod_orderOf] using hnat'
      have h_rep : (σ ^ m) s = Classical.choose (Quotient.exists_rep (⟦s⟧ :
          Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) := by
        have hm_apply := congr_arg (fun x : Equiv.Perm S => x s) hm
        have hk' : (k : Equiv.Perm S) s = Classical.choose (Quotient.exists_rep (⟦s⟧ :
            Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hk
        exact hm_apply.trans hk'
      have hfg_rep := congr_fun hfg (⟦s⟧ : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))
      have hfg' : f.val ((σ ^ m) s) = g.val ((σ ^ m) s) := by
        simpa [h_rep] using hfg_rep
      exact h_eq_zpow.1.symm.trans (hfg'.trans h_eq_zpow.2)
    · intro g
      use ⟨fun s => g (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) S) s), by
        simp +decide [ Quotient.eq ];
        congr! 1;
        exact Quotient.sound ⟨ ⟨ σ, Subgroup.mem_zpowers σ ⟩, rfl ⟩⟩
      generalize_proofs at *;
      ext q; have := Classical.choose_spec ( Quotient.exists_rep q ) ; aesop;
  have := Fintype.card_congr h_invariant;
  simp_all +decide [ Fintype.card_pi ];
  refine pow_le_pow_right₀ ( by decide ) ?_
  have hfix_le : Fintype.card (Function.fixedPoints σ) ≤ Fintype.card S := by
    simpa [Fintype.card_subtype] using (Finset.card_filter_le (Finset.univ : Finset S) (fun x => x ∈ Function.fixedPoints σ))
  have hfix_eq :
      Fintype.card (Function.fixedPoints σ) =
        #(Finset.filter (fun y : S => IsFixedPt (⇑σ) y) Finset.univ) := by
    simp [Fintype.card_subtype, Function.fixedPoints]
  exact h_orbits.trans (by omega)

/-
proved by subagent (long proof)

Bound on the number of edges fixed by σ: at most `s.choose 2 + (n-s)/2`
    where s is the number of vertex fixed points.
-/
-- The generated fixed-edge bound needs extra heartbeats for permutation-cycle cases.
set_option maxHeartbeats 800000 in
theorem card_fixedPoints_edgePerm_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (Function.fixedPoints (edgePerm σ)) ≤
    (Fintype.card (Function.fixedPoints σ)).choose 2 +
    (n - Fintype.card (Function.fixedPoints σ)) / 2 := by
  -- An edge e = s(u,v) is a fixed point of edgePerm σ iff {σ(u), σ(v)} = {u, v} (as an unordered pair). This happens in two cases:
  -- 1. Both u and v are fixed points of σ (σ(u) = u and σ(v) = v). There are (s choose 2) such edges where s = Fintype.card (fixedPoints σ).
  -- 2. σ swaps u and v: σ(u) = v and σ(v) = u, i.e., (u,v) form a 2-cycle of σ. The number of 2-cycles is at most (n-s)/2 since each 2-cycle uses 2 non-fixed points.
  have card_fixed_edges : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e)).card ≤ (Fintype.card (fixedPoints σ)).choose 2 + (n - Fintype.card (fixedPoints σ)) / 2 := by
    have h_fixed_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk u v ∧ u ∈ fixedPoints σ ∧ v ∈ fixedPoints σ)).card ≤ (Fintype.card (fixedPoints σ)).choose 2 := by
      have h_fixed_edges : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ e ∈ Finset.image (fun (uv : Fin n × Fin n) => Sym2.mk uv.1 uv.2) (Finset.offDiag (Finset.univ.filter (fun u => u ∈ fixedPoints σ))))).card ≤ (Finset.univ.filter (fun u => u ∈ fixedPoints σ)).card.choose 2 := by
        rw [ ← Finset.card_powersetCard ];
        refine le_of_eq ?_;
        refine Finset.card_bij ( fun e he => Finset.filter ( fun u => u ∈ e ) Finset.univ ) ?_ ?_ ?_ <;> simp +decide [ Finset.subset_iff ];
        · rintro a ha x y hx hy hxy rfl; simp_all +decide [ IsFixedPt ] ;
          exact Finset.card_eq_two.mpr ⟨ x, y, by aesop ⟩;
        · intro a₁ ha₁ x y hx hy hxy h₁ a₂ ha₂ u v hu hv huv h₂ h₃; ext w; replace h₃ := Finset.ext_iff.mp h₃ w; aesop;
        · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; use a, b; aesop;
      refine le_trans ?_ ( h_fixed_edges.trans ?_ );
      · refine Finset.card_le_card ?_;
        simp +contextual [ Finset.subset_iff ];
        intro e he hσ u v hu hv hv'; use u, v; aesop;
      · rw [ Fintype.card_subtype ]
    have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk u v ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card ≤ (n - Fintype.card (fixedPoints σ)) / 2 := by
      have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk u v ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card / 2 := by
        have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk u v ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card * 2 ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card := by
          have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk u v ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).sum (fun e => (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ ∧ e = Sym2.mk u (σ u))).card) ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card := by
            rw [ ← Finset.card_biUnion ];
            · exact Finset.card_le_card fun x hx => by aesop;
            · intros e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
              grind;
          refine le_trans ?_ h_swap_points;
          rw [ Finset.sum_const_nat ];
          simp +contextual [ Finset.card_eq_two ];
          intro e he₁ he₂ u hu₁ hu₂ hu₃ hu₄; use σ u, u; simp_all +decide [ IsFixedPt ] ;
          grind;
        rwa [ Nat.le_div_iff_mul_le zero_lt_two ];
      simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
    refine le_trans ?_ ( add_le_add h_fixed_points h_swap_points );
    rw [ ← Finset.card_union_add_card_inter ];
    refine le_add_right ( Finset.card_le_card ?_ );
    intro e he; simp_all +decide [ Sym2.forall ] ;
    rcases e with ⟨ u, v ⟩ ; simp_all +decide [ IsFixedPt, Sym2.eq_swap ] ;
    grind +ring;
  convert card_fixed_edges using 1;
  refine Finset.card_bij ( fun x hx => x.val ) ?_ ?_ ?_ <;> simp +decide [ edgePerm ];
  · grind +suggestions;
  · exact fun b hb hb' => by
      have hfixed : edgePerm σ ⟨b, hb⟩ = ⟨b, hb⟩ := by
        apply Subtype.ext
        exact hb'
      exact ⟨ hb, ⟨ hfixed, Finset.mem_univ _ ⟩ ⟩

/-- The main combinatorial bound: |Fix(σ)| ≤ 2^{(N + f) / 2}. -/
theorem card_fixedBy_le_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) ≤
    2 ^ ((n.choose 2 +
      Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
  calc Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ)
      = Fintype.card {f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool //
          ∀ e, f (edgePerm σ e) = f e} := by
        exact Fintype.card_congr (fixedBy_equiv_invariant σ)
    _ ≤ 2 ^ ((Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag} +
          Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
        exact card_invariant_bool_le (edgePerm σ)
    _ = 2 ^ ((n.choose 2 +
          Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
        congr 1; congr 1; congr 1
        rw [@Sym2.card_subtype_not_diag (Fin n) _ _, Fintype.card_fin]

/-! ## Step 3: From Burnside to the ratio -/

/-
Burnside gives: `numIsoClasses n / paperDenom n` equals the Burnside sum
    divided by `2^N`.
-/
theorem ratio_eq_burnside_over_two_pow (n : ℕ) :
    (numIsoClasses n : ℝ) / paperDenom n =
    (∑ σ : Equiv.Perm (Fin n),
      (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) /
    (2 ^ n.choose 2 : ℝ) := by
  unfold paperDenom;
  field_simp;
  exact_mod_cast UniqueSubgraphs.burnside_applied n |> Eq.symm

/-
Split: ratio = 1 + remainder from non-identity permutations.
-/
theorem ratio_eq_one_plus_remainder (n : ℕ) :
    (numIsoClasses n : ℝ) / paperDenom n = 1 +
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (· ≠ 1),
      (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) /
    (2 ^ n.choose 2 : ℝ) := by
  rw [ ratio_eq_burnside_over_two_pow ];
  have hsum :
      (∑ σ : Equiv.Perm (Fin n),
        (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) =
      (2 ^ n.choose 2 : ℝ) +
        (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (· ≠ 1),
          (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) := by
    rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem <| Finset.mem_univ ( 1 : Equiv.Perm ( Fin n ) ) ];
    norm_num [ Finset.filter_ne', card_fixedBy_one ];
    have hcard : (Fintype.card (SimpleGraph (Fin n)) : ℝ) = (2 ^ n.choose 2 : ℝ) := by
      exact_mod_cast card_simpleGraph_fin n
    rw [hcard]
    ring
  rw [ hsum ];
  field_simp

/-! ## Step 4: The remainder tends to 0 -/

/-
The exponent bound: for σ ≠ 1, `(N + f)/2 - N ≤ -m(n-2)/4`
    where `m = n - s`, `s` = fixed points. This means `|Fix(σ)|/2^N ≤ 2^{-m(n-2)/4}`.
-/
theorem saving_lower_bound {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    let s := Fintype.card (Function.fixedPoints σ)
    let m := n - s
    (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) ≤
    (2 : ℝ) ^ (n.choose 2 : ℤ) / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ) : ℤ) := by
  rw [ le_div_iff₀ ] <;> norm_cast;
  · refine le_trans ( Nat.mul_le_mul_right ( 2 ^ ((n - Fintype.card (Function.fixedPoints σ)) *
      (n - 2) / 4) ) ( card_fixedBy_le_pow σ ) ) ?_;
    rw [ ← pow_add ];
    refine pow_le_pow_right₀ ( by decide ) ?_;
    have h_exp_bound : Fintype.card (Function.fixedPoints (edgePerm σ)) ≤ (Fintype.card (Function.fixedPoints σ)).choose 2 + (n - Fintype.card (Function.fixedPoints σ)) / 2 := by
      convert card_fixedPoints_edgePerm_le σ using 1;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
    have h_exp_bound : (n + 1 + 1) * (n + 1) + #(filter (Membership.mem (fixedPoints ⇑σ)) univ) * (#(filter (Membership.mem (fixedPoints ⇑σ)) univ) - 1) + (n + 1 + 1 - #(filter (Membership.mem (fixedPoints ⇑σ)) univ)) + (n + 1 + 1 - #(filter (Membership.mem (fixedPoints ⇑σ)) univ)) * n ≤ 2 * (n + 1 + 1) * (n + 1) := by
      have h_exp_bound : #(filter (Membership.mem (fixedPoints ⇑σ)) univ) ≤ n + 1 + 1 := by
        exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      cases h : #(filter (Membership.mem (fixedPoints ⇑σ)) univ) <;> simp_all +decide [ Nat.mul_succ ]
      · nlinarith [ Nat.sub_add_cancel h_exp_bound ]
      · nlinarith only [ Nat.sub_add_cancel h_exp_bound ];
    simp [Fintype.card_subtype] at *
    grind
  · positivity

/-
The number of permutations on Fin n that move exactly m elements
    is at most n^m.
-/
theorem count_perms_moving_m_le {n m : ℕ} :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun σ : Equiv.Perm (Fin n) => n - Fintype.card (Function.fixedPoints σ) = m)).card ≤ n ^ m := by
  -- The number of permutations fixing at least $n - m$ points is at most $n^m$.
  have h_count_fix : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => n - Fintype.card (Function.fixedPoints σ) = m)).card ≤ Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => σ) (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => Finset.card (Finset.filter (fun x => x∉(Function.fixedPoints σ)) (Finset.univ : Finset (Fin n))) = m))) := by
    simp +decide [ Fintype.card_subtype, Finset.filter_not, Finset.card_sdiff ];
  -- Each permutation with exactly $m$ non-fixed points can be constructed by choosing $m$ elements to permute and then permuting them.
  have h_construction : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => Finset.card (Finset.filter (fun x => x∉(Function.fixedPoints σ)) (Finset.univ : Finset (Fin n))) = m) ⊆ Finset.biUnion (Finset.powersetCard m (Finset.univ : Finset (Fin n))) (fun t => Finset.image (fun σ : Equiv.Perm {x // x ∈ t} => Equiv.Perm.ofSubtype σ) (Finset.univ : Finset (Equiv.Perm {x // x ∈ t}))) := by
    intro σ hσ; simp_all +decide [ Finset.subset_iff ] ;
    refine ⟨ Finset.filter ( fun x => ¬IsFixedPt σ x ) Finset.univ, hσ, ?_ ⟩;
    refine ⟨ Equiv.Perm.subtypePerm σ ?_, ?_ ⟩;
    all_goals simp +decide [ Equiv.Perm.ext_iff, Equiv.Perm.ofSubtype ];
    all_goals simp +decide [ IsFixedPt, Equiv.Perm.extendDomain ];
    all_goals try rfl;
    intro x; by_cases hx : σ x = x <;> simp +decide [ hx, Equiv.Perm.subtypePerm ] <;> try rfl;
  refine le_trans h_count_fix <| le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun σ hσ => h_construction hσ ) <| le_trans ( Finset.card_biUnion_le ) ?_;
  refine le_trans ( Finset.sum_le_sum fun _ _ => Finset.card_image_le ) ?_;
  simp +decide [ Finset.card_univ, Fintype.card_perm ];
  refine le_trans ( Finset.sum_le_sum fun x hx => Nat.factorial_le <| Finset.mem_powersetCard.mp hx |>.2.le ) ?_ ; norm_num [ Finset.card_univ ];
  rw [ Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _

/-
n / 2^{(n-2)/4} → 0 as n → ∞.
-/
theorem ratio_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ ((n - 2) / 4 : ℕ))
      Filter.atTop (nhds 0) := by
  -- We'll use the fact that $n / 2^{(n-2)/4}$ tends to $0$ as $n$ tends to infinity.
  suffices h_exp : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2 ^ (n / 4)) Filter.atTop (nhds 0) by
    rw [ ← Filter.tendsto_add_atTop_iff_nat 2 ];
    convert h_exp.add ( show Filter.Tendsto ( fun n : ℕ => ( 2 : ℝ ) / 2 ^ ( n / 4 ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr <| fun x => ⟨ 4 * x, fun n hn => by omega ⟩ ) using 2 <;> norm_num ; ring;
  -- We can convert this limit into a form that is easier to handle by substituting $m = n / 4$.
  suffices h_convert : Filter.Tendsto (fun m : ℕ => (4 * m : ℝ) / 2 ^ m) Filter.atTop (nhds 0) by
    have h_convert : Filter.Tendsto (fun n : ℕ => (4 * (n / 4 : ℕ) : ℝ) / 2 ^ (n / 4)) Filter.atTop (nhds 0) := by
      exact h_convert.comp <| Filter.tendsto_atTop_atTop.mpr fun m => ⟨ 4 * m, fun n hn => by linarith [ Nat.div_add_mod n 4, Nat.mod_lt n zero_lt_four ] ⟩;
    have h_convert : Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 4 * (n / 4 : ℕ)) / 2 ^ (n / 4)) Filter.atTop (nhds 0) := by
      have h_convert : ∀ n : ℕ, ((n : ℝ) - 4 * (n / 4 : ℕ)) ≤ 3 := by
        exact fun n => by rw [ sub_le_iff_le_add ] ; norm_cast; linarith [ Nat.div_add_mod n 4, Nat.mod_lt n zero_lt_four ] ;
      exact squeeze_zero ( fun n => div_nonneg ( sub_nonneg_of_le <| by norm_cast; linarith [ Nat.div_mul_le_self n 4 ] ) <| by positivity ) ( fun n => div_le_div_of_nonneg_right ( h_convert n ) <| by positivity ) <| tendsto_const_nhds.div_atTop <| tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 4 * x, fun n hn => by linarith [ Nat.div_add_mod n 4, Nat.mod_lt n zero_lt_four ] ⟩;
    convert h_convert.add ‹Tendsto ( fun n : ℕ => 4 * ( n / 4 : ℕ ) / 2 ^ ( n / 4 ) : ℕ → ℝ ) Filter.atTop ( nhds 0 ) › using 2 <;> ring;
  refine squeeze_zero_norm' ?_ tendsto_inv_atTop_nhds_zero_nat ; norm_num;
  exact ⟨ 20, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith ⟩

/-
The remainder from non-identity permutations tends to 0.
-/
-- The generated remainder estimate needs extra heartbeats for geometric-series bounds.
set_option maxHeartbeats 1600000 in
theorem remainder_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ =>
        (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (· ≠ 1),
          (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) /
        (2 ^ n.choose 2 : ℝ))
      Filter.atTop (nhds 0) := by
  -- Using the bound from `saving_lower_bound`, we can show that the sum is bounded above by a geometric series.
  have h_bound : ∀ n ≥ 4, (∑ σ : Equiv.Perm (Fin n), if σ ≠ 1 then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0) ≤ (∑ m ∈ Finset.Icc 2 n, (n : ℝ) ^ m / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ))) := by
    intros n hn
    have h_sum_bound : ∑ σ : Equiv.Perm (Fin n), (if σ ≠ 1 then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0) ≤ ∑ m ∈ Finset.Icc 2 n, (∑ σ : Equiv.Perm (Fin n), if n - Fintype.card (Function.fixedPoints σ) = m then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0) := by
      rw [ ← Finset.sum_comm ];
      refine Finset.sum_le_sum fun σ _ => ?_;
      by_cases hσ : σ = 1 <;> simp +decide [ hσ ];
      -- Since σ is not the identity, there are at least two elements not fixed by σ.
      have h_not_fixed : ∃ x y : Fin n, x ≠ y ∧ σ x ≠ x ∧ σ y ≠ y := by
        obtain ⟨x, hx⟩ : ∃ x : Fin n, σ x ≠ x := by
          exact not_forall.mp fun h => hσ <| Equiv.Perm.ext h;
        by_cases h₂ : σ (σ x) = σ x;
        · exact False.elim <| hx <| σ.injective h₂;
        · grind +qlia;
      obtain ⟨ x, y, hxy, hx, hy ⟩ := h_not_fixed; have := Finset.card_le_card ( show Finset.filter ( fun z => σ z = z ) Finset.univ ⊆ Finset.univ \ { x, y } from fun z hz => by aesop ) ; simp_all +decide [ Finset.card_sdiff, Finset.card_singleton ] ;
      have hm_ge : 2 ≤ n - Fintype.card (Function.fixedPoints σ) := by
        simp [Fintype.card_subtype, Function.fixedPoints, IsFixedPt] at *
        omega
      have hm_ge' : 2 ≤ n - #(Finset.filter (fun x : Fin n => σ x = x) Finset.univ) := by
        simpa [Fintype.card_subtype, Function.fixedPoints, IsFixedPt] using hm_ge
      simp [hm_ge', Fintype.card_subtype, Function.fixedPoints, IsFixedPt];
    refine le_trans h_sum_bound <| Finset.sum_le_sum fun m hm => ?_;
    have h_card_bound : ∀ σ : Equiv.Perm (Fin n), n - Fintype.card (Function.fixedPoints σ) = m → (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) ≤ 1 / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ)) := by
      intros σ hσ
      have h_card_bound : (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) ≤ (2 : ℝ) ^ (n.choose 2 : ℤ) / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ)) := by
        convert saving_lower_bound ( by linarith : 2 ≤ n ) σ _ using 1;
        · norm_cast ; aesop;
        · rintro rfl; simp_all +decide [ Fintype.card_subtype ];
          linarith;
      rw [ div_le_iff₀ ]
      · simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h_card_bound
      · positivity
    have h_card_bound : (∑ σ : Equiv.Perm (Fin n), if n - Fintype.card (Function.fixedPoints σ) = m then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0) ≤ (Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => n - Fintype.card (Function.fixedPoints σ) = m) Finset.univ) : ℝ) * (1 / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ))) := by
      rw [ Finset.sum_ite ];
      simpa using Finset.sum_le_sum fun x hx => h_card_bound x <| Finset.mem_filter.mp hx |>.2;
    refine le_trans h_card_bound ?_;
    convert mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( count_perms_moving_m_le ( n := n ) ( m := m ) ) ) ( by positivity : ( 0 : ℝ ) ≤ 1 / 2 ^ ( m * ( n - 2 ) / 4 ) ) using 1 ; ring_nf;
    norm_num [ mul_comm ];
  -- Let $r_n = \frac{n}{2^{(n-2)/4}}$. By ratio_tendsto_zero, $r_n \to 0$ as $n \to \infty$.
  set r : ℕ → ℝ := fun n => (n : ℝ) / (2 : ℝ) ^ ((n - 2) / 4 : ℕ)
  have hr_zero : Filter.Tendsto r Filter.atTop (nhds 0) := by
    convert ratio_tendsto_zero using 1;
  -- So Σ_{σ≠1} |Fix(σ)|/2^N ≤ Σ_{m=2}^n r_n^m.
  have h_sum_bound : ∀ n ≥ 4, (∑ σ : Equiv.Perm (Fin n), if σ ≠ 1 then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0) ≤ (∑ m ∈ Finset.Icc 2 n, (r n : ℝ) ^ m) := by
    intro n hn; refine le_trans ( h_bound n hn ) ?_; refine Finset.sum_le_sum fun m hm => ?_; rw [ div_pow ] ; ring_nf; norm_num;
    exact mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( Nat.mul_div_le_mul_div_assoc _ _ _ ) ) ( by positivity );
  -- For large enough n, r_n < 1/2 (say), and the sum ≤ r_n^2 / (1-r_n) ≤ 2*r_n^2 → 0.
  have h_geo_series : ∀ᶠ n in Filter.atTop, (∑ m ∈ Finset.Icc 2 n, (r n : ℝ) ^ m) ≤ 2 * (r n : ℝ) ^ 2 := by
    have h_geo_series : ∀ᶠ n in Filter.atTop, r n < 1 / 2 := by
      exact hr_zero.eventually ( gt_mem_nhds <| by norm_num );
    filter_upwards [ h_geo_series, Filter.eventually_ge_atTop 2 ] with n hn hn';
    erw [ geom_sum_Ico ] <;> norm_num at *;
    · rw [ div_le_iff_of_neg ] <;> nlinarith [ show 0 ≤ r n from by positivity, pow_nonneg ( show 0 ≤ r n from by positivity ) 2, pow_nonneg ( show 0 ≤ r n from by positivity ) ( n + 1 ), pow_le_pow_of_le_one ( show 0 ≤ r n from by positivity ) ( show r n ≤ 1 by linarith ) ( show n + 1 ≥ 2 by linarith ) ];
    · linarith;
    · linarith;
  -- Using the bounds, we can show that the sum tends to 0.
  have h_tendsto_zero : Filter.Tendsto (fun n => (∑ σ : Equiv.Perm (Fin n), if σ ≠ 1 then (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) / 2 ^ (n.choose 2 : ℤ) else 0)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun n => 2 * r n ^ 2) ?_ ?_;
    · filter_upwards [ h_geo_series, Filter.eventually_ge_atTop 4 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; exact le_trans ( h_sum_bound n hn' ) hn;
    · simpa using tendsto_const_nhds.mul ( hr_zero.pow 2 );
  convert h_tendsto_zero using 2 ; norm_cast ; simp +decide [ Finset.sum_ite, Finset.filter_ne' ];
  rw [ ← Finset.sum_div, sub_div ]

/-! ## Main theorem -/

/-
**Pólya–Wright theorem**: `numIsoClasses n / paperDenom n → 1`.
    Mathematically identical to `UniqueSubgraphs.polya_wright_theorem`.
-/
theorem polya_wright_theorem_prime :
    Filter.Tendsto
      (fun n : ℕ => (numIsoClasses n : ℝ) / paperDenom n)
      Filter.atTop (nhds 1) := by
  have h1 : (1 : ℝ) = 1 + 0 := by ring
  rw [h1]
  apply Filter.Tendsto.congr (fun n => (ratio_eq_one_plus_remainder n).symm)
  exact Filter.Tendsto.const_add 1 remainder_tendsto_zero

end PolyaWright
end PolyaWrightSection

/-! ==================================================================
    Chernoff Bound
    (originally ChernoffBound.lean)
    ================================================================== -/

section ChernoffBoundSection

/-!
# Chernoff Bound (Hoeffding's Inequality for Fair Coin Flips)

This file proves the Chernoff/Hoeffding bound for sums of independent fair coin flips,
stated combinatorially: among all 2^N Boolean vectors, the fraction with sum deviating
from N/2 by ≥ t satisfies the bound ≤ 2·exp(−2t²/N).

The proof uses the standard exponential moment method:
1. Exponential Markov inequality (counting version)
2. MGF factorization over product type
3. The inequality cosh(x) ≤ exp(x²/2) (from Mathlib)
4. Optimization of the exponential tilt parameter
5. Symmetry (bit-flipping) for the lower tail
-/

open Finset Real Function
open scoped BigOperators

namespace ChernoffBound

/-! ## Definitions -/

/-- The count of `true` values in a Boolean function on `Fin N`. -/
abbrev boolCount {N : ℕ} (f : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

/-! ## Step 1: MGF factorization -/

/-
Key identity: the sum of exp(λ · count) over all Boolean vectors equals (1 + exp λ)^N.
    This is the product factorization of the moment generating function.
-/
lemma mgf_factorization (N : ℕ) (lam : ℝ) :
    ∑ f : Fin N → Bool, Real.exp (lam * (boolCount f : ℝ)) =
    (1 + Real.exp lam) ^ N := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ f : Fin N → Bool, ∏ i, Real.exp (lam * (if f i then 1 else 0)) = ∏ i : Fin N, (∑ b : Bool, Real.exp (lam * (if b then 1 else 0))) := by
        exact Eq.symm (Fintype.prod_sum fun i j => rexp (lam * if j = true then 1 else 0));
      convert h_fubini using 1;
      · simp +decide [ ← Real.exp_sum, mul_comm, Finset.sum_ite ];
      · norm_num [ add_comm, Finset.prod_pow ]

/-! ## Step 2: Exponential Markov inequality (counting version) -/

/-
Exponential Markov inequality: for λ ≥ 0, the number of Boolean vectors with
    count ≥ m is at most exp(-λm) times the MGF sum.
-/
lemma exp_markov_count (N : ℕ) (lam : ℝ) (m : ℝ) (hlam : lam ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ m)).card : ℝ) ≤
    Real.exp (-lam * m) *
    ∑ f : Fin N → Bool, Real.exp (lam * (boolCount f : ℝ)) := by
      have h_exp_markov : ∀ f : Fin N → Bool, (if (boolCount f : ℝ) ≥ m then 1 else 0) ≤ Real.exp (-lam * m) * Real.exp (lam * (boolCount f : ℝ)) := by
        intro f
        split_ifs <;> simp_all +decide [ ← Real.exp_add ]
        · nlinarith
        · positivity;
      simpa [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun f ( hf : f ∈ Finset.univ ) => h_exp_markov f

/-! ## Step 3: Bounding (1 + exp λ) -/

/-
The key analytical bound: (1 + exp λ) / 2 ≤ exp(λ/2 + λ²/8).
    This follows from (1+exp λ)/2 = exp(λ/2)·cosh(λ/2) and cosh(x) ≤ exp(x²/2).
-/
lemma one_plus_exp_half_bound (lam : ℝ) :
    (1 + Real.exp lam) / 2 ≤ Real.exp (lam / 2 + lam ^ 2 / 8) := by
      -- We'll use the exponential property to simplify the expression. Note that $(1 + \exp \lambda) / 2$ can be bounded above.
      have h_exp : (1 + Real.exp lam) / 2 ≤ Real.exp (lam / 2) * Real.cosh (lam / 2) := by
        rw [ Real.cosh_eq ] ; ring_nf ; norm_num [ ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf; norm_num;
      exact h_exp.trans ( by rw [ Real.exp_add ] ; exact mul_le_mul_of_nonneg_left ( by simpa using Real.cosh_le_exp_half_sq ( lam / 2 ) ) ( by positivity ) |> le_trans <| by ring_nf; norm_num )

/-! ## Step 4: Upper tail bound -/

/-
Upper tail Chernoff bound: the number of Boolean vectors with count ≥ N/2 + t
    is at most 2^N · exp(-2t²/N).
-/
lemma upper_tail_bound (N : ℕ) (t : ℝ) (ht : t ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
      by_cases hN : N = 0 <;> simp_all +decide [ neg_div, neg_mul ];
      · exact Finset.card_le_one.mpr ( by aesop );
      · -- Use exp_markov_count with lam₀ = 4*t/N, which is ≥ 0 since t ≥ 0 and N > 0.
        have h_exp_markov : ((Finset.univ.filter (fun f : Fin N → Bool => (boolCount f : ℝ) ≥ N / 2 + t)).card : ℝ) ≤
            Real.exp (-4 * t / N * (N / 2 + t)) * (∑ f : Fin N → Bool, Real.exp (4 * t / N * (boolCount f : ℝ))) := by
              convert exp_markov_count N ( 4 * t / N ) ( N / 2 + t ) ( by positivity ) using 1 ; ring_nf;
        -- Now bound (1 + exp lam₀)^N: (1 + exp lam₀) = 2 * ((1 + exp lam₀)/2) ≤ 2 * exp(lam₀/2 + lam₀²/8) (by one_plus_exp_half_bound)
        have h_bound : (∑ f : Fin N → Bool, Real.exp (4 * t / N * (boolCount f : ℝ))) ≤ 2 ^ N * Real.exp (N * (4 * t / N / 2 + (4 * t / N) ^ 2 / 8)) := by
          rw [ mgf_factorization ];
          have := one_plus_exp_half_bound ( 4 * t / N );
          rw [ ← div_le_iff₀' ( by positivity ) ];
          simpa only [ ← div_pow, ← Real.exp_nat_mul ] using pow_le_pow_left₀ ( by positivity ) this _;
        refine le_trans (h_exp_markov.trans (mul_le_mul_of_nonneg_left h_bound <| Real.exp_nonneg _)) ?_
        calc
          Real.exp (-4 * t / N * (N / 2 + t)) *
              (2 ^ N * Real.exp (N * (4 * t / N / 2 + (4 * t / N) ^ 2 / 8)))
              = 2 ^ N * Real.exp
                  (-4 * t / N * (N / 2 + t) +
                    N * (4 * t / N / 2 + (4 * t / N) ^ 2 / 8)) := by
                rw [Real.exp_add]
                ring
          _ = 2 ^ N * Real.exp (-(2 * t ^ 2 / N)) := by
                congr 1
                field_simp [hN]
                ring_nf
          _ ≤ 2 ^ N * Real.exp (-(2 * t ^ 2 / N)) := le_rfl

/-! ## Step 5: Bit-flipping symmetry -/

/-
Flipping all bits sends count k to N - k.
-/
lemma boolCount_not {N : ℕ} (f : Fin N → Bool) :
    boolCount (fun i => !(f i)) = N - boolCount f := by
      unfold boolCount;
      simpa using Finset.card_compl ( Finset.filter ( fun i => f i = Bool.true ) Finset.univ )

/-
The bit-flip map is a bijection on `Fin N → Bool`.
-/
lemma boolFlip_bijective (N : ℕ) :
    Bijective (fun (f : Fin N → Bool) (i : Fin N) => !(f i)) := by
      exact ⟨ fun f g h => by ext i; simpa using congr_fun h i, fun f => ⟨ fun i => !f i, by aesop ⟩ ⟩

/-! ## Step 6: Lower tail bound -/

/-
Lower tail Chernoff bound via bit-flipping symmetry.
-/
lemma lower_tail_bound (N : ℕ) (t : ℝ) (_ht : t ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
      convert ChernoffBound.upper_tail_bound N t _ht using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ ← Equiv.sum_comp ( show ( Fin N → Bool ) ≃ ( Fin N → Bool ) from Equiv.ofBijective ( fun f => fun i => !f i ) ( by exact ChernoffBound.boolFlip_bijective N ) ) ];
      norm_num [ ChernoffBound.boolCount_not ];
      refine congr_arg _ ( Finset.filter_congr fun x hx => ?_ );
      rw [ Nat.cast_sub ( show boolCount x ≤ N from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; constructor <;> intro <;> linarith

/-! ## Step 7: Combining tails -/

/-
The absolute deviation filter is contained in the union of upper and lower tails.
-/
lemma abs_deviation_card_le (N : ℕ) (t : ℝ) (_ht : t ≥ 0) :
    (Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card ≤
    (Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card +
    (Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        -- Let's simplify the set on the right-hand side.
        apply le_add_right; apply Finset.card_mono; intro f hf; simp_all +decide [ abs_eq_max_neg ] ;
        exact Or.imp ( fun h => by linarith! ) ( fun h => by linarith! ) hf

/-! ## Main Theorem -/

/-- **Chernoff bound** (Hoeffding's inequality for fair coin flips):
    For N independent fair coin flips, the number of Boolean vectors with sum deviating
    from N/2 by at least t is at most 2·2^N·exp(-2t²/N). -/
theorem chernoff_bound_prime :
    ∀ (N : ℕ) (t : ℝ), t ≥ 0 →
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ) ≤
    2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
  intro N t ht
  have h1 := abs_deviation_card_le N t ht
  have h2 := upper_tail_bound N t ht
  have h3 := lower_tail_bound N t ht
  calc ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ)
      ≤ ((Finset.univ.filter (fun f : Fin N → Bool =>
        (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card : ℝ) +
        ((Finset.univ.filter (fun f : Fin N → Bool =>
        (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card : ℝ) := by exact_mod_cast h1
      _ ≤ (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) +
          (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by linarith
      _ = 2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by ring

end ChernoffBound
end ChernoffBoundSection

/-! ==================================================================
    Azuma-Hoeffding Inequality
    (originally AzumaHoeffding.lean)
    ================================================================== -/

section AzumaHoeffdingSection

/-!
# Azuma–Hoeffding Inequality (Bounded Differences)

This file proves the Azuma–Hoeffding inequality for functions of independent
fair coin flips with bounded differences. The statement is copied exactly from
`RequestProject/Main.lean` (where it appears as a black-box placeholder).

## Main result

`azuma_hoeffding_prime` — identical statement to `azuma_hoeffding` in Main.lean.

## Proof strategy

We use the exponential moment method:

1. **Exponential moment bound** (`exp_moment_bound`): For any λ ∈ ℝ,
   `∑ x, exp(λ(μ - f(x))) ≤ 2^n * exp(λ²/8 * ∑ bᵢ²)`.
   Proved by induction on n, using `avg_exp_le` (which follows from
   `Real.cosh_le_exp_half_sq`) and averaging over coordinates.

2. **Markov's inequality** (`markov_counting`): combinatorial counting form.

3. **Optimization**: Choose λ = 4t/∑bᵢ² (when ∑bᵢ² > 0) to get the
   optimal bound `exp(-2t²/∑bᵢ²)`.
-/

open Finset Real

namespace AzumaHoeffding

/-! ## Part 1: Analytic helper -/

/-
Key analytic inequality: exp(a+d) + exp(a-d) ≤ 2·exp(a + d²/2).
    Follows from cosh(d) ≤ exp(d²/2).
-/
lemma avg_exp_le (a d : ℝ) :
    exp (a + d) + exp (a - d) ≤ 2 * exp (a + d ^ 2 / 2) := by
  -- By dividing both sides of the inequality by $e^a$, we get $e^d + e^{-d} \leq 2e^{d^2/2}$.
  have h_div : Real.exp d + Real.exp (-d) ≤ 2 * Real.exp (d^2 / 2) := by
    have := @Real.cosh_le_exp_half_sq;
    have := this d; rw [ Real.cosh_eq ] at this; linarith;
  calc
    Real.exp (a + d) + Real.exp (a - d)
        = Real.exp a * (Real.exp d + Real.exp (-d)) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
          ring
    _ ≤ Real.exp a * (2 * Real.exp (d ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left h_div (Real.exp_nonneg a)
    _ = 2 * Real.exp (a + d ^ 2 / 2) := by
          rw [Real.exp_add]
          ring

/-! ## Part 2: Combinatorial infrastructure -/

/-
Decomposition of sums over `Fin (n+1) → Bool` into sums over
    the first coordinate and the remaining coordinates.
-/
lemma sum_fin_succ_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → Bool, f x =
    ∑ b : Bool, ∑ y : Fin n → Bool, f (Fin.cons b y) := by
  rw [ ← Finset.sum_product' ];
  refine Finset.sum_bij ( fun x _ => ( x 0, x ∘ Fin.succ ) ) ?_ ?_ ?_ ?_ <;> simp +decide;
  · exact fun a₁ a₂ h₁ h₂ => funext fun i => by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
  · exact ⟨ fun b => ⟨ Fin.cons false b, rfl, rfl ⟩, fun b => ⟨ Fin.cons true b, rfl, rfl ⟩ ⟩;
  · exact fun x => by congr; ext i; induction i using Fin.inductionOn <;> aesop;

/-- The averaging function: average f over the first coordinate. -/
def avgFn {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun y => (f (Fin.cons false y) + f (Fin.cons true y)) / 2

/-! ## Part 3: Properties of avgFn -/

/-
The mean of avgFn equals the mean of f.
-/
lemma avgFn_mean {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ y : Fin n → Bool, avgFn f y) / ((2 : ℝ) ^ n) =
    (∑ x : Fin (n + 1) → Bool, f x) / ((2 : ℝ) ^ (n + 1)) := by
  simp +decide [ sum_fin_succ_eq, avgFn ];
  simpa only [ ← Finset.sum_div _ _ _, Finset.sum_add_distrib, add_comm ] using by ring;

/-
avgFn inherits bounded differences from f (with bounds shifted by Fin.succ).
-/
lemma avgFn_bounded_diff {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) (b : Fin (n + 1) → ℝ)
    (hbd : ∀ i : Fin (n + 1), ∀ x y : Fin (n + 1) → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) :
    ∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |avgFn f x - avgFn f y| ≤ b (Fin.succ i) := by
  -- By definition of `avgFn`, we have:
  intros i x y hxy
  simp [avgFn];
  rw [ abs_le ];
  constructor <;> linarith [ abs_le.mp ( hbd i.succ ( Fin.cons false x ) ( Fin.cons false y ) fun j hj => by cases j using Fin.inductionOn <;> aesop ), abs_le.mp ( hbd i.succ ( Fin.cons true x ) ( Fin.cons true y ) fun j hj => by cases j using Fin.inductionOn <;> aesop ) ]

/-
The difference |f(cons true y) - f(cons false y)| ≤ b 0.
-/
lemma cons_diff_bound {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) (b : Fin (n + 1) → ℝ)
    (hbd : ∀ i : Fin (n + 1), ∀ x y : Fin (n + 1) → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (y : Fin n → Bool) :
    |f (Fin.cons true y) - f (Fin.cons false y)| ≤ b 0 := by
  exact hbd 0 _ _ fun j hj => by cases j using Fin.inductionOn <;> tauto;

/-! ## Part 4: Exponential moment bound -/

/-
Base case of the exponential moment bound.
-/
lemma exp_moment_bound_zero (f : (Fin 0 → Bool) → ℝ) (lam : ℝ) :
    ∑ x : Fin 0 → Bool, exp (lam * ((∑ z : Fin 0 → Bool, f z) / ((2 : ℝ) ^ 0) - f x)) ≤
    ((2 : ℝ) ^ 0) * exp (lam ^ 2 / 8 * ∑ i : Fin 0, (0 : ℝ) ^ 2) := by
  simp +zetaDelta at *

/-
**Exponential moment bound**: For any function f of n independent fair coin flips
    with bounded differences bᵢ, and any λ ∈ ℝ:
    `∑ x, exp(λ(μ - f(x))) ≤ 2^n * exp(λ²/8 * ∑ bᵢ²)`.

    Proved by induction on n.
-/
theorem exp_moment_bound (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ)
    (hbd : ∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (lam : ℝ) :
    ∑ x : Fin n → Bool, exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≤
    ((2 : ℝ) ^ n) * exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2) := by
  revert n f b hbd;
  refine fun n => Nat.recOn n ?_ ?_;
  · aesop;
  · intro n ih f b hbd;
    -- Let μ = (∑ x, f x) / 2^(n+1) and g = avgFn f, μ_g = (∑ y, g y) / 2^n.
    set μ : ℝ := (∑ x, f x) / 2 ^ (n + 1)
    set g : (Fin n → Bool) → ℝ := avgFn f
    set μ_g : ℝ := (∑ y, g y) / 2 ^ n;
    -- By avgFn_mean, μ_g = μ.
    have hμ_g : μ_g = μ := by
      exact avgFn_mean f;
    -- Now f(cons false y) = g(y) - d(y) and f(cons true y) = g(y) + d(y) where d(y) = (f(cons true y) - f(cons false y))/2.
    have h_decomp : ∀ y : Fin n → Bool, Real.exp (lam * (μ - f (Fin.cons false y))) + Real.exp (lam * (μ - f (Fin.cons true y))) ≤ 2 * Real.exp (lam * (μ_g - g y) + lam ^ 2 * (b 0) ^ 2 / 8) := by
      intro y
      set d := (f (Fin.cons true y) - f (Fin.cons false y)) / 2
      have h_exp : Real.exp (lam * (μ - f (Fin.cons false y))) + Real.exp (lam * (μ - f (Fin.cons true y))) ≤ 2 * Real.exp (lam * (μ_g - g y) + lam ^ 2 * d ^ 2 / 2) := by
        convert avg_exp_le ( lam * ( μ_g - g y ) ) ( lam * d ) using 1 <;> ring_nf;
        simp +zetaDelta at *;
        rw [ hμ_g ] ; ring_nf;
        unfold avgFn; ring_nf;
      -- By cons_diff_bound, |f(cons true y) - f(cons false y)| ≤ b 0, so d² ≤ (b 0)² / 4.
      have h_d_bound : d ^ 2 ≤ (b 0) ^ 2 / 4 := by
        simp +zetaDelta at *;
        nlinarith only [ abs_le.mp ( hbd 0 ( Fin.cons true y ) ( Fin.cons false y ) fun j hj => by cases j using Fin.inductionOn <;> tauto ) ];
      exact h_exp.trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) zero_le_two );
    -- By the induction hypothesis applied to g with bounds (b ∘ Fin.succ) using avgFn_bounded_diff:
    have h_ind : ∑ y : Fin n → Bool, Real.exp (lam * (μ_g - g y)) ≤ 2 ^ n * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b (Fin.succ i)) ^ 2) := by
      exact ih g (fun i => b (Fin.succ i)) (avgFn_bounded_diff f b hbd);
    -- Combining the decomposition and induction hypothesis:
    have h_combined : ∑ x : Fin (n + 1) → Bool, Real.exp (lam * (μ - f x)) ≤ 2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) * ∑ y : Fin n → Bool, Real.exp (lam * (μ_g - g y)) := by
      calc
        ∑ x : Fin (n + 1) → Bool, Real.exp (lam * (μ - f x))
            = ∑ y : Fin n → Bool,
                (Real.exp (lam * (μ - f (Fin.cons false y))) +
                 Real.exp (lam * (μ - f (Fin.cons true y)))) := by
              rw [sum_fin_succ_eq]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => by
                rw [Finset.sum_eq_add false true] <;> simp +decide
        _ ≤ ∑ y : Fin n → Bool,
              2 * Real.exp (lam * (μ_g - g y) + lam ^ 2 * (b 0) ^ 2 / 8) := by
              exact Finset.sum_le_sum fun y _ => h_decomp y
        _ = 2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) *
              ∑ y : Fin n → Bool, Real.exp (lam * (μ_g - g y)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ => by
                rw [Real.exp_add]
                ring
    refine le_trans (h_combined.trans (mul_le_mul_of_nonneg_left h_ind <| by positivity)) ?_
    calc
      2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) *
          (2 ^ n * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i.succ) ^ 2))
          = 2 ^ n.succ *
              Real.exp (lam ^ 2 * (b 0) ^ 2 / 8 +
                lam ^ 2 / 8 * ∑ i : Fin n, (b i.succ) ^ 2) := by
            rw [Real.exp_add, pow_succ]
            norm_num
            ring
      _ = 2 ^ n.succ * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n.succ, (b i) ^ 2) := by
            congr 1
            rw [Fin.sum_univ_succ]
            ring_nf
      _ ≤ 2 ^ n.succ * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n.succ, (b i) ^ 2) := le_rfl

/-! ## Part 5: Counting Markov's inequality -/

/-
Counting form of Markov's inequality.
-/
lemma markov_counting {α : Type*} [Fintype α] (g : α → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, 0 ≤ g x) :
    ((Finset.univ.filter (fun x => g x ≥ c)).card : ℝ) * c ≤ ∑ x, g x := by
  have := Finset.sum_le_sum fun x ( hx : x ∈ Finset.univ ) => show g x ≥ if g x ≥ c then c else 0 by split_ifs <;> linarith [ hg x ];
  simpa [ Finset.sum_ite ] using this

/-! ## Part 6: Main theorem -/

/-
**Azuma–Hoeffding inequality** (bounded differences / McDiarmid's inequality).
    Exact copy of the statement from `Main.lean`.
-/
theorem azuma_hoeffding_prime :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i : Fin n, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let μ := (∑ x : (Fin n → Bool), f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter (fun x : Fin n → Bool => f x ≤ μ - t)).card : ℝ) ≤
    (2 ^ n : ℝ) * exp (-2 * t ^ 2 / ∑ i : Fin n, (b i) ^ 2) := by
  intros n f b hbd hb t ht;
  -- Use exp_moment_bound with lam = 4*t/S.
  set lam := 4 * t / (∑ i, b i ^ 2)
  have h_exp_moment : ∑ x : Fin n → Bool, Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≤ ((2 : ℝ) ^ n) * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2) := by
    exact exp_moment_bound n f b hbd lam;
  -- Apply Markov's inequality to the exponential moment bound.
  have h_markov : ((Finset.univ.filter (fun x => Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≥ Real.exp (lam * t))).card : ℝ) ≤ ((2 : ℝ) ^ n) * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2 - lam * t) := by
    have h_markov : ((Finset.univ.filter (fun x => Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≥ Real.exp (lam * t))).card : ℝ) * Real.exp (lam * t) ≤ ∑ x : Fin n → Bool, Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) := by
      have := markov_counting ( fun x => Real.exp ( lam * ( ( ∑ z, f z ) / 2 ^ n - f x ) ) ) ( Real.exp ( lam * t ) ) ( Real.exp_pos _ ) ( fun x => Real.exp_nonneg _ ) ; aesop;
    rw [ Real.exp_sub ];
    rw [ ← mul_div_assoc, le_div_iff₀ ( Real.exp_pos _ ) ] ; linarith;
  refine le_trans ?_ ( h_markov.trans ?_ );
  · norm_num;
    exact Finset.card_mono fun x hx => by exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by nlinarith [ Finset.mem_filter.mp hx, show 0 ≤ lam by exact div_nonneg ( mul_nonneg zero_le_four ht ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ⟩ ;
  · grind

end AzumaHoeffding
end AzumaHoeffdingSection

/-! ==================================================================
    Main Theorem — Unique Subgraphs Are Rare
    ================================================================== -/

/-!
# Unique Subgraphs Are Rare

Formalization of the paper "Unique subgraphs are rare" by Domagoj Bradač and Micha Christoph.

## Overview

A folklore result attributed to Pólya states that there are (1 + o(1))·2^{n choose 2}/n!
non-isomorphic graphs on n vertices. Given two graphs G and H on n vertices, we say that
G is a *unique subgraph* of H if H contains exactly one subgraph isomorphic to G.

For an n-vertex graph H, let f(H) be the number of non-isomorphic unique subgraphs of H
divided by 2^{n choose 2}/n!, and let f(n) denote the maximum of f(H) over all n-vertex
graphs H. Erdős asked (1975) whether there exists δ > 0 such that f(n) > δ for all n.

The paper shows that f(n) → 0, confirming Erdős' intuition that no graph on n vertices
contains a constant proportion of all graphs as unique subgraphs.

## Structure

The proof proceeds in three steps:
1. **Lemma 2.1** reduces f(H) to Pr_{G ∼ G(n,1/2)}[G has a unique embedding into H] + o(1).
2. **Lemma 2.2** shows that if this probability is ≥ δ, then H must be very dense:
   e(H) ≥ C(n,2) - Cn.
3. **Lemma 2.3** shows that for very dense H, the probability is o(1).

The main theorem follows from the composition of Lemmas 2.2 and 2.3.

## Black-box theorems (now fully proved)

Three standard results were previously taken as black-box placeholder axioms and are now
proved in separate files:
1. **Pólya–Wright theorem** — proved in `PolyaWright.lean`
2. **Chernoff bound** — proved in `ChernoffBound.lean`
3. **Azuma–Hoeffding inequality** — proved in `AzumaHoeffding.lean`

Core definitions and Burnside machinery are in `MainDefs.lean`.

## References

- Bradač, D., Christoph, M. "Unique subgraphs are rare" (2024)
- Erdős, P. "Problems and results in graph theory and combinatorial analysis" (1975)
-/

open Finset Function SimpleGraph

namespace UniqueSubgraphs

/-! ## Black-Box Theorems (proved via standalone files) -/

/-- **Pólya–Wright theorem**: the number of isomorphism classes of graphs on Fin n is
    asymptotically 2^{n choose 2} / n!. Stated as: the ratio tends to 1.
    Proved in `PolyaWright.lean`. -/
theorem polya_wright_theorem :
    Filter.Tendsto
      (fun n : ℕ => (numIsoClasses n : ℝ) / paperDenom n)
      Filter.atTop (nhds 1) :=
  PolyaWright.polya_wright_theorem_prime

/-- **Chernoff bound** (Hoeffding's inequality for fair coin flips).
    Proved in `ChernoffBound.lean`. -/
theorem chernoff_bound :
    ∀ (N : ℕ) (t : ℝ), t ≥ 0 →
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ) ≤
    2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) :=
  ChernoffBound.chernoff_bound_prime

/-- **Azuma–Hoeffding inequality** (bounded differences / McDiarmid's inequality).
    Proved in `AzumaHoeffding.lean`. -/
theorem azuma_hoeffding :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i : Fin n, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let μ := (∑ x : (Fin n → Bool), f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter (fun x : Fin n → Bool => f x ≤ μ - t)).card : ℝ) ≤
    (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / ∑ i : Fin n, (b i) ^ 2) :=
  AzumaHoeffding.azuma_hoeffding_prime

/-! ## Derivation of Key Lemmas -/

/-! ### Derivation of almost_all_trivial_aut -/

/-
Almost all graphs on n vertices have trivial automorphism group.
    Derived from Pólya–Wright via Burnside's lemma.
-/
theorem almost_all_trivial_aut :
    Filter.Tendsto
      (fun n : ℕ =>
        ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
          (autFinset G).card ≠ 1)).card : ℝ) /
        (2 ^ n.choose 2 : ℝ))
      Filter.atTop (nhds 0) := by
  -- From the nontrivial_aut_bound and polya_wright_theorem, we get:
  have upper_bound : ∀ n, ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => (autFinset G).card ≠ 1)).card : ℝ) / (2 ^ n.choose 2 : ℝ) ≤ (numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1 := by
    intro n;
    rw [ div_sub_one, div_le_div_iff_of_pos_right ] <;> norm_num;
    exact nontrivial_aut_bound n;
  -- By the squeeze theorem, if the upper bound tends to 0, then the original fraction tends to 0.
  have squeeze_theorem : Filter.Tendsto (fun n => (numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1) Filter.atTop (nhds 0) := by
    convert ( polya_wright_theorem.sub_const 1 ) using 2 <;> ring_nf!;
    unfold paperDenom; ring_nf;
    norm_num;
  exact squeeze_zero ( fun n => by positivity ) upper_bound squeeze_theorem

/-! ### Derivation of reduction_to_random -/

/-
Key equivalence: UniquelyEmbeds G H ↔ IsUniqueSubgraph G H ∧ |Aut(G)| = 1.
-/
theorem uniquelyEmbeds_iff_uniqueSub_trivialAut {n : ℕ} (G H : SimpleGraph (Fin n)) :
    UniquelyEmbeds G H ↔ IsUniqueSubgraph G H ∧ (autFinset G).card = 1 := by
  constructor;
  · intro h;
    constructor;
    · obtain ⟨φ, hφ⟩ : ∃! φ : Equiv.Perm (Fin n), IsEmbedding G H φ := by
        exact (Fintype.existsUnique_iff_card_one (IsEmbedding G H)).mpr h;
      use ⟨ Set.univ, fun u v => G.Adj ( φ⁻¹ u ) ( φ⁻¹ v ), by
        exact fun { v w } h => by simpa using hφ.1 ( φ⁻¹ v ) ( φ⁻¹ w ) h;, by
        exact fun _ => Set.mem_univ _, by
        exact ⟨fun u v huv => G.adj_symm huv⟩ ⟩
      generalize_proofs at *;
      constructor;
      · refine ⟨ ?_, ?_ ⟩;
        · exact Subgraph.isSpanning_iff.mpr rfl;
        · refine ⟨ ?_, ?_ ⟩;
          exacts [ φ⁻¹, by simp +decide [ SimpleGraph.spanningCoe ] ];
      · rintro ⟨ S, hS ⟩ ⟨ hS₁, ⟨ f ⟩ ⟩;
        have h_iso : ∃ ψ : Equiv.Perm (Fin n), ∀ u v, G.Adj u v ↔ hS (ψ u) (ψ v) := by
          use f.symm.toEquiv;
          exact fun u v => by simpa using f.symm.map_adj_iff.symm;
        obtain ⟨ ψ, hψ ⟩ := h_iso;
        have h_iso : ψ = φ := by
          apply hφ.right;
          intro u v huv; specialize hψ u v; aesop;
        congr! 1;
        · exact Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 ↦ hS₁ a;
        · ext u v; specialize hψ ( φ⁻¹ u ) ( φ⁻¹ v ) ; aesop;
    · rw [ Finset.card_eq_one ];
      obtain ⟨ φ, hφ ⟩ := Finset.card_eq_one.mp h;
      use 1; ext σ; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      constructor <;> intro hσ <;> simp_all +decide [ embeddingFinset, autFinset ];
      have := hφ.2 ( φ * σ ) ?_;
      · simpa using this;
      · intro u v huv; specialize hσ u v; aesop;
  · intro h
    obtain ⟨h_unique_subgraph, h_aut⟩ := h
    have h_embedding : ∀ φ₁ φ₂ : Equiv.Perm (Fin n), (IsEmbedding G H φ₁) → (IsEmbedding G H φ₂) → ∃ σ : Equiv.Perm (Fin n), σ ∈ autFinset G ∧ φ₂ = φ₁ * σ := by
      intros φ₁ φ₂ hφ₁ hφ₂
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ = φ₁⁻¹ * φ₂ ∧ ∀ u v : Fin n, G.Adj u v ↔ G.Adj (σ u) (σ v) := by
        obtain ⟨ S, hS₁, hS₂ ⟩ := h_unique_subgraph;
        have h_subgraph : ∀ φ : Equiv.Perm (Fin n), IsEmbedding G H φ → ∃ S' : H.Subgraph, S'.IsSpanning ∧ Nonempty (S'.spanningCoe.Iso G) ∧ ∀ u v : Fin n, G.Adj u v ↔ S'.Adj (φ u) (φ v) := by
          intro φ hφ
          use ⟨Set.univ, fun u v => G.Adj (φ⁻¹ u) (φ⁻¹ v), by
            exact fun { v w } hvw => by simpa using hφ ( φ⁻¹ v ) ( φ⁻¹ w ) hvw;, by
            exact fun _ => Set.mem_univ _, by
            exact ⟨fun u v h => G.adj_symm h⟩⟩
          generalize_proofs at *;
          refine ⟨ ?_, ?_, ?_ ⟩;
          · exact Subgraph.isSpanning_iff.mpr rfl;
          · refine ⟨ ?_, ?_ ⟩;
            · exact φ⁻¹
            · aesop;
          · simp +decide [ Equiv.Perm.inv_eq_iff_eq ];
        obtain ⟨ S₁, hS₁₁, hS₁₂, hS₁₃ ⟩ := h_subgraph φ₁ hφ₁
        obtain ⟨ S₂, hS₂₁, hS₂₂, hS₂₃ ⟩ := h_subgraph φ₂ hφ₂
        have hS₁₂_eq : S₁ = S₂ := by
          rw [ hS₂ S₁ ⟨ hS₁₁, hS₁₂ ⟩, hS₂ S₂ ⟨ hS₂₁, hS₂₂ ⟩ ];
        simp_all +decide [ Equiv.Perm.inv_eq_iff_eq ];
      exact ⟨ σ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ.2 ⟩, by simp +decide [ hσ.1, mul_assoc ] ⟩;
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Equiv.Perm (Fin n), IsEmbedding G H φ₁ := by
      obtain ⟨ S, hS₁, hS₂ ⟩ := h_unique_subgraph;
      obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Equiv.Perm (Fin n), ∀ u v, G.Adj u v ↔ S.Adj (φ₁ u) (φ₁ v) := by
        obtain ⟨ φ₁, hφ₁ ⟩ := hS₁.2;
        use φ₁.symm;
        intro u v; specialize @hφ₁ ( φ₁.symm u ) ( φ₁.symm v ) ; aesop;
      use φ₁;
      exact fun u v huv => S.adj_sub ( hφ₁ u v |>.1 huv );
    have h_unique_embedding : ∀ φ₂ : Equiv.Perm (Fin n), IsEmbedding G H φ₂ → φ₂ = φ₁ := by
      have := Finset.card_eq_one.mp h_aut;
      obtain ⟨ a, ha ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      have := ha.2 1 ( id_mem_autFinset G ) ; aesop;
    exact Finset.card_eq_one.mpr ⟨ φ₁, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hφ₁ ⟩, fun φ₂ hφ₂ => h_unique_embedding φ₂ <| Finset.mem_filter.mp hφ₂ |>.2 ⟩ ⟩

/-
Key bound: fH(H) ≤ probUniqueEmb(H) + error, where error → 0.
    The error comes from iso classes with non-trivial automorphisms.
-/
lemma uniqueSubgraphClasses_card_le {n : ℕ} (H : SimpleGraph (Fin n)) :
    (uniqueSubgraphClasses H).card ≤
    numUniquelyEmbedding H + (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      (autFinset G).card ≠ 1)).card := by
  refine le_trans ?_ ( Finset.card_union_le (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
    UniquelyEmbeds G H)) (Finset.univ.filter (fun G : SimpleGraph (Fin n) => (autFinset G).card ≠ 1)) );
  refine le_trans ( Finset.card_image_le ) ?_;
  refine Finset.card_mono ?_;
  intro G hG;
  by_cases h : ( autFinset G ).card = 1 <;> simp_all +decide [ uniquelyEmbeds_iff_uniqueSub_trivialAut ]

/-
Orbit-stabilizer for this action: number of graphs isomorphic to G
    times |Aut(G)| equals n!. Proved using Mathlib's orbit-stabilizer.
-/
lemma orbit_card_mul_aut (n : ℕ) (G : SimpleGraph (Fin n)) :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) * (autFinset G).card =
    Nat.factorial n := by
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group ( Equiv.Perm ( Fin n ) ) G using 1;
  · rw [ Fintype.card_subtype ];
    rw [ Fintype.card_of_subtype ];
    intro x; erw [ mem_fixedBy_iff_mem_autFinset ] ;
  · simp +decide [ Fintype.card_perm ]

/-- For G with |aut|=1, the orbit has exactly n! elements. -/
lemma orbit_card_of_trivial_aut {n : ℕ} (G : SimpleGraph (Fin n))
    (h : (autFinset G).card = 1) :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) = Nat.factorial n := by
  have := orbit_card_mul_aut n G; rw [h] at this; omega

/-
n! divides numUniquelyEmbedding. Each UniquelyEmbeds-class has |aut|=1
    hence n! representatives.
-/
lemma factorial_dvd_numUniquelyEmbedding {n : ℕ} (H : SimpleGraph (Fin n)) :
    Nat.factorial n ∣ numUniquelyEmbedding H := by
  -- Let $S$ be the set of graphs on $n$ vertices which uniquely embed into $H$.
  set S := Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H);
  -- By definition of $S$, we know that the set $S$ is a union of complete orbits under the action of the permutation group.
  have h_union_orbits : ∀ G ∈ S, MulAction.orbit (Equiv.Perm (Fin n)) G ⊆ S := by
    norm_num +zetaDelta at *;
    intro G hG x hx; obtain ⟨ σ, rfl ⟩ := hx; simp_all +decide [ UniquelyEmbeds ] ;
    unfold numEmbeddings at *;
    unfold embeddingFinset at *;
    rw [ Finset.card_eq_one ] at *;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    obtain ⟨ a, ha₁, ha₂ ⟩ := hG;
    refine ⟨ a * σ⁻¹, ?_, ?_ ⟩;
    · intro u v; specialize ha₁ ( σ⁻¹ u ) ( σ⁻¹ v ) ; aesop;
    · intro τ hτ
      have hτemb : IsEmbedding (σ • G) H τ := by
        simpa [embeddingFinset] using hτ
      have hτG : IsEmbedding G H (τ * σ) := by
        intro u v huv
        exact hτemb (σ u) (σ v) (by simpa [smul_adj] using huv)
      have h_eq := ha₂ (τ * σ) hτG
      simpa [mul_assoc] using
        congrArg (fun ρ : Equiv.Perm (Fin n) => ρ * σ⁻¹) h_eq
  -- Since each orbit has size $n!$, the cardinality of $S$ is the sum of the cardinalities of these orbits.
  have h_card_S : S.card = ∑ G ∈ Finset.image (fun G => MulAction.orbit (Equiv.Perm (Fin n)) G) S, (Finset.filter (fun G' => MulAction.orbit (Equiv.Perm (Fin n)) G' = G) S).card := by
    exact card_eq_sum_card_image (fun G ↦ MulAction.orbit (Equiv.Perm (Fin n)) G) S;
  -- Since each orbit has size $n!$, the cardinality of each orbit is $n!$.
  have h_orbit_card : ∀ G ∈ S, (Finset.filter (fun G' => MulAction.orbit (Equiv.Perm (Fin n)) G' = MulAction.orbit (Equiv.Perm (Fin n)) G) S).card = Nat.factorial n := by
    intros G hG
    have h_orbit_card : (Finset.filter (fun G' => MulAction.orbit (Equiv.Perm (Fin n)) G' = MulAction.orbit (Equiv.Perm (Fin n)) G) S).card = Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) := by
      rw [ Fintype.card_of_subtype ];
      simp +contextual [ MulAction.mem_orbit_iff ];
      intro x; exact ⟨ fun hx => by
        exact MulAction.mem_orbit_iff.mp ( hx.2.symm ▸ MulAction.mem_orbit_self _ ), fun hx => by
        obtain ⟨ σ, rfl ⟩ := hx;
        exact ⟨ h_union_orbits G hG ( MulAction.mem_orbit _ _ ), by ext; simp +decide [ MulAction.mem_orbit_iff ] ⟩ ⟩ ;
    rw [ h_orbit_card, orbit_card_of_trivial_aut ];
    exact uniquelyEmbeds_iff_uniqueSub_trivialAut G H |>.1 ( Finset.mem_filter.mp hG |>.2 ) |>.2;
  rw [ show numUniquelyEmbedding H = S.card from rfl ];
  rw [ h_card_S ];
  exact Finset.dvd_sum fun x hx => by obtain ⟨ G, hG, rfl ⟩ := Finset.mem_image.mp hx; exact h_orbit_card G hG ▸ dvd_rfl;

/-
Automorphism count is an isomorphism invariant.
-/
lemma aut_card_iso_invariant {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    (h : Nonempty (G₁.Iso G₂)) : (autFinset G₁).card = (autFinset G₂).card := by
  obtain ⟨ f ⟩ := h;
  refine Finset.card_bij ?_ ?_ ?_ ?_;
  · use fun a ha => f.toEquiv * a * f.symm.toEquiv;
  · unfold autFinset;
    simp +decide [ SimpleGraph.Iso.map_adj_iff ];
    intro a ha u v; rw [ ← ha ] ;
    exact Iff.symm (Iso.map_adj_iff f.symm);
  · simp +contextual [ funext_iff, Equiv.Perm.ext_iff ];
  · intro b hb;
    refine ⟨ f.symm.toEquiv * b * f.toEquiv, ?_, ?_ ⟩ <;> simp_all +decide [ autFinset ];
    · exact fun u v => by simpa [ ← f.map_adj_iff ] using hb ( f u ) ( f v ) ;
    · ext x; simp +decide [ Equiv.Perm.mul_apply ] ;

/-
UniquelyEmbeds is invariant under the Perm action on graphs.
-/
lemma uniquelyEmbeds_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (G H : SimpleGraph (Fin n)) :
    UniquelyEmbeds (σ • G) H ↔ UniquelyEmbeds G H := by
  have h_embedding_equiv : ∀ τ : Equiv.Perm (Fin n), IsEmbedding (σ • G) H τ ↔ IsEmbedding G H (τ * σ) := by
    intro τ
    simp [IsEmbedding, smul_adj];
    grind;
  simp +decide only [UniquelyEmbeds, numEmbeddings, embeddingFinset];
  rw [ show ( filter ( IsEmbedding ( σ • G ) H ) univ ) = Finset.image ( fun τ => τ * σ⁻¹ ) ( filter ( IsEmbedding G H ) univ ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
  ext τ; aesop

/-
The number of iso classes with nontrivial aut times n! is bounded by the
    Burnside excess. This is used to bound the error term in fH_le_probUniqueEmb_plus_error.
    Key idea: each nontrivial-aut iso class contributes ≥ n!/2 to ∑(|aut|-1).
-/
lemma nontrivial_aut_classes_bound (n : ℕ) :
    (((Finset.univ : Finset (SimpleGraph (Fin n))).image
      (@Quotient.mk _ (graphIsoSetoid n))).filter (fun q =>
      ∀ G : SimpleGraph (Fin n), @Quotient.mk _ (graphIsoSetoid n) G = q →
        (autFinset G).card ≠ 1)).card * (Nat.factorial n) ≤
    2 * (numIsoClasses n * Nat.factorial n - 2 ^ n.choose 2) := by
  -- Let's denote the set of iso classes with nontrivial aut as `S`.
  set S := Finset.filter (fun q => ∀ G : SimpleGraph (Fin n), ⟦G⟧ = q → (autFinset G).card ≠ 1) (Finset.univ.image (Quotient.mk (graphIsoSetoid n)));
  -- Each element in S corresponds to an iso class with nontrivial aut.
  have hS_card : S.card * n.factorial ≤ ∑ q ∈ S, ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) * 2 := by
    have hS_card : ∀ q ∈ S, ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) * 2 ≥ n.factorial := by
      intro q hq
      obtain ⟨G₀, hG₀⟩ : ∃ G₀ : SimpleGraph (Fin n), ⟦G₀⟧ = q ∧ (autFinset G₀).card ≠ 1 := by
        grind;
      -- Since $G₀$ has nontrivial automorphisms, the orbit of $G₀$ under the action of $S_n$ has size $n! / |Aut(G₀)|$.
      have h_orbit_size : (Finset.univ.filter (fun G => ⟦G⟧ = q)).card = n.factorial / (autFinset G₀).card := by
        have h_orbit_size : (Finset.univ.filter (fun G => ⟦G⟧ = q)).card = Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G₀) := by
          rw [ Fintype.card_of_subtype ];
          simp +decide [ ← hG₀.1, MulAction.orbitRel_apply ];
          intro x; rw [ Quotient.eq ] ;
          constructor <;> intro h;
          · obtain ⟨ σ, hσ ⟩ := h;
            use σ⁻¹;
            ext a b; simp +decide [ hσ ] ;
          · obtain ⟨ σ, rfl ⟩ := h;
            refine ⟨ ?_, ?_ ⟩;
            · exact σ⁻¹
            · aesop;
        have := orbit_card_mul_aut n G₀;
        rw [ h_orbit_size, ← this, Nat.mul_div_cancel _ ( Finset.card_pos.mpr ⟨ 1, id_mem_autFinset G₀ ⟩ ) ];
      -- Since $G₀$ has nontrivial automorphisms, each element in the orbit of $G₀$ has the same automorphism group size as $G₀$.
      have h_orbit_aut_size : ∀ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), (autFinset G).card = (autFinset G₀).card := by
        intros G hG
        have h_iso : Nonempty (G.Iso G₀) := by
          simp +zetaDelta at *;
          exact Quotient.exact ( hG.trans hG₀.1.symm );
        exact aut_card_iso_invariant h_iso;
      rw [ Finset.sum_congr rfl fun x hx => by rw [ h_orbit_aut_size x hx ] ] ; simp_all +decide [ Nat.mul_div_cancel' ];
      have h_aut_size : (autFinset G₀).card ≥ 2 := by
        exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ 1, id_mem_autFinset G₀ ⟩ ) ( Ne.symm hG₀.2 );
      nlinarith [ Nat.div_mul_cancel ( show #(autFinset G₀) ∣ n.factorial from orbit_card_mul_aut n G₀ ▸ dvd_mul_left _ _ ), Nat.sub_add_cancel ( show 1 ≤ #(autFinset G₀) from by linarith ) ];
    simpa using Finset.sum_le_sum hS_card;
  -- The sum over all iso classes of (|aut(G)| - 1) is equal to the excess.
  have h_sum_excess : ∑ q : Quotient (graphIsoSetoid n), ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) = numIsoClasses n * n.factorial - 2 ^ n.choose 2 := by
    have h_sum_excess : ∑ q : Quotient (graphIsoSetoid n), ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) = ∑ G : SimpleGraph (Fin n), ((autFinset G).card - 1) := by
      rw [ Finset.sum_sigma' ];
      refine Finset.sum_bij ( fun G _ => G.2 ) ?_ ?_ ?_ ?_ <;> aesop;
    rw [ h_sum_excess, ← sum_autFinset_eq ];
    rw [ Nat.sub_eq_of_eq_add ];
    zify [ ← card_simpleGraph ];
    rw [ Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Finset.card_pos.mpr <| autFinset_nonempty _ ] ; norm_num;
  simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  rw [ ← h_sum_excess, mul_comm ];
  rw [ mul_comm ];
  exact hS_card.trans ( by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset <| Finset.filter_subset _ _ ) zero_le_two )

/-
Burnside gives: numIsoClasses * n! ≥ 2^(n choose 2).
-/
lemma numIsoClasses_factorial_ge (n : ℕ) :
    2 ^ n.choose 2 ≤ numIsoClasses n * Nat.factorial n := by
  rw [ ← card_simpleGraph, ← sum_autFinset_eq ];
  exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => Finset.card_pos.mpr ( autFinset_nonempty _ ) )

/-
The number of trivial-aut unique-subgraph iso classes times n! equals
    numUniquelyEmbedding.
-/
lemma numUniquelyEmbedding_eq_factorial_mul {n : ℕ} (H : SimpleGraph (Fin n)) :
    (numUniquelyEmbedding H : ℝ) =
    (Nat.factorial n : ℝ) *
    (((uniqueSubgraphClasses H).filter (fun q =>
      ∃ G : SimpleGraph (Fin n), (autFinset G).card = 1 ∧
      @Quotient.mk _ (graphIsoSetoid n) G = q)).card : ℝ) := by
  -- The set S = {G : UniquelyEmbeds G H} is a union of complete orbits under the Perm action (each orbit has all its elements in S, by uniquelyEmbeds_smul).
  let S := Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H)
  have h_orbits : Finset.card S = (Finset.image (Quotient.mk (graphIsoSetoid n)) S).card * Nat.factorial n := by
    have h_orbits : ∀ q ∈ S.image (Quotient.mk (graphIsoSetoid n)), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ⟦G⟧ = q ∧ G ∈ S)).card = Nat.factorial n := by
      intros q hq
      obtain ⟨G, hG⟩ : ∃ G ∈ S, ⟦G⟧ = q := by
        grind;
      have h_orbit : (Finset.univ.filter (fun G' : SimpleGraph (Fin n) => G' ∈ MulAction.orbit (Equiv.Perm (Fin n)) G)).card = Nat.factorial n := by
        convert orbit_card_of_trivial_aut G _;
        · rw [ Fintype.card_of_subtype ] ; aesop;
        · exact uniquelyEmbeds_iff_uniqueSub_trivialAut G H |>.1 ( Finset.mem_filter.mp hG.1 |>.2 ) |>.2;
      convert h_orbit using 2;
      ext G'; simp [hG];
      rw [ ← hG.2, Quotient.eq ];
      constructor;
      · -- If G' is in the set S and is equivalent to G under the graphIsoSetoid n, then there exists a permutation σ such that G' = σ • G.
        intro h
        obtain ⟨σ, hσ⟩ := h.left;
        use σ⁻¹;
        ext a b; simp +decide [ hσ ] ;
      · rintro ⟨ σ, rfl ⟩;
        simp +zetaDelta at *;
        exact ⟨ ⟨ σ.symm, by aesop ⟩, by simpa using uniquelyEmbeds_smul σ G H |>.2 hG.1 ⟩
    have h_orbits : Finset.card S = Finset.sum (Finset.image (Quotient.mk (graphIsoSetoid n)) S) (fun q => (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ⟦G⟧ = q ∧ G ∈ S)).card) := by
      rw [ ← Finset.card_biUnion ];
      · congr with G ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    rw [ h_orbits, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
  have h_image_eq :
      S.image (Quotient.mk (graphIsoSetoid n)) =
        (uniqueSubgraphClasses H).filter (fun q =>
          ∃ G : SimpleGraph (Fin n), (autFinset G).card = 1 ∧
          @Quotient.mk _ (graphIsoSetoid n) G = q) := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨G, hG, rfl⟩
      have hUE : UniquelyEmbeds G H := (Finset.mem_filter.mp hG).2
      have h := (uniquelyEmbeds_iff_uniqueSub_trivialAut G H).1 hUE
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr
            ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, rfl⟩,
          ⟨G, h.2, rfl⟩⟩
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hq_unique, G, hAut, hGq⟩
      have h_unique_G : IsUniqueSubgraph G H := by
        rcases Finset.mem_image.mp hq_unique with ⟨G', hG', hG'q⟩
        have hIso : Nonempty (G.Iso G') := by
          exact Quotient.exact (hGq.trans hG'q.symm)
        exact (isUniqueSubgraph_iso_invariant hIso).2 (Finset.mem_filter.mp hG').2
      refine Finset.mem_image.mpr ⟨G, ?_, hGq⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          (uniquelyEmbeds_iff_uniqueSub_trivialAut G H).2 ⟨h_unique_G, hAut⟩⟩
  rw [show numUniquelyEmbedding H = S.card by rfl, h_orbits, h_image_eq]
  rw [Nat.cast_mul]
  ring

/-
fH ≤ probUniqueEmb + 2*(numIsoClasses * n! / 2^N - 1).
    Uses orbit-stabilizer. The second term tends to 0 by Pólya-Wright.
-/
lemma fH_le_probUniqueEmb_plus_error {n : ℕ} (H : SimpleGraph (Fin n)) :
    fH H ≤ probUniqueEmb H +
    2 * ((numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1) := by
  field_simp;
  unfold fH probUniqueEmb paperDenom;
  field_simp;
  have h_card_filter : ((uniqueSubgraphClasses H).card : ℝ) ≤
    (numUniquelyEmbedding H : ℝ) / (Nat.factorial n : ℝ) +
    (((Finset.univ : Finset (SimpleGraph (Fin n))).image
      (@Quotient.mk _ (graphIsoSetoid n))).filter (fun q =>
        ∀ G : SimpleGraph (Fin n), @Quotient.mk _ (graphIsoSetoid n) G = q →
          (autFinset G).card ≠ 1)).card := by
            rw [ numUniquelyEmbedding_eq_factorial_mul ];
            rw [ mul_div_cancel_left₀ _ ( by positivity ) ];
            rw_mod_cast [ ← Finset.card_union_add_card_inter ];
            refine le_add_right ( Finset.card_le_card ?_ );
            intro q hq;
            by_cases h : ∃ G : SimpleGraph (Fin n), (autFinset G).card = 1 ∧ ⟦G⟧ = q;
            · grind +extAll;
            · simp +zetaDelta at *;
              exact Or.inr ⟨ by rcases Quotient.exists_rep q with ⟨ G, rfl ⟩ ; exact ⟨ G, rfl ⟩, fun G hG hG' => h G hG' hG ⟩
  rw [ div_add', le_div_iff₀ ] at h_card_filter <;> norm_cast at *;
  · rw [ Int.subNatNat_of_le ] <;> norm_cast;
    · have := nontrivial_aut_classes_bound n;
      lia;
    · linarith [ numIsoClasses_factorial_ge n ];
  · positivity;
  · positivity

/-
**Lemma 2.1** (Reduction to random labelled graphs).
    Derived from Pólya–Wright and almost_all_trivial_aut.
-/
theorem reduction_to_random :
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    fH H ≥ δ → probUniqueEmb H ≥ δ / 2 := by
  -- By Lemma 2.1, fH H ≤ probUniqueEmb H + error(n) where error(n) = numIsoClasses(n) * n! / 2^N - 1 → 0 by Pólya-Wright.
  have h_lemma21 : Filter.Tendsto (fun n => ((numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1)) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.sub_const ( polya_wright_theorem.mul_const ( 1 : ℝ ) ) 1 using 2
    all_goals try norm_num [ paperDenom ]
    all_goals try ring_nf
    · norm_num ; ring;
  intro δ hδ_pos
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, ((numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1) < δ / 4 := by
    simpa using h_lemma21.eventually ( gt_mem_nhds <| by linarith );
  exact ⟨ n₀, fun n hn H hH => by
    have := fH_le_probUniqueEmb_plus_error H
    have := hn₀ n hn
    linarith ⟩

/-! ### First Moment Bound -/

/-
For each permutation σ, the number of graphs G such that σ is an embedding of G into H
    is exactly 2^{e(H)}, since the non-edge positions of H (under σ) must be 0 in G
    and the edge positions are free.
-/
lemma count_graphs_with_embedding {n : ℕ} (H : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      IsEmbedding G H σ)).card = 2 ^ H.edgeFinset.card := by
  -- The number of subgraphs of a graph G is 2^(e(G)), where e(G) is the number of edges in G.
  have h_subgraph_count (G : SimpleGraph (Fin n)) : (Finset.univ.filter (fun H : SimpleGraph (Fin n) => H ≤ G)).card = 2 ^ G.edgeFinset.card := by
    -- Each subgraph of $G$ corresponds to a subset of the edge set of $G$.
    have h_subgraph_subset : Finset.univ.filter (fun H : SimpleGraph (Fin n) => H ≤ G) = Finset.image (fun s : Finset (Sym2 (Fin n)) => SimpleGraph.fromEdgeSet (s.filter (fun e => e ∈ G.edgeFinset))) (Finset.powerset G.edgeFinset) := by
      ext H;
      simp +zetaDelta at *;
      constructor;
      · intro hH;
        use H.edgeFinset;
        aesop;
      · rintro ⟨ a, ha, rfl ⟩ ; intro u v; simp +decide [ SimpleGraph.fromEdgeSet ] ; aesop;
    rw [ h_subgraph_subset, Finset.card_image_of_injOn, Finset.card_powerset ];
    intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    intro x; replace h_eq := congr_arg ( fun f => f.edgeSet ) h_eq; simp_all +decide [ Set.subset_def ] ;
    replace h_eq := Set.ext_iff.mp h_eq x; by_cases hx : x ∈ G.edgeSet <;> simp_all +decide [ Sym2.diagSet ] ;
    · cases x ; aesop;
    · exact ⟨ fun hx' => False.elim <| hx <| hs x hx', fun hx' => False.elim <| hx <| ht x hx' ⟩;
  have h_filter :
      Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding G H σ) =
        Finset.univ.filter (fun G : SimpleGraph (Fin n) => G ≤ H.comap σ) := by
    ext G
    simp [IsEmbedding, SimpleGraph.le_iff_adj]
  have h_edge_card : (H.comap σ).edgeFinset.card = H.edgeFinset.card := by
    refine Finset.card_bij (fun e _ => Sym2.map σ e) ?_ ?_ ?_
    · rintro ⟨u, v⟩ huv
      simp_all +decide [SimpleGraph.comap, SimpleGraph.adj_comm]
    · intro a₁ ha₁ a₂ ha₂ h
      rcases a₁ with ⟨u₁, v₁⟩
      rcases a₂ with ⟨u₂, v₂⟩
      aesop
    · rintro ⟨u, v⟩ huv
      refine ⟨Sym2.mk (σ⁻¹ u) (σ⁻¹ v), ?_, ?_⟩
      · simp_all +decide [SimpleGraph.comap, SimpleGraph.adj_comm]
      · simp [Sym2.map_map]
  rw [h_filter, h_subgraph_count (H.comap σ)]
  exact congrArg (fun m => 2 ^ m) h_edge_card

/-
First moment bound: the number of uniquely-embedding graphs is at most
    n! * 2^{e(H)}. This follows from the union bound over all permutations.
-/
lemma first_moment_embedding_bound {n : ℕ} (H : SimpleGraph (Fin n)) :
    numUniquelyEmbedding H ≤ Nat.factorial n * 2 ^ H.edgeFinset.card := by
  have h_first_moment : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0)).card ≤ (Nat.factorial n) * 2 ^ H.edgeFinset.card := by
    have h_first_moment : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0)).card ≤ ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding G H σ)).card := by
      have h_union_bound : Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0) ⊆ Finset.biUnion Finset.univ (fun σ : Equiv.Perm (Fin n) => Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding G H σ)) := by
        intro G hG; contrapose! hG; simp_all +decide [ numEmbeddings ] ;
        exact Finset.eq_empty_of_forall_notMem fun σ hσ => hG σ <| Finset.mem_filter.mp hσ |>.2;
      exact le_trans ( Finset.card_le_card h_union_bound ) ( Finset.card_biUnion_le );
    exact h_first_moment.trans ( by rw [ Finset.sum_congr rfl fun σ _ => count_graphs_with_embedding H σ ] ; simp +decide [ Finset.card_univ, Fintype.card_perm ] );
  refine le_trans ?_ h_first_moment;
  exact Finset.card_mono (fun G hG => by unfold UniquelyEmbeds at hG; aesop);

/-
From first_moment_embedding_bound: probUniqueEmb H ≤ n! / 2^{C(n,2) - e(H)}.
-/
lemma probUniqueEmb_le_factorial_div {n : ℕ} (H : SimpleGraph (Fin n)) :
    probUniqueEmb H ≤ (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - H.edgeFinset.card) := by
  -- Using the first moment embedding bound, we have:
  have h_bound : numUniquelyEmbedding H ≤ Nat.factorial n * 2 ^ H.edgeFinset.card :=
    first_moment_embedding_bound H
  simp [probUniqueEmb] at *;
  rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num;
  convert Nat.mul_le_mul_right _ h_bound using 1;
  rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ];
  convert H.card_edgeFinset_le_card_choose_two;
  norm_num

/-! ### Universal Vertices and Twin Argument -/

/-- A vertex is universal in H if it is adjacent to all other vertices. -/
def IsUniversal {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∀ w : Fin n, w ≠ v → H.Adj v w

/-
If H has two distinct universal vertices, then every graph G on n vertices
    has at least 2 embeddings into H (the identity and the transposition of the
    two universal vertices). Hence no graph uniquely embeds.
-/
lemma no_unique_embedding_of_two_universal {n : ℕ} (H : SimpleGraph (Fin n))
    (u v : Fin n) (huv : u ≠ v) (hu : IsUniversal H u) (hv : IsUniversal H v) :
    numUniquelyEmbedding H = 0 := by
  -- Consider any permutation σ that is an embedding of G into H.
  have h_embedding : ∀ (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)), IsEmbedding G H σ → IsEmbedding G H (Equiv.swap u v * σ) := by
    intro G σ hσ a b hab;
    by_cases ha : σ a = u <;> by_cases hb : σ b = u <;> by_cases hc : σ a = v <;> by_cases hd : σ b = v <;> simp_all +decide [ Equiv.swap_apply_def ];
    all_goals have := hσ a b hab; simp_all +decide [ SimpleGraph.adj_comm ];
    · exact hv _ ( by tauto );
    · exact hv _ ( by aesop );
    · exact hu _ ( by aesop );
    · exact hu _ ( by aesop );
  -- Since there are at least two embeddings for any G, the number of uniquely embedding graphs is zero.
  have h_num_embeddings : ∀ (G : SimpleGraph (Fin n)), (∃ σ : Equiv.Perm (Fin n), IsEmbedding G H σ) → 2 ≤ numEmbeddings G H := by
    intros G hG
    obtain ⟨σ, hσ⟩ := hG
    have h_distinct : σ ≠ Equiv.swap u v * σ := by
      simp +decide [huv];
    exact Finset.one_lt_card.mpr ⟨ σ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ ⟩, Equiv.swap u v * σ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_embedding G σ hσ ⟩, h_distinct ⟩;
  simp_all +decide [ numUniquelyEmbedding ];
  intro G hG; specialize h_num_embeddings G; simp_all +decide [ UniquelyEmbeds ] ;
  unfold numEmbeddings at hG; simp_all +decide [ Finset.card_eq_one ] ;
  obtain ⟨ σ, hσ ⟩ := hG; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
  exact h_num_embeddings σ ( Finset.mem_filter.mp hσ.1 |>.2 )

/-! ### Derivation of reduction_to_dense -/

/-- For n ≤ 2*C + 1, C * n ≥ n.choose 2. -/
lemma small_n_vacuity (C n : ℕ) (hn : n ≤ 2 * C + 1) :
    n.choose 2 ≤ C * n := by
  rw [Nat.choose_two_right]
  have h2 : n * (n - 1) ≤ 2 * (C * n) := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one]
      have : n ≤ 2 * C := by omega
      nlinarith
  exact Nat.div_le_of_le_mul h2

/-- First moment bound: probUniqueEmb H ≤ n! · 2^{e(H)} / 2^N ≤ n!/2^m
    where m = N - e(H) is the number of non-edges. Combined with the
    edge-count concentration from the Chernoff bound, this implies
    that graphs with too many non-edges have small probUniqueEmb.

    **Core probabilistic lemma** (Lemma 2.2 from the paper):
    For every δ > 0 there exist C₀ and n₀ such that for n ≥ n₀,
    if probUniqueEmb H ≥ δ then e(H) + C₀·n ≥ C(n,2).

    The proof combines:
    1. The first moment bound (probUniqueEmb_le_factorial_div)
    2. The Chernoff bound for edge-count concentration
    3. A counting/process argument showing that when H has many non-edges,
       a random graph with unique embedding into H must have constrained
       edge count, contradicting concentration.

    The proof is decomposed into `process_bound` + `pow_ge_implies_close_to_one` +
    a final algebraic combination. See `process_bound` below.
-/
abbrev _root_.rdtln_placeholder := True

/-- **Process bound** (core of Lemma 2.2).

    If probUniqueEmb H ≥ δ, then (e(H)/N)^k ≥ α for some k = Ω(δn) and α = α(δ) > 0.

    The proof uses:
    1. Chernoff concentration: edge count of G(n,1/2) concentrates within O(n) of N/2.
    2. Anti-concentration: Pr[e(G) = m] ≤ O(1/n) for all m.
    3. Pigeonhole: ∃ m₀ with high conditional UE probability Pr[UE | e(G) = m₀].
    4. Random graph process + monotonicity: the set of edge counts where the
       process graph uniquely embeds forms an interval.
    5. Markov + interval structure: the interval length is Ω(n) with probability Ω(1).
    6. Conditional supergraph probability: for G₀ UE via σ, the probability that a
       random supergraph of G₀ also UE is C(e(H)-m₀, k)/C(N-m₀, k) ≤ (e(H)/N)^k.
    7. Combining 5 and 6: (e(H)/N)^k ≥ Ω(1).

    The proof is decomposed into the helper lemmas below. -/
abbrev _root_.process_bound_placeholder := True

/-
For G₀ with UniquelyEmbeds G₀ H, any supergraph G' ≥ G₀ that embeds into H
    must use the same unique embedding σ.
-/
lemma UE_supergraph_same_embedding {n : ℕ} {G₀ G' H : SimpleGraph (Fin n)}
    (hle : G₀ ≤ G') (hUE₀ : UniquelyEmbeds G₀ H)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ embeddingFinset G' H) :
    embeddingFinset G₀ H = {σ} := by
  -- Since σ is in embeddingFinset G' H and G₀ ≤ G', σ is also in embeddingFinset G₀ H.
  have hσ_G₀ : σ ∈ embeddingFinset G₀ H := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => Finset.mem_filter.mp hσ |>.2 u v ( hle huv ) ⟩;
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨ hσ_G₀, fun τ hτ => by have := Finset.card_eq_one.mp hUE₀; aesop ⟩

/-
Supergraph UE characterization: if G₀ UE via σ, then G' ≥ G₀ UE iff
    G' ≤ σ • H (every edge of G' maps to an edge of H under σ).
-/
lemma UE_supergraph_iff {n : ℕ} {G₀ G' H : SimpleGraph (Fin n)}
    (hle : G₀ ≤ G') (hUE₀ : UniquelyEmbeds G₀ H)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ embeddingFinset G₀ H) :
    UniquelyEmbeds G' H ↔ IsEmbedding G' H σ := by
  constructor;
  · intro h;
    -- By definition of UniquelyEmbeds, G' has exactly one embedding into H.
    obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), embeddingFinset G' H = {τ} := by
      exact Finset.card_eq_one.mp h;
    -- Since τ is the unique embedding of G' into H, and σ is an embedding of G₀ into H, we must have τ = σ.
    have hτ_eq_σ : τ = σ := by
      have hτ_eq_σ : τ ∈ embeddingFinset G₀ H := by
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hτ.1; exact this.2 u v ( hle huv ) ⟩;
      obtain ⟨η, hη⟩ := Finset.card_eq_one.mp hUE₀
      rw [hη] at hτ_eq_σ hσ
      exact (Finset.mem_singleton.mp hτ_eq_σ).trans (Finset.mem_singleton.mp hσ).symm;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact Finset.mem_filter.mp hτ.1 |>.2;
  · intro hσ';
    -- By definition of UniquelyEmbeds, we know that embeddingFinset G₀ H = {σ}.
    have h_embeddingFinset_G₀ : embeddingFinset G₀ H = {σ} := by
      apply_rules [ UE_supergraph_same_embedding ];
      exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ' ⟩;
    -- Since σ is in embeddingFinset G' H and G₀ ≤ G', we have that embeddingFinset G' H is a subset of embeddingFinset G₀ H.
    have h_embeddingFinset_G'_subset_G₀ : embeddingFinset G' H ⊆ embeddingFinset G₀ H := by
      intro τ hτ;
      exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => Finset.mem_filter.mp hτ |>.2 u v ( hle huv ) ⟩;
    rw [ h_embeddingFinset_G₀ ] at h_embeddingFinset_G'_subset_G₀;
    exact Finset.card_eq_one.mpr ⟨ σ, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ' ⟩, fun x hx => Finset.mem_singleton.mp ( h_embeddingFinset_G'_subset_G₀ hx ) ⟩ ⟩

/-
The number of (m+k)-edge supergraphs of G₀ that embed via σ
    equals C(e(H) - m, k), where m = e(G₀).
-/
-- The generated supergraph count needs extra heartbeats for embedding-set bijections.
set_option maxHeartbeats 800000 in
lemma supergraph_UE_count {n : ℕ} (G₀ H : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hUE : UniquelyEmbeds G₀ H) (hσ : σ ∈ embeddingFinset G₀ H)
    (hk : k ≤ H.edgeFinset.card - G₀.edgeFinset.card) :
    (Finset.univ.filter (fun G' : SimpleGraph (Fin n) =>
      G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k ∧
      UniquelyEmbeds G' H)).card =
    (H.edgeFinset.card - G₀.edgeFinset.card).choose k := by
  have h_bij : {G' : SimpleGraph (Fin n) | G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k ∧ UniquelyEmbeds G' H} = {G' : SimpleGraph (Fin n) | G₀ ≤ G' ∧ G' ≤ σ⁻¹ • H ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k} := by
    apply Set.ext
    intro G'
    simp [hUE, hσ];
    intro hG';
    constructor <;> intro h;
    · have := UE_supergraph_iff hG' hUE σ (by
      exact hσ)
      generalize_proofs at *;
      exact ⟨ fun u v huv => by simpa using this.mp h.2 u v huv, h.1 ⟩;
    · have h_unique_embedding : IsEmbedding G' H σ := by
        intro u v huv; have := h.1 huv; aesop;
      have h_unique_embedding : UniquelyEmbeds G' H ↔ IsEmbedding G' H σ := by
        apply_rules [ UE_supergraph_iff ];
      aesop;
  -- The set of valid G' corresponds to choosing k edges from a set of e(H) - m₀ available edges, which has C(e(H) - m₀, k) elements.
  have h_card : Finset.card (Finset.filter (fun G' : SimpleGraph (Fin n) => G₀ ≤ G' ∧ G' ≤ σ⁻¹ • H ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k) Finset.univ) = Finset.card (Finset.powersetCard k (Finset.filter (fun e => e ∈ (σ⁻¹ • H).edgeFinset ∧ e ∉ G₀.edgeFinset) (Finset.univ : Finset (Sym2 (Fin n)))) ) := by
    refine Finset.card_bij ( fun G' _ => G'.edgeFinset \ G₀.edgeFinset ) ?_ ?_ ?_;
    · intro G' hG'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG'
      rcases hG' with ⟨hG'₁, hG'₂, hG'₃⟩
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro e he
        rw [Finset.mem_sdiff] at he
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ e,
          SimpleGraph.edgeFinset_mono hG'₂ he.1, he.2⟩
      · rw [Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hG'₁), hG'₃]
        omega
    · simp +contextual [ Finset.ext_iff ];
      intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ h; ext u v; specialize h ( Sym2.mk u v ) ; by_cases hu : G₀.Adj u v <;> aesop;
    · intro b hb; use SimpleGraph.fromEdgeSet ( G₀.edgeFinset ∪ b ) ; simp_all +decide [ Finset.subset_iff ] ;
      refine ⟨ ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩, ?_ ⟩;
      · intro u v; simp_all +decide [ embeddingFinset ] ;
        exact hσ u v;
      · grind;
      · rw [ Finset.card_union_of_disjoint ] <;> simp_all +decide [ Finset.disjoint_left ];
        · convert hb.2 using 1;
          refine Finset.card_bij ( fun x hx => x ) ?_ ?_ ?_ <;> simp +decide [ SimpleGraph.edgeSet ];
          · grind;
          · intro x hx; specialize hb; have := hb.1 hx; simp_all +decide [ SimpleGraph.edgeSet ] ;
            exact fun h => by have := hb.1 hx; exact this.1 |> fun h' => by cases x; aesop;
        · intro x hx₁ hx₂; specialize hb; have := hb.1 hx₂; aesop;
      · ext; simp [hb];
        by_cases h : ‹Sym2 ( Fin n ) › ∈ G₀.edgeSet <;> simp_all +decide [ SimpleGraph.edgeSet ];
        · exact fun h' => hb.1 h' |>.2 h;
        · intro hx; specialize hb; have := hb.1 hx; simp_all +decide [ edgeSetEmbedding ] ;
          cases ‹Sym2 ( Fin n ) › ; simp_all +decide [ Sym2.fromRel ];
          intro h; have := hb.1 hx; simp_all +decide [ Sym2.lift ] ;
  convert h_card using 1;
  · congr! 1;
    convert h_bij using 1;
    simp +decide [ Finset.ext_iff, Set.ext_iff ];
  · rw [ Finset.card_powersetCard, show Finset.filter ( fun e => e ∈ ( σ⁻¹ • H ).edgeFinset ∧ e∉G₀.edgeFinset ) Finset.univ = ( σ⁻¹ • H ).edgeFinset \ G₀.edgeFinset by ext; aesop ];
    -- Since σ is a permutation, the number of edges in σ⁻¹ • H is the same as in H.
    have h_edge_card : (σ⁻¹ • H).edgeFinset.card = H.edgeFinset.card := by
      refine Finset.card_bij ( fun e he => Sym2.map σ e ) ?_ ?_ ?_ <;> simp +decide [ Sym2.map ];
      · intro e he; rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact he;
      · intro a₁ ha₁ a₂ ha₂ h; rcases a₁ with ⟨ u₁, v₁ ⟩ ; rcases a₂ with ⟨ u₂, v₂ ⟩ ; simp_all +decide [ Quot.map ] ;
      · rintro ⟨ u, v ⟩ huv;
        refine ⟨ Quot.mk _ ( σ⁻¹ u, σ⁻¹ v ), ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.edgeSetEmbedding ];
        exact Quot.sound ( by aesop );
    rw [ Finset.card_sdiff ];
    rw [ h_edge_card, Finset.inter_eq_left.mpr ];
    intro e he
    rcases e with ⟨ u, v ⟩
    have heAdj : G₀.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset] using he
    simpa +decide [ SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSetEmbedding ] using Finset.mem_filter.mp hσ |>.2 u v heAdj

/-
Anti-concentration: for N = C(n,2) with n ≥ 4, C(N,m)/2^N ≤ 4/n.
-/
lemma binomial_anticoncentration {n : ℕ} (hn : 4 ≤ n) (m : ℕ) :
    ((n.choose 2).choose m : ℝ) / 2 ^ (n.choose 2) ≤ 4 / n := by
  field_simp;
  -- By the properties of binomial coefficients, we know that $\binom{N}{m} \leq \binom{N}{\lfloor N/2 \rfloor}$.
  have h_binom_le : (Nat.choose (Nat.choose n 2) m : ℝ) ≤ (Nat.choose (Nat.choose n 2) (Nat.choose n 2 / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle _ _;
  -- By the properties of binomial coefficients, we know that $\binom{N}{\lfloor N/2 \rfloor} \leq 2^N / \sqrt{N/2 + 1}$.
  have h_binom_bound : (Nat.choose (Nat.choose n 2) (Nat.choose n 2 / 2) : ℝ) ≤ 2 ^ (Nat.choose n 2) / Real.sqrt ((Nat.choose n 2) / 2 + 1) := by
    -- By the properties of binomial coefficients, we know that $\binom{2k}{k} \leq \frac{4^k}{\sqrt{k+1}}$ for any $k$.
    have h_binom_bound : ∀ k : ℕ, (Nat.choose (2 * k) k : ℝ) ≤ 4 ^ k / Real.sqrt (k + 1) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        -- For the inductive step, we use the identity $\binom{2(k+1)}{k+1} = \frac{2(2k+1)}{k+1} \binom{2k}{k}$.
        have h_identity : (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) = (2 * (2 * k + 1) / (k + 1)) * (Nat.choose (2 * k) k : ℝ) := by
          rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
          norm_num [ two_mul, Nat.factorial ];
          rw [ div_mul_div_comm, div_eq_div_iff ] <;> first | positivity | ring_nf;
          try rw [ show 1 + k * 2 = k * 2 + 1 by ring, Nat.factorial_succ ] ; push_cast ; ring;
        rw [ h_identity, pow_succ' ];
        refine le_trans ( mul_le_mul_of_nonneg_left ih <| by positivity ) ?_;
        field_simp;
        norm_num ; nlinarith [ sq_nonneg ( Real.sqrt ( k + 1 ) - Real.sqrt ( k + 1 + 1 ) ), Real.mul_self_sqrt ( show ( k:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( k:ℝ ) + 1 + 1 ≥ 0 by positivity ), Real.sqrt_nonneg ( k + 1 ), Real.sqrt_nonneg ( k + 1 + 1 ) ];
    rcases Nat.even_or_odd' ( Nat.choose n 2 ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk ];
    · convert h_binom_bound k using 2 ; norm_num [ pow_mul ];
    · have := h_binom_bound ( k + 1 ) ; norm_num [ Nat.add_div, Nat.mul_succ, pow_succ', pow_mul ] at *;
      rw [ show ( 2 * k + 2 : ℕ ) = 2 * k + 1 + 1 by ring, Nat.choose_succ_succ ] at this;
      rw [ le_div_iff₀ ( by positivity ) ] at *;
      rw [ show ( 2 * k + 1 : ℕ ).choose k.succ = ( 2 * k + 1 : ℕ ).choose k from by rw [ Nat.choose_symm_of_eq_add ] ; linarith ] at this ; ring_nf at * ; norm_num at *;
      nlinarith [ Real.sqrt_nonneg ( 2 + k : ℝ ), Real.sqrt_nonneg ( 3 / 2 + k : ℝ ), Real.mul_self_sqrt ( show ( 0 : ℝ ) ≤ 2 + k by positivity ), Real.mul_self_sqrt ( show ( 0 : ℝ ) ≤ 3 / 2 + k by positivity ), Real.sqrt_le_sqrt ( show ( 2 + k : ℝ ) ≥ 3 / 2 + k by linarith ) ];
  -- We'll use that $n \leq 4 \sqrt{\frac{n(n-1)}{4} + 1}$ for $n \geq 4$.
  have h_sqrt_bound : (n : ℝ) ≤ 4 * Real.sqrt ((Nat.choose n 2) / 2 + 1) := by
    rw [ Nat.choose_two_right ];
    rcases n with ( _ | _ | _ | _ | n ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
    nlinarith only [ Real.sqrt_nonneg ( ( n + 1 + 1 + 1 + 1 : ℝ ) * ( n + 1 + 1 + 1 ) / 2 / 2 + 1 ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( n + 1 + 1 + 1 + 1 : ℝ ) * ( n + 1 + 1 + 1 ) / 2 / 2 + 1 ) ];
  rw [ le_div_iff₀ ] at h_binom_bound <;> first | positivity | nlinarith [ Real.sqrt_nonneg ( ( n.choose 2 : ℝ ) / 2 + 1 ), Real.mul_self_sqrt ( show 0 ≤ ( n.choose 2 : ℝ ) / 2 + 1 by positivity ) ] ;

/-
Chernoff tail bound for edge counts: given ε > 0, there exists L such that
    for all n, the number of graphs on n vertices with edge count deviating
    from N/2 by at least L*n is at most ε * 2^N.
-/
lemma chernoff_edge_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, 4 ≤ n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤
    ε * 2 ^ (n.choose 2) := by
  -- Apply the Chernoff bound with $t = L * n$.
  have h_chernoff : ∀ L : ℝ, 0 < L → ∀ n : ℕ, 4 ≤ n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => |((G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2)| ≥ (L : ℝ) * n)).card : ℝ) ≤
    2 * (2 ^ n.choose 2 : ℝ) * Real.exp (-2 * (L * (n : ℝ)) ^ 2 / n.choose 2) := by
      intros L hL n hn
      have h_chernoff : ((Finset.univ.filter (fun f : Fin (n.choose 2) → Bool => |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤ 2 * (2 ^ n.choose 2 : ℝ) * Real.exp (-2 * (L * (n : ℝ)) ^ 2 / n.choose 2) := by
        convert chernoff_bound ( n.choose 2 ) ( L * n ) ( by positivity ) using 1;
      have h_bij : ∃ f : SimpleGraph (Fin n) ≃ (Fin (n.choose 2) → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
        -- Define the bijection between SimpleGraph (Fin n) and (Fin (n.choose 2) → Bool) using the edgeSlot structure.
        have h_bij : ∃ f : SimpleGraph (Fin n) ≃ (Fin (n.choose 2) → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
          have h_edgeSlot : ∃ f : SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
            use UniqueSubgraphs.graphEquiv n;
            intro G; exact (by
            refine Finset.card_bij (fun a ha => Sym2.mk a.val.1 a.val.2) ?_ ?_ ?_;
            · simp +decide [ graphEquiv ];
              unfold graphEncode; aesop;
            · simp +decide [ Sym2.eq_iff ];
              rintro ⟨ ⟨ i, j ⟩, hij ⟩ hi ⟨ ⟨ k, l ⟩, hkl ⟩ hj ( h | h ) <;> simp_all +decide [ Fin.ext_iff, Prod.ext_iff ];
              · exact Subtype.ext <| Prod.ext ( Fin.ext h.1 ) ( Fin.ext h.2 );
              · grind;
            · intro b hb; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
              cases lt_trichotomy u v <;> simp_all +decide [ graphEquiv ];
              · exact ⟨ ⟨ ⟨ u, v ⟩, by assumption ⟩, by unfold graphEncode; aesop ⟩;
              · cases ‹_› <;> simp_all +decide [ graphEncode ];
                exact ⟨ ⟨ ( v, u ), by assumption ⟩, by simpa [ SimpleGraph.adj_comm ] using hb, Or.inr rfl ⟩)
          obtain ⟨ f, hf ⟩ := h_edgeSlot;
          have h_bij : ∃ g : EdgeSlot n ≃ Fin (n.choose 2), True := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ card_edgeSlot ], trivial ⟩;
          obtain ⟨ g, hg ⟩ := h_bij;
          use f.trans (Equiv.arrowCongr g (Equiv.refl Bool));
          intro G; specialize hf G; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
          rw [ ← hf, Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp g.symm ] ;
        exact h_bij;
      obtain ⟨ f, hf ⟩ := h_bij;
      convert h_chernoff using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      norm_cast
      rw [ ← Equiv.sum_comp f ];
      refine Finset.sum_congr rfl ?_;
      intro G hG
      rw [ hf G ];
  -- Choose $L$ such that $2 * \exp(-4L^2) \leq \epsilon$.
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 0 < L ∧ 2 * Real.exp (-4 * (L : ℝ) ^ 2) ≤ ε := by
    have h_exp_bound : Filter.Tendsto (fun L : ℕ => 2 * Real.exp (-4 * (L : ℝ) ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( by norm_num ) <| Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_exp_bound.eventually ( ge_mem_nhds hε ) ) |> fun ⟨ L, hL ⟩ => ⟨ L + 1, Nat.succ_pos _, hL _ ( Nat.le_succ _ ) ⟩;
  refine ⟨ L, hL.1, fun n hn => le_trans ( h_chernoff L ( Nat.cast_pos.mpr hL.1 ) n hn ) ?_ ⟩;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_right hL.2 <| by positivity );
  rw [ show ( n.choose 2 : ℝ ) = n * ( n - 1 ) / 2 by rw [ Nat.choose_two_right ] ; induction n <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] at * ] ; ring_nf ; norm_num;
  field_simp;
  rw [ le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 4 by norm_cast, show ( L : ℝ ) ^ 2 ≥ 0 by positivity ]

/-! ### Process bound infrastructure -/

/-- Number of graphs with exactly m edges that uniquely embed into H. -/
def numUEWithEdges {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
    G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).card

/-
Chain interval property: if G₁ ≤ G₂ ≤ G₃ and G₁, G₃ both UE into H,
    then G₂ also UE into H.
-/
lemma ue_chain_interval {n : ℕ} {G₁ G₂ G₃ H : SimpleGraph (Fin n)}
    (h12 : G₁ ≤ G₂) (h23 : G₂ ≤ G₃)
    (hUE1 : UniquelyEmbeds G₁ H) (hUE3 : UniquelyEmbeds G₃ H) :
    UniquelyEmbeds G₂ H := by
  obtain ⟨ σ₁, hσ₁ ⟩ := Finset.card_eq_one.mp hUE1;
  have hσ₂ : σ₁ ∈ embeddingFinset G₂ H := by
    obtain ⟨ σ₃, hσ₃ ⟩ := Finset.card_eq_one.mp hUE3;
    have hσ₂ : σ₁ = σ₃ := by
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      exact hσ₁.2 σ₃ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => hσ₃.1 |> Finset.mem_filter.mp |>.2 u v ( h12 huv |> h23 ) ⟩ ) ▸ rfl;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hσ₃.1; exact this.2 u v ( h23 huv ) ⟩;
  have hσ₃ : numEmbeddings G₂ H ≤ numEmbeddings G₁ H := by
    exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hx; exact this.2 u v ( h12 huv ) ⟩;
  exact le_antisymm ( le_trans hσ₃ hUE1.le ) ( Finset.card_pos.mpr ⟨ σ₁, hσ₂ ⟩ )

/-
The empty graph does not uniquely embed for n ≥ 2 (it has n! ≥ 2 embeddings).
-/
lemma numUEWithEdges_zero {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    numUEWithEdges H 0 = 0 := by
  rw [ numUEWithEdges ];
  simp [UniquelyEmbeds, numEmbeddings, embeddingFinset];
  rw [ Finset.card_eq_sum_ones, Finset.sum_filter ];
  rw [ Finset.sum_congr rfl fun x hx => if_pos <| by unfold IsEmbedding; aesop ] ; norm_num [ Finset.card_univ, Fintype.card_perm ] ; linarith [ Nat.self_le_factorial n ]

/-
Abstract algebraic process bound.
    Given f : ℕ → ℝ with f(0) = 0, f ≥ 0, satisfying
    f(m) ≤ p · f(m-1) + z(m) for z ≥ 0 with Σ z ≤ 1,
    we get Σ_{m∈S} f(m) ≤ k + |S| · p^{k-1}.
-/
lemma abstract_process_bound (N : ℕ) (f z : ℕ → ℝ) (p : ℝ) (k : ℕ) (S : Finset ℕ)
    (hf0 : f 0 = 0) (hf_nonneg : ∀ m, 0 ≤ f m) (hz_nonneg : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, 1 ≤ m → m ≤ N → f m ≤ p * f (m - 1) + z m)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hk : 1 ≤ k)
    (hS : ∀ m ∈ S, m ≤ N)
    (hz_sum : ∑ m ∈ Finset.range (N + 1), z m ≤ 1)
    (hf_large : ∀ m, N < m → f m = 0) :
    ∑ m ∈ S, f m ≤ ↑k + ↑S.card * p ^ (k - 1) := by
  -- For each $j$, $\sum_{m \in S, m \geq j} p^{m-j} \leq \# \{m \in S : m-j < k-1\} \cdot 1 + \# \{m \in S : m-j \geq k-1\} \cdot p^{k-1}$.
  have h_sum_bound : ∀ j ∈ Finset.range (N + 1), ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) ≤ (min k (Finset.card (S.filter (fun m => j ≤ m)))) + (Finset.card (S.filter (fun m => j ≤ m))) * p ^ (k - 1) := by
    intros j hj
    have h_split : ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) ≤ ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j < k), p ^ (m - j) + ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j ≥ k), p ^ (m - j) := by
      rw [ ← Finset.sum_union ];
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by by_cases h : x - j < k <;> aesop ) fun _ _ _ => pow_nonneg hp _;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    have h_bound : ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j < k), p ^ (m - j) ≤ (min k (Finset.card (S.filter (fun m => j ≤ m)))) ∧ ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j ≥ k), p ^ (m - j) ≤ (Finset.card (S.filter (fun m => j ≤ m ∧ m - j ≥ k))) * p ^ (k - 1) := by
      constructor;
      · refine le_trans ( Finset.sum_le_sum fun x hx => pow_le_one₀ hp hp1 ) ?_ ; norm_num;
        exact ⟨ le_trans ( Finset.card_le_card ( show { m ∈ S | j ≤ m ∧ m - j < k } ⊆ Finset.Ico j ( j + k ) from fun x hx => Finset.mem_Ico.mpr ⟨ by aesop, by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel ( show j ≤ x from by aesop ) ] ⟩ ) ) ( by simp +arith +decide ), Finset.card_mono ( fun x hx => by aesop ) ⟩;
      · exact le_trans ( Finset.sum_le_sum fun x hx => show p ^ ( x - j ) ≤ p ^ ( k - 1 ) by exact pow_le_pow_of_le_one hp hp1 ( by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel ( show 1 ≤ k from hk ) ] ) ) ( by norm_num );
    exact h_split.trans ( add_le_add h_bound.1 ( h_bound.2.trans ( mul_le_mul_of_nonneg_right ( mod_cast Finset.card_mono <| fun x hx => by aesop ) <| pow_nonneg hp _ ) ) );
  -- By interchanging the order of summation, we can rewrite the left-hand side of the inequality.
  have h_interchange : ∑ m ∈ S, f m ≤ ∑ j ∈ Finset.range (N + 1), z j * ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) := by
    have h_interchange : ∀ m ∈ S, f m ≤ ∑ j ∈ Finset.range (m + 1), z j * p ^ (m - j) := by
      intro m hm
      have h_induction : ∀ m ≤ N, f m ≤ ∑ j ∈ Finset.range (m + 1), z j * p ^ (m - j) := by
        intro m hm
        induction m with
        | zero =>
          simp_all +decide [ Finset.sum_range_succ ]
        | succ m ih =>
          simp_all +decide [ Finset.sum_range_succ ]
          refine le_trans ( hrec (m + 1) ( Nat.succ_pos m ) ( by linarith ) ) ?_;
          norm_num [ Nat.succ_eq_add_one, pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] at *;
          exact le_trans ( mul_le_mul_of_nonneg_left ( ih hm.le ) hp ) ( by rw [ show ∑ j ∈ Finset.range m, z j * p ^ ( m + 1 - j ) = p * ∑ j ∈ Finset.range m, z j * p ^ ( m - j ) by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.sub_add_comm ( by linarith [ Finset.mem_range.mp ‹_› ] ) ] ; ring ] ; linarith );
      exact h_induction m <| hS m hm;
    refine le_trans ( Finset.sum_le_sum h_interchange ) ?_;
    simp +decide only [Finset.mul_sum _ _ _];
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine le_of_eq ?_;
    refine Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst ⟩ ) ?_ ?_ ?_ ?_ <;> simp +decide;
    · exact fun a ha₁ ha₂ => ⟨ le_trans ha₂ ( hS _ ha₁ ), ha₁, ha₂ ⟩;
    · bound;
    · exact fun b hb₁ hb₂ hb₃ => ⟨ b.snd, b.fst, ⟨ hb₂, hb₃ ⟩, rfl ⟩;
  refine le_trans h_interchange <| le_trans ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( h_sum_bound j hj ) <| hz_nonneg j ) ?_;
  refine le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( add_le_add (
    Nat.cast_le.mpr <| min_le_left _ _ ) <| mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <|
      Finset.card_filter_le _ _ ) <| pow_nonneg hp _ ) <| hz_nonneg i ) ?_;
  rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ show 0 ≤ ( k : ℝ ) + ( S.card : ℝ ) * p ^ ( k - 1 ) by positivity ] ;

/-
Double counting lower bound: R(m-1)·(eH-m+1) ≤ m·R(m).
-/
lemma double_count_ue_pairs {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hm_le : m ≤ n.choose 2) :
    (numUEWithEdges H (m - 1) : ℝ) * ((H.edgeFinset.card : ℝ) - ↑m + 1) ≤
    ↑m * (numUEWithEdges H m : ℝ) := by
  rcases m with ( _ | m ) <;> simp_all +decide [ numUEWithEdges ];
  -- Let's count the number of pairs (G₀, G) where G₀ has m edges and G is a supergraph of G₀ with m+1 edges.
  have h_pairs : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).sum (fun G => (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card) ≥ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).sum (fun G => (H.edgeFinset.card - G.edgeFinset.card : ℕ)) := by
    have h_pairs : ∀ G₀ : SimpleGraph (Fin n), G₀.edgeFinset.card = m → UniquelyEmbeds G₀ H → (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ G₀ ≤ G ∧ UniquelyEmbeds G H)).card ≥ (H.edgeFinset.card - G₀.edgeFinset.card : ℕ) := by
      intro G₀ hG₀ hUE₀
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ ∈ embeddingFinset G₀ H := by
        contrapose! hUE₀; simp_all +decide [ UniquelyEmbeds ] ;
        exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_eq_zero.mpr ( by aesop ) |> le_of_eq ) ( by norm_num ) );
      have := supergraph_UE_count G₀ H σ 1 hUE₀ hσ;
      by_cases h : 1 ≤ #H.edgeFinset - #G₀.edgeFinset <;> simp_all +decide [ and_comm, and_left_comm, and_assoc ];
    refine le_trans ( Finset.sum_le_sum fun G₀ hG₀ => h_pairs G₀ ( Finset.mem_filter.mp hG₀ |>.2.1 ) ( Finset.mem_filter.mp hG₀ |>.2.2 ) ) ?_;
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
    any_goals exact Finset.univ.filter fun G => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H;
    · exact Finset.sum_le_sum fun x hx => Finset.card_mono fun y hy => by aesop;
    · aesop;
  -- Since each graph $G$ with $m+1$ edges has at most $m+1$ subgraphs with $m$ edges, we have:
  have h_bound : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).sum (fun G => (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card) ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).card * (m + 1) := by
    have h_bound : ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = m + 1 → (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card ≤ m + 1 := by
      intros G hG_card
      have h_subgraphs : (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)).card ≤ m + 1 := by
        have h_subgraphs : (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)).card ≤ Finset.card (Finset.powersetCard m G.edgeFinset) := by
          have h_subgraphs : Finset.image (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset) (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)) ⊆ Finset.powersetCard m G.edgeFinset := by
            grind +suggestions;
          have := Finset.card_le_card h_subgraphs;
          rwa [ Finset.card_image_of_injOn ] at this ; intro a ha b hb ; aesop;
        simp_all +decide [ Finset.card_powersetCard ];
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_subgraphs;
    exact Finset.sum_le_card_nsmul _ _ _ fun x hx => h_bound x <| Finset.mem_filter.mp hx |>.2.1;
  norm_cast;
  rw [ Int.subNatNat_eq_coe ] ; push_cast ; norm_num [ mul_comm ] at *;
  have h_sum_bound : ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H), (H.edgeFinset.card - G.edgeFinset.card : ℕ) ≥ (H.edgeFinset.card - m) * (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).card := by
    rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2.1 ] ] ; norm_num [ mul_comm ];
  by_cases h : #H.edgeFinset ≤ m <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
  · exact le_trans ( mul_nonpos_of_nonpos_of_nonneg ( by linarith ) ( Nat.cast_nonneg _ ) ) ( by positivity );
  · grind +locals

/-- The UE fraction: f(m) = R(m)/C(N,m). -/
noncomputable def fUE {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) : ℝ :=
  (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)

/-! ### Edge-subset bridge for the transition sum bound -/

/-- Graph constructed from a set of non-diagonal Sym2 elements. -/
private noncomputable def graphOfEdges {n : ℕ}
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (S.image Subtype.val : Set (Sym2 (Fin n)))

/-- The UE predicate on edge subsets. -/
private def UEPred {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}) : Prop :=
  UniquelyEmbeds (graphOfEdges S) H

private instance UEPred_decidable {n : ℕ} (H : SimpleGraph (Fin n)) :
    DecidablePred (UEPred H) := fun S => inferInstance

/-
Interval property for UEPred.
-/
private lemma UEPred_interval {n : ℕ} (H : SimpleGraph (Fin n))
    (S₁ S₂ S₃ : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag})
    (h12 : S₁ ⊆ S₂) (h23 : S₂ ⊆ S₃)
    (hP1 : UEPred H S₁) (hP3 : UEPred H S₃) :
    UEPred H S₂ := by
  apply ue_chain_interval;
  rotate_left;
  rotate_left;
  · exact hP1
  · exact hP3
  · intro u v; simp +decide [ graphOfEdges ] ;
    exact fun _ h => ⟨ ‹_›, h12 h ⟩;
  · rw [ graphOfEdges, graphOfEdges ] ; exact SimpleGraph.fromEdgeSet_mono <| by aesop_cat;

/-
UEPred on the empty set is false for n ≥ 2.
-/
private lemma UEPred_empty {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    ¬ UEPred H ∅ := by
  -- The empty Finset gives graphOfEdges ∅ = fromEdgeSet ∅ = ⊥ (the empty graph).
  simp [UEPred, graphOfEdges];
  -- The empty graph has n! embeddings into any graph H, so it cannot be uniquely embeddable.
  simp [UniquelyEmbeds];
  -- The number of embeddings of the empty graph into any graph H is the number of permutations of the vertices of H, which is n!.
  have h_empty_embeddings : numEmbeddings ⊥ H = Nat.factorial n := by
    convert numEmbeddings_top ⊥ using 1;
    unfold numEmbeddings;
    unfold embeddingFinset;
    unfold IsEmbedding; aesop;
  exact h_empty_embeddings.symm ▸ Nat.ne_of_gt ( Nat.lt_of_lt_of_le ( by decide ) ( Nat.factorial_le hn ) )

/-
Extension count: for S with UEPred H S, the number of extensions is eH - |S|.
-/
-- The generated UE extension count needs extra heartbeats for edge-set encodings.
set_option maxHeartbeats 1600000 in
private lemma UEPred_ext_count {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag})
    (hPS : UEPred H S) (hScard : S.card < Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag}) :
    ((Finset.univ : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}).filter
      (fun e => e ∉ S ∧ UEPred H (insert e S))).card =
    H.edgeFinset.card - S.card := by
  -- By definition of `UEPred`, there exists a unique embedding `σ` such that `σ ∈ embeddingFinset (graphOfEdges S) H`.
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : SimpleGraph (Fin n), graphOfEdges S = G₀ ∧ UniquelyEmbeds G₀ H := by
    exact ⟨ _, rfl, hPS ⟩;
  -- Since `σ` is in `embeddingFinset G₀ H`, by `supergraph_UE_count`, the number of supergraphs `G'` of `G₀` with `G'.edgeFinset.card = G₀.edgeFinset.card + 1` and `UniquelyEmbeds G' H` is `(H.edgeFinset.card - G₀.edgeFinset.card).choose 1`.
  have h_card_supergraphs : (Finset.univ.filter (fun G' : SimpleGraph (Fin n) => G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + 1 ∧ UniquelyEmbeds G' H)).card = (H.edgeFinset.card - G₀.edgeFinset.card) := by
    have := supergraph_UE_count G₀ H;
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ ∈ embeddingFinset G₀ H := by
      have hcard : (embeddingFinset G₀ H).card = 1 := by
        simpa [UniquelyEmbeds, numEmbeddings] using hG₀.2
      exact Finset.card_pos.mp (by rw [hcard]; norm_num);
    by_cases h : 1 ≤ H.edgeFinset.card - G₀.edgeFinset.card <;> simp_all +decide [ Nat.choose ];
    · simpa using this σ 1 hσ h;
    · intro G' hG' hG'_card hG'_UE
      have hG'_edgeFinset : G'.edgeFinset.card ≤ H.edgeFinset.card := by
        obtain ⟨ σ, hσ ⟩ := Finset.card_pos.mp ( show 0 < Finset.card ( Finset.filter ( fun σ : Equiv.Perm ( Fin n ) => IsEmbedding G' H σ ) Finset.univ ) from by
                                                  exact Nat.lt_of_sub_eq_succ hG'_UE );
        have hG'_edgeFinset : G'.edgeFinset.image (fun e => Sym2.map (fun v => σ v) e) ⊆ H.edgeFinset := by
          simp_all +decide [ Finset.subset_iff, IsEmbedding ];
          rintro ⟨ u, v ⟩ huv; specialize hσ u v; aesop;
        have := Finset.card_le_card hG'_edgeFinset; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
        rw [ Finset.card_image_of_injective ] at this <;> norm_num [ Function.Injective ] at *
        · linarith
        · rintro ⟨ a, b ⟩ ⟨ c, d ⟩ h; simp_all +decide [ Sym2.eq_iff ] ;
      omega;
  -- By definition of `graphOfEdges`, the edge set of `G₀` is exactly `S`.
  have h_edge_set : G₀.edgeFinset = S.image Subtype.val := by
    unfold graphOfEdges at hG₀; aesop;
  convert h_card_supergraphs using 1;
  · refine Finset.card_bij ( fun e he => graphOfEdges ( insert e S ) ) ?_ ?_ ?_ <;> simp_all +decide [ Finset.subset_iff ];
    · intro a ha hS hUE
      have hG₀_le : G₀ ≤ graphOfEdges (insert ⟨a, ha⟩ S) := by
        intro u v; simp_all +decide [ graphOfEdges ] ;
        replace h_edge_set := Finset.ext_iff.mp h_edge_set ( s(u, v) ) ; aesop;
      have hG₀_card : (graphOfEdges (insert ⟨a, ha⟩ S)).edgeFinset.card = (image Subtype.val S).card + 1 := by
        have hG₀_card : (graphOfEdges (insert ⟨a, ha⟩ S)).edgeFinset = (image Subtype.val S) ∪ {a} := by
          unfold graphOfEdges; aesop;
        rw [ hG₀_card, Finset.card_union ] ; aesop
      have hG₀_uniquelyEmbeds : UniquelyEmbeds (graphOfEdges (insert ⟨a, ha⟩ S)) H := by
        exact hUE
      exact ⟨hG₀_le, hG₀_card, hG₀_uniquelyEmbeds⟩;
    · intro a ha ha' ha'' b hb hb' hb'' hab; replace hab := congr_arg ( fun G => G.edgeFinset ) hab; simp_all +decide [ Finset.ext_iff, SimpleGraph.edgeSet ] ;
      specialize hab a ; simp_all +decide [ graphOfEdges ];
    · intro G' hG' hG'_card hG'_UE
      obtain ⟨e, he⟩ : ∃ e : {e : Sym2 (Fin n) // ¬e.IsDiag}, e ∉ S ∧ G'.edgeFinset = S.image Subtype.val ∪ {e.val} := by
        have h_edge_set : G'.edgeFinset ⊇ S.image Subtype.val := by
          exact h_edge_set ▸ SimpleGraph.edgeFinset_mono hG';
        have h_edge_set : ∃ e ∈ G'.edgeFinset, e ∉ S.image Subtype.val := by
          exact Finset.not_subset.mp fun h => by have := Finset.card_le_card h; linarith;
        obtain ⟨ e, he₁, he₂ ⟩ := h_edge_set; use ⟨ e, by
          cases e ; aesop ⟩ ; simp_all +decide [ Finset.ext_iff ] ;
        all_goals generalize_proofs at *;
        have := Finset.eq_of_subset_of_card_le ( show image Subtype.val S ∪ { e } ⊆ G'.edgeFinset from Finset.union_subset h_edge_set ( Finset.singleton_subset_iff.mpr <| by aesop ) ) ; simp_all +decide [ Finset.card_union ] ;
        intro a; replace this := Finset.ext_iff.mp this a; aesop;
      refine ⟨ e.val, e.property, ⟨ he.1, ?_ ⟩, ?_ ⟩ <;> simp_all +decide [ UEPred ];
      · convert hG'_UE using 1;
        ext u v; simp [graphOfEdges, he];
        replace he := Finset.ext_iff.mp he.2 ( s(u, v) ) ; aesop;
      · ext u v; simp +decide [ graphOfEdges, he ] ;
        replace he := Finset.ext_iff.mp he.2 ( s(u, v) ) ; aesop;
  · rw [ h_edge_set, Finset.card_image_of_injective _ Subtype.coe_injective ]

/-
Counting equivalence: numUEWithEdges matches the edge-subset count.
-/
-- The generated UE predicate count needs extra heartbeats for graph/edge-subset conversion.
set_option maxHeartbeats 800000 in
private lemma UEPred_countP {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) :
    numUEWithEdges H m =
    (Finset.univ.filter (fun S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag} =>
      S.card = m ∧ UEPred H S)).card := by
  refine Finset.card_bij ?_ ?_ ?_ ?_;
  · use fun G hG => Finset.univ.filter (fun e => e.val ∈ G.edgeFinset);
  · simp +contextual [ UEPred ];
    intro G hG hUE
    constructor
    ·
      convert hG using 1;
      refine Finset.card_bij ( fun e he => e.val ) ?_ ?_ ?_ <;> simp +decide;
      exact fun e he => ⟨ he, by cases e; aesop ⟩
    ·
      convert hUE using 1;
      ext u v; simp +decide [ graphOfEdges ] ;
      exact fun h => h.ne;
  · simp +contextual [ Finset.ext_iff, Set.ext_iff ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; ext u v; specialize h ( Sym2.mk u v ) ; aesop;
  · intro S hS;
    refine ⟨ graphOfEdges S, ?_, ?_ ⟩ <;> simp_all +decide [ UEPred ];
    · convert hS.1 using 1;
      refine Finset.card_bij ( fun e he => ⟨ e, ?_ ⟩ ) ?_ ?_ ?_ <;> simp_all +decide [ graphOfEdges ];
      tauto;
    · ext e; simp [graphOfEdges];
      grind

/-
The z-process sum ≤ 1: key process bound.
    Proved by applying the abstract transition sum bound with the UE predicate
    on edge subsets, using ue_chain_interval for the interval property and
    supergraph_UE_count for the extension count.
-/
-- The generated z-process sum proof needs extra heartbeats for transition-sum conversion.
set_option maxHeartbeats 1600000 in
lemma sum_z_refined_le_one {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    ∑ m ∈ Finset.range (n.choose 2 + 1),
      (fUE H m - ((H.edgeFinset.card : ℝ) - ↑m + 1) / (↑(n.choose 2) - ↑m + 1) *
       fUE H (m - 1)) ≤ 1 := by
  have := @EdgeOrderingCount.transition_sum_le_one_gen;
  convert this ( fun m => numUEWithEdges H m ) ( fun m => H.edgeFinset.card - m ) ( fun S => UEPred H S ) _ _ _ _ using 1;
  · rw [ Sym2.card_subtype_not_diag ];
    norm_num [ fUE ];
    refine Finset.sum_congr rfl fun x hx => ?_;
    rcases x with ( _ | x ) <;> norm_num;
    · exact Or.inr ( numUEWithEdges_zero hn H );
    · by_cases h : x ≤ H.edgeFinset.card;
      · exact Or.inl ( by rw [ Nat.cast_sub h ] ; ring );
      · exact Or.inr <| Or.inl <| by rw [ numUEWithEdges ] ; exact Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun G hG => by intro h; linarith [ show G.edgeFinset.card ≤ H.edgeFinset.card from by
                                                                                                                                                                  exact h.2 |> fun h => by
                                                                                                                                                                    obtain ⟨ σ, hσ ⟩ := Finset.card_eq_one.mp h;
                                                                                                                                                                    rw [ Finset.eq_singleton_iff_unique_mem ] at hσ;
                                                                                                                                                                    have h_card_le : G.edgeFinset.card ≤ (Finset.image (fun e => Sym2.map σ e) G.edgeFinset).card := by
                                                                                                                                                                      rw [ Finset.card_image_of_injective ];
                                                                                                                                                                      intro e₁ e₂ h; induction e₁ using Sym2.inductionOn ; induction e₂ using Sym2.inductionOn ; aesop;
                                                                                                                                                                    refine le_trans h_card_le <| Finset.card_le_card ?_;
                                                                                                                                                                    simp +decide [ Finset.subset_iff, SimpleGraph.edgeSet ];
                                                                                                                                                                    rintro ⟨ u, v ⟩ huv; simp_all +decide [ edgeSetEmbedding ] ;
                                                                                                                                                                    exact hσ.1 |> fun h => by simpa using Finset.mem_filter.mp h |>.2 u v huv; ] ;
  · exact fun S₁ S₂ S₃ a a_1 a_2 a_3 ↦ UEPred_interval H S₁ S₂ S₃ a a_1 a_2 a_3;
  · exact UEPred_empty hn H;
  · convert UEPred_ext_count hn H using 1;
  · exact fun m ↦ UEPred_countP H m

/-
**Process inequality** (key combinatorial bound from the random graph process).

    For any set S of edge counts, the sum of UE fractions f(m) = R(m)/C(N,m)
    is bounded by k + |S| · (eH/N)^{k-1}.

    Proved by combining abstract_process_bound with sum_z_refined_le_one.
-/
lemma process_inequality {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (k : ℕ) (hk : 1 ≤ k) (hk_le : k ≤ H.edgeFinset.card)
    (S : Finset ℕ) (hS : ∀ m ∈ S, m ≤ n.choose 2) :
    (∑ m ∈ S,
      (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≤
    ↑k + ↑S.card * ((H.edgeFinset.card : ℝ) / ↑(n.choose 2)) ^ (k - 1) := by
  have := @abstract_process_bound;
  contrapose! this;
  refine ⟨ n.choose 2, fun m => if m ≤ n.choose 2 then ( numUEWithEdges H m : ℝ ) / ( Nat.choose ( n.choose 2 ) m : ℝ ) else 0, fun m => if m ≤ n.choose 2 then Max.max 0 ( ( numUEWithEdges H m : ℝ ) / ( Nat.choose ( n.choose 2 ) m : ℝ ) - ( ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ) ) * ( if m = 0 then 0 else ( numUEWithEdges H ( m - 1 ) : ℝ ) / ( Nat.choose ( n.choose 2 ) ( m - 1 ) : ℝ ) ) ) else 0, ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ), k, S, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num;
  · exact numUEWithEdges_zero hn H;
  · intro m; split_ifs <;> positivity;
  · intro m; split_ifs <;> positivity;
  · grind +locals;
  · refine ⟨ div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ ?_ (
      Nat.cast_nonneg _ ), hk, hS, ?_, ?_, ?_ ⟩;
    · convert H.card_edgeFinset_le_card_choose_two;
      norm_num;
    · refine le_trans ?_ ( sum_z_refined_le_one hn H );
      refine Finset.sum_le_sum fun m hm => ?_;
      split_ifs <;> norm_num [ fUE ];
      · simp_all +decide [ numUEWithEdges_zero hn ];
      · constructor;
        · have := double_count_ue_pairs hn H m ( Nat.pos_of_ne_zero ‹_› ) ‹_›;
          rw [ div_mul_div_comm, div_le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ Nat.choose_succ_succ ];
          · rcases m <;> simp_all +decide [ Nat.add_one_mul_choose_eq, mul_assoc, mul_comm, mul_left_comm ];
            refine le_trans ( mul_le_mul_of_nonneg_left this ( Nat.cast_nonneg _ ) ) ?_;
            rw [ ← mul_assoc, ← mul_assoc ];
            exact mul_le_mul_of_nonneg_right ( by nlinarith [ Nat.add_one_mul_choose_eq ( Nat.choose n 2 ) ‹_›, Nat.choose_succ_succ ( Nat.choose n 2 ) ‹_› ] ) ( Nat.cast_nonneg _ );
          · exact Nat.choose_pos ( Nat.sub_le_of_le_add <| by linarith );
          · exact Nat.choose_pos ‹_›;
        · have h_frac_le : ((H.edgeFinset.card : ℝ) - m + 1) / (n.choose 2 - m + 1) ≤ (H.edgeFinset.card : ℝ) / (n.choose 2) := by
            rw [ div_le_div_iff₀ ] <;> norm_num;
            · have h_frac_le : (H.edgeFinset.card : ℝ) ≤ n.choose 2 := by
                have := H.card_edgeFinset_le_card_choose_two;
                aesop;
              nlinarith [ show ( m : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ‹_› ];
            · exact add_pos_of_nonneg_of_pos ( sub_nonneg_of_le ( mod_cast by linarith ) ) zero_lt_one;
            · exact Nat.choose_pos ( by linarith );
          nlinarith [ show 0 ≤ ( numUEWithEdges H ( m - 1 ) : ℝ ) / ( Nat.choose ( n.choose 2 ) ( m - 1 ) : ℝ ) by positivity ];
      · linarith [ Finset.mem_range.mp hm ];
    · intros; linarith;
    · exact this.trans_le ( Finset.sum_le_sum fun x hx => by rw [ if_pos ( hS x hx ) ] )

/-
Restricted sum lower bound: from probUniqueEmb H ≥ δ, Chernoff concentration,
    and the binomial anticoncentration bound, we get a large restricted sum of
    UE fractions over edge counts near N/2.
-/
-- The generated restricted-sum lower bound needs extra heartbeats for concentration estimates.
set_option maxHeartbeats 800000 in
lemma restricted_sum_lower_bound {n : ℕ} (hn : 4 ≤ n) (H : SimpleGraph (Fin n))
    (δ : ℝ) (hδ : 0 < δ) (hH : probUniqueEmb H ≥ δ)
    (L : ℕ) (hL : 0 < L)
    (hchern : ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤
      (δ / 4) * 2 ^ (n.choose 2)) :
    ∃ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) ∧
      S.card ≤ 2 * L * n + 1 ∧
      (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≥
        3 * δ * ↑n / 16 := by
  -- By definition of $probUniqueEmb$, we know that
  have h_prob_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ)) ≥ δ * 2 ^ (n.choose 2) := by
    refine le_trans ( mul_le_mul_of_nonneg_right hH ( by positivity ) ) ?_;
    unfold probUniqueEmb numUEWithEdges; norm_num;
    rw_mod_cast [ ← Finset.card_biUnion ];
    · refine Finset.card_mono ?_;
      intro G hG; simp_all +decide [ Finset.subset_iff ] ;
      simpa using G.card_edgeFinset_le_card_choose_two;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
  -- By definition of $numUEWithEdges$, we know that
  have h_numUE_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ)) ≤ (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ) * (if |((m : ℝ) - (n.choose 2 : ℝ) / 2)| < L * n then 1 else 0)) + (δ / 4) * 2 ^ (n.choose 2) := by
    have h_numUE_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ) * (if |((m : ℝ) - (n.choose 2 : ℝ) / 2)| ≥ L * n then 1 else 0)) ≤ (δ / 4) * 2 ^ (n.choose 2) := by
      refine le_trans ?_ hchern;
      simp +decide [ numUEWithEdges ];
      norm_num [ Finset.sum_ite ];
      rw_mod_cast [ ← Finset.card_biUnion ];
      · exact Finset.card_le_card fun x hx => by aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    convert add_le_add_left h_numUE_def _ using 1;
    all_goals rw [ add_comm ];
    rw [ add_comm, ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> linarith;
  -- Let's choose the set $S$ of edge counts $m$ such that $|m - N/2| < Ln$.
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) ∧ S.card ≤ 2 * L * n + 1 ∧ (∑ m ∈ S, (numUEWithEdges H m : ℝ)) ≥ (3 * δ / 4) * 2 ^ (n.choose 2) := by
    refine ⟨ Finset.filter ( fun m : ℕ => |( m : ℝ ) - n.choose 2 / 2| < L * n ) ( Finset.range ( n.choose 2 + 1 ) ), ?_, ?_, ?_ ⟩ <;> norm_num at *;
    · grind +revert;
    · let S : Finset ℕ := Finset.Ico ( Nat.ceil ( ( n.choose 2 : ℝ ) / 2 - L * n ) ) (
        Nat.ceil ( ( n.choose 2 : ℝ ) / 2 + L * n ) );
      refine le_trans ( Finset.card_le_card (t := S) ?_ ) ?_;
      · intro m hm; dsimp [S];
        simp_all +decide [ abs_lt ] ;
        exact ⟨ by linarith, Nat.lt_ceil.mpr <| by linarith ⟩;
      · dsimp [S];
        norm_num [ Nat.card_Ico ];
        nlinarith [
          Nat.le_ceil ( ( n.choose 2 : ℝ ) / 2 - L * n ),
          Nat.ceil_lt_add_one ( show 0 ≤ ( n.choose 2 : ℝ ) / 2 + L * n by positivity ) ];
    · norm_num [ Finset.sum_ite ] at * ; linarith;
  -- Apply the binomial anticoncentration bound to each term in the sum.
  have h_binom_anticoncentration : ∀ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ) ≥ (numUEWithEdges H m : ℝ) * (n / (4 * 2 ^ (n.choose 2))) := by
    intros m hm
    have h_binom_anticoncentration : ((n.choose 2).choose m : ℝ) / 2 ^ (n.choose 2) ≤ 4 / n := by
      exact binomial_anticoncentration hn m;
    rw [ ge_iff_le, mul_div, div_le_div_iff₀ ] <;> try positivity;
    · rw [ div_le_div_iff₀ ] at h_binom_anticoncentration <;> first | positivity | nlinarith [ show ( 0 : ℝ ) ≤ numUEWithEdges H m by positivity ] ;
    · exact Nat.cast_pos.mpr ( Nat.choose_pos ( hS.1 m hm ) );
  refine ⟨ S, hS.1, hS.2.1, le_trans ?_ ( Finset.sum_le_sum h_binom_anticoncentration ) ⟩;
  rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast, show ( 2 ^ n.choose 2 : ℝ ) > 0 by positivity, mul_div_cancel₀ ( n : ℝ ) ( by positivity : ( 4 * 2 ^ n.choose 2 : ℝ ) ≠ 0 ) ] ;

/-
For large n and probUniqueEmb H ≥ δ, H has at least n edges.
    Uses the union bound: probUniqueEmb H ≤ n! · 2^{eH} / 2^N,
    and for eH < n this is exponentially small for large n.
-/
lemma ue_implies_many_edges (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ → n ≤ H.edgeFinset.card := by
  -- Use probUniqueEmb_le_factorial_div which gives probUniqueEmb H ≤ n!/2^{N-eH}.
  have h_prob_le : ∀ n : ℕ, ∀ H : SimpleGraph (Fin n), probUniqueEmb H ≤ (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - H.edgeFinset.card) := by
    exact fun n H ↦ probUniqueEmb_le_factorial_div H;
  -- For n large enough: n!/2^{n(n-3)/2} < δ. This gives a contradiction with probUniqueEmb H ≥ δ.
  have h_contradiction : ∃ n₀ : ℕ, ∀ n ≥ n₀, (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - n) < δ := by
    -- We'll use that $n! / 2^{n(n-3)/2}$ tends to $0$ as $n$ tends to infinity.
    have h_lim : Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ) / 2 ^ (n * (n - 3) / 2)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $n! \leq n^n$ and $2^{n(n-3)/2}$ grows much faster than $n^n$.
      have h_bound : ∀ n : ℕ, n ≥ 10 → (n.factorial : ℝ) / 2 ^ (n * (n - 3) / 2) ≤ (n / 2 ^ ((n - 3) / 2 : ℝ)) ^ n := by
        intros n hn
        have h_factorial_bound : (n.factorial : ℝ) ≤ n ^ n := by
          exact mod_cast Nat.recOn n ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ih ) ( by gcongr ; linarith ) ;
        have h_exp_bound : (2 : ℝ) ^ (n * (n - 3) / 2) = (2 ^ ((n - 3) / 2 : ℝ)) ^ n := by
          rw [ ← Real.rpow_natCast _ n, ← Real.rpow_natCast _ ( n * ( n - 3 ) / 2 ), ← Real.rpow_mul ] <;> norm_num;
          rw [ ← Real.rpow_natCast ] ; rw [ Nat.cast_div ] <;> norm_num
          all_goals try ring_nf
          · rw [ Nat.cast_sub ( by linarith ) ] ; ring_nf;
          · rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ ← even_iff_two_dvd, mul_add, parity_simps ]
        rw [div_pow]
        field_simp [h_exp_bound];
        rw [ h_exp_bound, mul_comm ] ; gcongr;
      -- For $n \geq 10$, we have $n / 2^{(n-3)/2} < 1$, thus $(n / 2^{(n-3)/2})^n \to 0$ as $n \to \infty$.
      have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n / 2 ^ ((n - 3) / 2 : ℝ)) : ℕ → ℝ) Filter.atTop (nhds 0) := by
        -- We can use the fact that $2^{(n-3)/2}$ grows much faster than $n$.
        have h_exp_growth : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.exp ((n - 3) / 2 * Real.log 2)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $n / e^{(n-3)/2 \ln 2}$ tends to $0$ as $n$ tends to infinity.
          have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.exp (n * Real.log 2 / 4)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{n \ln 2}{4}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{4y}{e^y}$.
            suffices h_lim_y : Filter.Tendsto (fun y : ℝ => 4 * y / Real.exp y) Filter.atTop (nhds 0) by
              have h_subst : Filter.Tendsto (fun n : ℕ => 4 * (n * Real.log 2 / 4) / Real.exp (n * Real.log 2 / 4)) Filter.atTop (nhds 0) := by
                exact h_lim_y.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| tendsto_natCast_atTop_atTop.atTop_mul_const ( by positivity );
              convert h_subst.div_const ( Real.log 2 ) using 2 <;> ring_nf;
              norm_num [ mul_assoc, mul_comm, mul_left_comm ];
            simpa [div_eq_mul_inv, mul_assoc, Real.exp_neg] using
              tendsto_const_nhds.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1);
          refine squeeze_zero_norm' ?_ h_lim_zero;
          filter_upwards [ Filter.eventually_gt_atTop 12 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) ≥ 13 by exact_mod_cast hn ] ;
        convert h_exp_growth using 2 ; norm_num [ Real.rpow_def_of_pos, mul_comm ];
      refine squeeze_zero_norm' (a := fun n : ℕ => ( (n : ℝ) / 2 ^ ( ( (n : ℝ) - 3 ) / 2 ) ) ^ n) ?_ ?_;
      · filter_upwards [ Filter.eventually_ge_atTop 10 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound n hn;
      · rw [ Metric.tendsto_nhds ] at *;
        intro ε hε; filter_upwards [ h_lim_zero ( Min.min ε 1 ) ( lt_min hε zero_lt_one ), Filter.eventually_ge_atTop 10 ] with n hn hn'; simp_all +decide [ abs_div, abs_of_nonneg, Real.rpow_nonneg ] ;
        exact lt_of_le_of_lt ( pow_le_of_le_one ( by positivity ) hn.2.le ( by positivity ) ) hn.1;
    have := h_lim.eventually ( gt_mem_nhds hδ );
    obtain ⟨ n₀, hn₀ ⟩ := Filter.eventually_atTop.mp this; use n₀ + 4; intros n hn; specialize hn₀ n ( by linarith ) ; rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ] ;
    grind;
  contrapose! h_contradiction;
  intro n₀; obtain ⟨ n, hn₁, H, hn₂, hn₃ ⟩ := h_contradiction n₀; use n, hn₁; refine le_trans hn₂ ?_; refine le_trans ( h_prob_le n H ) ?_; gcongr ; linarith;

/-
**Process bound** (core of Lemma 2.2).
-/
lemma process_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ (α : ℝ), α > 0 ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    0 < n.choose 2 ∧
    ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ ⌊δ * ↑n / 32⌋₊ ≥ α := by
  -- Set α = (δ/(20*L))², n₀ = max(n₁, 4*L + ⌈64/δ⌉₊ + 1).
  obtain ⟨L, hL⟩ := chernoff_edge_tail (δ / 4) (by linarith)
  obtain ⟨n₁, hn₁⟩ := ue_implies_many_edges δ hδ
  set α := (δ / (20 * L)) ^ 2
  set n₀ := max n₁ (4 * L + Nat.ceil (64 / δ) + 1);
  refine ⟨ α, ?_, n₀, ?_ ⟩;
  · exact sq_pos_of_pos ( div_pos hδ ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr hL.1 ) ) );
  · intro n hn H hH
    have hn_ge_4 : 4 ≤ n := by
      grind
    have hn_ge_n₁ : n₁ ≤ n := by
      exact le_trans ( le_max_left _ _ ) hn
    have hn_ge_4L : 4 * L ≤ n := by
      grind
    have hn_ge_ceil : Nat.ceil (64 / δ) ≤ n := by
      grind
    have hn_ge_1 : 1 ≤ ⌊δ * n / 32⌋₊ := by
      exact Nat.floor_pos.mpr ( by nlinarith [ Nat.ceil_le.mp hn_ge_ceil, mul_div_cancel₀ 64 hδ.ne' ] );
    obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := restricted_sum_lower_bound hn_ge_4 H δ hδ hH L hL.1 ( hL.2 n hn_ge_4 );
    -- Apply process_inequality to get Σf ≤ k + |S|·(eH/N)^{k-1}.
    have h_process : (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≤ ⌊δ * n / 32⌋₊ + (2 * L * n + 1) * ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊δ * n / 32⌋₊ - 1) := by
      refine le_trans ( process_inequality ( by linarith ) H ⌊δ * n / 32⌋₊ hn_ge_1 ?_ S hS₁ ) ?_;
      · refine le_trans ?_ ( hn₁ n hn_ge_n₁ H hH );
        refine Nat.floor_le_of_le ?_;
        have := hH.trans ( show probUniqueEmb H ≤ 1 from probUniqueEmb_le_one H ) ; rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast, Nat.le_ceil ( 64 / δ ), mul_div_cancel₀ ( 64 : ℝ ) hδ.ne' ] ;
      · gcongr ; norm_cast;
    -- Combine the inequalities to get $(eH/N)^{k-1} \geq \delta/(20L)$.
    have h_combined : ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊δ * n / 32⌋₊ - 1) ≥ δ / (20 * L) := by
      rw [ ge_iff_le, div_le_iff₀ ] <;> try norm_num ; linarith;
      have := Nat.floor_le ( show 0 ≤ δ * n / 32 by positivity );
      nlinarith [ show ( L : ℝ ) ≥ 1 by norm_cast; linarith, show ( n : ℝ ) ≥ 4 by norm_cast, show ( ⌊δ * n / 32⌋₊ : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left ( show ( L : ℝ ) ≥ 1 by norm_cast; linarith ) ( show ( 0 : ℝ ) ≤ n by positivity ) ];
    refine ⟨ Nat.choose_pos ( by linarith ), ?_ ⟩;
    refine le_trans ( pow_le_pow_left₀ ( by positivity ) h_combined 2 ) ?_;
    rw [ ← pow_mul ];
    refine pow_le_pow_of_le_one ?_ ?_ ?_;
    · positivity;
    · refine div_le_one_of_le₀ ?_ ?_ <;> norm_cast;
      · convert H.card_edgeFinset_le_card_choose_two using 1;
        norm_num;
      · positivity;
    · rcases k : ⌊δ * n / 32⌋₊ with ( _ | _ | k ) <;> simp_all +decide;
      rw [ Nat.floor_eq_iff ] at k <;> norm_num at * <;> nlinarith [ show ( L : ℝ ) ≥ 1 by norm_cast; linarith, mul_div_cancel₀ ( 64 : ℝ ) hδ.ne' ]

/-
From x^k ≥ α > 0 and x ≤ 1, deduce x ≥ α^(1/k). Equivalently, 1 - x ≤ 1 - α^(1/k).
    For k large enough, 1 - α^(1/k) ≤ 2|ln α|/k.
-/
lemma pow_ge_implies_close_to_one {x α : ℝ} {k : ℕ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k) (h : x ^ k ≥ α) :
    1 - x ≤ -Real.log α / k := by
  by_cases hx_eq_zero : x = 0;
  · rw [ le_div_iff₀ ] <;> norm_num [ hk.ne', hx_eq_zero ] at * <;> linarith;
  · rw [ le_div_iff₀ ( by positivity ) ];
    nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < x by positivity ), Real.log_pow x k, Real.log_le_log ( by positivity ) h ]

lemma reduction_to_dense_large_n :
    ∀ δ : ℝ, δ > 0 →
    ∃ C₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    H.edgeFinset.card + C₀ * n ≥ n.choose 2 := by
  -- Use `process_bound` to get α > 0 and n₀ such that for n ≥ n₀ and probUniqueEmb H ≥ δ:
  intro δ hδ
  obtain ⟨α, hα_pos, n₀, hn₀⟩ := process_bound δ hδ;
  -- Choose C₀ = ⌈32 * (-log α) / δ⌉ + 1.
  use Nat.ceil (32 * (-Real.log α) / δ) + 1;
  -- Choose n₀ such that for n ≥ n₀, ⌊δn/32⌋₊ > 0 and the N/k bound holds.
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ n ≥ n₁, ⌊δ * (n : ℝ) / 32⌋₊ > 0 ∧ (n.choose 2 : ℝ) / ⌊δ * (n : ℝ) / 32⌋₊ ≤ 32 * (n : ℝ) / δ := by
    refine ⟨ ⌈32 / δ⌉₊ + 1, fun n hn => ⟨ ?_, ?_ ⟩ ⟩ <;> norm_num [ Nat.choose_two_right ] at *;
    · exact Nat.floor_pos.mpr ( by nlinarith [ Nat.lt_of_ceil_lt hn, mul_div_cancel₀ 32 hδ.ne' ] );
    · rw [ div_le_div_iff₀ ] <;> try positivity;
      · rcases n with ( _ | _ | n ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
        have := Nat.lt_floor_add_one ( δ * ( n + 1 + 1 ) / 32 );
        rw [ div_le_iff₀ ] at hn <;> nlinarith [ show ( ⌊δ * ( n + 1 + 1 ) / 32⌋₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.floor_pos.mpr ( by nlinarith [ mul_div_cancel₀ 32 hδ.ne' ] ) ) ];
      · exact Nat.cast_pos.mpr ( Nat.floor_pos.mpr ( by nlinarith [ Nat.le_ceil ( 32 / δ ), show ( n : ℝ ) ≥ ⌈32 / δ⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ 32 hδ.ne' ] ) );
  use Max.max n₀ n₁;
  intros n hn H hH
  have h_bound : (n.choose 2 : ℝ) - H.edgeFinset.card ≤ (n.choose 2 : ℝ) * (-Real.log α) / ⌊δ * (n : ℝ) / 32⌋₊ := by
    have h_bound : 1 - (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) ≤ -Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
      have h_bound : ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ ⌊δ * (n : ℝ) / 32⌋₊ ≥ α := by
        exact hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.2;
      have h_bound : 1 - (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) ≤ -Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
        have h_log : Real.log ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ≥ Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
          rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num;
          · simpa [ mul_comm ] using Real.log_le_log ( by positivity ) h_bound;
          · exact hn₁ n ( le_trans ( le_max_right _ _ ) hn ) |>.1
        have h_log : Real.log ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ≤ (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) - 1 := by
          by_cases h : ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ) = 0 <;> simp_all +decide [ Real.log_le_iff_le_exp ];
          · exact absurd h_bound ( not_le_of_gt ( by rw [ zero_pow ( Nat.ne_of_gt ( hn₁ n hn.2 |>.1 ) ) ] ; linarith ) );
          · exact Real.log_le_sub_one_of_pos ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero h.2 ) ) );
        grind;
      exact h_bound;
    rw [ mul_div_assoc ];
    rwa [ one_sub_div ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.1 ), div_le_iff₀' <| Nat.cast_pos.mpr <| hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.1 ] at h_bound;
  have h_bound : (n.choose 2 : ℝ) - H.edgeFinset.card ≤ 32 * (n : ℝ) * (-Real.log α) / δ := by
    refine le_trans h_bound ?_;
    convert mul_le_mul_of_nonneg_right ( hn₁ n ( le_trans ( le_max_right _ _ ) hn ) |>.2 ) ( neg_nonneg.mpr ( Real.log_nonpos hα_pos.le ( show α ≤ 1 from _ ) ) ) using 1 <;> ring_nf;
    exact le_trans ( hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.2 ) ( pow_le_one₀ ( by positivity ) ( div_le_one_of_le₀ ( mod_cast by
      convert H.card_edgeFinset_le_card_choose_two using 1;
      norm_num ) ( by positivity ) ) );
  have := Nat.le_ceil ( 32 * -Real.log α / δ );
  rw [ div_le_iff₀ ] at this <;> norm_num at * <;> try linarith;
  exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ ( - ( 32 * n * Real.log α ) ) hδ.ne' ] ;

/-- **Lemma 2.2** (Reduction to the very dense case).
    Derived from the Chernoff bound. -/
theorem reduction_to_dense :
    ∀ δ : ℝ, δ > 0 →
    ∃ C : ℕ, ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    H.edgeFinset.card + C * n ≥ n.choose 2 := by
  intro δ hδ
  obtain ⟨C₀, n₀, h₀⟩ := reduction_to_dense_large_n δ hδ
  use max C₀ (n₀ / 2 + 1)
  intro n H hH
  by_cases hn : n₀ ≤ n
  · -- Large n: use reduction_to_dense_large_n
    have h1 := h₀ n hn H hH
    calc H.edgeFinset.card + max C₀ (n₀ / 2 + 1) * n
        ≥ H.edgeFinset.card + C₀ * n := by
          apply Nat.add_le_add_left
          exact Nat.mul_le_mul_right n (le_max_left C₀ (n₀ / 2 + 1))
      _ ≥ n.choose 2 := h1
  · -- Small n: use vacuity
    push Not at hn
    have hn' : n ≤ 2 * (n₀ / 2 + 1) + 1 := by omega
    calc H.edgeFinset.card + max C₀ (n₀ / 2 + 1) * n
        ≥ (max C₀ (n₀ / 2 + 1)) * n := Nat.le_add_left _ _
      _ ≥ (n₀ / 2 + 1) * n := Nat.mul_le_mul_right n (le_max_right C₀ (n₀ / 2 + 1))
      _ ≥ n.choose 2 := small_n_vacuity (n₀ / 2 + 1) n hn'

/-! ### Switch-based infrastructure for Lemma 2.3 -/

/-- If σ embeds G into H and swap u v * σ also embeds, with u ≠ v,
    then there are at least 2 embeddings. -/
lemma switch_implies_two_embeddings {n : ℕ} {G H : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} {u v : Fin n}
    (huv : u ≠ v) (hσ : IsEmbedding G H σ) (hswap : IsEmbedding G H (Equiv.swap u v * σ)) :
    numEmbeddings G H ≥ 2 := by
  refine Finset.one_lt_card.mpr ?_;
  refine ⟨ σ, ?_, Equiv.swap u v * σ, ?_, ?_ ⟩ <;> simp_all +decide [ embeddingFinset ]

/-- The no-switch count is invariant under the base permutation σ. -/
lemma no_switch_count_invariant {n : ℕ} (H : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬ IsEmbedding G H (Equiv.swap u v * σ))).card =
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬ IsEmbedding G H (Equiv.swap u v))).card := by
  fapply Finset.card_bij;
  · exact fun G _ => σ • G
  · intro G hG
    simp [IsEmbedding] at hG ⊢;
    exact fun u v huv => by obtain ⟨ x, y, hxy, hyx ⟩ := hG u v huv; exact ⟨ σ x, σ y, by simpa using hxy, by simpa using hyx ⟩ ;
  · aesop;
  · intro b hb; use σ⁻¹ • b; simp_all +decide [ IsEmbedding ] ;
    exact fun u v huv => by obtain ⟨ x, y, hxy, hyx ⟩ := hb u v huv; exact ⟨ σ.symm x, σ.symm y, by simpa using hxy, by simpa using hyx ⟩ ;

/-- numUniquelyEmbedding H ≤ n! * #{G : no identity-switch}. -/
lemma numUniquelyEmbedding_le_factorial_mul_no_switch {n : ℕ} (H : SimpleGraph (Fin n)) :
    numUniquelyEmbedding H ≤
    n.factorial * (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬ IsEmbedding G H (Equiv.swap u v))).card := by
  set S := Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H);
  have h_subset : S ⊆ Finset.biUnion (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun σ => Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬ IsEmbedding G H (Equiv.swap u v * σ))) := by
    intro G hG
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), IsEmbedding G H σ ∧ ∀ τ : Equiv.Perm (Fin n), IsEmbedding G H τ → τ = σ := by
      simp +zetaDelta at *;
      obtain ⟨ σ, hσ ⟩ := Finset.card_eq_one.mp hG;
      exact ⟨ σ, Finset.mem_filter.mp ( hσ.symm ▸ Finset.mem_singleton_self _ ) |>.2, fun τ hτ => Finset.mem_singleton.mp ( hσ ▸ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hτ ⟩ ) ⟩;
    simp +zetaDelta at *;
    exact ⟨ σ, fun u v huv h => huv <| by have := hσ.2 ( Equiv.swap u v * σ ) h; simp_all +decide [ Equiv.swap_apply_def ] ⟩;
  refine le_trans ( Finset.card_le_card h_subset ) ?_;
  refine le_trans ( Finset.card_biUnion_le ) ?_;
  rw [ Finset.sum_congr rfl fun σ _ => no_switch_count_invariant H σ ] ; simp +decide [ Fintype.card_perm ]

/-- n! * exp(-n * log n) → 0. -/
lemma factorial_exp_tendsto_zero :
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) < ε := by
  intro ε hε_pos
  have h_lim : Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n))) Filter.atTop (nhds 0) := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ) / (↑n ^ n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_factorial_div_pow_self_atTop
    refine squeeze_zero_norm' ?_ h_lim;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf; norm_num [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log ( Nat.cast_pos.mpr hn ) ] ;
  simpa using h_lim.eventually ( gt_mem_nhds hε_pos )

/-! ### Complement duality infrastructure -/

/-
σ embeds G into H iff σ⁻¹ embeds Hᶜ into Gᶜ.
-/
lemma embedding_iff_compl {n : ℕ} {G H : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    IsEmbedding G H σ ↔ IsEmbedding Hᶜ Gᶜ σ⁻¹ := by
  -- By contrapositive on each direction.
  constructor <;> intro h <;> simp_all +decide [ IsEmbedding, SimpleGraph.compl_adj ];
  · exact fun u v huv huv' => fun huv'' => huv' <| by simpa [ huv ] using h _ _ huv'';
  · contrapose! h;
    obtain ⟨ u, v, huv, h ⟩ := h; use σ u, σ v; aesop;

/-
The number of embeddings of G into H equals the number of embeddings
    of Hᶜ into Gᶜ (via the bijection σ ↦ σ⁻¹).
-/
lemma numEmbeddings_compl {n : ℕ} (G H : SimpleGraph (Fin n)) :
    numEmbeddings G H = numEmbeddings Hᶜ Gᶜ := by
  unfold numEmbeddings embeddingFinset
  refine Finset.card_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_
  · intro σ hσ
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, embedding_iff_compl.mp (Finset.mem_filter.mp hσ).2⟩
  · intro σ _ τ _ hστ
    have := congrArg Inv.inv hστ
    simpa using this
  · intro τ hτ
    refine ⟨τ⁻¹, ?_, by simp⟩
    have hEmb : IsEmbedding Hᶜ Gᶜ τ := (Finset.mem_filter.mp hτ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hEmb' : IsEmbedding Hᶜ Gᶜ (τ⁻¹)⁻¹ := by
      simpa using hEmb
    exact (embedding_iff_compl (G := G) (H := H) (σ := τ⁻¹)).mpr hEmb'

/-
**Complement duality**: The number of graphs G that uniquely embed
    into H equals the number of graphs G' such that Hᶜ uniquely embeds into G'.
-/
lemma complement_duality {n : ℕ} (H : SimpleGraph (Fin n)) :
    numUniquelyEmbedding H =
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      numEmbeddings Hᶜ G = 1)).card := by
  apply Finset.card_bij (fun G _ => Gᶜ);
  · norm_num +zetaDelta at *;
    exact fun G hG => numEmbeddings_compl G H ▸ hG;
  · aesop;
  · intro b hb; use bᶜ; simp_all +decide [ UniquelyEmbeds ] ;
    rw [ numEmbeddings_compl ] ; aesop

/-
The original `no_switch_exponential_bound` counted *all* graphs G where no
   transposition is an embedding of G into H. That statement is false: for
   H = Kₙ minus one edge the set has size ~2^{C(n−2,2)}, which exceeds
   2^N · exp(−n log n) for large n.

   The paper (Lemma 2.3) instead uses a complement trick: σ embeds G into H iff
   σ⁻¹ embeds Hᶜ into Gᶜ, and since G(n,1/2) is self-complementary in law,
   Pr[G ↪_unique H] = Pr[Hᶜ ↪_unique G]. The switch argument is then applied to
   the sparse graph Hᶜ embedded into a random G, where Azuma–Hoeffding gives the
   needed concentration.

   The resulting bound (combining complement duality, union bound over n!
   bijections, and the Azuma-based switch probability) is:
     probUniqueEmb H ≤ n! · exp(−n log n)
   which tends to 0. We state this as the corrected replacement.

**Corrected Azuma-based bound (Lemma 2.3 core)**:
    For H with ≤ C·n non-edges, `probUniqueEmb H ≤ n! · exp(−n · log n)`.

    **Proof sketch (from the paper)**:
    1. *Complement duality*: σ embeds G into H iff σ⁻¹ embeds Hᶜ into Gᶜ.
       Since G ∼ G(n,1/2) is self-complementary in distribution,
       Pr_G[G ↪_unique H] = Pr_G[Hᶜ ↪_unique G].
    2. *Switch definition*: For a bijection π and distinct u,v ∈ V(G),
       {u,v} is a π-switch if N_G(v) ⊇ π(N_{Hᶜ}(π⁻¹(u)) \ N_{Hᶜ}(π⁻¹(v)))
       and symmetrically. If π embeds Hᶜ into G and {u,v} is a π-switch,
       then swapping yields a second embedding.
    3. *Claim 2.4 (iterative pruning)*: Find T ⊆ V(H) with |T| ≥ n/log^D(n),
       low-degree in Hᶜ, independent, with controlled high-degree interaction.
    4. *Azuma*: S = Σ_{u,v ∈ T} 𝟙[{u,v} is π-switch]. E[S] ≥ 2^{−8C}C(|T|,2)
       and Σ b_e² ≤ 2Cn³/log^{6D}(n). By `azuma_hoeffding`: Pr[S = 0] ≤ e^{−n log n}.
    5. *Union bound*: Pr[∃ π without switch] ≤ n! · e^{−n log n}.

    Derived from the `azuma_hoeffding` black box + Claim 2.4 pruning.

    The proof uses the paper's **switch condition**: for distinct u,v ∈ V(G),
    {u,v} is an id-switch for Hᶜ in G if
      N_G(v) ⊇ N_{Hᶜ}(u) \ N_{Hᶜ}(v) and N_G(u) ⊇ N_{Hᶜ}(v) \ N_{Hᶜ}(u).
    This is weaker than `IsEmbedding Hᶜ G (swap u v)`, but sufficient to
    produce a second embedding when composed with any embedding of Hᶜ into G.
-/

/-  The paper's switch condition IsIdSwitch is defined in SwitchHelpers.lean.
    {u,v} is an id-switch for a sparse graph Hc in G if the asymmetric
    neighborhoods of u and v in Hc are contained in the neighborhoods of
    v and u (respectively) in G. -/

/-
If π embeds Hc into G and {u,v} is an id-switch, then swap(u,v)*π
    also embeds Hc into G.
-/
-- The generated switch embedding proof needs extra heartbeats for permutation rewrites.
set_option maxHeartbeats 800000 in
lemma switch_gives_second_embedding {n : ℕ}
    {Hc G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {u v : Fin n}
    (huv : u ≠ v)
    (hπ : IsEmbedding Hc G π)
    (hswitch : IsIdSwitch Hc (π⁻¹ • G) (π⁻¹ u) (π⁻¹ v)) :
    IsEmbedding Hc G (Equiv.swap u v * π) := by
  unfold IsEmbedding at *; simp_all +decide [ IsIdSwitch, Equiv.swap_apply_def ];
  intro a b hab;
  by_cases ha : π a = u <;> by_cases hb : π b = u <;> by_cases ha' : π a = v <;> by_cases hb' : π b = v <;> simp_all +decide [ SimpleGraph.adj_comm ];
  all_goals have := hπ a b hab; simp_all +decide [ SimpleGraph.adj_comm ] ;
  · grind +suggestions;
  · grind +suggestions;
  · grind +suggestions;
  · grind +suggestions

/-
If Hc uniquely embeds into G via π, then there is no id-switch
    in π⁻¹•G for any pair of vertices.
-/
lemma unique_implies_no_switch {n : ℕ}
    {Hc G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    (hπ : IsEmbedding Hc G π)
    (huniq : ∀ τ : Equiv.Perm (Fin n), IsEmbedding Hc G τ → τ = π)
    (u v : Fin n) (huv : u ≠ v) :
    ¬IsIdSwitch Hc (π⁻¹ • G) (π⁻¹ u) (π⁻¹ v) := by
  contrapose! huniq;
  refine ⟨ Equiv.swap u v * π, switch_gives_second_embedding huv hπ huniq, ?_ ⟩;
  simp +decide [ Equiv.swap_apply_def, huv ]

/-
The number of G such that Hc uniquely embeds into G is at most
    n! times the number of G with no id-switch for Hc (using the switch condition).
-/
lemma complement_unique_le_factorial_mul_no_switch {n : ℕ} (Hc : SimpleGraph (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      numEmbeddings Hc G = 1)).card ≤
    n.factorial * (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
  -- Let π be the unique embedding of Hc into G.
  have h_unique_embedding : ∀ G : SimpleGraph (Fin n), numEmbeddings Hc G = 1 → ∃ σ : Equiv.Perm (Fin n), IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v) := by
    intro G hG
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), IsEmbedding Hc G σ ∧ ∀ τ : Equiv.Perm (Fin n), IsEmbedding Hc G τ → τ = σ := by
      obtain ⟨ σ, hσ ⟩ := Finset.card_eq_one.mp hG;
      rw [ Finset.eq_singleton_iff_unique_mem ] at hσ;
      exact ⟨ σ, Finset.mem_filter.mp hσ.1 |>.2, fun τ hτ => hσ.2 τ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hτ ⟩ ) ⟩;
    exact ⟨ σ, hσ.1, fun u v huv => unique_implies_no_switch hσ.1 hσ.2 u v huv ⟩;
  -- For each permutation σ, the set of graphs G with a unique embedding π such that π⁻¹ • G is in the no-switch set for σ is at most the number of graphs with no switch for σ.
  have h_card_bound : ∀ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))).card ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
    intro σ
    have h_card_bound : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))).card ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
      have : Finset.image (fun G => σ⁻¹ • G) (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))) ⊆ Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v) := by
        simp +contextual [ Finset.subset_iff ];
        rintro _ G hG hG' rfl u v huv; specialize hG' ( σ u ) ( σ v ) ; aesop;
      exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ) ( Finset.card_mono this );
    convert h_card_bound using 1;
  refine le_trans ?_ ( le_trans ( Finset.sum_le_sum (s := Finset.univ) fun σ _ => h_card_bound σ ) ?_ );
  · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
  · norm_num [ Finset.card_univ, Fintype.card_perm ]

/-! ### Azuma infrastructure for per_perm_switch_bound -/

/-- **Monotonicity of embeddings**: adding edges to G can only decrease
    the number of embeddings into H. -/
lemma numEmbeddings_antitone {n : ℕ} {G G' H : SimpleGraph (Fin n)}
    (hle : G ≤ G') :
    numEmbeddings G' H ≤ numEmbeddings G H := by
  apply Finset.card_le_card
  intro σ hσ
  simp [embeddingFinset, IsEmbedding] at *
  exact fun u v huv => hσ u v (hle huv)

/-! ### Azuma composition and independent set extraction -/

/-- Applying Azuma-Hoeffding to bound the number of inputs where a
    nonneg function equals zero. If f ≥ 0 has bounded differences with
    bounds b (with Σb² > 0), and c ≤ 2μ²/Σb², then
    #{x : f(x) = 0} ≤ 2^N · exp(-c). -/
lemma azuma_for_zero_count (N : ℕ) (f : (Fin N → Bool) → ℝ)
    (b : Fin N → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hbd : ∀ i : Fin N, ∀ x y : Fin N → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (hb_nonneg : ∀ i : Fin N, 0 ≤ b i)
    (hb_pos : 0 < ∑ i : Fin N, (b i) ^ 2)
    (c : ℝ) (hc : c ≥ 0)
    (hexp : c ≤ 2 * ((∑ x : Fin N → Bool, f x) / (2 ^ N : ℝ)) ^ 2 /
      (∑ i : Fin N, (b i) ^ 2)) :
    ((Finset.univ.filter (fun x : Fin N → Bool => f x = 0)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-c) := by
  set μ := (∑ x : Fin N → Bool, f x) / (2 ^ N : ℝ) with hμ_def
  have hμ_nonneg : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun _ _ => hf_nonneg _) (by positivity)
  have h_azuma := azuma_hoeffding N f b hbd hb_nonneg μ hμ_nonneg
  dsimp only at h_azuma
  simp only [hμ_def, sub_self] at h_azuma
  have h_eq : (Finset.univ.filter (fun x => f x = 0)) =
      (Finset.univ.filter (fun x => f x ≤ 0)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => le_of_eq h, fun h => le_antisymm h (hf_nonneg x)⟩
  rw [h_eq]
  apply le_trans h_azuma
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 ^ N)
  apply Real.exp_le_exp.mpr
  rw [show (∑ x : Fin N → Bool, f x) / (2 : ℝ) ^ N = μ from hμ_def.symm]
  have h_neg : -(2 * μ ^ 2 / ∑ i, b i ^ 2) ≤ -c := neg_le_neg hexp
  have h_eq2 : -2 * μ ^ 2 / ∑ i, b i ^ 2 = -(2 * μ ^ 2 / ∑ i, b i ^ 2) := by ring
  linarith

/-- Combining low_degree_set_large and greedy_independent_set:
    for Hc with ≤ Cn edges and n ≥ 2, there exists an independent set T
    with |T| ≥ n/(8C+2) and all vertices having degree ≤ 4C in Hc. -/
lemma find_good_independent_set {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (hCn : Hc.edgeFinset.card ≤ C * n) (hn : n ≥ 2) :
    ∃ T : Finset (Fin n),
    (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v) ∧
    (∀ v ∈ T, Hc.degree v ≤ 4 * C) ∧
    T.card ≥ n / (8 * C + 2) ∧
    T.card ≥ 1 := by
  set B := Finset.univ.filter (fun v => Hc.degree v ≤ 4 * C);
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin n), I ⊆ B ∧ (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬Hc.Adj u v) ∧ B.card ≤ I.card * (4 * C + 1) := by
    convert greedy_independent_set Hc B ( 4 * C ) ( fun v hv => Finset.mem_filter.mp hv |>.2 ) using 1;
  refine ⟨ I, hI.2.1, fun v hv => Finset.mem_filter.mp ( hI.1 hv ) |>.2, ?_, ?_ ⟩;
  · have hB_card : B.card ≥ n / 2 := by
      convert low_degree_set_large C Hc hCn using 1;
    rw [ ge_iff_le, Nat.div_le_iff_le_mul_add_pred ];
    · grind;
    · linarith;
  · have := low_degree_set_large C Hc hCn;
    grind +locals

/-
The sum of squared bounded-differences constants for switchCount
    through the edge-slot encoding.
    Σ switchBound(e)² ≤ 4·|T|·Σ_w dT(w)².

    Proof: for each w ∉ T, there are exactly |T| edge slots with
    one endpoint w and the other in T. Each contributes (2·dT(w))² = 4·dT(w)².
    For w ∈ T, dT(w) = 0 (T independent), so these contribute 0.
    Total: Σ_e switchBound(e)² = Σ_{w∉T} |T| · 4·dT(w)² = 4|T|·Σ_w dT(w)².
-/
-- The generated switch-count square bound needs extra heartbeats for edge-slot sums.
set_option maxHeartbeats 1600000 in
lemma switchCount_sum_sq_bound {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v) :
    ∑ e : EdgeSlot n, switchBound Hc T e ^ 2 ≤
    (4 : ℝ) * ↑(T.card) * ∑ w : Fin n,
      (↑((T.filter (fun v => Hc.Adj v w)).card) : ℝ) ^ 2 := by
  have h_sum_bound :
      ∑ e : EdgeSlot n, switchBound Hc T e ^ 2 ≤
        ∑ w : Fin n, ∑ v ∈ T,
          (4 : ℝ) * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2 := by
    have h_point : ∀ e : EdgeSlot n,
        switchBound Hc T e ^ 2 ≤
          ∑ w : Fin n, ∑ v ∈ T,
            (if (e.val.1 = v ∧ e.val.2 = w) ∨
                (e.val.1 = w ∧ e.val.2 = v) then
              (4 : ℝ) * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2 else 0) := by
      intro e
      rcases e with ⟨⟨a, b⟩, hab⟩
      simp [switchBound]
      split_ifs <;> norm_num [mul_pow]
      · simp_all +decide [Finset.sum_ite]
        refine le_trans ?_
          (Finset.single_le_sum
            (fun x _ => by
              exact mul_nonneg (Nat.cast_nonneg _) (by positivity))
            (Finset.mem_univ b))
        refine le_mul_of_one_le_left
          (show 0 ≤ (4 : ℝ) * ((T.filter (fun u => Hc.Adj u b)).card : ℝ) ^ 2 by
            positivity) ?_
        norm_num
        exact ⟨a, by simp_all +decide⟩
      · simp_all +decide [Finset.sum_ite]
        refine le_trans ?_
          (Finset.single_le_sum
            (fun x _ => by
              exact mul_nonneg (Nat.cast_nonneg _) (by positivity))
            (Finset.mem_univ a))
        refine le_mul_of_one_le_left
          (show 0 ≤ (4 : ℝ) * ((T.filter (fun u => Hc.Adj u a)).card : ℝ) ^ 2 by
            positivity) ?_
        norm_num
        exact ⟨b, by simp_all +decide⟩
      · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    refine le_trans (Finset.sum_le_sum fun e _ => h_point e) ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun v hv => ?_
    simp +decide [Finset.sum_ite]
    refine mul_le_of_le_one_left (by positivity) ?_
    norm_num
    refine mod_cast Finset.card_le_one.mpr ?_
    intro e he f hf
    rcases e with ⟨⟨a, b⟩, hab⟩
    rcases f with ⟨⟨c, d⟩, hcd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rcases hf with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exfalso; exact (not_lt_of_ge hcd.le) hab
    · exfalso; exact (not_lt_of_ge hcd.le) hab
    · rfl
  simpa [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h_sum_bound

/-! ### Iterative pruning infrastructure -/

/-
**Core pruning step**: given T ⊆ B' independent with a problematic
    vertex v (has ≥ τ neighbors in T but T ⊄ N_Hc(v)), replacing T by
    T ∩ N_Hc(v) preserves subset, independence, degree bound, and |T| ≥ τ.
-/
lemma pruning_step_props {n : ℕ} (Hc : SimpleGraph (Fin n))
    (B' T : Finset (Fin n)) (v : Fin n) (τ : ℕ)
    (hTB : T ⊆ B') (hv_not : v ∉ T)
    (hv_card : (T.filter (fun u => Hc.Adj u v)).card ≥ τ)
    (hv_notall : ¬∀ u ∈ T, Hc.Adj u v) :
    let T' := T.filter (fun u => Hc.Adj u v)
    T' ⊆ B' ∧ T' ⊂ T ∧ T'.card ≥ τ := by
  grind

/-
**Iterative pruning with fixed threshold**.
    Given B' independent with vertex degrees ≤ 4C, and a threshold τ ≤ |B'|,
    there exists T ⊆ B' with |T| ≥ τ and controlled neighborhoods.
-/
lemma iterative_pruning_fixed_threshold {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (B' : Finset (Fin n))
    (_hB'_indep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (_hB'_deg : ∀ v ∈ B', Hc.degree v ≤ 4 * C)
    (τ : ℕ) (_hτ : τ ≥ 2) (hτ_le : τ ≤ B'.card) :
    ∃ T : Finset (Fin n),
    T ⊆ B' ∧ T.card ≥ τ ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < τ) := by
  -- We proceed by strong induction on the size of the candidate subset of B'.
  have h_ind : ∀ S ⊆ B', τ ≤ S.card → ∃ T ⊆ S, τ ≤ T.card ∧ ∀ w ∉ T, (∀ v ∈ T, Hc.Adj v w) ∨ (T.filter (fun v => Hc.Adj v w)).card < τ := by
    intro S hS_sub hS_card
    induction S using Finset.strongInduction with
    | H S ih =>
      by_cases hS_prop : ∀ w ∉ S, (∀ v ∈ S, Hc.Adj v w) ∨ (S.filter (fun v => Hc.Adj v w)).card < τ;
      · exact ⟨ S, Finset.Subset.refl _, hS_card, hS_prop ⟩;
      · grind;
  exact h_ind B' Finset.Subset.rfl hτ_le

/-! ### Claim 2.4: Iterative pruning -/

/-
**Claim 2.4 (Iterative pruning)**.
    Given B' independent in Hc with |B'| ≥ n/(8C+2) and vertex degrees ≤ 4C,
    there exists T ⊆ B' with |T| ≥ 2 and controlled neighborhoods:
    for every w ∉ T, either T ⊆ N_Hc(w) or |N_Hc(w) ∩ T| < threshold.
    The output satisfies (|T|-1)² / threshold ≥ const · n · log n.

    The algorithm iterates: if ∃ v ∉ T with |N_Hc(v) ∩ T| ≥ threshold_i and
    T ⊄ N_Hc(v), replace T ← T ∩ N_Hc(v). This terminates in ≤ 4C steps
    because the selected v's become common neighbors of the final T ⊆ B',
    and vertices in B' have degree ≤ 4C.

The proof requires the iterative pruning with the "4C+1 common neighbors"
    argument (proof by contradiction): under the assumption that no good
    (T, threshold) pair exists, we iteratively prune B' to produce 4C+1
    distinct common neighbors outside B', contradicting the degree bound 4C.
    The key analytical fact is that after each pruning step, |T| stays
    large enough (because n is large enough depending on C) to continue.

C = 0 case of claim_2_4_pruning: K = 0, so ratio ≥ 0 is trivial.
-/
private lemma claim_2_4_pruning_zero :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ 0 * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * 0) →
    B'.card ≥ n / (8 * 0 + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * 0 + 4) * 0 * (↑n * Real.log ↑n) := by
  refine ⟨4, ?_⟩
  intro n hn Hc hHc B' hInd hDeg hBcard
  have hcard2 : 2 ≤ B'.card := by
    have hn2 : 2 ≤ n / 2 := by omega
    omega
  refine ⟨B', 1, subset_rfl, hcard2, ?_, ?_, ?_⟩
  · intro w hw
    refine Or.inr ?_
    rw [Nat.lt_one_iff]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hxB hxAdj
    have hpos : 0 < Hc.degree x := hxAdj.degree_pos_left
    have hzero : Hc.degree x = 0 := by
      have := hDeg x hxB
      omega
    omega
  · have hcard_real : (1 : ℝ) < B'.card := by exact_mod_cast hcard2
    linarith
  · simpa using sq_nonneg ((B'.card : ℝ) - 1)

/-- C ≥ 1 case of claim_2_4_pruning: the main iterative pruning chain. -/
private lemma claim_2_4_pruning_pos (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) :=
  claim_2_4_pruning_pos_result C hC

lemma claim_2_4_pruning (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) := by
  -- The proof follows the iterative pruning from the paper.
  -- For C = 0: K = 0, so RHS = 0. Use T = B', threshold = B'.card.
  -- For C ≥ 1: use the paper's multi-level pruning chain.
  rcases Nat.eq_zero_or_pos C with rfl | hC_pos
  · -- C = 0: RHS = 0, use T = B', threshold = B'.card
    convert claim_2_4_pruning_zero using 6; all_goals simp
  · -- C ≥ 1: the main case
    exact claim_2_4_pruning_pos C (by omega)

/-! ### Sum of squares with tight bound and pruning -/

/-
Sum of squares of switchBoundTight, restricted to controlled neighborhoods.
    After pruning: for w ∉ T with dT(w) < threshold, the contribution is bounded.
    For w with T ⊆ N_Hc(w), switchBoundTight gives 0 for all edge slots involving w.
-/
-- The generated tight switch-count bound needs extra heartbeats for pruning cases.
set_option maxHeartbeats 3200000 in
lemma switchCount_sum_sq_tight {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (threshold : ℕ)
    (hcontrol : ∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) :
    ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤
    (16 : ℝ) * C * ↑(T.card) ^ 2 * ↑threshold := by
  have h_sum_bound : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w ∉ T, (T.card - (T.filter (fun v => Hc.Adj v w)).card) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) ^ 2 := by
    have h_sum_bound : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w∉T, ∑ v ∈ T, (if Hc.Adj v w then 0 else 4 * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2) := by
      have h_sum_bound : ∀ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w∉T, ∑ v ∈ T, (if e.val.1 = v ∧ e.val.2 = w ∨ e.val.1 = w ∧ e.val.2 = v then (if Hc.Adj v w then 0 else 4 * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2) else 0) := by
        intro e
        simp [switchBoundTight];
        split_ifs <;> norm_num [ mul_pow ];
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
        · rw [ Finset.sum_eq_single ( e.val.2 ) ] <;> simp_all +decide [ Finset.sum_ite ];
          · exact le_mul_of_one_le_left ( by positivity ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ by tauto, by tauto ⟩, by tauto ⟩ ⟩ );
          · grind +ring;
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
        · rw [ Finset.sum_eq_single ( e.val.1 ) ] <;> simp_all +decide [ Finset.sum_ite ];
          · exact le_mul_of_one_le_left ( by positivity ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ by tauto, by tauto ⟩, by tauto ⟩ ⟩ );
          · grind;
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
      refine le_trans ( Finset.sum_le_sum fun e _ => h_sum_bound e ) ?_;
      rw [ Finset.sum_comm ];
      refine Finset.sum_le_sum fun w hw => ?_;
      rw [ Finset.sum_comm ];
      refine Finset.sum_le_sum fun v hv => ?_;
      split_ifs <;> simp_all +decide [ Finset.sum_ite ];
      refine mul_le_of_le_one_left ( by positivity ) ?_;
      refine mod_cast Finset.card_le_one.mpr ?_;
      intro e he f hf
      rcases e with ⟨⟨a, b⟩, hab⟩
      rcases f with ⟨⟨c, d⟩, hcd⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
      rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        rcases hf with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exfalso; exact (not_lt_of_ge hcd.le) hab
      · exfalso; exact (not_lt_of_ge hcd.le) hab
      · rfl
    simp_all +decide [ Finset.sum_ite, mul_assoc ];
    refine le_trans h_sum_bound ?_;
    gcongr;
    rw [ le_sub_iff_add_le ] ; norm_cast ; rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr <| by aesop ) ] ; exact Finset.card_mono <| by aesop_cat;
  have h_sum_bound : ∑ w ∉ T, (T.card - (T.filter (fun v => Hc.Adj v w)).card) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) ^ 2 ≤ ∑ w ∉ T, (T.card : ℝ) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) * threshold := by
    refine Finset.sum_le_sum fun w hw => ?_;
    rcases hcontrol w (by aesop) with h_all | h_lt
    · simp_all +decide [mul_assoc]
      positivity
    · simp_all +decide [mul_assoc]
      nlinarith only [ show ( Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) : ℝ ) ≤ threshold by exact_mod_cast le_of_lt h_lt, show ( Finset.card T : ℝ ) ≥ 0 by positivity, show ( Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) : ℝ ) ^ 2 ≤ threshold * Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) by exact_mod_cast by nlinarith only [ h_lt ] ];
  have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card ≤ ∑ v ∈ T, Hc.degree v := by
    have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card = ∑ v ∈ T, ∑ w ∉ T, (if Hc.Adj v w then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    rw [h_sum_bound]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← Finset.card_filter]
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    exact Finset.card_mono fun y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      simpa [SimpleGraph.mem_neighborSet] using hy.2
  have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card ≤ 4 * C * T.card := by
    exact h_sum_bound.trans ( by simpa [ mul_comm ] using Finset.sum_le_sum hT_deg );
  refine le_trans ‹_› <| le_trans ‹_› ?_;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  exact mul_le_mul_of_nonneg_right ( by norm_cast; nlinarith ) ( Nat.cast_nonneg _ )

/-! ### Graph↔Bool transfer for Azuma -/

/-
Transfer lemma: apply azuma_for_zero_count through graphEquiv.
    Given bounds b on switchCount through graphDecode and sufficient
    Azuma exponent, derive the zero-count bound for SimpleGraph.
-/
lemma azuma_for_switchCount_zero {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (b : EdgeSlot n → ℝ)
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hC8 : 8 * C ≤ n.choose 2)
    (hT_card : T.card ≥ 2)
    (hbd : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool,
      (∀ e', e' ≠ e → x e' = y e') →
      |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode y)| ≤ b e)
    (hb_nonneg : ∀ e, 0 ≤ b e)
    (hb_pos : 0 < ∑ e : EdgeSlot n, (b e) ^ 2)
    (hexp : ↑n * Real.log ↑n ≤
      2 * ((∑ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x)) /
           (2 ^ Fintype.card (EdgeSlot n) : ℝ)) ^ 2 /
      (∑ e : EdgeSlot n, (b e) ^ 2)) :
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  have := @azuma_for_zero_count;
  contrapose! this;
  refine ⟨ Fintype.card ( EdgeSlot n ),
    fun x => switchCount Hc T ( graphDecode ( fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) ),
    fun i => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm i ), ?_, ?_, ?_, ?_ ⟩;
  · exact fun x => switchCount_nonneg _ _ _;
  · intro i x y hxy; specialize hbd ( Fintype.equivFin ( EdgeSlot n ) |>.symm i ) ( fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) ( fun e => y ( Fintype.equivFin ( EdgeSlot n ) e ) ) ; aesop;
  · exact fun i => hb_nonneg _;
  · refine ⟨ ?_, n * Real.log n, ?_, ?_, ?_ ⟩;
    · convert hb_pos using 1;
      conv_rhs => rw [ ← Equiv.sum_comp ( Fintype.equivFin ( EdgeSlot n ) |> Equiv.symm ) ] ;
    · positivity;
    · convert hexp using 1;
      refine congrArg₂ _ ( congrArg₂ _ rfl ( congrArg₂ _ ( congr_arg ( fun x : ℝ => x / _ ) ( Finset.sum_bij ( fun x _ => fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) ?_ ?_ ?_ ?_ ) ) rfl ) ) ( Finset.sum_bij ( fun x _ => ( Fintype.equivFin ( EdgeSlot n ) ).symm x ) ?_ ?_ ?_ ?_ ) <;> simp +decide;
      · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( Fintype.equivFin ( EdgeSlot n ) |>.symm x ) ;
      · exact fun b => ⟨ fun e => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm e ), by ext; simp +decide ⟩;
      · exact fun e => ⟨ _, Equiv.apply_symm_apply _ _ ⟩;
    · convert this using 1;
      · rw [ card_edgeSlot ];
      · convert rfl;
        convert graphEquiv_card_filter _;
        refine Finset.card_bij ( fun x hx => fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) ?_ ?_ ?_ <;> simp +decide;
        · exact fun a₁ ha₁ a₂ ha₂ h => funext fun i => by simpa using congr_fun h ( Fintype.equivFin ( EdgeSlot n ) |>.symm i ) ;
        · exact fun b hb => ⟨ fun e => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm e ), by simpa using hb, by ext; simp +decide ⟩

/-! ### Azuma exponent calculation -/

/-
The Azuma exponent is sufficient: given the mean lower bound and sum-of-squares
    upper bound and the ratio from claim 2.4, we have 2μ²/Σb² ≥ n·log n.
-/
-- The generated Azuma exponent proof needs extra heartbeats for nonlinear estimates.
set_option maxHeartbeats 6400000 in
lemma azuma_exponent_sufficient {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (threshold : ℕ)
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hC8 : 8 * C ≤ n.choose 2)
    (hT_card : T.card ≥ 2)
    (hT_control : ∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold)
    (hT_pos : (T.card : ℝ) - 1 > 0)
    (hT_ratio : ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n))
    (h_sum_pos : 0 < ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2) :
    ↑n * Real.log ↑n ≤
    2 * ((∑ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x)) /
         (2 ^ Fintype.card (EdgeSlot n) : ℝ)) ^ 2 /
    (∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2) := by
  -- By combining the results from the mean switch count lower bound and the sum of squares upper bound, we can derive the required inequality for the Azuma exponent.
  have h_combined : 2 * ((T.offDiag.card : ℝ) * (2 : ℝ) ^ (n.choose 2 - 8 * C)) ^ 2 / (2 ^ n.choose 2) ^ 2 / (16 * C * (T.card : ℝ) ^ 2 * threshold) ≥ n * Real.log n := by
    rw [ div_div, ge_iff_le, le_div_iff₀ ];
    · rcases eq_or_ne threshold 0 <;> simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ];
      rw [ Nat.cast_sub ( by nlinarith ) ] ; push_cast ; ring_nf at *;
      rw [ show n.choose 2 * 2 = ( n.choose 2 - C * 8 ) * 2 + C * 16 by linarith [ Nat.sub_add_cancel hC8 ] ] ; norm_num [ pow_add, pow_mul ] ; ring_nf at *;
      field_simp at *;
      nlinarith [ show ( T.card : ℝ ) ≥ 2 by norm_cast ];
    · cases eq_or_ne C 0 <;> cases eq_or_ne threshold 0 <;> simp_all +decide;
      · contrapose! h_sum_pos; simp_all +decide [ switchBoundTight ] ;
      · unfold switchBoundTight at h_sum_pos ; simp_all +decide;
        contrapose! h_sum_pos
        refine Finset.sum_nonpos fun x hx => ?_
        by_cases hleft : x.val.1 ∈ T ∧ x.val.2 ∉ T
        · by_cases hadj : Hc.Adj x.val.1 x.val.2
          · simp [hleft, hadj]
          · have hfilter : (T.filter (fun v => Hc.Adj v x.val.2)).card = 0 := by
              refine Finset.card_eq_zero.mpr ?_
              exact Finset.filter_eq_empty_iff.mpr fun v hvT hvAdj => by
                have hzero := hT_deg v hvT
                have hpos : 0 < Hc.degree v := hvAdj.degree_pos_left
                omega
            simp [hleft, hadj, hfilter]
        · by_cases hright : x.val.2 ∈ T ∧ x.val.1 ∉ T
          · by_cases hadj : Hc.Adj x.val.2 x.val.1
            · simp [hleft, hright, hadj]
            · have hfilter : (T.filter (fun v => Hc.Adj v x.val.1)).card = 0 := by
                refine Finset.card_eq_zero.mpr ?_
                exact Finset.filter_eq_empty_iff.mpr fun v hvT hvAdj => by
                  have hzero := hT_deg v hvT
                  have hpos : 0 < Hc.degree v := hvAdj.degree_pos_left
                  omega
              simp [hleft, hright, hadj, hfilter]
          · simp [hleft, hright]
      · contrapose! hT_ratio;
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        · contradiction;
        · contradiction;
        · exact mul_pos ( mul_pos ( by positivity ) ( by positivity ) ) ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) );
      · positivity;
  -- Substitute the bounds from mean_switchCount_lower and switchCount_sum_sq_tight into the expression.
  have h_subst : 2 * ((∑ G : SimpleGraph (Fin n), switchCount Hc T G) / (2 ^ n.choose 2 : ℝ)) ^ 2 / (16 * C * (T.card : ℝ) ^ 2 * threshold) ≥ n * Real.log n := by
    refine le_trans h_combined ?_;
    rw [ div_pow, mul_div_assoc' ];
    gcongr;
    convert mean_switchCount_lower Hc C T hT_indep hT_deg hC8 using 1;
  refine le_trans ?_ ( h_subst.trans ?_ );
  · norm_num;
  · rw [ show ( ∑ x : SimpleGraph ( Fin n ), switchCount Hc T x ) = ( ∑ x : EdgeSlot n → Bool, switchCount Hc T ( graphDecode x ) ) from ?_ ];
    · rw [ card_edgeSlot ];
      gcongr;
      convert switchCount_sum_sq_tight C Hc T hT_indep hT_deg threshold hT_control using 1;
    · apply Finset.sum_bij (fun G _ => graphEncode G);
      · simp;
      · exact fun G₁ _ G₂ _ h => by simpa using graphEquiv n |>.injective h;
      · exact fun b _ => ⟨ graphDecode b, Finset.mem_univ _, graphEquiv n |>.right_inv b ⟩;
      · exact fun G _ => congr_arg ( fun f => switchCount Hc T f ) ( graphEquiv n |>.left_inv G ) ▸ rfl

/-! ### Assembly: switchCount_zero_bound -/

-- The generated switch-count zero bound needs extra heartbeats for final assembly.
set_option maxHeartbeats 6400000 in
/-- **Azuma bound for switchCount = 0**.
    Combines Claim 2.4 pruning, tight bounded differences, and
    Azuma-Hoeffding to show: for large n, for Hc with ≤ Cn edges,
    ∃ T such that #{switchCount = 0} ≤ 2^N · exp(-n log n). -/
lemma switchCount_zero_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∃ T : Finset (Fin n),
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  -- Get n₀ from claim_2_4_pruning
  obtain ⟨n₁, hn₁⟩ := claim_2_4_pruning C
  use max (max n₁ 2) (8 * C + 3)
  intro n hn Hc hCn
  have hn2 : n ≥ 2 := le_trans (le_max_of_le_left (le_max_right _ _)) hn
  have hn1 : n ≥ n₁ := le_trans (le_max_of_le_left (le_max_left _ _)) hn
  -- Get independent set B'
  obtain ⟨B', hB'_indep, hB'_deg, hB'_card, _⟩ := find_good_independent_set C Hc hCn hn2
  -- Apply pruning
  obtain ⟨T, threshold, hTB, hT_card, hT_control, hT_pos, hT_ratio⟩ :=
    hn₁ n hn1 Hc hCn B' hB'_indep hB'_deg hB'_card
  -- T inherits properties from B'
  have hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v :=
    fun u hu v hv huv => hB'_indep u (hTB hu) v (hTB hv) huv
  have hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C :=
    fun v hv => hB'_deg v (hTB hv)
  have hC8 : 8 * C ≤ n.choose 2 := by
    have hnn : n ≥ 8 * C + 3 := le_trans (le_max_right _ _) hn
    rw [Nat.choose_two_right]
    have h1 : n ≥ 1 := by linarith
    have h2 : n - 1 ≥ 8 * C + 2 := by omega
    have : n * (n - 1) ≥ (8 * C + 3) * (8 * C + 2) :=
      Nat.mul_le_mul hnn h2
    have : (8 * C + 3) * (8 * C + 2) ≥ 16 * C := by nlinarith
    omega
  -- Case split on whether switchBoundTight sum is positive
  by_cases h_sum_pos : 0 < ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2
  · -- Case B: Σb² > 0, apply Azuma
    use T
    apply azuma_for_switchCount_zero C Hc T (fun e => switchBoundTight Hc T e)
      hT_indep hT_deg hC8 hT_card
    · -- bounded differences
      exact fun e x y hxy => switchCount_bounded_diff_tight Hc T hT_indep e x y hxy
    · -- b nonneg
      exact fun e => switchBoundTight_nonneg Hc T e
    · -- Σb² > 0
      exact h_sum_pos
    · -- Azuma exponent sufficient
      exact azuma_exponent_sufficient C Hc T threshold hT_indep hT_deg hC8 hT_card
        hT_control hT_pos hT_ratio h_sum_pos
  · -- Case A: Σb² = 0, switchCount is constant
    push Not at h_sum_pos
    have h_sum_zero : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 = 0 :=
      le_antisymm h_sum_pos (Finset.sum_nonneg fun e _ => sq_nonneg _)
    -- All switchBoundTight are 0
    have hb_zero : ∀ e : EdgeSlot n, switchBoundTight Hc T e = 0 := by
      intro e
      have := Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (switchBoundTight Hc T e))
        |>.mp h_sum_zero e (Finset.mem_univ _)
      exact sq_eq_zero_iff.mp this
    -- switchCount is constant
    have hconst : ∀ x y : EdgeSlot n → Bool,
        switchCount Hc T (graphDecode x) = switchCount Hc T (graphDecode y) := by
      intros x y
      have h_diff_zero : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool, (∀ e', e' ≠ e → x e' = y e') → |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode y)| ≤ switchBoundTight Hc T e := by
        exact fun e x y a ↦ switchCount_bounded_diff_tight Hc T hT_indep e x y a;
      induction hs : Finset.univ.filter (fun e => x e ≠ y e) using Finset.induction generalizing x y with
      | empty =>
        simp_all +decide [ Finset.ext_iff ];
        have hxy : x = y := by
          funext e
          by_contra hne
          have : e ∈ Finset.univ.filter (fun e => x e ≠ y e) := by simp [hne]
          simp_all
        rw [ hxy ];
      | insert e s hnot ih =>
        have h_diff_zero : |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode (fun e' => if e' = e then y e else x e'))| ≤ switchBoundTight Hc T e := by
          grind;
        specialize ih ( fun e' => if e' = e then y e else x e' ) y ; simp_all +decide [ Finset.ext_iff ];
        grind +ring
    -- The constant must be > 0 (from mean_switchCount_lower)
    have hmean_pos : ∑ G : SimpleGraph (Fin n), switchCount Hc T G > 0 := by
      have hmean := mean_switchCount_lower Hc C T hT_indep hT_deg hC8
      have hoff : (T.offDiag.card : ℝ) > 0 := by
        have : T.offDiag.card > 0 := by
          have : T.card ≥ 2 := hT_card
          simp [Finset.offDiag_card]; omega
        exact Nat.cast_pos.mpr this
      have hpow : (0:ℝ) < 2 ^ (n.choose 2 - 8 * C) := by positivity
      calc (∑ G : SimpleGraph (Fin n), switchCount Hc T G)
          ≥ (T.offDiag.card : ℝ) * 2 ^ (n.choose 2 - 8 * C) := hmean
        _ > 0 := mul_pos hoff hpow
    -- So switchCount > 0 for all G, hence #{switchCount = 0} = 0
    use T
    -- switchCount is constant on SimpleGraph too
    have hconst' : ∀ G₁ G₂ : SimpleGraph (Fin n), switchCount Hc T G₁ = switchCount Hc T G₂ := by
      intro G₁ G₂
      have := hconst (graphEncode G₁) (graphEncode G₂)
      have h1 : graphDecode (graphEncode G₁) = G₁ := (graphEquiv n).left_inv G₁
      have h2 : graphDecode (graphEncode G₂) = G₂ := (graphEquiv n).left_inv G₂
      rw [h1, h2] at this; exact this
    -- All switchCount values equal some constant c > 0
    have hne : switchCount Hc T ⊥ > 0 := by
      by_contra h
      push Not at h
      have h0 : switchCount Hc T ⊥ = 0 := le_antisymm h (switchCount_nonneg _ _ _)
      have : ∀ G, switchCount Hc T G = 0 := fun G => by rw [hconst' G ⊥, h0]
      have : ∑ G : SimpleGraph (Fin n), switchCount Hc T G = 0 :=
        Finset.sum_eq_zero fun G _ => this G
      linarith
    have : (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        switchCount Hc T G = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro G _; exact ne_of_gt (hconst' G ⊥ ▸ hne)
    simp [this]; positivity

lemma per_perm_switch_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  obtain ⟨n₀, hn₀⟩ := switchCount_zero_bound C
  exact ⟨n₀, fun n hn Hc hCn => by
    obtain ⟨T, hT⟩ := hn₀ n hn Hc hCn
    exact le_trans (by exact_mod_cast Finset.card_le_card (no_switch_subset_switchCount_zero Hc T)) hT⟩

lemma complement_switch_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    H.edgeFinset.card + C * n ≥ n.choose 2 →
    probUniqueEmb H ≤ (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) := by
  have := @per_perm_switch_bound C;
  obtain ⟨ n₀, hn₀ ⟩ := this; use n₀ + 2; intros n hn H hH; rw [ probUniqueEmb ] ; specialize hn₀ n ( by linarith ) ( Hᶜ ) ; simp_all +decide;
  have h_card : (numUniquelyEmbedding H : ℝ) ≤ (n.factorial : ℝ) * (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, ¬u = v → ¬IsIdSwitch Hᶜ G u v)).card := by
    convert complement_unique_le_factorial_mul_no_switch Hᶜ using 1;
    rw [ complement_duality ] ; norm_cast;
  rw [ div_le_iff₀ ( by positivity ) ];
  convert h_card.trans ( mul_le_mul_of_nonneg_left ( hn₀ _ ) ( Nat.cast_nonneg _ ) ) using 1
  · ring
  have h_card : H.edgeFinset.card + Hᶜ.edgeFinset.card = n.choose 2 := by
    have h_card : H.edgeFinset ∪ Hᶜ.edgeFinset = Finset.univ.filter (fun e => e ∈ SimpleGraph.edgeFinset (⊤ : SimpleGraph (Fin n))) := by
      ext e; simp [SimpleGraph.edgeFinset];
      rcases e with ⟨ u, v ⟩ ; by_cases hu : u = v <;> simp +decide [ hu ] ; tauto;
    rw [ ← Finset.card_union_of_disjoint, h_card ];
    · simp +decide [ SimpleGraph.edgeFinset ];
      rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ Finset.card_univ, Sym2.card ];
      rw [ show ( Finset.univ.filter fun x : Sym2 ( Fin n ) => x.IsDiag ) = Finset.image ( fun x : Fin n => Sym2.mk x x ) Finset.univ from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · exact Nat.sub_eq_of_eq_add <| by induction n <;> simp +decide [ Nat.choose ] at * ; linarith;
      · ext ⟨ x, y ⟩ ; aesop;
    · simp +decide [ Finset.disjoint_left ];
      rintro ⟨ u, v ⟩ huv; simp_all +decide [ SimpleGraph.compl_adj ] ;
  grind

/-! ### Derivation of dense_case -/

/-- **Lemma 2.3** (Very dense H implies few unique embeddings).
    Derived from `complement_switch_bound` and `factorial_exp_tendsto_zero`. -/
theorem dense_case :
    ∀ C : ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    H.edgeFinset.card + C * n ≥ n.choose 2 →
    probUniqueEmb H < ε := by
  intro C ε hε
  obtain ⟨n₁, hn₁⟩ := complement_switch_bound C
  obtain ⟨n₂, hn₂⟩ := factorial_exp_tendsto_zero ε hε
  use max n₁ n₂
  intro n hn H hH
  exact lt_of_le_of_lt (hn₁ n (le_of_max_le_left hn) H hH) (hn₂ n (le_of_max_le_right hn))

/-! ## Main Theorem -/

/-- **Theorem 1.2** (Main Theorem — Unique subgraphs are rare).
    Proof: Suppose probUniqueEmb H ≥ ε. By Lemma 2.2, H must be very dense.
    But by Lemma 2.3, very dense graphs have probUniqueEmb < ε. Contradiction. -/
theorem unique_embeddings_vanish :
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H < ε := by
  intro ε hε
  obtain ⟨C, hC⟩ := reduction_to_dense ε hε
  obtain ⟨n₀, hn₀⟩ := dense_case C ε hε
  exact ⟨n₀, fun n hn H => by
    by_contra h
    push Not at h
    exact absurd (hn₀ n hn H (hC n H h)) (not_lt.mpr h)⟩

/-- The main theorem stated in terms of f(H). -/
theorem main_theorem :
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    fH H < ε := by
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := reduction_to_random ε hε
  have hε2 : ε / 2 > 0 := half_pos hε
  obtain ⟨n₂, hn₂⟩ := unique_embeddings_vanish (ε / 2) hε2
  exact ⟨max n₁ n₂, fun n hn H => by
    by_contra h
    push Not at h
    have h1 : n ≥ n₁ := le_of_max_le_left hn
    have h2 : n ≥ n₂ := le_of_max_le_right hn
    have := hn₁ n h1 H h
    exact absurd (hn₂ n h2 H) (not_lt.mpr this)⟩

/-! ## Corollary: f(n) → 0 -/

/-- f(n) → 0 as n → ∞. -/
theorem f_tendsto_zero : Filter.Tendsto fSeq Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := main_theorem ε hε
  exact ⟨n₀, fun n hn => by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (fSeq_nonneg n)]
    unfold fSeq
    rw [Finset.sup'_lt_iff]
    exact fun H _ => hn₀ n hn H⟩

#print axioms f_tendsto_zero
-- 'Erdos426.UniqueSubgraphs.f_tendsto_zero' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end UniqueSubgraphs

end

end Erdos426
