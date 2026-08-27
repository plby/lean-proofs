import Arxiv.Arxiv2411_18291.VariableFirstElimination
import Arxiv.Arxiv2411_18291.EliminationMultiplicity

/-!
# The pairs for further elimination

Index the second stage by the bad negative cliques of the first stage.
Their positive far partners are constructed from the proved uniqueness
statement. Shared negative-root edges lie in those positive partners,
which is precisely the criterion that removes all remaining overlaps.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N : Block U q} {e₀ : Block U (r + 1)}

structure VariableFurtherEliminationPairs (F : VariableSplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ') where
  positive : E.badNegative → Block V q
  edge : E.badNegative → Block V (r + 1)
  positive_mem : ∀ i, positive i ∈ F.positiveFar
  old_inter : ∀ i, cliqueEdges (r + 1) i.val ∩ F.graph = {edge i}
  edge_positive : ∀ i, edge i ∈ cliqueEdges (r + 1) (positive i)
  vertex_inter : ∀ i, (positive i).val ∩ i.val.val = (edge i).val
  positive_unique : ∀ i, ∀ Q ∈ F.positiveCliques,
    edge i ∈ cliqueEdges (r + 1) Q → Q = positive i

theorem exists_variable_further_elimination_pairs (F : VariableSplittingFamily S D B C θ)
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) : Nonempty (VariableFurtherEliminationPairs F E) := by
  have h (i : E.badNegative) := variable_first_bad_negative_partner F hA₀ E hpair i.property
  choose e Q hQ hOld heQ hInt hUniq using h
  refine ⟨⟨Q, e, hQ, hOld, heQ, ?_, hUniq⟩⟩
  intro i
  simpa only [inter_comm] using hInt i

variable {F : VariableSplittingFamily S D B C θ}
variable {E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ'}

theorem VariableFurtherEliminationPairs.pair_injective (L : VariableFurtherEliminationPairs F E) :
    Function.Injective fun i : E.badNegative => (L.positive i, i.val) := by
  intro i j h
  exact Subtype.ext (congrArg Prod.snd h)

theorem VariableFurtherEliminationPairs.positive_mem_cliques
    (L : VariableFurtherEliminationPairs F E)
    (i : E.badNegative) : L.positive i ∈ F.cliques := by
  rw [F.cliques_eq_signs]
  exact mem_union_left _ (mem_sdiff.mp (L.positive_mem i)).1

theorem VariableFurtherEliminationPairs.root_inter_splitting
    (L : VariableFurtherEliminationPairs F E)
    (i : E.badNegative) :
    cliqueEdges (r + 1) i.val ∩ F.graph ⊆ cliqueEdges (r + 1) (L.positive i) := by
  rw [L.old_inter i]
  exact singleton_subset_iff.mpr (L.edge_positive i)

theorem VariableFurtherEliminationPairs.root_overlap_cover (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N e₀) (i j : E.badNegative) (hij : i ≠ j) :
    cliqueEdges (r + 1) i.val ∩ cliqueEdges (r + 1) j.val ⊆
      cliqueEdges (r + 1) (L.positive i) := by
  intro e he
  have heOld := E.negative_inter_subset_original hpair (mem_sdiff.mp i.property).1
    (mem_sdiff.mp j.property).1 (fun h => hij (Subtype.ext h)) he
  exact L.root_inter_splitting i (mem_inter.mpr ⟨(mem_inter.mp he).1, heOld⟩)

def variableRetainedNegative (F : VariableSplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ') : Finset (Block V q) :=
  F.negativeFar ∪ E.goodNegative

theorem variableRetainedNegative_support (F : VariableSplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) :
    cliqueSupport (r + 1) (variableRetainedNegative F E) ⊆ E.graph := by
  intro e he
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
  rcases mem_union.mp hR with hf | he
  · have hF : R ∈ F.cliques := by
      rw [F.cliques_eq_signs]
      exact mem_union_right _ (mem_sdiff.mp hf).1
    exact mem_union_left _ (F.cliques_support (mem_biUnion.mpr ⟨R, hF, heR⟩))
  · have hE : R ∈ E.cliques := by
      rw [E.cliques_eq_signs]
      exact mem_union_right _ (mem_filter.mp he).1
    exact E.cliques_support hpair (mem_biUnion.mpr ⟨R, hE, heR⟩)

theorem VariableFurtherEliminationPairs.root_inter_retained
    (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N e₀) (i : E.badNegative) :
    cliqueEdges (r + 1) i.val ∩ cliqueSupport (r + 1) (variableRetainedNegative F E) ⊆
      cliqueEdges (r + 1) (L.positive i) := by
  intro e he
  obtain ⟨heI, heOld⟩ := mem_inter.mp he
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp heOld
  rcases mem_union.mp hR with hf | hg
  · have hF : R ∈ F.cliques := by
      rw [F.cliques_eq_signs]
      exact mem_union_right _ (mem_sdiff.mp hf).1
    exact L.root_inter_splitting i (mem_inter.mpr
      ⟨heI, F.cliques_support (mem_biUnion.mpr ⟨R, hF, heR⟩)⟩)
  · have hneq : R ≠ i.val := by
      intro h
      exact (mem_sdiff.mp i.property).2 (h ▸ hg)
    exact (disjoint_left.mp (E.goodNegative_disjoint hpair hg
      (mem_sdiff.mp i.property).1 hneq) heR heI).elim

end Arxiv2411_18291
