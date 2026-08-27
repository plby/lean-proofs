import Arxiv.Arxiv2411_18291.VariableSplittingPartners
import Arxiv.Arxiv2411_18291.FarPartnerIntersections

/-!
# A positive far clique has only one near edge

Positive frame locality places every intersection with the near family
inside one distinguished negative clique. The opposite-clique intersection
bound then leaves at most one edge. This property survives the separated
splitting placements and prevents reusing a far partner in cancellation.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {C : Block V q → ℕ}

variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

theorem VariableSplittingFamily.positiveFar_near_edges_unique
    (F : VariableSplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    {P N M : Block V q} (hP : P ∈ F.positiveFar)
    (hN : N ∈ F.negativeNear) (hM : M ∈ F.negativeNear) {e f : Block V (r + 1)}
    (heP : e ∈ cliqueEdges (r + 1) P) (heN : e ∈ cliqueEdges (r + 1) N)
    (hfP : f ∈ cliqueEdges (r + 1) P) (hfM : f ∈ cliqueEdges (r + 1) M) : e = f := by
  obtain ⟨s, N₀, hN₀, hs, hNs⟩ := F.negativeNear_source hN
  obtain ⟨t, M₀, hM₀, _, hMt⟩ := F.negativeNear_source hM
  obtain ⟨u, _, hPu⟩ := mem_biUnion.mp (mem_sdiff.mp hP).1
  have heB : e ∉ B := fun h => disjoint_left.mp (F.positiveFar_disjoint_original hP) heP h
  have hfB : f ∉ B := fun h => disjoint_left.mp (F.positiveFar_disjoint_original hP) hfP h
  have hPg : cliqueEdges (r + 1) P ⊆ mapGraph (F.embedding u) S.graph :=
    (S.map (F.embedding u)).replacement_clique_subset
      ((S.map (F.embedding u)).positiveReplacement_subset _ hPu)
  have hNg : cliqueEdges (r + 1) N ⊆ mapGraph (F.embedding s) S.graph := by
    rw [← hNs, ← map_cliqueEdges]
    exact mapGraph_mono _ (S.negative_decomposition.clique_subset (S.near_negative hN₀))
  have hMg : cliqueEdges (r + 1) M ⊆ mapGraph (F.embedding t) S.graph := by
    rw [← hMt, ← map_cliqueEdges]
    exact mapGraph_mono _ (S.negative_decomposition.clique_subset (S.near_negative hM₀))
  have hus := F.copy_index_unique (hPg heP) (hNg heN) heB
  have hut := F.copy_index_unique (hPg hfP) (hMg hfM) hfB
  subst u
  subst t
  rw [S.positiveReplacement_map] at hPu
  obtain ⟨P₀, hP₀, hPs⟩ := (mem_mapGraph _ _ _).mp hPu
  have hP₀' : P₀ ∈ S.positive.erase S.base := by
    simpa only [ExchangeSystem.positiveReplacement, hs, Bool.false_eq_true, if_false] using hP₀
  rw [← hNs, ← map_cliqueEdges] at heN
  obtain ⟨e₀, heN₀, hes⟩ := (mem_mapGraph _ _ _).mp heN
  rw [← hMt, ← map_cliqueEdges] at hfM
  obtain ⟨f₀, hfM₀, hfs⟩ := (mem_mapGraph _ _ _).mp hfM
  have heP₀ : e₀ ∈ cliqueEdges (r + 1) P₀ := by
    apply (mem_cliqueEdges _ _).mpr
    apply (mapBlock_subset_mapBlock (F.embedding s) _ _).mp
    exact (mem_cliqueEdges _ _).mp (hes.symm ▸ hPs.symm ▸ heP)
  have hfP₀ : f₀ ∈ cliqueEdges (r + 1) P₀ := by
    apply (mem_cliqueEdges _ _).mpr
    apply (mapBlock_subset_mapBlock (F.embedding s) _ _).mp
    exact (mem_cliqueEdges _ _).mp (hfs.symm ▸ hPs.symm ▸ hfP)
  have hef := hlocal.near_edges_unique hA hcross (Nat.succ_pos r) hP₀' hN₀ hM₀
    heP₀ heN₀ hfP₀ hfM₀
  exact hes.symm.trans ((congrArg (mapBlock (F.embedding s)) hef).trans hfs)

end Arxiv2411_18291
