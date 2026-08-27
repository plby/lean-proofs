import Arxiv.Arxiv2411_18291.SplittingMultiplicity

/-!
# All opposite-sign near cancellation pairs

The first elimination stage uses exactly the pairs of near cliques with
a common edge. The index type is finite, contains no repeated pair, and
has the required exact vertex intersections. Each negative root's edges
in the original graph already lie in its positive partner.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

abbrev CliqueCancellationPairs (r : ℕ) (N P : Finset (Block V q)) :=
  {i : N × P // (cliqueEdges r i.1.val ∩ cliqueEdges r i.2.val).Nonempty}

variable {W : Type*} [Fintype W] [DecidableEq W] {C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

abbrev SplittingFamily.NearPairs (F : SplittingFamily S D B C θ) :=
  CliqueCancellationPairs (r + 1) F.negativeNear F.positiveNear

def SplittingFamily.pairPositive (F : SplittingFamily S D B C θ) (i : F.NearPairs) : Block V q :=
  i.val.2.val

def SplittingFamily.pairNegative (F : SplittingFamily S D B C θ) (i : F.NearPairs) : Block V q :=
  i.val.1.val

theorem SplittingFamily.near_pair_injective (F : SplittingFamily S D B C θ) :
    Function.Injective fun i : F.NearPairs => (F.pairPositive i, F.pairNegative i) := by
  intro i j h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg Prod.snd h)) (Subtype.ext (congrArg Prod.fst h))

theorem SplittingFamily.pairPositive_mem (F : SplittingFamily S D B C θ) (i : F.NearPairs) :
    F.pairPositive i ∈ F.cliques := by
  rw [F.cliques_eq_signs]
  exact mem_union_left _ (mem_filter.mp i.val.2.property).1

theorem SplittingFamily.pairNegative_mem (F : SplittingFamily S D B C θ) (i : F.NearPairs) :
    F.pairNegative i ∈ F.cliques := by
  rw [F.cliques_eq_signs]
  exact mem_union_right _ (mem_filter.mp i.val.1.property).1

theorem SplittingFamily.near_pair_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (i : F.NearPairs) :
    ∃ e : Block V (r + 1), (F.pairPositive i).val ∩ (F.pairNegative i).val = e.val := by
  obtain ⟨e, he⟩ := i.property
  refine ⟨e, ?_⟩
  have h := F.opposite_near_inter hA i.val.1.property i.val.2.property
    (mem_inter.mp he).1 (mem_inter.mp he).2
  simpa only [pairPositive, pairNegative, inter_comm] using h

theorem SplittingFamily.opposite_near_edge_original (F : SplittingFamily S D B C θ)
    {R T : Block V q} (hR : R ∈ F.negativeNear) (hT : T ∈ F.positiveNear)
    {e : Block V (r + 1)} (heR : e ∈ cliqueEdges (r + 1) R)
    (heT : e ∈ cliqueEdges (r + 1) T) : e ∈ B := by
  obtain ⟨s, R₀, hR₀, hs, rfl⟩ := F.negativeNear_source hR
  obtain ⟨t, T₀, hT₀, ht, rfl⟩ := F.positiveNear_source hT
  have hst : s ≠ t := by
    intro h
    have heq : false = true := hs.symm.trans ((congrArg (fun u => u.2.1) h).trans ht)
    exact Bool.false_ne_true heq
  apply F.copy_inter_subset hst
  exact mem_inter.mpr
    ⟨mapGraph_mono _ (S.negative_decomposition.clique_subset (S.near_negative hR₀))
        (by rwa [map_cliqueEdges]),
      mapGraph_mono _ (S.negative_decomposition.clique_subset (S.near_negative hT₀))
        (by rwa [map_cliqueEdges])⟩

theorem SplittingFamily.near_pair_old_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (i : F.NearPairs) :
    cliqueEdges (r + 1) (F.pairNegative i) ∩ B ⊆
      cliqueEdges (r + 1) (F.pairPositive i) := by
  obtain ⟨e, he⟩ := i.property
  have heB := F.opposite_near_edge_original i.val.1.property i.val.2.property
    (mem_inter.mp he).1 (mem_inter.mp he).2
  obtain ⟨d, _, hd⟩ := F.negativeNear_inter hA i.val.1.property
  have hed : e = d := by
    have h := mem_inter.mpr ⟨(mem_inter.mp he).1, heB⟩
    rwa [hd, mem_singleton] at h
  intro f hf
  have hfd : f = d := by
    change f ∈ cliqueEdges (r + 1) i.val.1.val ∩ B at hf
    rwa [hd, mem_singleton] at hf
  rw [hfd, ← hed]
  exact (mem_inter.mp he).2

end Arxiv2411_18291
