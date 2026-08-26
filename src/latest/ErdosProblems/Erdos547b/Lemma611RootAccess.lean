/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma611Full

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma611RootAccess

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

/-- Lemma 6.11(i), in the exact form needed in Claim 6.16: every endpoint
of the constructed `M_in` has positive `A`-density, hence is adjacent to the
distinguished reduced vertex `A`. -/
theorem V1_adj_distinguished_of_min_subset_clean
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {A : K} {density : K → K → ℝ} {N eta : ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L density N A))
    (hclean : D.minEdges ⊆
      sourceCleanEdges C67.M L O density A eta D.mbEdges)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hdensityAdj : ∀ x, 0 < density A x → R.Adj A x) :
    ∀ x ∈ D.V1, R.Adj A x := by
  intro x hx
  obtain ⟨e, he, hx0 | hx1⟩ := (mem_matchingSupport D.Min x).mp hx
  · have hd := sourceCleanEdges_density C67.M L O density A eta heta D.mbEdges
      (hclean he)
    have hpos : 0 < density A (orientedEndpoint C67.M L e 0) := by
      linarith [hd.1]
    exact hx0 ▸ hdensityAdj _ hpos
  · have hd := sourceCleanEdges_density C67.M L O density A eta heta D.mbEdges
      (hclean he)
    have hpos : 0 < density A (orientedEndpoint C67.M L e 1) := by
      linarith [hd.2.1]
    exact hx1 ▸ hdensityAdj _ hpos

theorem selected_cluster_adj_distinguished
    {L O C : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {A : K} {density : K → K → ℝ} {N eta : ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L density N A))
    (hclean : D.minEdges ⊆
      sourceCleanEdges C67.M L O density A eta D.mbEdges)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hdensityAdj : ∀ x, 0 < density A x → R.Adj A x)
    (hCV1 : C ⊆ D.V1) :
    ∀ x ∈ C, R.Adj A x := by
  intro x hx
  exact V1_adj_distinguished_of_min_subset_clean D hclean heta hetaHalf
    hdensityAdj x (hCV1 hx)

#print axioms V1_adj_distinguished_of_min_subset_clean
#print axioms selected_cluster_adj_distinguished

end Erdos547b.ZhaoLemma611RootAccess
