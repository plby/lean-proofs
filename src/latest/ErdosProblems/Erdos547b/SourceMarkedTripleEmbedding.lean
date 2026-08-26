/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.MarkedTripleEmbedding
import ErdosProblems.Erdos547b.SourceEmbeddingHost
import ErdosProblems.Erdos547b.SourceFreshChunkBounds

/-!
# The actual marked-branch graph step at the source parameter schedule

Two actual reduced edges and three current sets of gamma*N vertices
supply every local typicality and greedy-embedding inequality.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedTripleEmbedding

open Finset SimpleGraph
open Erdos547b.ZhaoMarkedTripleEmbedding Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm

theorem parameter_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (N : ℕ) :
    (epsilon α : ℝ) < gamma α ∧ 0 ≤ (densityCutoff α : ℝ) - epsilon α ∧
      (freshBranchBound α N : ℝ) + 2 * (epsilon α : ℝ) * N ≤
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * ((gamma α : ℝ) * N) := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast hp.2.2.2.2.2.2.2
  have hg : (0 : ℝ) < gamma α := by exact_mod_cast hp.2.2.2.2.2.2.1
  have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast hp.2.2.2.2.2.1
  have heg : (epsilon α : ℝ) ≤ (gamma α : ℝ) / 1000000 := by exact_mod_cast hu.2.2.2.2.2.2
  have hg1Q : gamma α ≤ 1 := by
    linarith only [hu.2.2.2.2.2.1, (reservoir_cleanup_bounds hα hα1).2.2.2.2.2]
  have hg1 : (gamma α : ℝ) ≤ 1 := by exact_mod_cast hg1Q
  have hprod : 10 * (epsilon α : ℝ) ≤ (densityCutoff α : ℝ) * (gamma α : ℝ) := by
    exact_mod_cast (regularity_product_margin hα hα1).le
  have hdprod := mul_le_mul_of_nonneg_left hg1 hd.le
  have heprod := mul_le_mul_of_nonneg_left hg1 he.le
  have hm : (freshBranchBound α N : ℝ) ≤ (epsilon α : ℝ) * N / 2 := Nat.floor_le (by positivity)
  have hscale := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hscale' := mul_le_mul_of_nonneg_right heprod (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  refine ⟨by linarith only [heg, hg], by linarith only [hprod, hdprod, he], ?_⟩
  nlinarith only [hm, hscale, hscale', mul_nonneg he.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem exists_markedBranchCopy
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C X Y : Index W) (hCX : (reduced W).Adj C X) (hYX : (reduced W).Adj Y X)
    (C' X' Y' : Finset (Fin hostN))
    (hC : C' ⊆ clusterVertices (assignment W) C)
    (hX : X' ⊆ clusterVertices (assignment W) X)
    (hY : Y' ⊆ clusterVertices (assignment W) Y)
    (hCLarge : (gamma α : ℝ) * W.clusterSize ≤ (C'.card : ℝ))
    (hXLarge : (gamma α : ℝ) * W.clusterSize ≤ (X'.card : ℝ))
    (hYLarge : (gamma α : ℝ) * W.clusterSize ≤ (Y'.card : ℝ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A) (special : Finset A)
    (hspecial : ∀ a ∈ special, hT.coloringTwoOfVert root a = 0)
    (hsmall : Fintype.card A ≤ freshBranchBound α W.clusterSize)
    (z : Fin hostN) (hattach : ∀ v ∈ C', (embeddingHost W).Adj z v) :
    ∃ f : T.Copy (embeddingHost W), (embeddingHost W).Adj z (f root) ∧ f root ∈ C' ∧
      (∀ a ∈ special, f a ∈ C') ∧
      ∀ a, a ≠ root → a ∉ special →
        f a ∈ if hT.coloringTwoOfVert root a = 0 then Y' else X' := by
  have hcard (i : Index W) : (clusterVertices (assignment W) i).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters i.1 i.2
  obtain ⟨heg, hfactor, hmargin⟩ := parameter_margin hα hα1 W.clusterSize
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have heN := mul_lt_mul_of_pos_right heg hN
  have he : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hb : (Fintype.card A : ℝ) ≤ freshBranchBound α W.clusterSize := by exact_mod_cast hsmall
  have hCmargin := mul_le_mul_of_nonneg_left hCLarge hfactor
  have hXmargin := mul_le_mul_of_nonneg_left hXLarge hfactor
  have hYmargin := mul_le_mul_of_nonneg_left hYLarge hfactor
  have pCX := embedding_pair_of_adj W hCX
  have pYX := embedding_pair_of_adj W hYX
  apply exists_markedCopy_of_uniform (embeddingHost W) T hT root special hspecial z
    (clusterVertices (assignment W) C) (clusterVertices (assignment W) X)
    (clusterVertices (assignment W) Y) C' X' Y'
    (epsilon α : ℝ) (densityCutoff α : ℝ) (densityCutoff α : ℝ)
    pCX.1 pYX.1 hC hX hY
  · rw [hcard]
    exact heN.trans_le hCLarge
  · rw [hcard]
    exact heN.le.trans hXLarge
  · rw [hcard]
    exact heN.le.trans hYLarge
  · exact pCX.2
  · exact pYX.2
  · rw [hcard]
    linarith only [hb, hmargin, hXmargin]
  · rw [hcard]
    linarith only [hb, hmargin, hXmargin]
  · rw [hcard]
    nlinarith only [hb, hmargin, hCmargin, mul_nonneg he hN.le]
  · rw [hcard]
    nlinarith only [hb, hmargin, hYmargin, mul_nonneg he hN.le]
  · exact hattach

end Erdos547b.ZhaoSourceMarkedTripleEmbedding

#print axioms Erdos547b.ZhaoSourceMarkedTripleEmbedding.parameter_margin
#print axioms Erdos547b.ZhaoSourceMarkedTripleEmbedding.exists_markedBranchCopy
