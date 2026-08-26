/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceEmbeddingHost
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning

/-!
# Online roots with only a small set of unavailable targets

The root pool can already impose a parent-neighbor constraint and exclude
used vertices. Lower typicality is measured against actual target subsets.
The exceptional count is independent of the regularity bound. This is a
root-selection step, not a completed online forest embedding.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOnlineRootSelection

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoSourceRootIncidence
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

/-- Choose a root with source-relative lower degree on almost all targets,
even when the root pool has been restricted by earlier embedding choices. -/
theorem exists_root_source_lower_most
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A pool : Finset V) (J : Finset I) (whole raw : I → Finset V)
    (source : I → ℝ) (ε δ : ℝ)
    (hε : ε ≤ 1) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, H.IsUniform ε A (whole j))
    (hraw : ∀ j ∈ J, raw j ⊆ whole j)
    (hrawLarge : ∀ j ∈ J, ε * (whole j).card ≤ (raw j).card)
    (hsource : ∀ j ∈ J, source j ≤ H.edgeDensity A (whole j) + ε)
    (hpool : pool ⊆ A) (hpoolCard : δ * A.card < pool.card) :
    ∃ z ∈ pool, ∃ D ⊆ J, (D.card : ℝ) ≤ δ * J.card ∧
      ∀ j ∈ J \ D,
        (source j - 2 * ε) * (raw j).card ≤ (degreeInto H z (raw j) : ℝ) := by
  let bad := fun j => targetLowDegreeVertices H ε A (whole j) A (raw j)
  have hA : ε * A.card ≤ (A.card : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg A.card)
  have hbad : ∀ j ∈ J, ((bad j).card : ℝ) ≤ ε * A.card := by
    intro j hj
    exact card_targetLowDegreeVertices_le H (huniform j hj)
      (Finset.Subset.refl A) (hraw j hj) hA (hrawLarge j hj)
  obtain ⟨z, hz, hcount, hgood⟩ :=
    exists_root_few_badTargets A pool J bad ε δ hδ hεδ hbad hpool hpoolCard
  refine ⟨z, hz, badTargets J bad z, Finset.filter_subset _ _, hcount, ?_⟩
  intro j hj
  have hjJ := (Finset.mem_sdiff.mp hj).1
  have hlow := target_degree_ge_of_not_mem_lowDegree H ε A (whole j) A (raw j)
    z (hpool hz) (hgood j hj)
  have hsource' : source j - 2 * ε ≤ (H.edgeDensity A (whole j) : ℝ) - ε := by
    linarith only [hsource j hjJ]
  exact (mul_le_mul_of_nonneg_right hsource' (Nat.cast_nonneg (raw j).card)).trans hlow

/-- Rejecting an edge only when one of its two targets is bad loses at
most the number of bad targets, regardless of which endpoint was bad. -/
theorem projected_bad_edges
    {E : Type*} [DecidableEq E] (M : Finset E) (D : Finset (E × Fin 2))
    (hD : D ⊆ M ×ˢ Finset.univ) :
    D.image Prod.fst ⊆ M ∧ (D.image Prod.fst).card ≤ D.card ∧
      ∀ e ∈ M \ D.image Prod.fst, ∀ c : Fin 2, (e, c) ∉ D := by
  refine ⟨?_, Finset.card_image_le, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_product.mp (hD hx)).1
  · intro e he c hc
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_image.mpr ⟨(e, c), hc, rfl⟩)

/-- The exact `4 * delta * N * |M|` capacity cost of the temporary
unavailable matching edges at one online root-selection step. -/
theorem projected_bad_capacity
    {E : Type*} [DecidableEq E] (M : Finset E) (D : Finset (E × Fin 2))
    (w : E → ℝ) (δ N : ℝ)
    (hD : D ⊆ M ×ˢ Finset.univ)
    (hcount : (D.card : ℝ) ≤ δ * (M ×ˢ (Finset.univ : Finset (Fin 2))).card)
    (hN : 0 ≤ N) (hcap : ∀ e ∈ M, w e ≤ 2 * N) :
    (∑ e ∈ M, w e) ≤ (∑ e ∈ M \ D.image Prod.fst, w e) + 4 * δ * N * M.card := by
  obtain ⟨hsub, hcard, _⟩ := projected_bad_edges M D hD
  have hcardR : ((D.image Prod.fst).card : ℝ) ≤ 2 * δ * M.card := by
    have h := (show ((D.image Prod.fst).card : ℝ) ≤ D.card by exact_mod_cast hcard).trans hcount
    simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using h
  have hsum : (∑ e ∈ D.image Prod.fst, w e) ≤ ((D.image Prod.fst).card : ℝ) * (2 * N) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (D.image Prod.fst) w (2 * N)
      (fun e he => hcap e (hsub he))
  have hscaled := mul_le_mul_of_nonneg_right hcardR (show 0 ≤ 2 * N by positivity)
  have hsplit := Finset.sum_sdiff hsub (f := w)
  nlinarith only [hsum, hscaled, hsplit]

open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost

/-- Specialization to either distinguished source row in the actual
degree-form construction and its compatible embedding host. -/
theorem exists_actual_source_root_lower_most
    {α : ℚ} {hostN q M : ℕ} {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
    (W : Witness α q M G) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {Q : Certificate W} (F : CleanSourceWitness W Q)
    (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (pool : Finset (Fin hostN)) (J : Finset (EvenPadding (Index W)))
    (raw : EvenPadding (Index W) → Finset (Fin hostN))
    (hJ : ∀ x ∈ J, x ≠ Sum.inl Q.A ∧ x ≠ Sum.inl Q.B ∧
      0 < rootDensity W F (Sum.inl C) x)
    (hraw : ∀ x ∈ J, raw x ⊆ padCluster (clusterVertices (assignment W)) x)
    (hrawLarge : ∀ x ∈ J, (epsilon α : ℝ) *
      (padCluster (clusterVertices (assignment W)) x).card ≤ (raw x).card)
    (hpool : pool ⊆ clusterVertices (assignment W) C)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, ∃ D ⊆ J, (D.card : ℝ) ≤ (rootTypicality α : ℝ) * J.card ∧
      ∀ x ∈ J \ D,
        (rootDensity W F (Sum.inl C) x - 2 * (epsilon α : ℝ)) * (raw x).card ≤
          (degreeInto (embeddingHost W) z (raw x) : ℝ) := by
  obtain ⟨_, _, _, _, hεd, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have hεQ : epsilon α ≤ 1 := by linarith only [hεd, hd1]
  have hε : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast hεQ
  have hδ : (0 : ℝ) < rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1
  have hεδ : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have hpair (x) (hx : x ∈ J) :
      (embeddingHost W).IsUniform (epsilon α : ℝ)
          (clusterVertices (assignment W) C) (padCluster (clusterVertices (assignment W)) x) ∧
        (densityCutoff α : ℝ) ≤ (embeddingHost W).edgeDensity
          (clusterVertices (assignment W) C) (padCluster (clusterVertices (assignment W)) x) ∧
        rootDensity W F (Sum.inl C) x ≤ (embeddingHost W).edgeDensity
          (clusterVertices (assignment W) C) (padCluster (clusterVertices (assignment W)) x) +
            (epsilon α : ℝ) := by
    obtain ⟨hxA, hxB, hpos⟩ := hJ x hx
    rcases hC with rfl | rfl
    · exact source_pair_A W F hxA hxB hpos
    · exact source_pair_B W F hxA hxB hpos
  have hcard : (clusterVertices (assignment W) C).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters C.1 C.2
  exact exists_root_source_lower_most (embeddingHost W)
    (clusterVertices (assignment W) C) pool J (padCluster (clusterVertices (assignment W)))
    raw (rootDensity W F (Sum.inl C)) (epsilon α : ℝ) (rootTypicality α : ℝ)
    hε hδ hεδ (fun x hx => (hpair x hx).1) hraw hrawLarge
    (fun x hx => (hpair x hx).2.2) hpool (by simpa only [hcard] using hpoolCard)

end Erdos547b.ZhaoSourceOnlineRootSelection

#print axioms Erdos547b.ZhaoSourceOnlineRootSelection.exists_root_source_lower_most
#print axioms Erdos547b.ZhaoSourceOnlineRootSelection.projected_bad_edges
#print axioms Erdos547b.ZhaoSourceOnlineRootSelection.projected_bad_capacity
#print axioms Erdos547b.ZhaoSourceOnlineRootSelection.exists_actual_source_root_lower_most
