import Wikipedia.HopfProblem.OrbitPairFinitePosetChainBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mesh convergence for actual finite iterated subdivision

The cardinality bound is uniform over all stages. The previously verified
face-mean contraction therefore iterates with one fixed ratio less than
one. The resulting estimate applies to every pair of points in each
native characteristic simplex, after the actual subdivision homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder Filter Topology

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex Subdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedVertices_mesh (P : PartOrd.{u}) (v : P → E) (N : ℕ)
    (hN : ChainCardBound P N) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ A : NonemptyFiniteChains P, ∀ p ∈ A.finset, ∀ q ∈ A.finset,
      dist (v p) (v q) ≤ D) (r : ℕ) :
    ∀ A : NonemptyFiniteChains ((iteratedChains r).obj P),
      ∀ p ∈ A.finset, ∀ q ∈ A.finset,
        dist (iteratedVertices P v r p) (iteratedVertices P v r q) ≤
          ((N : ℝ) / (N + 1)) ^ r * D := by
  induction r with
  | zero =>
    intro A p hp q hq
    change dist (v p) (v q) ≤ ((N : ℝ) / (N + 1)) ^ 0 * D
    simpa only [pow_zero, one_mul] using hv A p hp q hq
  | succ r ih =>
    intro B A hA C hC
    have hr : 0 ≤ ((N : ℝ) / (N + 1)) ^ r * D :=
      mul_nonneg (pow_nonneg (meshRatio_nonneg N) r) hD
    have hc := iteratedChains_cardBound P N hN r
    have he : dist (faceMean (iteratedVertices P v r) A.finset)
        (faceMean (iteratedVertices P v r) C.finset) ≤
          ((N : ℝ) / (N + 1)) * (((N : ℝ) / (N + 1)) ^ r * D) := by
      rcases B.comparable ⟨A, hA⟩ ⟨C, hC⟩ with hAC | hCA
      · exact faceMeans_dist_le_mesh (iteratedVertices P v r) A.finset C.finset
          A.nonempty hAC N (hc C) _ hr (ih C)
      · rw [dist_comm]
        exact faceMeans_dist_le_mesh (iteratedVertices P v r) C.finset A.finset
          C.nonempty hCA N (hc A) _ hr (ih A)
    change dist (faceMean (iteratedVertices P v r) A.finset)
      (faceMean (iteratedVertices P v r) C.finset) ≤ _
    exact he.trans_eq (by rw [pow_succ]; ring)

theorem iterationAffineMap_mesh (P : PartOrd.{u}) [Finite P] (v : P → E) (N : ℕ)
    (hN : ChainCardBound P N) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ p q, dist (v p) (v q) ≤ D) (r k : ℕ)
    (x : (nerve ((iteratedChains r).obj P)) _⦋k⦌) (t s : Simplex k) :
    dist (iterationAffineMap P v r
      (characteristic (nerve ((iteratedChains r).obj P)) k x t))
      (iterationAffineMap P v r
        (characteristic (nerve ((iteratedChains r).obj P)) k x s)) ≤
          ((N : ℝ) / (N + 1)) ^ r * D := by
  have hverts : ∀ i j : Fin (k + 1),
      dist (iteratedVertices P v r (x.obj i)) (iteratedVertices P v r (x.obj j)) ≤
        ((N : ℝ) / (N + 1)) ^ r * D := by
    intro i j
    exact iteratedVertices_mesh P v N hN D hD (fun _ p _ q _ ↦ hv p q) r
      (simplexVertexChain ((iteratedChains r).obj P) k x)
      (x.obj i) (mem_simplexVertexChain ((iteratedChains r).obj P) k x i)
      (x.obj j) (mem_simplexVertexChain ((iteratedChains r).obj P) k x j)
  exact (congrArg₂ dist (iterationAffineMap_characteristic P v r k x t)
    (iterationAffineMap_characteristic P v r k x s)).le.trans
      (affineValues_dist_le (fun i ↦ iteratedVertices P v r (x.obj i)) t s _ hverts)

theorem meshBound_tendsto_zero (N : ℕ) (D : ℝ) :
    Tendsto (fun r : ℕ ↦ ((N : ℝ) / (N + 1)) ^ r * D) atTop (𝓝 0) := by
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (meshRatio_nonneg N) (meshRatio_lt_one N)).mul_const D

theorem exists_iterationAffineMap_mesh_lt (P : PartOrd.{u}) [Finite P]
    (v : P → E) (N : ℕ) (hN : ChainCardBound P N) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ p q, dist (v p) (v q) ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ k : ℕ, ∀ x : (nerve ((iteratedChains r).obj P)) _⦋k⦌,
      ∀ t s : Simplex k,
        dist (iterationAffineMap P v r
          (characteristic (nerve ((iteratedChains r).obj P)) k x t))
          (iterationAffineMap P v r
            (characteristic (nerve ((iteratedChains r).obj P)) k x s)) < ε := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((meshBound_tendsto_zero N D).eventually (gt_mem_nhds hε))
  exact ⟨R, fun r hr k x t s ↦
    (iterationAffineMap_mesh P v N hN D hD hv r k x t s).trans_lt (hR r hr)⟩

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
