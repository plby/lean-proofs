import ErdosProblems.Erdos19.TotalDemandCapacity
import ErdosProblems.Erdos19.ApproximateListColoring

/-! # Approximate sparse-list coloring with total-demand capacities -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem bounded_approximate_capacity_coloring_of_demand_bound
    (r C : ℕ) (hr : 0 < r) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E I A : Type) [DecidableEq V] [Fintype E] [DecidableEq E]
        [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A],
        ∀ (H : FiniteHypergraph V E) (D L : ℕ)
          (B P : I → Finset V) (T : I → ℕ) (F : E → Finset A),
          D₀ ≤ D → 0 < L → (L : ℝ) < delta * (D : ℝ) →
          H.IsBounded r → H.vertexSet.card ≤ C * D →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L) →
          (Pairwise fun i j ↦ Disjoint (B i) (B j)) →
          (Pairwise fun i j ↦ Disjoint (P i) (P j)) →
          (∀ i, P i ⊆ H.vertexSet) → (∀ e i, Disjoint (H.support e) (P i)) →
          (∀ i, (∑ e : E, (H.support e ∩ B i).card) ≤ T i) →
          (∀ i, T i / D + 2 * r +
            (2 * r) * ((2 * r) * D / L) < (P i).card) →
          (∀ e, ((F e).card : ℝ) ≤ delta * (D : ℝ)) →
          (1 + epsilon) * (D : ℝ) ≤ Fintype.card A →
          ∃ c : H.conflictGraph.Coloring A, (∀ e, c e ∉ F e) ∧
            ∀ i a, (B i).card - (P i).card ≤
              (B i \ ((univ.filter fun e ↦ c e = a).biUnion fun e ↦ H.support e ∩ B i)).card := by
  classical
  obtain ⟨delta, hdelta, D₀, hcolor⟩ :=
    bounded_approximate_coloring_avoiding_sparse (2 * r) C (by omega) epsilon hepsilon
  refine ⟨delta, hdelta, max D₀ 1, ?_⟩
  intro V E I A _ _ _ _ _ _ _ H D L B P T F hDlarge hL hLsmall hbound hvertices
    hdeg hpair hB hP hpool hunused hloadBound hroom hF hpalette
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDlarge
  have hD : 0 < D := (by norm_num : 0 < (1 : ℕ)).trans_le
    ((le_max_right _ _).trans hDlarge)
  obtain ⟨K, hKv, hKs, hKr, hKd, hKp, hKcapacity⟩ :=
    exists_capacity_augmentation_of_demand_bound H r D L hD hL B P T hB hP hpool hunused hbound
      hdeg hpair hloadBound hroom
  have hKvertices : K.vertexSet.card ≤ C * D := by simpa only [hKv] using hvertices
  have hKcodegree : ∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y →
      (K.edgePairDegree x y : ℝ) < delta * (D : ℝ) := by
    intro x hx y hy hxy
    have hle : (K.edgePairDegree x y : ℝ) ≤ L := by exact_mod_cast hKp x hx y hy hxy
    exact hle.trans_lt hLsmall
  obtain ⟨c, hcF⟩ := hcolor V E A K D F hD₀ hKr hKvertices hKd hKcodegree hF hpalette
  refine ⟨coloringOfSupportExtension H K hKs c, ?_, ?_⟩
  · intro e
    exact hcF e
  · intro i a
    exact coloring_uncovered_buffer_ge H K (B i) (P i)
      (fun e ↦ (hKcapacity e i).symm.le) c a

#print axioms bounded_approximate_capacity_coloring_of_demand_bound

end Erdos19
