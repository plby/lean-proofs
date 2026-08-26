import ErdosProblems.Erdos19.Uniformization

/-!
# Approximate coloring for bounded-rank hypergraphs
-/

namespace Erdos19

open Erdos76 Erdos76.FiniteHypergraph Uniformization

/-- An unconditional approximate edge-coloring theorem with a rank bound,
maximum degree bound, and small codegrees. No minimum degree is required. -/
theorem bounded_approximate_edgeColoring (r : ℕ) (hr : 0 < r)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
        ∀ (H : FiniteHypergraph V E) (D : ℕ),
          D₀ ≤ D → H.IsBounded r →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
            (H.edgePairDegree u v : ℝ) < delta * (D : ℝ)) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ (1 + epsilon) * (D : ℝ) ∧
            Nonempty (H.EdgeColoring q) := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    uniform_approximate_edgeColoring r hr epsilon hepsilon
  obtain ⟨D₁, hD₁⟩ := exists_nat_gt (1 / delta)
  refine ⟨delta / 2, div_pos hdelta (by norm_num), max D₀ D₁, ?_⟩
  intro V E _ _ _ H D hDlarge hbound hdeg hpair
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDlarge
  have hD₁le : D₁ ≤ D := (le_max_right _ _).trans hDlarge
  have hratio : 1 / delta < (D : ℝ) := hD₁.trans_le (by exact_mod_cast hD₁le)
  have hdeltaD : 1 < delta * (D : ℝ) := by
    have h := (div_lt_iff₀ hdelta).mp hratio
    nlinarith
  have hDposR : (0 : ℝ) < D := by nlinarith
  have hDpos : 0 < D := by exact_mod_cast hDposR
  have hsmall : (delta / 2) * (D : ℝ) < delta * (D : ℝ) := by nlinarith
  have hpdeg : ∀ v ∈ (padded H r).vertexSet, (padded H r).edgeDegree v ≤ D := by
    intro v hv
    rcases v with v | ⟨e, i⟩
    · rw [padded_edgeDegree_inl]
      exact hdeg v ((mem_padded_vertexSet_inl H r v).mp hv)
    · exact (padded_edgeDegree_inr_le_one H r e i).trans hDpos
  have hppair : ∀ u ∈ (padded H r).vertexSet, ∀ v ∈ (padded H r).vertexSet,
      u ≠ v → ((padded H r).edgePairDegree u v : ℝ) < delta * (D : ℝ) := by
    intro u hu v hv huv
    rcases u with u | ⟨e, i⟩
    · rcases v with v | ⟨f, j⟩
      · rw [padded_edgePairDegree_inl]
        exact (hpair u ((mem_padded_vertexSet_inl H r u).mp hu)
          v ((mem_padded_vertexSet_inl H r v).mp hv)
          (fun h ↦ huv (congrArg Sum.inl h))).trans hsmall
      · have hle := (pairDegree_le_degree_right (padded H r) (Sum.inl u)
          (Sum.inr (f, j))).trans (padded_edgeDegree_inr_le_one H r f j)
        have hleR : ((padded H r).edgePairDegree (Sum.inl u) (Sum.inr (f, j)) : ℝ) ≤ 1 := by
          exact_mod_cast hle
        exact hleR.trans_lt hdeltaD
    · have hle := (pairDegree_le_degree_left (padded H r) (Sum.inr (e, i)) v).trans
        (padded_edgeDegree_inr_le_one H r e i)
      have hleR : ((padded H r).edgePairDegree (Sum.inr (e, i)) v : ℝ) ≤ 1 := by
        exact_mod_cast hle
      exact hleR.trans_lt hdeltaD
  obtain ⟨q, hq, hqbound, ⟨c⟩⟩ := hround (V ⊕ (E × ℕ)) E (padded H r) D hD₀
    (padded_isUniform H r hbound) hpdeg hppair
  exact ⟨q, hq, hqbound, ⟨restrictColoring H r q c⟩⟩

#print axioms bounded_approximate_edgeColoring

end Erdos19
