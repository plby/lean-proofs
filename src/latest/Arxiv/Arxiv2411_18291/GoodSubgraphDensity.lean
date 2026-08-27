import Arxiv.Arxiv2411_18291.PermutationBlocks
import Arxiv.Arxiv2411_18291.TypicalityDensity

/-!
# Density and permutation probabilities after removing a small edge fraction

The fraction of deleted edges bounds the change in density. Combining this
with a reference-density estimate gives the exact error used for each colour
in the extension argument.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

omit [DecidableEq V] in
theorem density_mono {G K : Hypergraph V r} (hGK : G ⊆ K) : density G ≤ density K := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hGK)
    (Nat.cast_nonneg _)

theorem density_subgraph_difference {G K : Hypergraph V r} (hGK : G ⊆ K) :
    density K - density G = (K \ G).card / ((Fintype.card V).choose r : ℝ) := by
  unfold density
  rw [card_sdiff_of_subset hGK, Nat.cast_sub (card_le_card hGK), sub_div]

theorem density_subgraph_error {G K : Hypergraph V r} {ε : ℝ}
    (hGK : G ⊆ K) (hloss : ((K \ G).card : ℝ) ≤ ε * K.card) :
    |density G - density K| ≤ ε * density K := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (density_mono hGK)),
    density_subgraph_difference hGK]
  simpa only [density, mul_div_assoc] using
    div_le_div_of_nonneg_right hloss (Nat.cast_nonneg ((Fintype.card V).choose r) :
      (0 : ℝ) ≤ (Fintype.card V).choose r)

theorem density_subgraph_reference_error {G K : Hypergraph V r} {ε δ p : ℝ}
    (hGK : G ⊆ K) (hε : 0 ≤ ε) (hloss : ((K \ G).card : ℝ) ≤ ε * K.card)
    (hbase : |density K - p| ≤ δ * p) :
    |density G - p| ≤ (ε + δ + ε * δ) * p := by
  have hK : density K ≤ (1 + δ) * p := by
    have h := (abs_le.mp hbase).2
    linarith
  calc
    _ ≤ |density G - density K| + |density K - p| := abs_sub_le _ _ _
    _ ≤ ε * density K + δ * p := add_le_add (density_subgraph_error hGK hloss) hbase
    _ ≤ ε * ((1 + δ) * p) + δ * p :=
      add_le_add (mul_le_mul_of_nonneg_left hK hε) le_rfl
    _ = _ := by ring

variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem uniform_permuted_good_probability_error (e : Block V r)
    {G K : Hypergraph V r} {ε δ p : ℝ} (hGK : G ⊆ K) (hε : 0 ≤ ε)
    (hloss : ((K \ G).card : ℝ) ≤ ε * K.card) (hbase : |density K - p| ≤ δ * p) :
    |(PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | e ∈ mapGraph σ.toEmbedding G} - p| ≤ (ε + δ + ε * δ) * p := by
  rw [uniform_permuted_family_probability]
  exact density_subgraph_reference_error hGK hε hloss hbase

end Arxiv2411_18291
