import Mathlib
import ErdosProblems.Erdos550.OffTuranReducedDegreeData
import ErdosProblems.Erdos550.OffTuranReducedAssembly

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From cleaned regularity data to heavy heads and a whole matching
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

theorem OffTuranReducedDegreeData.exists_heavy_head_and_matching
    {W₀ : Type} [Fintype W₀] (F : SimpleGraph W₀)
    (q : ℕ) (hq : 1 ≤ q) (d ε₀ : ℝ) (m₀ B : ℕ)
    (hcap : ∀ {W : Type} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], ¬ (F ⊑ Hᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset W)), P.IsUniform H ε →
      ∀ (A : Finset {C // C ∈ P.parts}),
        4 * q ^ 2 ≤ A.card →
        ((P.parts.card : ℝ) ^ 2 * ε <
          (A.card : ℝ) ^ 2 / (4 * q)) →
        (∀ C ∈ A, m₀ ≤ C.1.card) →
        ∃ C ∈ A, ∃ E ∈ A, C ≠ E ∧ H.IsUniform ε C.1 E.1 ∧
          d ≤ (H.edgeDensity C.1 E.1 : ℝ))
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε base η : ℝ}
    (D : OffTuranReducedDegreeData G ε d base η m₀)
    (hF : ¬ (F ⊑ Gᶜ))
    (hε0 : 0 ≤ ε) (hεcap : ε ≤ ε₀)
    (hBbig : 4 * q ^ 2 ≤ B)
    (hBirregular :
      (D.P.parts.card : ℝ) ^ 2 * ε <
        (B : ℝ) ^ 2 / (4 * q))
    (hBfit :
      (B : ℝ) ≤ (20 * η) * (D.P.parts.card : ℝ))
    (hN : 0 < Fintype.card V)
    (hbase : 0 ≤ base + 80 * η * Fintype.card V) :
    ∃ X Y : {C // C ∈ D.P.parts},
      X ∈ heavyClusterFamily Finset.univ
          (clusterNormalizedDegree
            (G.regularityReduced D.P ε d) D.P D.scale)
          base η (Fintype.card V) ∧
      Y ∈ heavyClusterFamily Finset.univ
          (clusterNormalizedDegree
            (G.regularityReduced D.P ε d) D.P D.scale)
          base η (Fintype.card V) ∧
      (offTuranReducedGraph G D.P ε d).Adj X Y ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (cL cR : κ → {C // C ∈ D.P.parts})
        (U : Finset {C // C ∈ D.P.parts}),
        (∀ k, (offTuranReducedGraph G D.P ε d).Adj (cL k) (cR k)) ∧
        Function.Injective (Sum.elim cL cR) ∧
        (∀ k, cL k ≠ X ∧ cL k ≠ Y ∧
          cR k ≠ X ∧ cR k ≠ Y) ∧
        U.card < B ∧
        (∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
          a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR) ∧
        (Finset.univ \
          (Finset.univ.image cL ∪ Finset.univ.image cR)).card < B + 2 := by
  apply exists_offTuran_heavy_head_and_matching
    F q hq d ε₀ m₀ B hcap G hF ε hε0 hεcap D.P D.uniform
    hBbig hBirregular D.part_size_lower
    Finset.univ
      (clusterNormalizedDegree
        (G.regularityReduced D.P ε d) D.P D.scale)
    base η (Fintype.card V) (by exact_mod_cast hN) hbase
  · intro i hi
    exact clusterNormalizedDegree_le_card
      (G.regularityReduced D.P ε d) D.P D.scale
      D.scale_pos D.part_size_upper i
  · simpa using! D.normalized_average
  · simpa using! hBfit

end Erdos550
