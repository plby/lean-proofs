/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.FiniteES

/-!
# Erdős Problem 88: final finite-order assembly

This file isolates the elementary deduction of Problem 88 from the two deep
inputs.  The inputs are explicit propositions, not axioms: later modules must
construct proofs of them.
-/

open Classical SimpleGraph

namespace Erdos88

/-- Constant quadratic edge density for every sufficiently large Ramsey graph. -/
def HasRamseyDensity : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ a : ℝ, 0 < a ∧
      ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n → RamseyFree C G →
          a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)

/-- The finite Erdős--Szemerédi theorem supplies the density input used by the
final assembly. -/
theorem hasRamseyDensity : HasRamseyDensity := by
  intro C hC
  obtain ⟨a, ha, N, hN⟩ := FiniteES.ramseyFree_edgeCount_density_lower C hC
  refine ⟨a, ha, N, ?_⟩
  intro n G hn hG
  simpa [FiniteES.edgeCount] using hN n hn G hG

/-- The KSSS prescribed-count theorem, in the exact finite interface needed here. -/
def HasPrescribedCounts : Prop :=
  ∀ C : ℝ, 0 < C → ∀ η : ℝ, 0 < η →
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      N ≤ n → RamseyFree C G →
        ∀ m : ℕ,
          (m : ℝ) ≤ (1 - η) * (G.edgeFinset.card : ℝ) →
            ∃ S : Finset (Fin n), inducedEdges G S = m

/-- The exact statement of Problem 88 follows by choosing `η = 1/2`, using
quadratic density, and shrinking `δ` to absorb the finitely many smaller graph
orders. -/
theorem erdos_88_of_deep_inputs
    (hDensity : HasRamseyDensity) (hPrescribed : HasPrescribedCounts) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree ε G →
            ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m := by
  intro ε hε
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := ε * Real.log 2
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hε hlogTwo
  obtain ⟨a, ha, N₁, hDensity₁⟩ := hDensity C hC
  obtain ⟨N₂, hPrescribed₂⟩ := hPrescribed C hC (1 / 2 : ℝ) (by norm_num)
  let N : ℕ := max N₁ N₂ + 1
  have hN : 0 < N := by
    dsimp [N]
    omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let δ : ℝ := min (a / 2) (1 / (2 * (N : ℝ) ^ 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos ha (by norm_num))
      (one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hNreal)))
  refine ⟨δ, hδ, ?_⟩
  intro n G hG m hm
  have hRamsey : RamseyFree C G := by
    exact (homogeneousFree_iff_ramseyFree ε G).mp hG
  by_cases hn : N ≤ n
  · have hN₁n : N₁ ≤ n := by
      apply le_trans _ hn
      dsimp [N]
      omega
    have hN₂n : N₂ ≤ n := by
      apply le_trans _ hn
      dsimp [N]
      omega
    have hEdge := hDensity₁ n G hN₁n hRamsey
    have hδa : δ ≤ a / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hmHalf :
        (m : ℝ) ≤ (1 - (1 / 2 : ℝ)) * (G.edgeFinset.card : ℝ) := by
      calc
        (m : ℝ) ≤ δ * (n : ℝ) ^ 2 := hm
        _ ≤ (a / 2) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hδa (sq_nonneg (n : ℝ))
        _ = (1 / 2 : ℝ) * (a * (n : ℝ) ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hEdge (by norm_num)
        _ = (1 - (1 / 2 : ℝ)) * (G.edgeFinset.card : ℝ) := by ring
    exact hPrescribed₂ n G hN₂n hRamsey m hmHalf
  · have hnlt : n < N := Nat.lt_of_not_ge hn
    have hnreal : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnlt
    have hδN : δ ≤ 1 / (2 * (N : ℝ) ^ 2) := by
      dsimp [δ]
      exact min_le_right _ _
    have hnsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ) - n)]
    have hfactor : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
    have hhalf :
        (1 / (2 * (N : ℝ) ^ 2)) * (N : ℝ) ^ 2 = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt hNreal]
    have hmOne : (m : ℝ) < 1 := by
      calc
        (m : ℝ) ≤ δ * (n : ℝ) ^ 2 := hm
        _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hδN (sq_nonneg (n : ℝ))
        _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hnsq hfactor
        _ = (1 / 2 : ℝ) := hhalf
        _ < 1 := by norm_num
    have hmNat : m < 1 := by exact_mod_cast hmOne
    have hmZero : m = 0 := by omega
    refine ⟨∅, ?_⟩
    simpa [hmZero]

end Erdos88
