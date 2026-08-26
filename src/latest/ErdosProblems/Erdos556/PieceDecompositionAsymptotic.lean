import ErdosProblems.Erdos556.PieceDecomposition

/-!
# A uniform small-error decomposition

For each fixed error tolerance and minimum piece order, sufficiently
large graphs have a disjoint-piece decomposition with at most `ε N²`
discarded edges. All thresholds are independent of the graph.
-/

namespace Erdos556

open SimpleGraph Finset

private theorem decomposition_real_bound (r N e s : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hr : 2 ≤ ε * (r + 1))
    (hN : 2 * (r + 1) ≤ ε * N)
    (he : (r + 1) * e ≤ (r + 1) * s + (r + 1) ^ 2 * N + N ^ 2) :
    (e : ℝ) ≤ s + ε * (N : ℝ) ^ 2 := by
  have heR : ((r : ℝ) + 1) * e ≤ ((r : ℝ) + 1) * s +
      ((r : ℝ) + 1) ^ 2 * N + (N : ℝ) ^ 2 := by exact_mod_cast he
  have h1 := mul_le_mul_of_nonneg_right hN
    (by positivity : (0 : ℝ) ≤ ((r : ℝ) + 1) * N)
  have h2 := mul_le_mul_of_nonneg_right hr
    (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
  have hbound : ((r : ℝ) + 1) * e ≤ ((r : ℝ) + 1) * (s + ε * (N : ℝ) ^ 2) := by
    nlinarith only [heR, h1, h2]
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mp hbound

theorem exists_uniform_piece_decomposition (ε : ℝ) (hε : 0 < ε) (R : ℕ) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N₀ ≤ Fintype.card V →
      ∃ P : Finset (Finset V), IsTwoConnectedPieceFamily G R P ∧
        (G.edgeFinset.card : ℝ) ≤
          (∑ A ∈ P, ((G.induce (A : Set V)).edgeFinset.card : ℝ)) +
            ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨r, hr⟩ := exists_nat_gt ((R : ℝ) + 2 + 2 / ε)
  have hdiv : (0 : ℝ) ≤ 2 / ε := by positivity
  have hrR : R ≤ r := by exact_mod_cast (show (R : ℝ) ≤ r by linarith)
  have hr2 : 2 ≤ r := by exact_mod_cast (show (2 : ℝ) ≤ r by linarith)
  have hrε : (2 : ℝ) ≤ ε * (r + 1) := by
    have hx : 2 / ε < (r : ℝ) + 1 := by linarith [Nat.cast_nonneg R (α := ℝ)]
    have hx' := (div_lt_iff₀ hε).mp hx
    nlinarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * ((r : ℝ) + 1) / ε)
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ hN
  obtain ⟨P, hP, heP⟩ := exists_piece_decomposition G r hr2
  have hNreal : (N₀ : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hNε : 2 * ((r : ℝ) + 1) ≤ ε * Fintype.card V := by
    have hx := (div_lt_iff₀ hε).mp (hN₀.trans_le hNreal)
    nlinarith
  refine ⟨P, ⟨hP.1, fun A hA => ⟨hrR.trans_lt (hP.2 A hA).1, (hP.2 A hA).2⟩⟩, ?_⟩
  have h := decomposition_real_bound r (Fintype.card V) G.edgeFinset.card
    (∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card) ε hε hrε hNε heP
  simpa only [Nat.cast_sum] using h

#print axioms exists_uniform_piece_decomposition

end Erdos556
