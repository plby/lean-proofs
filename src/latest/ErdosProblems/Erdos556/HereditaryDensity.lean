import ErdosProblems.Erdos556.CoreConnectivity
import ErdosProblems.Erdos556.CoreDensity

/-!
# Hereditary density from the connected-core dichotomy

The graph-theoretic assembly is separated from choosing the scalar
parameters. Every hypothesis below is either a graph assumption or an
explicit numerical inequality.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_hereditary_density_parameter_bound (D B : ℕ) (hD : 0 < D) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b d k : ℕ) (r η : ℝ),
      TwoConnected G → ¬ G.Colorable 2 → 1 ≤ k → 0 ≤ r → 0 ≤ η →
      ((2 * (b + 3 * D + 3) : ℕ) : ℝ) ≤ r →
      ((2 * (b + 3 * D + 3) : ℕ) : ℝ) * Fintype.card V ≤
        2 * η * (r - (2 * (b + 3 * D + 3) : ℕ)) ^ 2 →
      ((d + 2 * (b + 3 * D + 3) : ℕ) : ℝ) ≤ r →
      Fintype.card V ≤ D * d → Fintype.card V ≤ B * b →
      ((N₀ + (b + 3 * D + 3) + 2 : ℕ) : ℝ) ≤ r →
      (k : ℝ) + 2 * q * Fintype.card V + (b + 3 * D + 5 : ℕ) ≤ r →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ∀ A : Finset V, ((G.induce (A : Set V)).edgeFinset.card : ℝ) ≤
        r * A.card + η * (A.card : ℝ) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_core_density_bound D B hD hB q hq0 hq1
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ b d k r η hG hnb hk hr hη ht hbudget hdeg hDcard hBcard horder hmargin ho A
  by_contra hA
  obtain ⟨S, hS, hdense, hmin, hc⟩ := exists_connected_quadratic_dense_core_of_subset
    G (2 * (b + 3 * D + 3)) r η hr hη ht hbudget A (lt_of_not_ge hA)
  have hScard : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hSle : S.card ≤ Fintype.card V := card_le_univ S
  obtain ⟨v, hv⟩ := hS
  have hminv := hmin ⟨v, hv⟩
  have hvdeg := (G.induce (S : Set V)).degree_lt_card_verts ⟨v, hv⟩
  rw [hScard] at hvdeg
  have hvdegR : ((G.induce (S : Set V)).degree ⟨v, hv⟩ : ℝ) < S.card := by exact_mod_cast hvdeg
  have hSorder : N₀ + (b + 3 * D + 3) + 2 ≤ S.card := by
    have h : ((N₀ + (b + 3 * D + 3) + 2 : ℕ) : ℝ) ≤ S.card := by linarith
    exact_mod_cast h
  have hdegrees (w : S) : d + 2 * (b + 3 * D + 3) ≤ (G.induce (S : Set V)).degree w := by
    have h := hdeg.trans (hmin w).le
    exact_mod_cast h
  have hbound := hN₀ G S b d k hG hnb hSorder hc hdegrees
    (hSle.trans hDcard) (hSle.trans hBcard) hk ho
  have hSleR : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hSle
  have hsq := mul_le_mul_of_nonneg_right hSleR (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  have hqmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * q)
  have hrmul := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  have hηmul := mul_nonneg hη (sq_nonneg (S.card : ℝ))
  nlinarith

#print axioms exists_hereditary_density_parameter_bound

end Erdos556
