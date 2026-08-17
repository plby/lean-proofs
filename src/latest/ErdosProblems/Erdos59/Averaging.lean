import ErdosProblems.Erdos59.Duplication

/-!
# The deterministic averaging step in the FNV duplication construction

This file rewrites the fixed-size-subset double count from `Duplication` in
the form used by Füredi--Naor--Verstraëte.  If a graph has `N` vertices and
`e` edges, some `K` vertices meet at least

`e * (K / N) * (2 - (K - 1) / (N - 1))`

edges.  The main theorem below is over the natural numbers with both
denominators cleared.  Thus it also covers the degenerate cases `N < 2`
without making any division convention part of the statement.
-/

namespace Erdos59

open scoped BigOperators
open Finset

namespace FNV

/-! ## The binomial coefficient in the double count -/

private lemma choose_avoid_mul_denominator {N K : ℕ} (hN : 2 ≤ N) :
    (N - 2).choose K * (N * (N - 1)) =
      N.choose K * ((N - K) * (N - K - 1)) := by
  have h₁ := Nat.choose_mul_succ_eq (N - 2) K
  have h₂ := Nat.choose_mul_succ_eq (N - 1) K
  have hNm2 : N - 2 + 1 = N - 1 := by omega
  have hNm1 : N - 1 + 1 = N := by omega
  rw [hNm2] at h₁
  rw [hNm1] at h₂
  have hsub₁ : N - 1 - K = N - K - 1 := by omega
  rw [hsub₁] at h₁
  calc
    (N - 2).choose K * (N * (N - 1)) =
        ((N - 2).choose K * (N - 1)) * N := by ring
    _ = ((N - 1).choose K * (N - K - 1)) * N := by rw [h₁]
    _ = ((N - 1).choose K * N) * (N - K - 1) := by ring
    _ = (N.choose K * (N - K)) * (N - K - 1) := by rw [h₂]
    _ = N.choose K * ((N - K) * (N - K - 1)) := by ring

/-- The proportion of `K`-subsets meeting a fixed two-element edge,
expressed with all denominators cleared. -/
theorem choose_incident_mul_denominator {N K : ℕ} (hN : 2 ≤ N)
    (hK : K ≤ N) :
    (N.choose K - (N - 2).choose K) * (N * (N - 1)) =
      N.choose K * (K * (2 * N - K - 1)) := by
  have havoid := choose_avoid_mul_denominator (N := N) (K := K) hN
  have hnum :
      (N - K) * (N - K - 1) + K * (2 * N - K - 1) =
        N * (N - 1) := by
    by_cases hKN : K = N
    · subst K
      have hself : 2 * N - N - 1 = N - 1 := by omega
      rw [hself]
      simp
    · have hKlt : K < N := lt_of_le_of_ne hK hKN
      have hsplit₁ : N - K - 1 + K = N - 1 := by omega
      have hsplit₂ : 2 * N - K - 1 = (N - K) + (N - 1) := by omega
      rw [hsplit₂]
      calc
        (N - K) * (N - K - 1) + K * ((N - K) + (N - 1)) =
            (N - K) * ((N - K - 1) + K) + K * (N - 1) := by ring
        _ = (N - K) * (N - 1) + K * (N - 1) := by rw [hsplit₁]
        _ = ((N - K) + K) * (N - 1) := by ring
        _ = N * (N - 1) := by rw [Nat.sub_add_cancel hK]
  rw [Nat.sub_mul, havoid, ← Nat.mul_sub_left_distrib]
  congr 1
  omega

/-! ## A subset attaining the deterministic average -/

section Averaging

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Some `K`-set meets the FNV fraction of all edges.  This is the natural-number
form of
`e * K/N * (2 - (K-1)/(N-1)) ≤ incidentEdges`; its denominators are cleared.

The proof is deterministic: it sums over the finite set of all `K`-subsets
and selects one with maximal incident-edge count. -/
theorem exists_subset_incidentEdges_fnv {K : ℕ}
    (hK : K ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = K ∧
      G.edgeFinset.card *
          (K * (2 * Fintype.card V - K - 1)) ≤
        (incidentEdges G A).card *
          (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  let N := Fintype.card V
  obtain ⟨A, hAcard, haverage⟩ :=
    exists_subset_incidentEdges_average (G := G) hK
  refine ⟨A, hAcard, ?_⟩
  by_cases hN : 2 ≤ N
  · have hid := choose_incident_mul_denominator (N := N) (K := K) hN hK
    have hscaled := Nat.mul_le_mul_right (N * (N - 1)) haverage
    have hchoose : 0 < N.choose K := Nat.choose_pos hK
    dsimp [N] at hid hscaled hchoose ⊢
    rw [mul_assoc, hid] at hscaled
    apply le_of_mul_le_mul_left (a := (Fintype.card V).choose K) ?_ hchoose
    calc
      (Fintype.card V).choose K *
          (G.edgeFinset.card * (K * (2 * Fintype.card V - K - 1))) =
        G.edgeFinset.card *
          ((Fintype.card V).choose K * (K * (2 * Fintype.card V - K - 1))) := by
            ring
      _ ≤ (Fintype.card V).choose K * (incidentEdges G A).card *
          (Fintype.card V * (Fintype.card V - 1)) := hscaled
      _ = (Fintype.card V).choose K *
          ((incidentEdges G A).card *
            (Fintype.card V * (Fintype.card V - 1))) := by ring
  · have hcard : Fintype.card V ≤ 1 := by omega
    have hedge : G.edgeFinset.card = 0 := by
      have hedgeBound := G.card_edgeFinset_le_card_choose_two
      have hchooseTwo : (Fintype.card V).choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      omega
    simp [hedge]

/-- The same conclusion in the literal rational form used in the paper. -/
theorem exists_subset_incidentEdges_fnv_rat {K : ℕ}
    (hN : 2 ≤ Fintype.card V) (hK : K ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = K ∧
      (G.edgeFinset.card : ℚ) * (K : ℚ) / (Fintype.card V : ℚ) *
          (2 - ((K : ℚ) - 1) / ((Fintype.card V : ℚ) - 1)) ≤
        ((incidentEdges G A).card : ℚ) := by
  obtain ⟨A, hAcard, hbound⟩ := exists_subset_incidentEdges_fnv (G := G) hK
  refine ⟨A, hAcard, ?_⟩
  have hcastNum :
      (((2 * Fintype.card V - K - 1 : ℕ) : ℚ)) =
        2 * (Fintype.card V : ℚ) - (K : ℚ) - 1 := by
    calc
      (((2 * Fintype.card V - K - 1 : ℕ) : ℚ)) =
          ((2 * Fintype.card V - K : ℕ) : ℚ) - 1 := by
            exact Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card V - K)
      _ = ((2 * Fintype.card V : ℕ) : ℚ) - (K : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : K ≤ 2 * Fintype.card V)]
      _ = 2 * (Fintype.card V : ℚ) - (K : ℚ) - 1 := by norm_num
  have hboundQ :
      (G.edgeFinset.card : ℚ) *
          ((K : ℚ) * (((2 * Fintype.card V - K - 1 : ℕ) : ℚ))) ≤
        ((incidentEdges G A).card : ℚ) *
          ((Fintype.card V : ℚ) * (((Fintype.card V - 1 : ℕ) : ℚ))) := by
    exact_mod_cast hbound
  rw [hcastNum, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at hboundQ
  norm_num at hboundQ
  have hNQ : (0 : ℚ) < (Fintype.card V : ℚ) := by positivity
  have hNsubQ : (0 : ℚ) < (Fintype.card V : ℚ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < Fintype.card V by omega)
  rw [show
      (G.edgeFinset.card : ℚ) * (K : ℚ) / (Fintype.card V : ℚ) *
          (2 - ((K : ℚ) - 1) / ((Fintype.card V : ℚ) - 1)) =
        ((G.edgeFinset.card : ℚ) * (K : ℚ) *
            (2 * (Fintype.card V : ℚ) - (K : ℚ) - 1)) /
          ((Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1)) by
        field_simp [ne_of_gt hNQ, ne_of_gt hNsubQ]
        ring]
  exact (div_le_iff₀ (mul_pos hNQ hNsubQ)).2 (by nlinarith)

/-! ## Transfer to the exact duplication edge count -/

/-- For the averaging set, every choice of orientation gives a duplicated graph
whose exact edge count satisfies the cleared FNV lower bound. -/
theorem exists_subset_duplication_edge_bound {K : ℕ}
    (hK : K ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = K ∧
      ∀ (O : Orientation G A) [DecidableRel O.Dir],
        G.edgeFinset.card *
            (Fintype.card V * (Fintype.card V - 1) +
              K * (2 * Fintype.card V - K - 1)) ≤
          (duplication G A O).edgeFinset.card *
            (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  obtain ⟨A, hAcard, hinc⟩ := exists_subset_incidentEdges_fnv (G := G) hK
  refine ⟨A, hAcard, fun O _ ↦ ?_⟩
  rw [card_edgeFinset_duplication (G := G) (A := A) (O := O)]
  nlinarith

end Averaging

end FNV

end Erdos59
