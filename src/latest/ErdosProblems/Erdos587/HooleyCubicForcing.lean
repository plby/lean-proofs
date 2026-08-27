import ErdosProblems.Erdos587.HooleyStructuralTerminal
import ErdosProblems.Erdos587.HooleyStructuralCardinality
import ErdosProblems.Erdos587.NaturalSubsetBridge
import ErdosProblems.Erdos587.CubicBudgets

/-! # One cubic log-log surplus forces a square in the full-width structure -/

namespace Erdos587

theorem exists_delta_cubic_structural_forcing (R d F C : ℕ)
    (hR : 0 < R) (hF : 0 < F) (hC : 0 < C) :
    ∃ E : ℕ, 0 < E ∧ ∃ Tmin : ℝ,
      ∀ (A : Finset ℕ) (N m : ℕ) (Q : GeneralizedAP) (Λ : ℝ),
        A ⊆ Finset.Icc 1 N → 0 < N → 0 < m → A.card ≤ R * m →
        0 < Q.rank → Q.rank ≤ d → Q.Proper → Q.HasHomogeneousBase →
        Q.carrier ⊆ natToIntFinset A.subsetSum →
        (∀ i, m ≤ F * Q.length i) →
        m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card →
        (Q.upperEndpoint : ℝ) ≤ (C : ℝ) * Q.coefficientSpan →
        1 ≤ Λ → max 1 (Real.log (Real.log ((R * m * N : ℕ) : ℝ))) ≤ Λ →
        (F : ℝ) * Tmin ≤ m → (E : ℝ) * N * Λ ^ 44 ≤ (m : ℝ) ^ 3 →
        ¬ SquareSubsetSumFree A := by
  let D := 8 * F ^ 2
  let E := F ^ 4 * R + 16 * D ^ 2 * R + 4 * F ^ d * R + 1
  obtain ⟨Tmin, hterminal⟩ := exists_delta_structural_terminal (C : ℝ) (by exact_mod_cast hC)
  refine ⟨E, Nat.succ_pos _, Tmin, ?_⟩
  intro A N m Q Λ hA hN hm hretain hQpos hQrank hQproper hQhom hQsub
    hside hsize hheight hΛ hlog hmin hsurplus
  have hV₀ : Q.carrier.card ≤ A.card * N + 1 := by
    have hsum : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
      NVGeneration.subsetSum_subset_Icc_of_subset (Finset.Subset.refl A) hA (by simp)
    calc
      Q.carrier.card ≤ (natToIntFinset A.subsetSum).card := Finset.card_le_card hQsub
      _ = A.subsetSum.card := card_natToIntFinset _
      _ ≤ (Finset.Icc 0 (A.card * N)).card := Finset.card_le_card hsum
      _ = A.card * N + 1 := by simp
  have hV : Q.carrier.card ≤ (2 * R) * m * N := by
    have hmul := Nat.mul_le_mul_right N hretain
    have hpos : 0 < R * m * N := Nat.mul_pos (Nat.mul_pos hR hm) hN
    nlinarith
  have hEside : F ^ 4 * R ≤ E := by dsimp only [E]; omega
  have hEone : 16 * D ^ 2 * R ≤ E := by dsimp only [E]; omega
  have hErank : 4 * F ^ d * R < E := by dsimp only [E]; omega
  have hEpos : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hΛpow : (1 : ℝ) ≤ Λ ^ 44 := one_le_pow₀ hΛ
  have hEbasic : (E : ℝ) * N ≤ (m : ℝ) ^ 3 :=
    (le_mul_of_one_le_right (mul_nonneg hEpos (Nat.cast_nonneg N)) hΛpow).trans hsurplus
  have hrankLarge : 2 * F ^ d * (2 * R) * N < m ^ 3 := by
    have hstrict : ((4 * F ^ d * R : ℕ) : ℝ) * N < (m : ℝ) ^ 3 :=
      (mul_lt_mul_of_pos_right (by exact_mod_cast hErank) (by exact_mod_cast hN)).trans_le hEbasic
    have hnat : 4 * F ^ d * R * N < m ^ 3 := by exact_mod_cast hstrict
    nlinarith only [hnat]
  have hrankTwo := CFP.delta_rank_le_two_of_cardinality hm hF hQrank hsize hV hrankLarge
  have hQsub' : Q.carrier ⊆ (natToIntFinset A).subsetSum := by
    rwa [subsetSum_natToIntFinset]
  have hupper := Q.upperEndpoint_le_interval_budget (natToIntFinset A) N (R * m)
    (natToIntFinset_subset_Icc hA) (by simpa only [card_natToIntFinset] using hretain) hQsub'
  have hD : (1 : ℝ) ≤ D := by
    have hDpos : 0 < D := by dsimp only [D]; positivity
    exact_mod_cast hDpos
  obtain ⟨hsideBudget, hareaBudget, honeBudget⟩ := terminal_budgets_of_cubic_surplus 11
    (show (0 : ℝ) ≤ m by positivity) (show (0 : ℝ) ≤ N by positivity)
    (show (0 : ℝ) ≤ R by positivity) (show (0 : ℝ) ≤ F by positivity) hD hΛ
    (by exact_mod_cast hEside) (by exact_mod_cast hEone) hsurplus
  apply hterminal A Q m F (R * m * N) Λ hQpos hrankTwo hQproper hQhom hQsub hm hF
    hside hsize hupper hheight hΛ hlog hmin
  · simpa only [Nat.cast_mul] using hsideBudget
  · simpa only [D, Nat.cast_mul] using hareaBudget
  · simpa only [D, Nat.cast_mul] using honeBudget

end Erdos587
