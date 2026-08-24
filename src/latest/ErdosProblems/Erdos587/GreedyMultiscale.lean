import ErdosProblems.Erdos587.GreedyDensity

/-!
Multiscale greedy density. Once high-fold cardinalities have uniformly
bounded doubling, each successive density threshold costs only a constant
multiple of its fold count. Summing the dyadic costs removes the previous
logarithmic loss in the size of the selected subset.
-/

open scoped Pointwise

namespace Erdos587.CFP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem greedySubset_next_density (A : Finset G) (h K T₀ T₁ a r : ℕ)
    (hh : 0 < h) (hstart : T₀ ≤ 4 * (greedySubset A a).subsetSum.card)
    (hratio : T₁ ≤ K * T₀) (hbudget : a + (2 * h) * K ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * T₁ < 4 * (h • insert 0 D).card) :
    T₁ ≤ 4 * (greedySubset A (a + (2 * h) * K)).subsetSum.card := by
  by_contra hnot
  have hlast : 4 * (greedySubset A (a + (2 * h) * K)).subsetSum.card < T₁ :=
    lt_of_not_ge hnot
  have hsteps (j : ℕ) (hj : j < (2 * h) * K) :
      (((2 * h : ℕ) : ℝ) + 1) * ((greedySubset A (a + j)).subsetSum.card : ℝ) ≤
        (2 * h : ℕ) * ((greedySubset A (a + j + 1)).subsetSum.card : ℝ) := by
    have hsub := greedySubset_subset A (a + j)
    have hcard := card_greedySubset_le A (a + j)
    have hcardA := Finset.card_le_card hsub
    have hcost : A.card ≤ (A \ greedySubset A (a + j)).card + r := by
      rw [Finset.card_sdiff_of_subset hsub]
      omega
    have hd := hdense (A \ greedySubset A (a + j)) Finset.sdiff_subset hcost
    have hmono := greedySubset_card_mono A (show a + j ≤ a + (2 * h) * K by omega)
    have hlarge : 2 * (greedySubset A (a + j)).subsetSum.card ≤
        (h • insert 0 (A \ greedySubset A (a + j))).card := by nlinarith
    exact_mod_cast greedySubset_growth A (a + j) h hlarge
  have hg := growth_interval_linear (greedySubset_real_card_mono A) (2 * h) a
    ((2 * h) * K) hsteps
  have hgN : ((2 * h) * K + 2 * h) * (greedySubset A a).subsetSum.card ≤
      (2 * h) * (greedySubset A (a + (2 * h) * K)).subsetSum.card := by
    exact_mod_cast hg
  have hcancel : (K + 1) * (greedySubset A a).subsetSum.card ≤
      (greedySubset A (a + (2 * h) * K)).subsetSum.card := by
    apply Nat.le_of_mul_le_mul_left (c := 2 * h) _ (by positivity)
    nlinarith [hgN]
  nlinarith

def densitySteps (h K a : ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => densitySteps h K a n + (2 * (2 ^ (n + 1) * h)) * K

theorem densitySteps_le (h K a n : ℕ) :
    densitySteps h K a n ≤ a + 4 * K * (2 ^ n * h) := by
  induction n with
  | zero => simp [densitySteps]
  | succ n ih =>
      calc
        densitySteps h K a (n + 1) ≤
            (a + 4 * K * (2 ^ n * h)) + (2 * (2 ^ (n + 1) * h)) * K :=
          Nat.add_le_add_right ih _
        _ = a + 4 * K * (2 ^ (n + 1) * h) := by rw [pow_succ]; ring

theorem greedySubset_multiscale_density
    (A : Finset G) (h K a n r : ℕ) (T : ℕ → ℕ) (hh : 0 < h)
    (hstart : T 0 ≤ 4 * (greedySubset A a).subsetSum.card)
    (hratio : ∀ j < n, T (j + 1) ≤ K * T j)
    (hbudget : densitySteps h K a n ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card) :
    T n ≤ 4 * (greedySubset A (densitySteps h K a n)).subsetSum.card := by
  induction n with
  | zero => exact hstart
  | succ n ih =>
      have hprev := ih (fun j hj => hratio j (by omega))
        ((Nat.le_add_right _ _).trans hbudget)
        (fun D hDA hcost j hj => hdense D hDA hcost j (by omega))
      exact greedySubset_next_density A (2 ^ (n + 1) * h) K (T n) (T (n + 1))
        (densitySteps h K a n) r (by positivity) hprev (hratio n (by omega)) hbudget
        (fun D hDA hcost => hdense D hDA hcost (n + 1) (by omega))

/-- A linear-size actual subset with constant subset-sum density at the
final fold count. All growth and bounded-deletion hypotheses are explicit. -/
theorem exists_linear_size_dense_subsetSums
    (A : Finset G) (h K n r : ℕ) (T : ℕ → ℕ) (hh : 0 < h)
    (hratio : ∀ j < n, T (j + 1) ≤ K * T j)
    (hinitial : (2 * h) * (Nat.log 2 (T 0) + 1) ≤ 2 ^ n * h)
    (hbudget : (4 * K + 1) * (2 ^ n * h) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card) :
    ∃ S ⊆ A, S.card ≤ (4 * K + 1) * (2 ^ n * h) ∧ T n ≤ 4 * S.subsetSum.card := by
  let a := (2 * h) * (Nat.log 2 (T 0) + 1)
  have htime : densitySteps h K a n ≤ (4 * K + 1) * (2 ^ n * h) := by
    calc
      densitySteps h K a n ≤ a + 4 * K * (2 ^ n * h) := densitySteps_le h K a n
      _ ≤ (2 ^ n * h) + 4 * K * (2 ^ n * h) := Nat.add_le_add_right hinitial _
      _ = (4 * K + 1) * (2 ^ n * h) := by ring
  have habudget : a ≤ r := by
    exact hinitial.trans ((by nlinarith : 2 ^ n * h ≤ (4 * K + 1) * (2 ^ n * h)).trans hbudget)
  have hstart : T 0 ≤ 4 * (greedySubset A a).subsetSum.card := by
    apply (greedySubset_reaches_density A h 4 (T 0) r hh (by omega) habudget ?_).le
    intro D hDA hcost
    simpa only [pow_zero, one_mul] using hdense D hDA hcost 0 (Nat.zero_le _)
  refine ⟨greedySubset A (densitySteps h K a n), greedySubset_subset A _,
    (card_greedySubset_le A _).trans htime, ?_⟩
  exact greedySubset_multiscale_density A h K a n r T hh hstart hratio
    (htime.trans hbudget) hdense

end Erdos587.CFP
