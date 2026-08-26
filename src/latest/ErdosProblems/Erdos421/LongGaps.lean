import ErdosProblems.Erdos421.Greedy

/-!
# Converting prime-free starts into a bound on gap lengths

This is the finite combinatorial part of the long-gap argument. The estimate
for the number of exceptional starting points is not assumed or proved here.
-/

namespace Erdos421

theorem not_prime_between {k n : ℕ} (hlo : prime k < n) (hhi : n < prime (k + 1)) :
    ¬ n.Prime := by
  intro hn
  have heq : prime (Nat.count Nat.Prime n) = n := Nat.nth_count hn
  have hklo : k < Nat.count Nat.Prime n := by
    apply prime_strictMono.lt_iff_lt.mp
    rwa [heq]
  have hkhi : Nat.count Nat.Prime n < k + 1 := by
    apply prime_strictMono.lt_iff_lt.mp
    rwa [heq]
  omega

/-- Integer starts below `B` for which the closed interval of radius `H` has no prime. -/
def primeFreeStarts (B H : ℕ) : Finset ℕ :=
  (Finset.range B).filter (fun a ↦ ∀ p ∈ Finset.Icc a (a + H), ¬ p.Prime)

/-- Starts whose entire closed interval stays strictly inside the `k`th prime gap. -/
noncomputable def safeStarts (k H : ℕ) : Finset ℕ :=
  Finset.Icc (prime k + 1) (prime (k + 1) - H - 1)

theorem safeStarts_bounds {k H a : ℕ} (ha : a ∈ safeStarts k H) :
    prime k < a ∧ a + H < prime (k + 1) := by
  have h := Finset.mem_Icc.mp ha
  have hp := (prime_prime k).two_le
  omega

theorem safeStarts_subset_primeFreeStarts {k H B : ℕ} (hB : prime (k + 1) ≤ B) :
    safeStarts k H ⊆ primeFreeStarts B H := by
  intro a ha
  obtain ⟨hlo, hhi⟩ := safeStarts_bounds ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  intro p hp
  obtain ⟨hap, hpaH⟩ := Finset.mem_Icc.mp hp
  exact not_prime_between (hlo.trans_le hap) (hpaH.trans_lt hhi)

theorem safeStarts_disjoint {i j H : ℕ} (hij : i ≠ j) :
    Disjoint (safeStarts i H) (safeStarts j H) := by
  apply Finset.disjoint_left.mpr
  intro a hai haj
  obtain ⟨hilo, hihi⟩ := safeStarts_bounds hai
  obtain ⟨hjlo, hjhi⟩ := safeStarts_bounds haj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := prime_strictMono.monotone (show i + 1 ≤ j from hij)
    omega
  · have h := prime_strictMono.monotone (show j + 1 ≤ i from hji)
    omega

/-- A gap at least twice the trimmed boundary loss supplies half its length in safe starts. -/
theorem gapLength_le_two_mul_safeStarts_card {k H : ℕ}
    (hlong : 2 * (H + 1) ≤ prime (k + 1) - prime k) :
    prime (k + 1) - prime k ≤ 2 * (safeStarts k H).card := by
  rw [safeStarts, Nat.card_Icc]
  omega

/-- Disjoint long prime gaps are charged to distinct prime-free starting integers. -/
theorem sum_long_gap_lengths_le (I : Finset ℕ) (B H : ℕ)
    (hB : ∀ k ∈ I, prime (k + 1) ≤ B)
    (hlong : ∀ k ∈ I, 2 * (H + 1) ≤ prime (k + 1) - prime k) :
    (∑ k ∈ I, (prime (k + 1) - prime k)) ≤ 2 * (primeFreeStarts B H).card := by
  classical
  have hdisj : (↑I : Set ℕ).Pairwise (fun i j ↦ Disjoint (safeStarts i H) (safeStarts j H)) :=
    fun _ _ _ _ hij ↦ safeStarts_disjoint hij
  have hsub : I.biUnion (fun k ↦ safeStarts k H) ⊆ primeFreeStarts B H := by
    intro a ha
    obtain ⟨k, hk, ha⟩ := Finset.mem_biUnion.mp ha
    exact safeStarts_subset_primeFreeStarts (hB k hk) ha
  calc
    (∑ k ∈ I, (prime (k + 1) - prime k)) ≤ ∑ k ∈ I, 2 * (safeStarts k H).card :=
      Finset.sum_le_sum (fun k hk ↦ gapLength_le_two_mul_safeStarts_card (hlong k hk))
    _ = 2 * (I.biUnion (fun k ↦ safeStarts k H)).card := by
      rw [Finset.card_biUnion hdisj, Finset.mul_sum]
    _ ≤ 2 * (primeFreeStarts B H).card := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)

end Erdos421
