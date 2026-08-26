import ErdosProblems.Erdos421.SplitIntegerCounts
import ErdosProblems.Erdos421.PrimeSolutionSelection

/-! # Selecting a prime and one residue class for the free variables -/

namespace Erdos421

noncomputable def primeDistinctTuples (k N p : ℕ) : Finset (Fin k → Fin N) := by
  classical
  exact Finset.univ.filter (fun x ↦ Function.Injective (fun i ↦ (x i : ZMod p)))

def integerResidueClass (N p : ℕ) (c : ZMod p) : Finset (Fin N) :=
  Finset.univ.filter (fun y ↦ (y : ZMod p) + 1 = c)

theorem primeDistinctSolutions_card_eq_mixed (s k N p : ℕ) :
    (primeDistinctSolutions s k N p).card =
      mixedIntegerCount (primeDistinctTuples k N p) Finset.univ s k := by
  classical
  rw [mixedIntegerCount_univ_card]
  apply congrArg Finset.card
  ext z
  simp only [primeDistinctSolutions, primeDistinctTuples, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem exists_prime_residue_concentration (s k N p : ℕ) [NeZero p] (hs : 0 < s) :
    ∃ c : ZMod p, (primeDistinctSolutions s k N p).card ≤
      p ^ (2 * s) *
        mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k := by
  obtain ⟨c, hc⟩ := exists_mixedIntegerCount_fiber (primeDistinctTuples k N p)
    Finset.univ (fun y : Fin N ↦ (y : ZMod p) + 1) hs
  rw [← primeDistinctSolutions_card_eq_mixed, ZMod.card] at hc
  exact ⟨c, hc⟩

theorem exists_prime_and_residue_at_root_scale (s k N M : ℕ)
    (hks : 2 ≤ k + s) (hk : 0 < k) (hs : 0 < s)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hM : 1 < M) (hNM : N ≤ M ^ k) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ (2 * k ^ 3) * M ∧ N < p ^ k ∧
      ∃ c : ZMod p, vinogradovCount (k + s) k N ≤
        4 * k ^ 3 * p ^ (2 * s) *
          mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k := by
  obtain ⟨p, hp, hMp, hup, hNp, hcount⟩ := exists_prime_many_residue_distinct_at_root_scale
    s k N M hks hk hN hM hNM
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := exists_prime_residue_concentration s k N p hs
  refine ⟨p, hp, hMp, hup, hNp, c, ?_⟩
  calc
    _ ≤ 4 * k ^ 3 * (primeDistinctSolutions s k N p).card := hcount
    _ ≤ 4 * k ^ 3 * (p ^ (2 * s) *
        mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k) :=
      Nat.mul_le_mul_left _ hc
    _ = _ := (mul_assoc _ _ _).symm

end Erdos421
