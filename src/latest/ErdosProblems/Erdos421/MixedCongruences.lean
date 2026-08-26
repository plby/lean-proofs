import ErdosProblems.Erdos421.PowerSumFibers
import ErdosProblems.Erdos421.PrimePowerTuples
import ErdosProblems.Erdos421.ResidueFibers

/-! # Nonsingular power-sum systems with different prime-power moduli

Each coordinate is lifted to the common modulus `p^d`. Its number of
lifts is exact, and every full power-sum fiber contains at most `n!`
tuples when the entries are distinct modulo `p`.
-/

namespace Erdos421

theorem primePower_vector_fiber_card_le {p d n : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hn : n < p) (S : Finset (Fin n → ZMod (p ^ d))) (v : Fin n → ZMod (p ^ d))
    (hS : ∀ x ∈ S, Function.Injective (fun i ↦ primePowerReduction p d hd (x i))) :
    (S.filter (fun x ↦ powerSumVector n x = v)).card ≤ n.factorial := by
  classical
  by_cases hne : (S.filter (fun x ↦ powerSumVector n x = v)).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hsub : S.filter (fun x ↦ powerSumVector n x = v) ⊆
        S.filter (fun x : Fin n → ZMod (p ^ d) ↦ ∀ k : ℕ, 0 < k → k ≤ n →
          (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
      apply (powerSumVector_eq_iff x y).mp
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    exact (Finset.card_le_card hsub).trans
      (primePower_power_sum_fiber_card_le hp hd hn S y (hS y (Finset.mem_filter.mp hy).1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

theorem primePower_mixed_power_sum_card_le {p d n : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hn : n < p) (S : Finset (Fin n → ZMod (p ^ d)))
    (hS : ∀ x ∈ S, Function.Injective (fun i ↦ primePowerReduction p d hd (x i)))
    (e : Fin n → ℕ) (he : ∀ j, e j ≤ d) (w : ∀ j : Fin n, ZMod (p ^ e j)) :
    (S.filter (fun x ↦ ∀ j : Fin n, primePowerCast p d (e j) (he j)
      (powerSumVector n x j) = w j)).card ≤
      n.factorial * p ^ (Finset.univ.sum (fun j : Fin n ↦ d - e j)) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let T := S.filter (fun x ↦ ∀ j : Fin n, primePowerCast p d (e j) (he j)
    (powerSumVector n x j) = w j)
  let U : Finset (Fin n → ZMod (p ^ d)) := Fintype.piFinset (fun j ↦
    Finset.univ.filter (fun a ↦ primePowerCast p d (e j) (he j) a = w j))
  have hmap : ∀ x ∈ T, powerSumVector n x ∈ U := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun j ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2 j⟩)
  have hfiber : ∀ v ∈ U, (T.filter (fun x ↦ powerSumVector n x = v)).card ≤ n.factorial := by
    intro v _
    apply primePower_vector_fiber_card_le hp hd hn
    intro x hx
    exact hS x (Finset.mem_filter.mp hx).1
  have hcard : U.card = p ^ (Finset.univ.sum (fun j : Fin n ↦ d - e j)) := by
    simp only [U, Fintype.card_piFinset, primePowerCast_fiber_card,
      Finset.prod_pow_eq_pow_sum]
  calc
    T.card = ∑ v ∈ U, (T.filter (fun x ↦ powerSumVector n x = v)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _v ∈ U, n.factorial := Finset.sum_le_sum hfiber
    _ = n.factorial * p ^ (Finset.univ.sum (fun j : Fin n ↦ d - e j)) := by
      rw [Finset.sum_const, smul_eq_mul, hcard, mul_comm]

theorem sum_fin_complement (n : ℕ) :
    (Finset.univ.sum (fun j : Fin n ↦ n - ((j : ℕ) + 1))) = n * (n - 1) / 2 := by
  calc
    _ = ∑ j : Fin n, (j.rev : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_rev]
    _ = ∑ j : Fin n, (j : ℕ) :=
      Equiv.sum_comp Fin.revPerm (fun j : Fin n ↦ (j : ℕ))
    _ = ∑ j ∈ Finset.range n, j := Fin.sum_univ_eq_sum_range (fun j ↦ j) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

/-- The complete system has moduli `p,p²,...,pⁿ`; after lifting every
coordinate to `pⁿ`, the total number of lifts is `p^(n(n-1)/2)`. -/
theorem primePower_complete_congruence_card_le {p n : ℕ} (hp : p.Prime) (hn0 : 0 < n)
    (hn : n < p) (S : Finset (Fin n → ZMod (p ^ n)))
    (hS : ∀ x ∈ S, Function.Injective (fun i ↦ primePowerReduction p n hn0 (x i)))
    (w : ∀ j : Fin n, ZMod (p ^ ((j : ℕ) + 1))) :
    (S.filter (fun x ↦ ∀ j : Fin n,
      primePowerCast p n ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
        (powerSumVector n x j) = w j)).card ≤ n.factorial * p ^ (n * (n - 1) / 2) := by
  simpa only [sum_fin_complement] using primePower_mixed_power_sum_card_le hp hn0 hn S hS
    (fun j ↦ (j : ℕ) + 1) (fun j ↦ Nat.succ_le_of_lt j.isLt) w

end Erdos421
