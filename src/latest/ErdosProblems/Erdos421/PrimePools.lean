import ErdosProblems.Erdos421.PrimeAvoidance
import Mathlib.NumberTheory.Bertrand

/-! # Finite prime pools from Bertrand's postulate

The interval expands by a degree-dependent constant. No asymptotic
prime-counting theorem is needed to construct these pools.
-/

namespace Erdos421

theorem exists_prime_pool (M r : ℕ) (hM : 0 < M) :
    ∃ S : Finset ℕ, S.card = r ∧ ∀ p ∈ S, p.Prime ∧ M < p ∧ p ≤ 2 ^ r * M := by
  classical
  have hex (i : Fin r) : ∃ p : ℕ, p.Prime ∧ 2 ^ (i : ℕ) * M < p ∧
      p ≤ 2 * (2 ^ (i : ℕ) * M) :=
    Nat.exists_prime_lt_and_le_two_mul _ (Nat.mul_pos (pow_pos (by decide) _) hM).ne'
  choose P hP hlo hhi using hex
  have hmono : StrictMono P := by
    intro i j hij
    calc
      P i ≤ 2 * (2 ^ (i : ℕ) * M) := hhi i
      _ = 2 ^ ((i : ℕ) + 1) * M := by rw [pow_succ]; ring
      _ ≤ 2 ^ (j : ℕ) * M :=
        Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hij))
      _ < P j := hlo j
  refine ⟨Finset.univ.image P, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨hP i, ?_, ?_⟩
    · apply lt_of_le_of_lt _ (hlo i)
      exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
    · calc
        P i ≤ 2 * (2 ^ (i : ℕ) * M) := hhi i
        _ = 2 ^ ((i : ℕ) + 1) * M := by rw [pow_succ]; ring
        _ ≤ 2 ^ r * M :=
          Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt i.isLt))

theorem exists_prime_distinct_residues_in_interval {n N M r : ℕ} (hM : 0 < M)
    (x y : Fin n → ℕ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxN : ∀ i, x i ≤ N) (hyN : ∀ i, y i ≤ N)
    (hbound : N ^ (2 * (n * (n - 1))) < M ^ r) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ r * M ∧
      Function.Injective (fun i ↦ (x i : ZMod p)) ∧
        Function.Injective (fun i ↦ (y i : ZMod p)) := by
  obtain ⟨S, hcard, hS⟩ := exists_prime_pool M r hM
  have hprod : M ^ r ≤ ∏ p ∈ S, p := by
    calc
      M ^ r = ∏ _p ∈ S, M := by rw [Finset.prod_const, hcard]
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun p hp ↦ (hS p hp).2.1.le)
  obtain ⟨p, hp, hxyp⟩ := exists_prime_distinct_tuple_residues x y hx hy hxN hyN S
    (fun p hp ↦ (hS p hp).1) (hbound.trans_le hprod)
  exact ⟨p, (hS p hp).1, (hS p hp).2.1, (hS p hp).2.2, hxyp⟩

theorem root_scale_prime_pool_bound {n N M : ℕ}
    (hn : 0 < n) (hM : 1 < M) (hN : N ≤ M ^ n) :
    N ^ (2 * (n * (n - 1))) < M ^ (2 * n ^ 3) := by
  have he : n * (2 * (n * (n - 1))) < 2 * n ^ 3 := by
    have hid : n * (2 * (n * (n - 1))) + 2 * n ^ 2 = 2 * n ^ 3 := by
      calc
        _ = 2 * n * n * (n - 1 + 1) := by ring
        _ = 2 * n ^ 3 := by rw [Nat.sub_add_cancel hn]; ring
    have hp : 0 < 2 * n ^ 2 := Nat.mul_pos (by decide) (pow_pos hn _)
    omega
  calc
    _ ≤ (M ^ n) ^ (2 * (n * (n - 1))) := Nat.pow_le_pow_left hN _
    _ = M ^ (n * (2 * (n * (n - 1)))) := (pow_mul _ _ _).symm
    _ < M ^ (2 * n ^ 3) := pow_lt_pow_right₀ hM he

theorem exists_prime_distinct_residues_at_root_scale {n N M : ℕ}
    (hn : 0 < n) (hM : 1 < M) (hN : N ≤ M ^ n)
    (x y : Fin n → ℕ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxN : ∀ i, x i ≤ N) (hyN : ∀ i, y i ≤ N) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ (2 * n ^ 3) * M ∧ N < p ^ n ∧
      Function.Injective (fun i ↦ (x i : ZMod p)) ∧
        Function.Injective (fun i ↦ (y i : ZMod p)) := by
  have hb := root_scale_prime_pool_bound hn hM hN
  obtain ⟨p, hp, hMp, hup, hxyp⟩ := exists_prime_distinct_residues_in_interval
    (Nat.zero_lt_of_lt hM) x y hx hy hxN hyN hb
  refine ⟨p, hp, hMp, hup, hN.trans_lt ?_, hxyp⟩
  exact Nat.pow_lt_pow_left hMp hn.ne'

end Erdos421
