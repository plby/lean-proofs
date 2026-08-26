import ErdosProblems.Erdos421.VectorCharacters
import ErdosProblems.Erdos421.VinogradovCounts

/-! # Exact finite Fourier moments for the integer power-sum equations

Choosing a modulus larger than every power sum prevents wraparound.
The resulting moment is the integer solution count, not a relaxation
to a congruence system.
-/

namespace Erdos421

def vinogradovPhasePoint (q k : ℕ) {N : ℕ} (x : Fin N) : Fin k → ZMod q :=
  fun j ↦ ((x : ZMod q) + 1) ^ ((j : ℕ) + 1)

noncomputable def vinogradovWeylSum (q k N : ℕ) [NeZero q] (a : Fin k → ZMod q) : ℂ :=
  vectorCharacterSum Finset.univ (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) a

theorem vinogradov_nat_sum_lt {s k N q : ℕ} (hq : s * (N + 1) ^ k < q)
    (x : Fin s → Fin N) (j : Fin k) :
    (∑ i : Fin s, ((x i : ℕ) + 1) ^ ((j : ℕ) + 1)) < q := by
  calc
    _ ≤ ∑ _i : Fin s, (N + 1) ^ k := by
      apply Finset.sum_le_sum
      intro i _
      exact (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_of_lt (x i).isLt) 1) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.succ_le_of_lt j.isLt))
    _ = s * (N + 1) ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ < q := hq

theorem vinogradov_residue_sums_eq_iff {s k N q : ℕ} (hq : s * (N + 1) ^ k < q)
    (x y : Fin s → Fin N) :
    (∑ i : Fin s, vinogradovPhasePoint q k (x i)) =
      (∑ i : Fin s, vinogradovPhasePoint q k (y i)) ↔
        vinogradovSums k x = vinogradovSums k y := by
  have hz (z : Fin s → Fin N) (j : Fin k) :
      (∑ i : Fin s, vinogradovPhasePoint q k (z i)) j =
        ((∑ i : Fin s, ((z i : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ) : ZMod q) := by
    simp only [Finset.sum_apply, vinogradovPhasePoint, Nat.cast_sum, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one]
  constructor
  · intro h
    funext j
    have he := congrFun h j
    rw [hz x j, hz y j] at he
    have hn := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (vinogradov_nat_sum_lt hq x j),
      ZMod.val_natCast_of_lt (vinogradov_nat_sum_lt hq y j)] at hn
    change (∑ i : Fin s, ((x i : ℤ) + 1) ^ ((j : ℕ) + 1)) =
      ∑ i : Fin s, ((y i : ℤ) + 1) ^ ((j : ℕ) + 1)
    exact_mod_cast hn
  · intro h
    funext j
    rw [hz x j, hz y j]
    have hn : (∑ i : Fin s, ((x i : ℕ) + 1) ^ ((j : ℕ) + 1)) =
        ∑ i : Fin s, ((y i : ℕ) + 1) ^ ((j : ℕ) + 1) := by
      have he := congrFun h j
      simp only [vinogradovSums] at he
      exact_mod_cast he
    rw [hn]

theorem vinogradovWeylSum_moment {s k N q : ℕ} [NeZero q]
    (hq : s * (N + 1) ^ k < q) :
    (∑ a : Fin k → ZMod q, ‖vinogradovWeylSum q k N a‖ ^ (2 * s)) =
      (q : ℝ) ^ k * (vinogradovCount s k N : ℝ) := by
  have h := vectorCharacterSum_moment (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) s
  have hset : (Finset.univ : Finset ((Fin s → Fin N) × (Fin s → Fin N))).filter
      (fun p ↦ (∑ i : Fin s, vinogradovPhasePoint q k (p.1 i)) =
        ∑ i : Fin s, vinogradovPhasePoint q k (p.2 i)) = vinogradovSolutions s k N 0 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vinogradovSolutions, sub_eq_zero]
    exact vinogradov_residue_sums_eq_iff hq p.1 p.2
  rw [hset] at h
  exact h

end Erdos421
