import ErdosProblems.Erdos421.RepeatedMoments
import ErdosProblems.Erdos421.VinogradovMoments

/-! # Repeated-coordinate counts for the actual integer equations -/

namespace Erdos421

def repeatTuple {X : Type*} {n : ℕ} (x : (Fin n → X) × X) : Fin (n + 2) → X :=
  Fin.append x.1 (fun _ : Fin 2 ↦ x.2)

theorem sum_repeatTuple {X G : Type*} [AddCommMonoid G] {n : ℕ}
    (f : X → G) (x : (Fin n → X) × X) :
    (∑ i : Fin (n + 2), f (repeatTuple x i)) = (∑ i : Fin n, f (x.1 i)) + f x.2 + f x.2 := by
  rw [Fin.sum_univ_add]
  simp only [repeatTuple, Fin.append_left, Fin.append_right, Fin.sum_univ_two, add_assoc]

def repeatedIntegerCount (n k N : ℕ) : ℕ :=
  ((Finset.univ : Finset (((Fin n → Fin N) × Fin N) × (Fin (n + 2) → Fin N))).filter
    (fun p ↦ vinogradovSums k (repeatTuple p.1) = vinogradovSums k p.2)).card

theorem repeatedCongruenceCount_eq_integer {n k N q : ℕ} [NeZero q]
    (hq : (n + 2) * (N + 1) ^ k < q) :
    repeatedCongruenceCount (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) n =
      repeatedIntegerCount n k N := by
  unfold repeatedCongruenceCount repeatedIntegerCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← sum_repeatTuple]
  exact vinogradov_residue_sums_eq_iff hq (repeatTuple p.1) p.2

theorem repeatedIntegerCount_le_moment (n k N : ℕ) {B : ℝ} (hB : 0 < B)
    (hJ : (vinogradovCount (n + 2) k N : ℝ) ≤ B ^ (2 * (n + 2))) :
    (repeatedIntegerCount n k N : ℝ) ≤ B ^ (2 * n + 3) := by
  let q := 2 * ((n + 2) * (N + 1) ^ k) + 1
  have hqpos : 0 < q := by dsimp only [q]; omega
  let : NeZero q := ⟨hqpos.ne'⟩
  have hq : (n + 2) * (N + 1) ^ k < q := by dsimp only [q]; omega
  have h2 : IsUnit (2 : ZMod q) := by
    apply (ZMod.isUnit_iff_coprime 2 q).mpr
    apply Nat.coprime_two_left.mpr
    exact odd_two_mul_add_one _
  have hfm : (∑ a : Fin k → ZMod q, ‖vinogradovWeylSum q k N a‖ ^ (2 * (n + 2))) ≤
      (q : ℝ) ^ k * B ^ (2 * (n + 2)) := by
    rw [vinogradovWeylSum_moment hq]
    exact mul_le_mul_of_nonneg_left hJ (pow_nonneg (Nat.cast_nonneg q) _)
  have h := repeatedCongruenceCount_le_moment
    (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) n h2 hB hfm
  rwa [repeatedCongruenceCount_eq_integer hq] at h

theorem exists_vinogradov_moment_scale {s N : ℕ} (hs : 0 < s) (hN : 0 < N) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ B ^ (2 * s) = (vinogradovCount s k N : ℝ) ∧ (N : ℝ) ≤ B ^ 2 := by
  have hJ : (0 : ℝ) < (vinogradovCount s k N : ℝ) := by
    exact_mod_cast (pow_pos hN s).trans_le (pow_le_vinogradovCount s k N)
  have he : (2 * s : ℕ) ≠ 0 := Nat.mul_ne_zero (by decide) hs.ne'
  let B := (vinogradovCount s k N : ℝ) ^ (1 / ((2 * s : ℕ) : ℝ))
  have hB : 0 < B := Real.rpow_pos_of_pos hJ _
  have hpower : B ^ (2 * s) = (vinogradovCount s k N : ℝ) := by
    dsimp only [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ.le,
      one_div_mul_cancel (Nat.cast_ne_zero.mpr he), Real.rpow_one]
  refine ⟨B, hB, hpower, ?_⟩
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg N) (sq_nonneg B) hs.ne').mp
  rw [← pow_mul, hpower]
  exact_mod_cast pow_le_vinogradovCount s k N

/-- If solutions with one specified repeated coordinate dominate, the
interval must be small. All counts in the hypothesis are the actual
integer counts; no mean-value theorem is an input. -/
theorem repeatedInteger_dominance_forces_small_interval (n k N : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hdom : (vinogradovCount (n + 2) k N : ℝ) ≤ C * (repeatedIntegerCount n k N : ℝ)) :
    (N : ℝ) ≤ C ^ 2 := by
  by_cases hN : N = 0
  · simp only [hN, Nat.cast_zero]
    exact sq_nonneg C
  obtain ⟨B, hB, hpower, hNB⟩ := exists_vinogradov_moment_scale
    (by omega : 0 < n + 2) (Nat.pos_of_ne_zero hN) k
  have hrep := repeatedIntegerCount_le_moment n k N hB hpower.ge
  have hBC : B ≤ C := by
    have hm : B ^ (2 * n + 3) * B ≤ B ^ (2 * n + 3) * C := by
      calc
        _ = B ^ (2 * (n + 2)) := by rw [← pow_succ]; congr 1
        _ = (vinogradovCount (n + 2) k N : ℝ) := hpower
        _ ≤ C * (repeatedIntegerCount n k N : ℝ) := hdom
        _ ≤ C * B ^ (2 * n + 3) := mul_le_mul_of_nonneg_left hrep hC
        _ = _ := mul_comm _ _
    exact (mul_le_mul_iff_right₀ (pow_pos hB _)).mp hm
  exact hNB.trans (pow_le_pow_left₀ hB.le hBC 2)

end Erdos421
