import Mathlib

/-!
# Elementary asymptotic bookkeeping for Erdős Problem 186

This file contains no combinatorial input.  It packages the two standard
ways of writing an `N ^ (a + o(1))` upper bound for a nonnegative real-valued
sequence, and records the elementary natural-floor estimates used to pass
from Bosznay's fourth-power construction to arbitrary `N`.
-/

open Filter
open scoped Topology

namespace Erdos186

/-! ## Big-O and pointwise bounds -/

/-- For a nonnegative real-valued sequence, a big-O bound by a real power is
equivalent to an eventual pointwise bound with a positive constant. -/
theorem isBigO_nat_rpow_iff_eventually_le {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f n) :
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ a) ↔
      ∃ C > 0, ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) ^ a := by
  constructor
  · intro hO
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
    filter_upwards [hf, hC] with n hfn hn
    rw [Real.norm_of_nonneg hfn,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left C 1)
      (Real.rpow_nonneg (Nat.cast_nonneg n) a))
  · rintro ⟨C, _hC, h⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hf, h] with n hfn hn
    simpa only [Real.norm_of_nonneg hfn,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] using hn

/-- The explicit-threshold form of `isBigO_nat_rpow_iff_eventually_le`. -/
theorem isBigO_nat_rpow_iff_exists_threshold {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ a) ↔
      ∃ C > 0, ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → f n ≤ C * (n : ℝ) ^ a := by
  rw [isBigO_nat_rpow_iff_eventually_le (Eventually.of_forall hf)]
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
    exact ⟨C, hC, N₀, hN₀⟩
  · rintro ⟨C, hC, N₀, hN₀⟩
    exact ⟨C, hC, eventually_atTop.mpr ⟨N₀, hN₀⟩⟩

/-- An eventual pointwise bound with coefficient one gives the corresponding
big-O bound. -/
theorem isBigO_nat_rpow_of_eventually_le {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ a) :
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ a) := by
  apply (isBigO_nat_rpow_iff_eventually_le hf).mpr
  exact ⟨1, zero_lt_one, by simpa using h⟩

/-- Positive real powers of the natural-number variable tend to infinity. -/
theorem nat_rpow_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop

/-- The coefficient-free eventual formulation of `N ^ (a + o(1))` is
equivalent to requiring a big-O estimate for every positive epsilon.

The reverse implication absorbs the big-O constant into `N ^ (ε / 2)`. -/
theorem eventually_le_nat_rpow_add_iff_forall_isBigO {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + ε)) ↔
      (∀ ε : ℝ, 0 < ε →
        f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (a + ε))) := by
  constructor
  · intro h ε hε
    exact isBigO_nat_rpow_of_eventually_le (Eventually.of_forall hf) (h ε hε)
  · intro h ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨C, hC, hbound⟩ :=
      (isBigO_nat_rpow_iff_eventually_le (Eventually.of_forall hf)).mp (h δ hδ)
    have hCpow : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ δ :=
      (nat_rpow_tendsto_atTop hδ).eventually_ge_atTop C
    have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact_mod_cast (show 0 < n by omega)
    filter_upwards [hbound, hCpow, hnpos] with n hfn hCn hn
    calc
      f n ≤ C * (n : ℝ) ^ (a + δ) := hfn
      _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (a + δ) :=
        mul_le_mul_of_nonneg_right hCn
          (Real.rpow_nonneg (Nat.cast_nonneg n) (a + δ))
      _ = (n : ℝ) ^ (a + ε) := by
        rw [mul_comm, ← Real.rpow_add hn]
        congr 1
        dsimp [δ]
        ring

/-- The version with a big-O constant and an explicit natural threshold,
uniformly quantified over positive epsilon. -/
theorem forall_isBigO_nat_rpow_add_iff_exists_threshold {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    (∀ ε : ℝ, 0 < ε →
      f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (a + ε))) ↔
      (∀ ε : ℝ, 0 < ε → ∃ C > 0, ∃ N₀ : ℕ,
        ∀ n, N₀ ≤ n → f n ≤ C * (n : ℝ) ^ (a + ε)) := by
  constructor
  · intro h ε hε
    exact (isBigO_nat_rpow_iff_exists_threshold hf).mp (h ε hε)
  · intro h ε hε
    exact (isBigO_nat_rpow_iff_exists_threshold hf).mpr (h ε hε)

/-! ## Natural floors and fourth roots -/

/-- Eventually a nonnegative real is at most twice its natural floor. -/
theorem eventually_half_le_natFloor :
    ∀ᶠ x : ℝ in atTop, x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  rw [eventually_atTop]
  refine ⟨2, fun x hx ↦ ?_⟩
  linarith [Nat.sub_one_lt_floor x]

/-- Flooring a positive real power of a natural number eventually loses at
most a factor of two. -/
theorem eventually_half_nat_rpow_le_floor {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a / 2 ≤ (⌊(n : ℝ) ^ a⌋₊ : ℝ) :=
  (nat_rpow_tendsto_atTop ha).eventually eventually_half_le_natFloor

/-- The integer part of the real fourth root. -/
noncomputable def fourthRootFloor (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- The fourth-root floor is at most the real fourth root. -/
theorem fourthRootFloor_cast_le (N : ℕ) :
    (fourthRootFloor N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The fourth-root floor is eventually at least half the real fourth root. -/
theorem eventually_half_fourthRoot_le_floor :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (fourthRootFloor N : ℝ) := by
  simpa [fourthRootFloor] using
    (eventually_half_nat_rpow_le_floor (a := (1 / 4 : ℝ)) (by norm_num))

/-- Once the real fourth root is at least four, subtracting one from its
natural floor still leaves at least one quarter of the root. -/
theorem quarter_fourthRoot_le_floor_sub_one {N : ℕ}
    (hroot : 4 ≤ (N : ℝ) ^ (1 / 4 : ℝ)) :
    (N : ℝ) ^ (1 / 4 : ℝ) / 4 ≤ ((fourthRootFloor N - 1 : ℕ) : ℝ) := by
  have hfour : 4 ≤ fourthRootFloor N := by
    apply Nat.le_floor
    exact hroot
  rw [Nat.cast_sub (show 1 ≤ fourthRootFloor N by omega)]
  have hfloor : (N : ℝ) ^ (1 / 4 : ℝ) - 1 < (fourthRootFloor N : ℝ) := by
    exact Nat.sub_one_lt_floor _
  linarith

/-- Eventual version of `quarter_fourthRoot_le_floor_sub_one`. -/
theorem eventually_quarter_fourthRoot_le_floor_sub_one :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 4 : ℝ) / 4 ≤ ((fourthRootFloor N - 1 : ℕ) : ℝ) := by
  have hroot : ∀ᶠ N : ℕ in atTop, 4 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    (nat_rpow_tendsto_atTop (a := (1 / 4 : ℝ)) (by norm_num)).eventually_ge_atTop 4
  exact hroot.mono fun _ hN ↦ quarter_fourthRoot_le_floor_sub_one hN

/-- The real fourth-root scale is big-O of the integer quantity produced by
the fourth-power construction (which has size `fourthRootFloor N - 1`). -/
theorem fourthRoot_isBigO_floor_sub_one :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
      (fun N : ℕ ↦ ((fourthRootFloor N - 1 : ℕ) : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨4, ?_⟩
  filter_upwards [eventually_quarter_fourthRoot_le_floor_sub_one] with N hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith

/-- The fourth power of the fourth-root floor does not exceed `N`. -/
theorem fourthRootFloor_pow_four_le (N : ℕ) :
    fourthRootFloor N ^ 4 ≤ N := by
  have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ fourthRootFloor N by positivity)
    (fourthRootFloor_cast_le N) 4
  have hrootpow : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (N : ℝ) := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (show (4 : ℕ) ≠ 0 by norm_num)
      using 1
    all_goals norm_num
  rw [hrootpow] at h
  exact_mod_cast h

end Erdos186
