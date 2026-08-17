/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Ford's finite divisor-interval objects

This file gives the exact finite objects used in Kevin Ford's work on
integers with a divisor in an interval.  The natural-endpoint versions are
convenient for the arithmetic construction in Erdős Problem 896.  Versions
with real interval endpoints are included as well, since Ford states his
analytic estimates for real `y` and `z`.

The convention inherited from `Nat.divisors` is that zero has no divisors.
Thus every set counted by `H`, `Hr`, `H1`, and their real-endpoint analogues
consists of positive integers.
-/

namespace Erdos896.Ford

open MeasureTheory

/-! ## Divisors in an interval -/

/-- The divisors `d ∣ n` in the half-open interval `(y, z]`.

This is the finite set underlying Ford's `τ(n; y, z)` when the endpoints are
natural numbers. -/
def divisorWindow (n y z : ℕ) : Finset ℕ :=
  n.divisors.filter fun d ↦ y < d ∧ d ≤ z

/-- Ford's divisor count `τ(n; y, z)` for natural endpoints. -/
def tau (n y z : ℕ) : ℕ :=
  (divisorWindow n y z).card

@[simp]
theorem mem_divisorWindow {n y z d : ℕ} :
    d ∈ divisorWindow n y z ↔ d ∣ n ∧ n ≠ 0 ∧ y < d ∧ d ≤ z := by
  simp [divisorWindow, and_assoc]

@[simp]
theorem divisorWindow_zero (y z : ℕ) : divisorWindow 0 y z = ∅ := by
  ext d
  simp

@[simp]
theorem tau_zero (y z : ℕ) : tau 0 y z = 0 := by
  simp [tau]

theorem tau_pos_iff {n y z : ℕ} :
    0 < tau n y z ↔ ∃ d : ℕ, d ∣ n ∧ n ≠ 0 ∧ y < d ∧ d ≤ z := by
  rw [tau, Finset.card_pos]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, mem_divisorWindow.mp hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, mem_divisorWindow.mpr hd⟩

theorem tau_eq_zero_iff {n y z : ℕ} :
    tau n y z = 0 ↔ ∀ d : ℕ, d ∣ n → n ≠ 0 → ¬(y < d ∧ d ≤ z) := by
  rw [tau, Finset.card_eq_zero]
  constructor
  · intro hempty d hdn hn0 hdyz
    have hdmem : d ∈ divisorWindow n y z :=
      mem_divisorWindow.mpr ⟨hdn, hn0, hdyz.1, hdyz.2⟩
    simpa [hempty] using hdmem
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨hdn, hn0, hyd, hdz⟩ := mem_divisorWindow.mp hd
    exact h d hdn hn0 ⟨hyd, hdz⟩

theorem tau_eq_one_iff {n y z : ℕ} :
    tau n y z = 1 ↔
      ∃! d : ℕ, d ∣ n ∧ n ≠ 0 ∧ y < d ∧ d ≤ z := by
  rw [tau, Finset.card_eq_one_iff_existsUnique]
  simp only [mem_divisorWindow]

/-- The same divisor window with real endpoints. -/
noncomputable def divisorWindowR (n : ℕ) (y z : ℝ) : Finset ℕ :=
  n.divisors.filter fun d ↦ y < d ∧ (d : ℝ) ≤ z

/-- Ford's divisor count `τ(n; y, z)` with real endpoints. -/
noncomputable def tauR (n : ℕ) (y z : ℝ) : ℕ :=
  (divisorWindowR n y z).card

@[simp]
theorem mem_divisorWindowR {n d : ℕ} {y z : ℝ} :
    d ∈ divisorWindowR n y z ↔
      d ∣ n ∧ n ≠ 0 ∧ y < (d : ℝ) ∧ (d : ℝ) ≤ z := by
  simp [divisorWindowR, and_assoc]

@[simp]
theorem divisorWindowR_zero (y z : ℝ) : divisorWindowR 0 y z = ∅ := by
  ext d
  simp

@[simp]
theorem tauR_zero (y z : ℝ) : tauR 0 y z = 0 := by
  simp [tauR]

theorem tauR_pos_iff {n : ℕ} {y z : ℝ} :
    0 < tauR n y z ↔
      ∃ d : ℕ, d ∣ n ∧ n ≠ 0 ∧ y < (d : ℝ) ∧ (d : ℝ) ≤ z := by
  rw [tauR, Finset.card_pos]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, mem_divisorWindowR.mp hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, mem_divisorWindowR.mpr hd⟩

theorem tauR_eq_one_iff {n : ℕ} {y z : ℝ} :
    tauR n y z = 1 ↔
      ∃! d : ℕ, d ∣ n ∧ n ≠ 0 ∧ y < (d : ℝ) ∧ (d : ℝ) ≤ z := by
  rw [tauR, Finset.card_eq_one_iff_existsUnique]
  simp only [mem_divisorWindowR]

theorem divisorWindowR_natCast (n y z : ℕ) :
    divisorWindowR n y z = divisorWindow n y z := by
  ext d
  simp

theorem tauR_natCast (n y z : ℕ) : tauR n y z = tau n y z := by
  simp [tauR, tau, divisorWindowR_natCast]

/-! ## The counting functions `H` and `H_r` -/

/-- Positive integers `n ≤ x` with at least one divisor in `(y, z]`. -/
def HSet (x y z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ 0 < tau n y z

/-- Ford's `H(x, y, z)` for natural parameters. -/
def H (x y z : ℕ) : ℕ :=
  (HSet x y z).card

/-- Positive integers `n ≤ x` with exactly `r` divisors in `(y, z]`. -/
def HrSet (r x y z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ tau n y z = r

/-- Ford's `H_r(x, y, z)` for natural parameters. -/
def Hr (r x y z : ℕ) : ℕ :=
  (HrSet r x y z).card

/-- Ford's exact-one-divisor count `H₁(x, y, z)`. -/
def H1 (x y z : ℕ) : ℕ :=
  Hr 1 x y z

/-- The squarefree members counted by `H(x,y,z)`.  This is the finite set
underlying Ford's `H*(x,y,z)`. -/
def HStarSet (x y z : ℕ) : Finset ℕ :=
  (HSet x y z).filter Squarefree

/-- Ford's squarefree divisor-interval count `H*(x,y,z)`. -/
def HStar (x y z : ℕ) : ℕ :=
  (HStarSet x y z).card

@[simp]
theorem mem_HSet {n x y z : ℕ} :
    n ∈ HSet x y z ↔
      1 ≤ n ∧ n ≤ x ∧ ∃ d : ℕ, d ∣ n ∧ y < d ∧ d ≤ z := by
  simp only [HSet, Finset.mem_filter, Finset.mem_Icc, tau_pos_iff]
  constructor
  · rintro ⟨⟨hn1, hnx⟩, d, hdn, -, hyd, hdz⟩
    exact ⟨hn1, hnx, d, hdn, hyd, hdz⟩
  · rintro ⟨hn1, hnx, d, hdn, hyd, hdz⟩
    exact ⟨⟨hn1, hnx⟩, d, hdn, (Nat.one_le_iff_ne_zero.mp hn1), hyd, hdz⟩

@[simp]
theorem mem_HrSet {r n x y z : ℕ} :
    n ∈ HrSet r x y z ↔ 1 ≤ n ∧ n ≤ x ∧ tau n y z = r := by
  simp only [HrSet, Finset.mem_filter, Finset.mem_Icc]
  tauto

@[simp]
theorem mem_HrSet_one {n x y z : ℕ} :
    n ∈ HrSet 1 x y z ↔
      1 ≤ n ∧ n ≤ x ∧
        ∃! d : ℕ, d ∣ n ∧ y < d ∧ d ≤ z := by
  rw [mem_HrSet, tau_eq_one_iff]
  constructor
  · rintro ⟨hn1, hnx, d, hd, hu⟩
    refine ⟨hn1, hnx, d, ?_, ?_⟩
    · exact ⟨hd.1, hd.2.2.1, hd.2.2.2⟩
    · intro e he
      apply hu e
      exact ⟨he.1, Nat.one_le_iff_ne_zero.mp hn1, he.2.1, he.2.2⟩
  · rintro ⟨hn1, hnx, d, hd, hu⟩
    refine ⟨hn1, hnx, d, ?_, ?_⟩
    · exact ⟨hd.1, Nat.one_le_iff_ne_zero.mp hn1, hd.2.1, hd.2.2⟩
    · intro e he
      exact hu e ⟨he.1, he.2.2.1, he.2.2.2⟩

@[simp]
theorem mem_HStarSet {n x y z : ℕ} :
    n ∈ HStarSet x y z ↔
      1 ≤ n ∧ n ≤ x ∧ Squarefree n ∧
        ∃ d : ℕ, d ∣ n ∧ y < d ∧ d ≤ z := by
  simp only [HStarSet, Finset.mem_filter, mem_HSet]
  tauto

theorem HStarSet_subset_HSet (x y z : ℕ) : HStarSet x y z ⊆ HSet x y z :=
  Finset.filter_subset _ _

theorem HStar_le_H (x y z : ℕ) : HStar x y z ≤ H x y z :=
  Finset.card_le_card (HStarSet_subset_HSet x y z)

/-! ## Cross-multiplied windows used in Problem 896 -/

/-- The exact natural-number form of `N/(2p) < d ≤ N/p`, avoiding any
rounding convention at the two rational endpoints. -/
def scaledWindow (N p d : ℕ) : Prop :=
  N < 2 * p * d ∧ p * d ≤ N

instance (N p : ℕ) : DecidablePred (scaledWindow N p) := by
  intro d
  unfold scaledWindow
  infer_instance

/-- Divisors of `n` in the cross-multiplied Problem 896 window. -/
def scaledDivisorWindow (N p n : ℕ) : Finset ℕ :=
  n.divisors.filter (scaledWindow N p)

/-- Number of divisors in the cross-multiplied Problem 896 window. -/
def scaledTau (N p n : ℕ) : ℕ :=
  (scaledDivisorWindow N p n).card

/-- Positive `n ≤ X` having exactly one divisor in the scaled window. -/
def scaledH1Set (N p X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ scaledTau N p n = 1

/-- Cardinality of `scaledH1Set`. -/
def scaledH1 (N p X : ℕ) : ℕ :=
  (scaledH1Set N p X).card

@[simp]
theorem mem_scaledDivisorWindow {N p n d : ℕ} :
    d ∈ scaledDivisorWindow N p n ↔
      d ∣ n ∧ n ≠ 0 ∧ N < 2 * p * d ∧ p * d ≤ N := by
  simp [scaledDivisorWindow, scaledWindow, and_assoc]

theorem scaledTau_eq_one_iff {N p n : ℕ} :
    scaledTau N p n = 1 ↔
      ∃! d : ℕ, d ∣ n ∧ n ≠ 0 ∧ N < 2 * p * d ∧ p * d ≤ N := by
  rw [scaledTau, Finset.card_eq_one_iff_existsUnique]
  simp only [mem_scaledDivisorWindow]

@[simp]
theorem mem_scaledH1Set {N p X n : ℕ} :
    n ∈ scaledH1Set N p X ↔
      1 ≤ n ∧ n ≤ X ∧
        ∃! d : ℕ, d ∣ n ∧ N < 2 * p * d ∧ p * d ≤ N := by
  simp only [scaledH1Set, Finset.mem_filter, Finset.mem_Icc, scaledTau_eq_one_iff]
  constructor
  · rintro ⟨⟨hn1, hnX⟩, d, hd, hu⟩
    refine ⟨hn1, hnX, d, ⟨hd.1, hd.2.2.1, hd.2.2.2⟩, ?_⟩
    intro e he
    exact hu e ⟨he.1, Nat.one_le_iff_ne_zero.mp hn1, he.2.1, he.2.2⟩
  · rintro ⟨hn1, hnX, d, hd, hu⟩
    refine ⟨⟨hn1, hnX⟩, d,
      ⟨hd.1, Nat.one_le_iff_ne_zero.mp hn1, hd.2.1, hd.2.2⟩, ?_⟩
    intro e he
    exact hu e ⟨he.1, he.2.2.1, he.2.2.2⟩

theorem scaledWindow_iff_real {N p d : ℕ} (hp : 0 < p) :
    scaledWindow N p d ↔
      (N : ℝ) / (2 * (p : ℝ)) < (d : ℝ) ∧
        (d : ℝ) ≤ (N : ℝ) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h2pR : (0 : ℝ) < 2 * p := mul_pos (by norm_num) hpR
  unfold scaledWindow
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [div_lt_iff₀ h2pR]
      have hlowerR : (N : ℝ) < 2 * (p : ℝ) * (d : ℝ) := by
        exact_mod_cast hlower
      nlinarith
    · rw [le_div_iff₀ hpR]
      have hupper' : d * p ≤ N := by simpa [mul_comm] using hupper
      exact_mod_cast hupper'
  · rintro ⟨hlower, hupper⟩
    constructor
    · have hlowerR := (div_lt_iff₀ h2pR).mp hlower
      have : (N : ℝ) < 2 * (p : ℝ) * (d : ℝ) := by
        nlinarith
      exact_mod_cast this
    · have hupperR := (le_div_iff₀ hpR).mp hupper
      have hupper' : d * p ≤ N := by exact_mod_cast hupperR
      simpa [mul_comm] using hupper'

theorem scaledDivisorWindow_eq_divisorWindowR
    (N p n : ℕ) (hp : 0 < p) :
    scaledDivisorWindow N p n =
      divisorWindowR n ((N : ℝ) / (2 * (p : ℝ))) ((N : ℝ) / (p : ℝ)) := by
  ext d
  simp only [mem_scaledDivisorWindow, mem_divisorWindowR]
  constructor
  · rintro ⟨hdn, hn0, hlower, hupper⟩
    exact ⟨hdn, hn0, (scaledWindow_iff_real hp).mp ⟨hlower, hupper⟩⟩
  · rintro ⟨hdn, hn0, hlower, hupper⟩
    exact ⟨hdn, hn0, (scaledWindow_iff_real hp).mpr ⟨hlower, hupper⟩⟩

theorem scaledTau_eq_tauR (N p n : ℕ) (hp : 0 < p) :
    scaledTau N p n =
      tauR n ((N : ℝ) / (2 * (p : ℝ))) ((N : ℝ) / (p : ℝ)) := by
  simp [scaledTau, tauR, scaledDivisorWindow_eq_divisorWindowR N p n hp]

theorem HrSet_subset_HSet {r x y z : ℕ} (hr : 0 < r) :
    HrSet r x y z ⊆ HSet x y z := by
  intro n hn
  rw [mem_HrSet] at hn
  rw [mem_HSet]
  refine ⟨hn.1, hn.2.1, ?_⟩
  have htau : 0 < tau n y z := by simpa [hn.2.2] using hr
  obtain ⟨d, hdn, -, hyd, hdz⟩ := tau_pos_iff.mp htau
  exact ⟨d, hdn, hyd, hdz⟩

theorem Hr_le_H {r x y z : ℕ} (hr : 0 < r) : Hr r x y z ≤ H x y z := by
  exact Finset.card_le_card (HrSet_subset_HSet hr)

theorem H1_le_H (x y z : ℕ) : H1 x y z ≤ H x y z := by
  exact Hr_le_H (by decide)

/-- Positive integers `n ≤ x` with a real-endpoint divisor window. -/
noncomputable def HSetR (x : ℕ) (y z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ 0 < tauR n y z

/-- `H(x, y, z)` with a natural upper cutoff and real divisor endpoints. -/
noncomputable def HR (x : ℕ) (y z : ℝ) : ℕ :=
  (HSetR x y z).card

/-- The exact-`r` counting set with real divisor endpoints. -/
noncomputable def HrSetR (r x : ℕ) (y z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ tauR n y z = r

/-- `H_r(x, y, z)` with a natural upper cutoff and real divisor endpoints. -/
noncomputable def HrR (r x : ℕ) (y z : ℝ) : ℕ :=
  (HrSetR r x y z).card

/-- `H₁(x, y, z)` with a natural upper cutoff and real divisor endpoints. -/
noncomputable def H1R (x : ℕ) (y z : ℝ) : ℕ :=
  HrR 1 x y z

/-- Squarefree integers in the real-endpoint divisor count. -/
noncomputable def HStarSetR (x : ℕ) (y z : ℝ) : Finset ℕ :=
  (HSetR x y z).filter Squarefree

/-- Real-endpoint version of Ford's `H*`. -/
noncomputable def HStarR (x : ℕ) (y z : ℝ) : ℕ :=
  (HStarSetR x y z).card

@[simp]
theorem mem_HSetR {n x : ℕ} {y z : ℝ} :
    n ∈ HSetR x y z ↔
      1 ≤ n ∧ n ≤ x ∧
        ∃ d : ℕ, d ∣ n ∧ y < (d : ℝ) ∧ (d : ℝ) ≤ z := by
  simp only [HSetR, Finset.mem_filter, Finset.mem_Icc, tauR_pos_iff]
  constructor
  · rintro ⟨⟨hn1, hnx⟩, d, hdn, -, hyd, hdz⟩
    exact ⟨hn1, hnx, d, hdn, hyd, hdz⟩
  · rintro ⟨hn1, hnx, d, hdn, hyd, hdz⟩
    exact ⟨⟨hn1, hnx⟩, d, hdn, Nat.one_le_iff_ne_zero.mp hn1, hyd, hdz⟩

@[simp]
theorem mem_HrSetR {r n x : ℕ} {y z : ℝ} :
    n ∈ HrSetR r x y z ↔ 1 ≤ n ∧ n ≤ x ∧ tauR n y z = r := by
  simp only [HrSetR, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem HSetR_natCast (x y z : ℕ) : HSetR x y z = HSet x y z := by
  ext n
  simp [HSetR, HSet, tauR_natCast]

theorem HR_natCast (x y z : ℕ) : HR x y z = H x y z := by
  simp [HR, H, HSetR_natCast]

theorem HrSetR_natCast (r x y z : ℕ) : HrSetR r x y z = HrSet r x y z := by
  ext n
  simp [HrSetR, HrSet, tauR_natCast]

theorem HrR_natCast (r x y z : ℕ) : HrR r x y z = Hr r x y z := by
  simp [HrR, Hr, HrSetR_natCast]

theorem H1R_natCast (x y z : ℕ) : H1R x y z = H1 x y z := by
  simp [H1R, H1, HrR_natCast]

theorem HStarSetR_natCast (x y z : ℕ) :
    HStarSetR x y z = HStarSet x y z := by
  ext n
  simp [HStarSetR, HStarSet, HSetR_natCast]

theorem HStarR_natCast (x y z : ℕ) : HStarR x y z = HStar x y z := by
  simp [HStarR, HStar, HStarSetR_natCast]

theorem scaledH1Set_eq_HrSetR (N p X : ℕ) (hp : 0 < p) :
    scaledH1Set N p X =
      HrSetR 1 X ((N : ℝ) / (2 * (p : ℝ))) ((N : ℝ) / (p : ℝ)) := by
  ext n
  simp [scaledH1Set, HrSetR, scaledTau_eq_tauR N p n hp]

theorem scaledH1_eq_H1R (N p X : ℕ) (hp : 0 < p) :
    scaledH1 N p X =
      H1R X ((N : ℝ) / (2 * (p : ℝ))) ((N : ℝ) / (p : ℝ)) := by
  simp [scaledH1, H1R, HrR, scaledH1Set_eq_HrSetR N p X hp]

/-! ## Squarefree numbers supported on a prime interval -/

/-- Every prime factor of `n` lies in the half-open interval `(s, t]`.

For `n = 1` this condition is true, matching Ford's convention that
`1 ∈ 𝒫(s,t)`. -/
def PrimeFactorsIn (s t n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, s < p ∧ p ≤ t

instance (s t : ℕ) : DecidablePred (PrimeFactorsIn s t) := by
  intro n
  unfold PrimeFactorsIn
  infer_instance

/-- The primes in the half-open interval `(s,t]`. -/
def primeInterval (s t : ℕ) : Finset ℕ :=
  (Finset.Icc (s + 1) t).filter Nat.Prime

/-- All squarefree products of primes from `(s,t]`.

Unlike `smoothSet`, this set needs no numerical truncation: there are only
finitely many squarefree products supported on a fixed finite prime interval.
It is a direct finite model of Ford's `𝒫*(s,t)`. -/
def squarefreeSmoothSupport (s t : ℕ) : Finset ℕ :=
  (primeInterval s t).powerset.image fun P ↦ ∏ p ∈ P, p

@[simp]
theorem mem_primeInterval {p s t : ℕ} :
    p ∈ primeInterval s t ↔ Nat.Prime p ∧ s < p ∧ p ≤ t := by
  simp [primeInterval]
  tauto

theorem mem_squarefreeSmoothSupport_iff {a s t : ℕ} :
    a ∈ squarefreeSmoothSupport s t ↔
      ∃ P : Finset ℕ, P ⊆ primeInterval s t ∧ ∏ p ∈ P, p = a := by
  simp [squarefreeSmoothSupport]

/-- The finite truncation at `x` of Ford's `𝒫(s,t)`. -/
def smoothSet (x s t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (PrimeFactorsIn s t)

/-- The finite truncation at `x` of Ford's `𝒫*(s,t)`, the squarefree
members of `𝒫(s,t)`. -/
def squarefreeSmoothSet (x s t : ℕ) : Finset ℕ :=
  (smoothSet x s t).filter Squarefree

@[simp]
theorem mem_smoothSet {a x s t : ℕ} :
    a ∈ smoothSet x s t ↔
      1 ≤ a ∧ a ≤ x ∧ ∀ p ∈ a.primeFactors, s < p ∧ p ≤ t := by
  simp only [smoothSet, Finset.mem_filter, Finset.mem_Icc, PrimeFactorsIn,
    Nat.mem_primeFactors]
  tauto

@[simp]
theorem mem_squarefreeSmoothSet {a x s t : ℕ} :
    a ∈ squarefreeSmoothSet x s t ↔
      1 ≤ a ∧ a ≤ x ∧ Squarefree a ∧
        ∀ p ∈ a.primeFactors, s < p ∧ p ≤ t := by
  simp only [squarefreeSmoothSet, Finset.mem_filter, mem_smoothSet]
  aesop

theorem squarefreeSmoothSet_subset_smoothSet (x s t : ℕ) :
    squarefreeSmoothSet x s t ⊆ smoothSet x s t := by
  exact Finset.filter_subset _ _

theorem primeFactorsIn_of_mem_smoothSet {a x s t : ℕ}
    (ha : a ∈ smoothSet x s t) : PrimeFactorsIn s t a := by
  simpa [PrimeFactorsIn] using (mem_smoothSet.mp ha).2.2

theorem squarefree_of_mem_squarefreeSmoothSet {a x s t : ℕ}
    (ha : a ∈ squarefreeSmoothSet x s t) : Squarefree a :=
  (mem_squarefreeSmoothSet.mp ha).2.2.1

theorem one_mem_smoothSet {x s t : ℕ} (hx : 1 ≤ x) :
    1 ∈ smoothSet x s t := by
  simp [hx]

theorem one_mem_squarefreeSmoothSet {x s t : ℕ} (hx : 1 ≤ x) :
    1 ∈ squarefreeSmoothSet x s t := by
  simp [hx]

/-- Real-endpoint version of `PrimeFactorsIn`. -/
def PrimeFactorsInR (s t : ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, s < (p : ℝ) ∧ (p : ℝ) ≤ t

noncomputable instance (s t : ℝ) : DecidablePred (PrimeFactorsInR s t) := by
  intro n
  unfold PrimeFactorsInR
  infer_instance

/-- The bounded real-endpoint version of Ford's `𝒫(s,t)`. -/
noncomputable def smoothSetR (x : ℕ) (s t : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (PrimeFactorsInR s t)

/-- The bounded real-endpoint version of Ford's `𝒫*(s,t)`. -/
noncomputable def squarefreeSmoothSetR (x : ℕ) (s t : ℝ) : Finset ℕ :=
  (smoothSetR x s t).filter Squarefree

@[simp]
theorem mem_squarefreeSmoothSetR {a x : ℕ} {s t : ℝ} :
    a ∈ squarefreeSmoothSetR x s t ↔
      1 ≤ a ∧ a ≤ x ∧ Squarefree a ∧
        ∀ p ∈ a.primeFactors, s < (p : ℝ) ∧ (p : ℝ) ≤ t := by
  simp [squarefreeSmoothSetR, smoothSetR, PrimeFactorsInR]
  aesop

theorem squarefreeSmoothSetR_natCast (x s t : ℕ) :
    squarefreeSmoothSetR x s t = squarefreeSmoothSet x s t := by
  ext a
  simp

/-! ## Ford's global logarithmic divisor set and its measure -/

/-- The logarithmic interval `[-σ + log d, log d)` contributed by `d`. -/
def logDivisorInterval (d : ℕ) (σ : ℝ) : Set ℝ :=
  Set.Ico (-σ + Real.log d) (Real.log d)

/-- Ford's set `ℒ(a;σ)`: the union of the logarithmic intervals contributed
by all divisors of `a`.

For positive `a` this is exactly
`{x | τ(a; exp x, exp (x + σ)) ≥ 1}`. -/
def logDivisorUnion (a : ℕ) (σ : ℝ) : Set ℝ :=
  ⋃ d : ↥a.divisors, logDivisorInterval d σ

@[simp]
theorem mem_logDivisorInterval {d : ℕ} {σ x : ℝ} :
    x ∈ logDivisorInterval d σ ↔
      -σ + Real.log d ≤ x ∧ x < Real.log d := by
  rfl

@[simp]
theorem mem_logDivisorUnion {a : ℕ} {σ x : ℝ} :
    x ∈ logDivisorUnion a σ ↔
      ∃ d : ℕ, d ∈ a.divisors ∧
        -σ + Real.log d ≤ x ∧ x < Real.log d := by
  constructor
  · intro hx
    rw [logDivisorUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨d, hd⟩ := hx
    exact ⟨d.1, d.2, hd⟩
  · rintro ⟨d, hddiv, hdx⟩
    rw [logDivisorUnion]
    simp only [Set.mem_iUnion]
    exact ⟨⟨d, hddiv⟩, hdx⟩

theorem measurableSet_logDivisorUnion (a : ℕ) (σ : ℝ) :
    MeasurableSet (logDivisorUnion a σ) := by
  apply MeasurableSet.iUnion
  intro d
  exact measurableSet_Ico

/-- The extended nonnegative Lebesgue measure of `ℒ(a;σ)`. -/
noncomputable def divisorLogMeasure (a : ℕ) (σ : ℝ) : ENNReal :=
  volume (logDivisorUnion a σ)

/-- Ford's `L(a;σ)`, as a real-valued Lebesgue measure. -/
noncomputable def L (a : ℕ) (σ : ℝ) : ℝ :=
  (divisorLogMeasure a σ).toReal

@[simp]
theorem logDivisorUnion_zero (σ : ℝ) : logDivisorUnion 0 σ = ∅ := by
  simp [logDivisorUnion]

@[simp]
theorem divisorLogMeasure_zero (σ : ℝ) : divisorLogMeasure 0 σ = 0 := by
  simp [divisorLogMeasure]

@[simp]
theorem L_zero (σ : ℝ) : L 0 σ = 0 := by
  simp [L]

theorem L_nonneg (a : ℕ) (σ : ℝ) : 0 ≤ L a σ := by
  exact ENNReal.toReal_nonneg

end Erdos896.Ford
