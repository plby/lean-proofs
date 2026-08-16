import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryEulerBridge

/-!
# Power bounds for the canonical carry-cell boundary

The canonical carry Euler bridge has an exact error with two terms:

* the outer part of the `N`-box removed when trimming to side-`D` blocks;
* the carry-transition set inside the trimmed box.

This file converts that exact expression into the standard power estimate.
Under `2 * D ≤ N`, the trimmed side is at least `N / 2`; hence its
`t`-dimensional volume loses at most a factor `2^t`.  Combining this with
the existing codimension-one carry-transition count gives an explicit
`O_{k,|κ|}(D/N)` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Combinatorial constant in the family carry-transition count. -/
def cfzCanonicalCarryBoundaryConstant
    (κ : Type*) [Fintype κ] (k : ℕ) : ℕ :=
  Fintype.card κ *
    ((2 * cfzCarryRange k + 1) *
      (2 * Fintype.card (CFZVariable k) * k + 1))

/-- If at least two full block sides fit inside the ambient side, trimming
to a multiple of `D` retains at least half the side. -/
theorem le_two_mul_trimToMultiple
    {D N : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N) :
    N ≤ 2 * trimToMultiple D N := by
  have htrimle : trimToMultiple D N ≤ N :=
    trimToMultiple_le D N
  have hloss : N - trimToMultiple D N < D :=
    trimToMultiple_boundary_lt hD
  have hdecomp :
      trimToMultiple D N +
          (N - trimToMultiple D N) = N :=
    Nat.add_sub_of_le htrimle
  omega

/-- Real power form of the retained-half-volume estimate. -/
theorem pow_le_two_pow_mul_trimToMultiple_pow
    {D N t : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N) :
    (N : ℝ) ^ t ≤
      (2 : ℝ) ^ t * (trimToMultiple D N : ℝ) ^ t := by
  have hside : (N : ℝ) ≤
      2 * (trimToMultiple D N : ℝ) := by
    exact_mod_cast le_two_mul_trimToMultiple hD hfit
  calc
    (N : ℝ) ^ t ≤
        (2 * (trimToMultiple D N : ℝ)) ^ t :=
      pow_le_pow_left₀ (by positivity) hside t
    _ = (2 : ℝ) ^ t *
        (trimToMultiple D N : ℝ) ^ t := by
      rw [mul_pow]

/-- Dividing by the trimmed volume costs at most `2^t` relative to dividing
by the full volume. -/
theorem div_trimToMultiple_pow_le_mul_two_pow_div
    {D N t : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N)
    {a A : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) :
    a / (trimToMultiple D N : ℝ) ^ t ≤
      A * (2 : ℝ) ^ t / (N : ℝ) ^ t := by
  have hN : 0 < N := by omega
  have htrim : 0 < trimToMultiple D N := by
    have hhalf := le_two_mul_trimToMultiple hD hfit
    omega
  have hNpow : 0 < (N : ℝ) ^ t := by positivity
  have htrimpow :
      0 < (trimToMultiple D N : ℝ) ^ t := by
    positivity
  have hpow :=
    pow_le_two_pow_mul_trimToMultiple_pow
      (t := t) hD hfit
  have hinv :
      (1 : ℝ) / (trimToMultiple D N : ℝ) ^ t ≤
        (2 : ℝ) ^ t / (N : ℝ) ^ t := by
    rw [div_le_div_iff₀ htrimpow hNpow]
    simpa only [one_mul] using hpow
  have hA : 0 ≤ A := ha.trans haA
  calc
    a / (trimToMultiple D N : ℝ) ^ t =
        a * ((1 : ℝ) /
          (trimToMultiple D N : ℝ) ^ t) := by ring
    _ ≤ A * ((1 : ℝ) /
          (trimToMultiple D N : ℝ) ^ t) := by
      gcongr
    _ ≤ A * ((2 : ℝ) ^ t /
          (N : ℝ) ^ t) := by
      gcongr
    _ = A * (2 : ℝ) ^ t / (N : ℝ) ^ t := by
      ring

/-- The trimmed family carry-bad set obeys the same codimension-one count
as the global bad set. -/
theorem card_cfzTrimmedFamilyCarryBadPoints_le_power
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (forms : κ → CFZFormIndex k) :
    (cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms).card ≤
      cfzCanonicalCarryBoundaryConstant κ k *
        D * N ^ (Fintype.card (CFZVariable k) - 1) := by
  calc
    (cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms).card ≤
        (cfzFamilyCarryBadPoints
          (N := N) D forms).card :=
      card_cfzTrimmedFamilyCarryBadPoints_le D forms
    _ ≤
        Fintype.card κ *
          ((2 * cfzCarryRange k + 1) *
            (2 * Fintype.card (CFZVariable k) * k + 1) *
            D * N ^ (Fintype.card (CFZVariable k) - 1)) :=
      card_cfzFamilyCarryBadPoints_le_linear
        hk hD forms
    _ =
        cfzCanonicalCarryBoundaryConstant κ k *
          D * N ^ (Fintype.card (CFZVariable k) - 1) := by
      unfold cfzCanonicalCarryBoundaryConstant
      ring

/-- Explicit power bound for the complete canonical carry-cell error. -/
theorem cfzCanonicalCarryCellBoundaryError_le_power
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D) (hfit : 2 * D ≤ N)
    (forms : κ → CFZFormIndex k) :
    cfzCanonicalCarryCellBoundaryError
        (N := N) D forms ≤
      4 * (D : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 *
          ((cfzCanonicalCarryBoundaryConstant κ k : ℕ) : ℝ) *
          (D : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) *
          (2 : ℝ) ^ Fintype.card (CFZVariable k) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let t := Fintype.card (CFZVariable k)
  let C := cfzCanonicalCarryBoundaryConstant κ k
  have houter :
      (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
        (D : ℝ) * (t : ℝ) *
          (N : ℝ) ^ (t - 1) :=
    cast_pow_sub_trimToMultiple_pow_le hD
  have hbadNat :
      (cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card ≤
        C * D * N ^ (t - 1) := by
    simpa only [C, t] using
      card_cfzTrimmedFamilyCarryBadPoints_le_power
        hk hD forms
  have hbad :
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) ≤
        (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) := by
    exact_mod_cast hbadNat
  have hbadDiv :
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
          (trimToMultiple D N : ℝ) ^ t ≤
        ((C : ℝ) * (D : ℝ) *
            (N : ℝ) ^ (t - 1)) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t := by
    exact
      div_trimToMultiple_pow_le_mul_two_pow_div
        hD hfit (by positivity) hbad
  unfold cfzCanonicalCarryCellBoundaryError
  simp only [Finset.prod_const, Finset.card_univ]
  change
    4 * (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) /
          (N : ℝ) ^ t +
        2 *
          (((cfzTrimmedFamilyCarryBadPoints
              (N := N) D forms).card : ℝ) /
            (trimToMultiple D N : ℝ) ^ t) ≤
      4 * (D : ℝ) * (t : ℝ) *
          (N : ℝ) ^ (t - 1) / (N : ℝ) ^ t +
        2 * (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t
  apply add_le_add
  · exact
      div_le_div_of_nonneg_right
        (by
          calc
            4 * (((N ^ t -
                (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
                4 * ((D : ℝ) * (t : ℝ) *
                  (N : ℝ) ^ (t - 1)) :=
              mul_le_mul_of_nonneg_left houter (by norm_num)
            _ = 4 * (D : ℝ) * (t : ℝ) *
                (N : ℝ) ^ (t - 1) := by ring)
        (by positivity)
  · calc
      2 *
          (((cfzTrimmedFamilyCarryBadPoints
              (N := N) D forms).card : ℝ) /
            (trimToMultiple D N : ℝ) ^ t) ≤
          2 * (((C : ℝ) * (D : ℝ) *
              (N : ℝ) ^ (t - 1)) *
            (2 : ℝ) ^ t / (N : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_left hbadDiv (by norm_num)
      _ = 2 * (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t := by ring

/-- A single explicit coefficient for the outer trimming loss and all
canonical carry-transition cells. -/
def cfzCanonicalCarryCellErrorConstant
    (κ : Type*) [Fintype κ] (k : ℕ) : ℕ :=
  4 * Fintype.card (CFZVariable k) +
    2 * cfzCanonicalCarryBoundaryConstant κ k *
      2 ^ Fintype.card (CFZVariable k)

/-- Collapsed `C_{k,|κ|} D/N` form of the complete canonical carry-cell
boundary error. -/
theorem cfzCanonicalCarryCellBoundaryError_le_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D) (hfit : 2 * D ≤ N)
    (forms : κ → CFZFormIndex k) :
    cfzCanonicalCarryCellBoundaryError
        (N := N) D forms ≤
      (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
        (D : ℝ) / (N : ℝ) := by
  have hbase :=
    cfzCanonicalCarryCellBoundaryError_le_power
      hk hD hfit forms
  let t := Fintype.card (CFZVariable k)
  have hkpos : 0 < k := by omega
  have htpos : 0 < t := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0, hkpos⟩, false)⟩
  have htOne : 1 ≤ t := htpos
  have hpow :
      (N : ℝ) ^ t =
        (N : ℝ) ^ (t - 1) * (N : ℝ) := by
    calc
      (N : ℝ) ^ t =
          (N : ℝ) ^ ((t - 1) + 1) := by
        rw [Nat.sub_add_cancel htOne]
      _ = (N : ℝ) ^ (t - 1) * (N : ℝ) := by
        rw [pow_succ]
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  calc
    cfzCanonicalCarryCellBoundaryError
        (N := N) D forms ≤
      4 * (D : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 *
          ((cfzCanonicalCarryBoundaryConstant κ k : ℕ) : ℝ) *
          (D : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) *
          (2 : ℝ) ^ Fintype.card (CFZVariable k) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbase
    _ =
      (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
        (D : ℝ) / (N : ℝ) := by
      change
        4 * (D : ℝ) * (t : ℝ) *
              (N : ℝ) ^ (t - 1) / (N : ℝ) ^ t +
            2 *
              (cfzCanonicalCarryBoundaryConstant κ k : ℝ) *
              (D : ℝ) * (N : ℝ) ^ (t - 1) *
              (2 : ℝ) ^ t / (N : ℝ) ^ t =
          (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
            (D : ℝ) / (N : ℝ)
      rw [hpow]
      unfold cfzCanonicalCarryCellErrorConstant
      push_cast
      field_simp
      ring

end Wikipedia.SzemeredisTheorem
