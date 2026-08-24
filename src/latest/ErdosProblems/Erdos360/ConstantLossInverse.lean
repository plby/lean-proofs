/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.DenseCoreCompletion
import ErdosProblems.Erdos360.LowLayerInverse

/-!
# Constant-loss local inverse connector for Erdős 360

The final order-of-growth theorem only needs an absolute multiplicative
constant.  This module therefore replaces the sharp `52/25` progression
mass by `κ` times the dyadic sumset cardinality and propagates that loss
through quotient contraction and the almost-period trichotomy.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- An inverse progression of mass at most `κ|B|` occupies at most half of
the quotient whenever `2κ|B|` is smaller than the ambient cyclic group. -/
lemma quotient_half_of_progression_mass_loss
    {t L BCard κ : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    (hmass : L * Nat.card H ≤ κ * BCard)
    (hsparse : 2 * κ * BCard < t) :
    2 * L ≤ Nat.card (ZMod t ⧸ H) := by
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hcard : t = Nat.card (ZMod t ⧸ H) * Nat.card H := by
    simpa using H.card_eq_card_quotient_mul_card_addSubgroup
  have hmul : (2 * L) * Nat.card H <
      Nat.card (ZMod t ⧸ H) * Nat.card H := by
    rw [← hcard]
    calc
      (2 * L) * Nat.card H = 2 * (L * Nat.card H) := by ring
      _ ≤ 2 * (κ * BCard) := Nat.mul_le_mul_left 2 hmass
      _ = 2 * κ * BCard := by ring
      _ < t := hsparse
  exact ((Nat.mul_lt_mul_right hHpos).mp hmul).le

/-- Generic constant-loss version of CFP's contracted progression estimate.
The factor `32` is deliberately integral and uniform. -/
lemma cfp_contracted_progression_mass_le_loss
    {S D i j ell BCard κ : ℕ}
    (hκpos : 0 < κ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hscale : S < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) * BCard ≤ 4 * S)
    (hcontract : 2 ^ (j - 1) * ell ≤ κ * BCard) :
    ell ≤ 32 * κ * D := by
  have hpowj : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  have hpowi : 2 ^ i = 2 ^ (i - j) * 2 ^ j := by
    rw [← pow_add]
    congr 2
    omega
  have hpos : 0 < 2 ^ (i - j) * 2 ^ (j - 1) := by positivity
  have hmain :
      (2 ^ (i - j) * 2 ^ (j - 1)) * ell <
        (2 ^ (i - j) * 2 ^ (j - 1)) * (32 * κ * D) := by
    calc
      (2 ^ (i - j) * 2 ^ (j - 1)) * ell =
          2 ^ (i - j) * (2 ^ (j - 1) * ell) := by ring
      _ ≤ 2 ^ (i - j) * (κ * BCard) :=
        Nat.mul_le_mul_left _ hcontract
      _ = κ * (2 ^ (i - j) * BCard) := by ring
      _ ≤ κ * (4 * S) := Nat.mul_le_mul_left κ hlevel
      _ < κ * (4 * (4 * D * 2 ^ i)) := by
        exact (Nat.mul_lt_mul_left hκpos).2 (by omega)
      _ = (2 ^ (i - j) * 2 ^ (j - 1)) * (32 * κ * D) := by
        rw [hpowi, hpowj]
        ring
  exact (Nat.lt_of_mul_lt_mul_left hmain).le

/-- Constant-loss contraction of a slow-scale cyclic progression. -/
theorem almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_loss
    {t : ℕ} [NeZero t]
    {S : Finset (ZMod t)} {D i j L κ : ℕ}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hκpos : 0 < κ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hclosure : AddSubgroup.closure
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) = ⊤)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card)
    (hsum : dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L)
    (hDFmass : L * Nat.card H ≤
      κ * (dyadicFinsetSum (almostPeriods S D) j).card)
    (hsparse : 2 * κ *
      (dyadicFinsetSum (almostPeriods S D) j).card < t) :
    HasCyclicCosetProgressionBound
      (almostPeriods S D) (32 * κ * D) := by
  classical
  let P := almostPeriods S D
  let k := 2 ^ j
  let BCard := (dyadicFinsetSum (almostPeriods S D) j).card
  have hzero : 0 ∈ P := by simp [P]
  have hk : 0 < k := by simp [k]
  have hsum' : iteratedFinsetSum P k ⊆
      cyclicCosetProgression H a d L := by
    rw [show iteratedFinsetSum P k = dyadicFinsetSum P j by
      simpa [k] using (dyadicFinsetSum_eq_iteratedFinsetSum P j).symm]
    simpa [P] using hsum
  have hhalf : 2 * L ≤ Nat.card (ZMod t ⧸ H) :=
    quotient_half_of_progression_mass_loss H hDFmass hsparse
  have hkL : k ≤ L :=
    k_le_length_of_generating_cyclic_coset_iterated_subset
      H a d hzero hk (by simpa [P] using hclosure) hhalf hsum'
  obtain ⟨a', ell, hPprog, hcontract⟩ :=
    cyclic_coset_progression_contraction_of_closure_eq_top
      H a d hzero hk hkL (by simpa [P] using hclosure) hhalf hsum'
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  have hcontract' : 2 ^ (j - 1) * (ell * Nat.card H) ≤
      L * Nat.card H := by
    have htwo : 2 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        2 * (L * Nat.card H) := by
      calc
        2 * (2 ^ (j - 1) * (ell * Nat.card H)) =
            k * (ell * Nat.card H) := by rw [show k = 2 ^ j by rfl, hpow]; ring
        _ ≤ 2 * (L * Nat.card H) := hcontract
    omega
  have hcontractLoss :
      2 ^ (j - 1) * (ell * Nat.card H) ≤
        κ * (dyadicFinsetSum (almostPeriods S D) j).card :=
    hcontract'.trans hDFmass
  have hmass : ell * Nat.card H ≤ 32 * κ * D :=
    cfp_contracted_progression_mass_le_loss hκpos hj hji hscale hlevel
      hcontractLoss
  exact ⟨H, a', d, ell, by simpa [P] using hPprog, hmass⟩

/-- Corrected local DF alternative with an arbitrary integral loss factor. -/
def CFPLocalDyadicInverseAlternativeWithLoss
    {t : ℕ} [NeZero t] (κ : ℕ)
    (S : Finset (ZMod t)) (D j : ℕ) : Prop :=
  (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
    ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
      (K : Set (ZMod t))) ∨
  ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
    dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L ∧
    L * Nat.card H ≤
      κ * (dyadicFinsetSum (almostPeriods S D) j).card

/-- Canonical polynomial trichotomy with a constant-loss local DF input.
Its structural cover has mass `192κD`. -/
theorem almostPeriod_longProgressionCover_polynomial_trichotomy_of_sparse_localDF_loss
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D κ : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hκpos : 0 < κ) (hκ : 4 * κ < 2000000000)
    (hambient : 2000000000 * S.card ≤ t)
    (hlocalDF : ∀ j, 2 ≤ j →
      j < Nat.log 2 (S.card / (2 * D)) →
      1000000000 *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ t →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      CFPLocalDyadicInverseAlternativeWithLoss κ S D j) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 *
        (almostPeriods S D).card ^ 100 ≤
      2 ^ 406 * S.card ^ 100 ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (192 * κ * D) := by
  classical
  let P := almostPeriods S D
  let q := S.card / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨hi, hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change 2 ≤ i at hi
  change 2 * ((2 ^ i) * D) ≤ S.card at hbudget
  change q < 2 ^ (i + 1) at hqpow
  have hscale : S.card < 4 * D * 2 ^ i := by
    simpa [i, q] using
      (almostPeriod_chosenIndex_card_lt_four_mul hD hlarge)
  have hScardPos : 0 < S.card := Finset.card_pos.mpr hS
  have hsparseEq : 2 * S.card < Fintype.card (ZMod t) := by
    rw [ZMod.card]
    nlinarith only [hambient, hScardPos]
  by_cases hproper : ∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((P : Finset (ZMod t)) : Set (ZMod t)) ⊆ (K : Set (ZMod t))
  · exact Or.inl (by simpa [P] using hproper)
  have hclosure : AddSubgroup.closure
      ((P : Finset (ZMod t)) : Set (ZMod t)) = ⊤ := by
    by_contra hne
    apply hproper
    exact ⟨AddSubgroup.closure ((P : Finset (ZMod t)) : Set (ZMod t)),
      hne, AddSubgroup.subset_closure⟩
  rcases almostPeriod_dyadic_trichotomy_from_two hS hi hbudget with
      hproper' | hsmall | hnumeric
  · exact Or.inl hproper'
  · obtain ⟨j, hj, hji, hslow⟩ := hsmall
    have hBcard := card_dyadicFinsetSum_almostPeriods_le_two_mul_of_le
      hS (Nat.le_of_lt hji) hbudget
    have hDFsparse : 1000000000 *
        (dyadicFinsetSum (almostPeriods S D) j).card ≤ t := by
      calc
        1000000000 *
            (dyadicFinsetSum (almostPeriods S D) j).card ≤
            1000000000 * (2 * S.card) :=
          Nat.mul_le_mul_left 1000000000 hBcard
        _ = 2000000000 * S.card := by ring
        _ ≤ t := hambient
    rcases hlocalDF j hj (by simpa [i, q] using hji) hDFsparse hslow with
      hlocalProper | ⟨H, a, d, L, hprog, hDFmass⟩
    · exact Or.inl hlocalProper
    · right; right
      have hlevel0 := pow_two_mul_card_dyadic_le_two_mul_final
        hS (Nat.le_of_lt hji) hbudget hsparseEq (by simpa [P] using hproper)
      have hfinal := card_dyadicFinsetSum_almostPeriods_le_two_mul
        hS hbudget
      have hlevel : 2 ^ (i - j) *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card :=
        hlevel0.trans (by omega)
      have hcontractSparse : 2 * κ *
          (dyadicFinsetSum (almostPeriods S D) j).card < t := by
        calc
          2 * κ * (dyadicFinsetSum (almostPeriods S D) j).card ≤
              2 * κ * (2 * S.card) :=
            Nat.mul_le_mul_left (2 * κ) hBcard
          _ = (4 * κ) * S.card := by ring
          _ < 2000000000 * S.card :=
            (Nat.mul_lt_mul_right hScardPos).2 hκ
          _ ≤ t := hambient
      have hstruct :=
        almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_loss
          H a d hκpos (by omega) (Nat.le_of_lt hji)
          (by simpa [P] using hclosure) hscale hlevel hprog hDFmass
          hcontractSparse
      have hPnonempty : (almostPeriods S D).Nonempty :=
        ⟨0, zero_mem_almostPeriods S D⟩
      have hcover := hstruct.longProgressionCover hPnonempty
      convert hcover using 1 <;> ring
  · right; left
    have hshift : i - 2 + 3 = i + 1 := by omega
    have hpoly := dyadic_numeric_bound_one_point_zero_two
      (n := i - 2) (q := q) (P := (almostPeriods S D).card)
      (S := S.card) (by simpa [hshift] using hqpow) hnumeric
    simpa [q] using hpoly

/-- Start-at-five form of the constant-loss polynomial trichotomy.  The
extra hypothesis supplies five available dyadic levels.  It lets the local
inverse input be used only where the complete `j ≥ 5` theorem applies; the
sole cost is replacing the absolute numerical factor `2^406` by `2^712`.
-/
theorem almostPeriod_cyclicProgressionBound_polynomial_trichotomy_of_sparse_localDF_loss_from_five
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D κ : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hfive : 64 * D ≤ S.card)
    (hκpos : 0 < κ) (hκ : 4 * κ < 2000000000)
    (hambient : 2000000000 * S.card ≤ t)
    (hlocalDF : ∀ j, 5 ≤ j →
      j < Nat.log 2 (S.card / (2 * D)) →
      1000000000 *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ t →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      CFPLocalDyadicInverseAlternativeWithLoss κ S D j) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 *
        (almostPeriods S D).card ^ 100 ≤
      2 ^ 712 * S.card ^ 100 ∨
    HasCyclicCosetProgressionBound (almostPeriods S D) (32 * κ * D) := by
  classical
  let P := almostPeriods S D
  let q := S.card / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨_hi, hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change 2 * ((2 ^ i) * D) ≤ S.card at hbudget
  change q < 2 ^ (i + 1) at hqpow
  have hden : 0 < 2 * D := by omega
  have hq32 : 32 ≤ q := by
    rw [show q = S.card / (2 * D) by rfl]
    apply (Nat.le_div_iff_mul_le hden).2
    nlinarith
  have hi : 5 ≤ i := by
    apply Nat.le_log_of_pow_le (by omega : 1 < 2)
    norm_num at hq32 ⊢
    exact hq32
  have hscale : S.card < 4 * D * 2 ^ i := by
    simpa [i, q] using
      (almostPeriod_chosenIndex_card_lt_four_mul hD hlarge)
  have hScardPos : 0 < S.card := Finset.card_pos.mpr hS
  have hsparseEq : 2 * S.card < Fintype.card (ZMod t) := by
    rw [ZMod.card]
    nlinarith only [hambient, hScardPos]
  by_cases hproper : ∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((P : Finset (ZMod t)) : Set (ZMod t)) ⊆ (K : Set (ZMod t))
  · exact Or.inl (by simpa [P] using hproper)
  have hclosure : AddSubgroup.closure
      ((P : Finset (ZMod t)) : Set (ZMod t)) = ⊤ := by
    by_contra hne
    apply hproper
    exact ⟨AddSubgroup.closure ((P : Finset (ZMod t)) : Set (ZMod t)),
      hne, AddSubgroup.subset_closure⟩
  rcases almostPeriod_dyadic_trichotomy_from_five hS hi hbudget with
      hproper' | hsmall | hnumeric
  · exact Or.inl hproper'
  · obtain ⟨j, hj, hji, hslow⟩ := hsmall
    have hBcard := card_dyadicFinsetSum_almostPeriods_le_two_mul_of_le
      hS (Nat.le_of_lt hji) hbudget
    have hDFsparse : 1000000000 *
        (dyadicFinsetSum (almostPeriods S D) j).card ≤ t := by
      calc
        1000000000 *
            (dyadicFinsetSum (almostPeriods S D) j).card ≤
            1000000000 * (2 * S.card) :=
          Nat.mul_le_mul_left 1000000000 hBcard
        _ = 2000000000 * S.card := by ring
        _ ≤ t := hambient
    rcases hlocalDF j hj (by simpa [i, q] using hji) hDFsparse hslow with
      hlocalProper | ⟨H, a, d, L, hprog, hDFmass⟩
    · exact Or.inl hlocalProper
    · right; right
      have hlevel0 := pow_two_mul_card_dyadic_le_two_mul_final
        hS (Nat.le_of_lt hji) hbudget hsparseEq (by simpa [P] using hproper)
      have hfinal := card_dyadicFinsetSum_almostPeriods_le_two_mul
        hS hbudget
      have hlevel : 2 ^ (i - j) *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card :=
        hlevel0.trans (by omega)
      have hcontractSparse : 2 * κ *
          (dyadicFinsetSum (almostPeriods S D) j).card < t := by
        calc
          2 * κ * (dyadicFinsetSum (almostPeriods S D) j).card ≤
              2 * κ * (2 * S.card) :=
            Nat.mul_le_mul_left (2 * κ) hBcard
          _ = (4 * κ) * S.card := by ring
          _ < 2000000000 * S.card :=
            (Nat.mul_lt_mul_right hScardPos).2 hκ
          _ ≤ t := hambient
      have hstruct :=
        almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_loss
          H a d hκpos (by omega) (Nat.le_of_lt hji)
          (by simpa [P] using hclosure) hscale hlevel hprog hDFmass
          hcontractSparse
      exact hstruct
  · right; left
    have hshift : i - 5 + 6 = i + 1 := by omega
    have hpoly := dyadic_numeric_bound_one_point_zero_two_six
      (n := i - 5) (q := q) (P := (almostPeriods S D).card)
      (S := S.card) (by simpa [hshift] using hqpow) hnumeric
    simpa [q] using hpoly

end Erdos360
