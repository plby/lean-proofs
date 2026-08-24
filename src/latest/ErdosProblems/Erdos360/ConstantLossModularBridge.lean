/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ConstantLossInverse
import ErdosProblems.Erdos360.ModularInverseBridge

/-!
# Constant-loss modular inverse connector for Erdős 360

The order-of-growth statement is insensitive to an absolute loss in the
progression mass.  This file is the phase-level counterpart of
`ConstantLossInverse`: it excludes a selected almost period when the local
inverse theorem returns a cover of mass `192 * κ * e`.

The statement is deliberately independent of the recursive selector.  In
particular, `TranslationNewMaximal` is an explicit hypothesis and can only be
supplied by a selector which really maximizes the relevant translation.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-- Recentring all residues preserves a cyclic coset-progression bound with
the same mass. -/
lemma HasCyclicCosetProgressionBound.recentered
    {b mass : ℕ} [NeZero b] {R : Finset (ZMod b)}
    (base : ℕ) (h : HasCyclicCosetProgressionBound R mass) :
    HasCyclicCosetProgressionBound (recenteredZmodValues base R) mass := by
  obtain ⟨H, a, d, L, hsub, hmass⟩ := h
  refine ⟨H, a - (base : ZMod b), d, L, ?_, hmass⟩
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, hri⟩ := mem_cyclicCosetProgression_iff.mp (hsub hr)
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i, hi, ?_⟩
  convert hri using 1 <;> abel

/-- One complete inverse/sieve phase with an arbitrary integral loss `κ` in
the local cyclic inverse theorem. -/
theorem picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve
    {b : ℕ} [NeZero b]
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {S R : Finset (ZMod b)} {pick : ZMod b} {e κ : ℕ}
    (hS : S.Nonempty) (he : 0 < e) (hlarge : 8 * e < S.card)
    (hκpos : 0 < κ) (hκ : 4 * κ < 2000000000)
    (hambient : 2000000000 * S.card ≤ b)
    (hmax : TranslationNewMaximal S R pick)
    (hgen : AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b)) = ⊤)
    (hnumeric : 2 ^ 406 * S.card ^ 100 <
      (S.card / (2 * e)) ^ 102 * R.card ^ 100)
    (hlocalDF : ∀ j, 2 ≤ j →
      j < Nat.log 2 (S.card / (2 * e)) →
      1000000000 *
          (dyadicFinsetSum (almostPeriods S e) j).card ≤ b →
      25 * (dyadicFinsetSum (almostPeriods S e) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S e) j).card →
      CFPLocalDyadicInverseAlternativeWithLoss κ S e j)
    (n y sieveLevel Q : ℕ) (ratio : ℝ)
    (hn : 0 < n) (hy : 2 ≤ y) (hlevel : 101 ≤ sieveLevel) (hQ : 0 < Q)
    (hlog : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99)
    (hcop : ∀ x ∈ shiftedZmodValues R,
      Nat.Coprime (missingPrimeProduct n y) x)
    (hscale : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ R.card)
    (hratio0 : 0 ≤ ratio)
    (hratio : ∀ step : ℕ, 0 < step → step ≤ b →
      ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio)
    (hstrict :
      (((192 * κ : ℕ) : ℝ) * e) *
        (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card) :
    pick ∉ almostPeriods S e := by
  intro hpick
  have hRP : R ⊆ almostPeriods S e :=
    subset_almostPeriods_of_translationNewMaximal hmax hpick
  rcases
      almostPeriod_longProgressionCover_polynomial_trichotomy_of_sparse_localDF_loss
        hS he hlarge hκpos hκ hambient hlocalDF with hproper | hpoly | hcover
  · exact (not_subset_proper_subgroup_of_closure_eq_top hgen hRP) hproper
  · exact polynomial_branch_false_of_subset hRP hpoly hnumeric
  · have hRne : R.Nonempty := by
      apply Finset.card_pos.mp
      have : 0 < (Q * (y ^ sieveLevel) ^ 2) ^ 3 := by positivity
      omega
    have hXne : (shiftedZmodValues R).Nonempty := by
      rw [← Finset.card_pos, card_shiftedZmodValues]
      exact Finset.card_pos.mpr hRne
    have hcoverR : HasStepBoundedLongProgressionCover
        (shiftedZmodValues R) ((192 * κ) * e) b :=
      hcover.toStepBounded_shiftedZmodValues.mono_set
        (shiftedZmodValues_mono hRP)
    have hscaleX : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤
        (shiftedZmodValues R).card := by
      simpa [card_shiftedZmodValues] using hscale
    have hlt := hsieve n y sieveLevel (192 * κ) e e b Q
      (shiftedZmodValues R) ratio hn hy hlevel hQ hlog hXne
      hcoverR hcop hscaleX hratio0 hratio
    dsimp only at hlt
    have hstrictX :
        (((192 * κ : ℕ) : ℝ) * e) *
          (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
              (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) <
            ((shiftedZmodValues R).card : ℝ) := by
      simpa [card_shiftedZmodValues] using hstrict
    exact (Nat.lt_irrefl e) (hlt hstrictX)

/-- Start-at-five one-phase connector.  It consumes the complete local
inverse theorem only at dyadic levels at least five and uses the adjusted
absolute polynomial factor `2^712`. -/
theorem picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve_from_five
    {b : ℕ} [NeZero b]
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {S R : Finset (ZMod b)} {pick : ZMod b} {e κ base : ℕ}
    (hS : S.Nonempty) (he : 0 < e) (hlarge : 8 * e < S.card)
    (hfive : 64 * e ≤ S.card)
    (hκpos : 0 < κ) (hκ : 4 * κ < 2000000000)
    (hambient : 2000000000 * S.card ≤ b)
    (hmax : TranslationNewMaximal S R pick)
    (hgen : AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b)) = ⊤)
    (hnumeric : 2 ^ 712 * S.card ^ 100 <
      (S.card / (2 * e)) ^ 102 * R.card ^ 100)
    (hlocalDF : ∀ j, 5 ≤ j →
      j < Nat.log 2 (S.card / (2 * e)) →
      1000000000 *
          (dyadicFinsetSum (almostPeriods S e) j).card ≤ b →
      25 * (dyadicFinsetSum (almostPeriods S e) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S e) j).card →
      CFPLocalDyadicInverseAlternativeWithLoss κ S e j)
    (n y sieveLevel Q : ℕ) (ratio : ℝ)
    (hn : 0 < n) (hy : 2 ≤ y) (hlevel : 101 ≤ sieveLevel) (hQ : 0 < Q)
    (hlog : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99)
    (hbase : base ≤ b)
    (hcop : ∀ x ∈ intervalZmodValues base R,
      Nat.Coprime (missingPrimeProduct n y) x)
    (hscale : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤
      (intervalZmodValues base R).card)
    (hratio0 : 0 ≤ ratio)
    (hratio : ∀ step : ℕ, 0 < step → step ≤ b →
      ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio)
    (hstrict :
      (((192 * κ : ℕ) : ℝ) * e) *
        (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card) :
    pick ∉ almostPeriods S e := by
  intro hpick
  have hRP : R ⊆ almostPeriods S e :=
    subset_almostPeriods_of_translationNewMaximal hmax hpick
  rcases
      almostPeriod_cyclicProgressionBound_polynomial_trichotomy_of_sparse_localDF_loss_from_five
        hS he hlarge hfive hκpos hκ hambient hlocalDF with
      hproper | hpoly | hcover
  · exact (not_subset_proper_subgroup_of_closure_eq_top hgen hRP) hproper
  · exact polynomial_branch_false_of_subset hRP hpoly hnumeric
  · have hRne : R.Nonempty := by
      apply Finset.card_pos.mp
      have : 0 < (Q * (y ^ sieveLevel) ^ 2) ^ 3 := by positivity
      have hscale' : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ R.card := by
        simpa using hscale
      omega
    have hXne : (intervalZmodValues base R).Nonempty := by
      rw [← Finset.card_pos, card_intervalZmodValues]
      exact Finset.card_pos.mpr hRne
    have hcoverR : HasStepBoundedLongProgressionCover
        (intervalZmodValues base R) ((192 * κ) * e) b := by
      have hrec : recenteredZmodValues base R ⊆
          recenteredZmodValues base (almostPeriods S e) :=
        recenteredZmodValues_mono hRP
      have hshift : HasStepBoundedLongProgressionCover
          (shiftedZmodValues (recenteredZmodValues base R))
            ((192 * κ) * e) b := by
        have hP : (recenteredZmodValues base
            (almostPeriods S e)).Nonempty := by
          obtain ⟨x, hx⟩ : (almostPeriods S e).Nonempty :=
            ⟨0, zero_mem_almostPeriods S e⟩
          exact ⟨x - (base : ZMod b), Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
        have hc := (hcover.recentered base).longProgressionCover hP
        have hc' : HasLongProgressionCover
            (shiftedZmodValues (recenteredZmodValues base
              (almostPeriods S e))) ((192 * κ) * e) := by
          convert hc using 1 <;> ring
        exact hc'.toStepBounded_shiftedZmodValues.mono_set
          (shiftedZmodValues_mono hrec)
      have hinter :=
        stepBoundedLongProgressionCover_interval_of_shifted_recentered
          (base := base) (mass := (192 * κ) * e) (stepBound := b)
          hbase R
      exact hinter hshift
    have hlt := hsieve n y sieveLevel (192 * κ) e e b Q
      (intervalZmodValues base R) ratio hn hy hlevel hQ hlog hXne
      hcoverR hcop hscale hratio0 hratio
    dsimp only at hlt
    have hstrictX :
        (((192 * κ : ℕ) : ℝ) * e) *
          (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
              (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) <
            ((intervalZmodValues base R).card : ℝ) := by
      simpa using hstrict
    exact (Nat.lt_irrefl e) (hlt hstrictX)

/-- Absolute sieve constants for the constant-loss one-phase connector. -/
theorem exists_picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ {b : ℕ} [NeZero b]
        {S R : Finset (ZMod b)} {pick : ZMod b} {e κ : ℕ},
        S.Nonempty → 0 < e → 8 * e < S.card →
        0 < κ → 4 * κ < 2000000000 →
        2000000000 * S.card ≤ b →
        TranslationNewMaximal S R pick →
        AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b)) = ⊤ →
        2 ^ 406 * S.card ^ 100 <
          (S.card / (2 * e)) ^ 102 * R.card ^ 100 →
        (∀ j, 2 ≤ j →
          j < Nat.log 2 (S.card / (2 * e)) →
          1000000000 *
              (dyadicFinsetSum (almostPeriods S e) j).card ≤ b →
          25 * (dyadicFinsetSum (almostPeriods S e) (j + 1)).card ≤
            51 * (dyadicFinsetSum (almostPeriods S e) j).card →
          CFPLocalDyadicInverseAlternativeWithLoss κ S e j) →
        ∀ n y sieveLevel Q : ℕ, ∀ ratio : ℝ,
          0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
          Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
          (∀ x ∈ shiftedZmodValues R,
            Nat.Coprime (missingPrimeProduct n y) x) →
          (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ R.card →
          0 ≤ ratio →
          (∀ step : ℕ, 0 < step → step ≤ b →
            ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
          (((192 * κ : ℕ) : ℝ) * e) *
            (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
                (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card →
          pick ∉ almostPeriods S e := by
  obtain ⟨A, C, hA, hC, hsieve⟩ :=
    exists_growth_gt_of_stepBoundedLongProgressionCover_absorbed
  refine ⟨A, C, hA, hC, ?_⟩
  intro b _ S R pick e κ hS he hlarge hκpos hκ hambient hmax hgen
    hnumeric hlocalDF n y sieveLevel Q ratio hn hy hlevel hQ hlog hcop
    hscale hratio0 hratio hstrict
  exact picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve
    A C hsieve hS he hlarge hκpos hκ hambient hmax hgen hnumeric hlocalDF
    n y sieveLevel Q ratio hn hy hlevel hQ hlog hcop hscale hratio0 hratio
    hstrict

end Erdos360

#print axioms Erdos360.picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve
#print axioms Erdos360.exists_picked_not_mem_almostPeriods_of_sparse_localDF_loss_and_stepSieve
