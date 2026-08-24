/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.AdaptiveSelector
import ErdosProblems.Erdos360.LowLayerInverse
import ErdosProblems.Erdos360.StepBoundedCover

/-!
# The almost-period inverse/sieve connector for Erdős 360

This file closes the deterministic part of an unsaturated modular phase.
The remaining set is first put inside an almost-period set by maximality of
the selected translation.  The three conclusions of the corrected cyclic
inverse theorem are then excluded respectively by generation, a numerical
cardinality inequality, and the step-bounded progression sieve.

The only additive-combinatorial input retained by the final theorem is the
public predicate `CFPLocalDyadicInverseAlternative`.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-- The precise maximality property used at an unsaturated phase: the
chosen shift introduces at least as many points as every remaining shift. -/
def TranslationNewMaximal {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S R : Finset G) (pick : G) : Prop :=
  ∀ x ∈ R, (translationNew S x).card ≤ (translationNew S pick).card

/-- Maximality converts one small selected translation into the inclusion
of every remaining translation in the same almost-period set. -/
lemma subset_almostPeriods_of_translationNewMaximal
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S R : Finset G} {pick : G} {e : ℕ}
    (hmax : TranslationNewMaximal S R pick)
    (hpick : pick ∈ almostPeriods S e) :
    R ⊆ almostPeriods S e := by
  intro x hx
  rw [mem_almostPeriods_iff_card_translationNew_le] at hpick ⊢
  exact (hmax x hx).trans hpick

/-- A set containing a generating subset cannot lie in a proper subgroup. -/
lemma not_subset_proper_subgroup_of_closure_eq_top
    {G : Type*} [AddCommGroup G]
    {R P : Finset G}
    (hgen : AddSubgroup.closure ((R : Finset G) : Set G) = ⊤)
    (hRP : R ⊆ P) :
    ¬ ∃ K : AddSubgroup G, K ≠ ⊤ ∧
      ((P : Finset G) : Set G) ⊆ (K : Set G) := by
  rintro ⟨K, hK, hPK⟩
  apply hK
  apply top_unique
  rw [← hgen]
  exact (AddSubgroup.closure_le K).2
    (fun x hx ↦ hPK (hRP hx))

/-- Monotonicity needed to exclude the polynomial-cardinality branch of
the almost-period trichotomy. -/
lemma polynomial_branch_false_of_subset
    {R P : Finset α} {q s constant : ℕ}
    (hRP : R ⊆ P)
    (hpoly : q ^ 102 * P.card ^ 100 ≤ constant * s ^ 100)
    (hstrict : constant * s ^ 100 < q ^ 102 * R.card ^ 100) : False := by
  have hcard : R.card ≤ P.card := Finset.card_le_card hRP
  have hpow : R.card ^ 100 ≤ P.card ^ 100 := Nat.pow_le_pow_left hcard 100
  have hmono : q ^ 102 * R.card ^ 100 ≤ q ^ 102 * P.card ^ 100 :=
    Nat.mul_le_mul_left _ hpow
  omega

/-- One complete inverse/sieve phase.  If the selected translation were an
`e`-almost period, maximality would put all remaining translations in the
almost-period set.  Generation and the explicit polynomial inequality
exclude the first two inverse alternatives.  The third produces a cover of
mass `768e`; the sharp bounded-step sieve, used with `target = growth = e`,
would then prove `e < e`.

All number-theoretic hypotheses are stated only for the shifted standard
representatives of `R`, so no coprimality assertion is made about the whole
almost-period set. -/
theorem picked_not_mem_almostPeriods_of_sparse_localDF_and_stepSieve
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
    {S R : Finset (ZMod b)} {pick : ZMod b} {e : ℕ}
    (hS : S.Nonempty) (he : 0 < e) (hlarge : 8 * e < S.card)
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
      CFPLocalDyadicInverseAlternative S e j)
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
      ((768 : ℝ) * e) *
        (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
            (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card) :
    pick ∉ almostPeriods S e := by
  intro hpick
  have hRP : R ⊆ almostPeriods S e :=
    subset_almostPeriods_of_translationNewMaximal hmax hpick
  rcases almostPeriod_longProgressionCover_polynomial_trichotomy_of_sparse_localDF
      hS he hlarge hambient hlocalDF with hproper | hpoly | hcover
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
        (shiftedZmodValues R) (768 * e) b :=
      hcover.toStepBounded_shiftedZmodValues.mono_set
        (shiftedZmodValues_mono hRP)
    have hscaleX : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤
        (shiftedZmodValues R).card := by
      simpa [card_shiftedZmodValues] using hscale
    have hlt := hsieve n y sieveLevel 768 e e b Q
      (shiftedZmodValues R) ratio hn hy hlevel hQ hlog hXne
      hcoverR hcop hscaleX hratio0 hratio
    dsimp only at hlt
    have hstrictX :
        ((768 : ℝ) * e) *
          (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
              (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) <
            ((shiftedZmodValues R).card : ℝ) := by
      simpa [card_shiftedZmodValues] using hstrict
    exact (Nat.lt_irrefl e) (hlt hstrictX)

/-- The sharp sieve supplies absolute constants for the preceding complete
one-phase connector. -/
theorem exists_picked_not_mem_almostPeriods_of_sparse_localDF_and_stepSieve :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ {b : ℕ} [NeZero b]
        {S R : Finset (ZMod b)} {pick : ZMod b} {e : ℕ},
        S.Nonempty → 0 < e → 8 * e < S.card →
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
          CFPLocalDyadicInverseAlternative S e j) →
        ∀ n y sieveLevel Q : ℕ, ∀ ratio : ℝ,
          0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
          Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
          (∀ x ∈ shiftedZmodValues R,
            Nat.Coprime (missingPrimeProduct n y) x) →
          (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ R.card →
          0 ≤ ratio →
          (∀ step : ℕ, 0 < step → step ≤ b →
            ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
          ((768 : ℝ) * e) *
            (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
                (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card →
          pick ∉ almostPeriods S e := by
  obtain ⟨A, C, hA, hC, hsieve⟩ :=
    exists_growth_gt_of_stepBoundedLongProgressionCover_absorbed
  refine ⟨A, C, hA, hC, ?_⟩
  intro b _ S R pick e hS he hlarge hambient hmax hgen hnumeric hlocalDF
    n y sieveLevel Q ratio hn hy hlevel hQ hlog hcop hscale hratio0 hratio
    hstrict
  exact picked_not_mem_almostPeriods_of_sparse_localDF_and_stepSieve
    A C hsieve hS he hlarge hambient hmax hgen hnumeric hlocalDF
    n y sieveLevel Q ratio hn hy hlevel hQ hlog hcop hscale hratio0 hratio
    hstrict

/-! ## Phase-machine packaging -/

/-- All non-DF hypotheses needed to exclude the three inverse-theorem
outputs at one unsaturated phase.  They are bundled to keep the phasewise
connector readable. -/
structure CFPInverseSievePhaseConditions
    (A C : ℝ) (n y sieveLevel Q : ℕ) (ratio : ℝ)
    {b : ℕ} [NeZero b]
    (S R : Finset (ZMod b)) (pick : ZMod b) (e : ℕ) : Prop where
  S_nonempty : S.Nonempty
  e_pos : 0 < e
  large : 8 * e < S.card
  ambient : 2000000000 * S.card ≤ b
  maximal : TranslationNewMaximal S R pick
  generates :
    AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b)) = ⊤
  polynomial_reverse :
    2 ^ 406 * S.card ^ 100 <
      (S.card / (2 * e)) ^ 102 * R.card ^ 100
  n_pos : 0 < n
  y_ge : 2 ≤ y
  sieveLevel_ge : 101 ≤ sieveLevel
  Q_pos : 0 < Q
  log_bound : Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99
  coprime : ∀ x ∈ shiftedZmodValues R,
    Nat.Coprime (missingPrimeProduct n y) x
  long_scale : (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ R.card
  ratio_nonneg : 0 ≤ ratio
  ratio_bound : ∀ step : ℕ, 0 < step → step ≤ b →
    ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio
  sieve_reverse :
    ((768 : ℝ) * e) *
      (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)) *
          (C * ratio / Real.log (y : ℝ))) + 1 / (Q : ℝ)) < R.card

/-- A phasewise family of the preceding certificates, plus the corrected
local DF alternative at every dyadic scale, discharges exactly the residual
`CFPPickedShiftEscapesAlmostPeriods` expected by `AdaptiveSelector`. -/
theorem cfpPickedShiftEscapesAlmostPeriods_of_phasewise_sparse_localDF
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
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (phaseQ D : ℕ) (sat : ℕ → ℕ) (k : ℕ)
    (n y sieveLevel sieveQ : ℕ) (ratio : ℝ)
    (hconditions : ∀ i < k,
      IsCFPUnsaturatedPhase hb R₀ E hE hdiverse phaseQ sat i →
      CFPInverseSievePhaseConditions A C n y sieveLevel sieveQ ratio
        (modularPhaseSums hb R₀ E hE hdiverse i)
        (cfpRemainder hb R₀ E hE hdiverse i)
        (modularPhasePick hb R₀ E hE hdiverse
          (cfpRemainder hb R₀ E hE hdiverse i))
        (D - 1))
    (hlocalDF : ∀ i < k,
      IsCFPUnsaturatedPhase hb R₀ E hE hdiverse phaseQ sat i →
      ∀ j, 2 ≤ j →
        j < Nat.log 2
          ((modularPhaseSums hb R₀ E hE hdiverse i).card /
            (2 * (D - 1))) →
        1000000000 *
            (dyadicFinsetSum
              (almostPeriods
                (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1)) j).card ≤
          b →
        25 *
            (dyadicFinsetSum
              (almostPeriods
                (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1))
              (j + 1)).card ≤
          51 *
            (dyadicFinsetSum
              (almostPeriods
                (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1)) j).card →
        CFPLocalDyadicInverseAlternative
          (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1) j) :
    CFPPickedShiftEscapesAlmostPeriods
      hb R₀ E hE hdiverse phaseQ D sat k := by
  intro i hi hu
  let S := modularPhaseSums hb R₀ E hE hdiverse i
  let R := cfpRemainder hb R₀ E hE hdiverse i
  let pick := modularPhasePick hb R₀ E hE hdiverse R
  have hc := hconditions i hi hu
  exact picked_not_mem_almostPeriods_of_sparse_localDF_and_stepSieve
    (b := b)
    (S := modularPhaseSums hb R₀ E hE hdiverse i)
    (R := cfpRemainder hb R₀ E hE hdiverse i)
    (pick := modularPhasePick hb R₀ E hE hdiverse
      (cfpRemainder hb R₀ E hE hdiverse i))
    (e := D - 1)
    A C hsieve hc.S_nonempty hc.e_pos hc.large hc.ambient hc.maximal
    hc.generates hc.polynomial_reverse (hlocalDF i hi hu)
    n y sieveLevel sieveQ ratio hc.n_pos hc.y_ge hc.sieveLevel_ge hc.Q_pos
    hc.log_bound hc.coprime hc.long_scale hc.ratio_nonneg hc.ratio_bound
    hc.sieve_reverse

/-- Absolute sieve constants for the phasewise residual connector. -/
theorem exists_cfpPickedShiftEscapesAlmostPeriods_of_phasewise_sparse_localDF :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ {b : ℕ} [NeZero b]
        (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
        (hdiverse : PhaseDiverse hb R₀)
        (phaseQ D : ℕ) (sat : ℕ → ℕ) (k : ℕ)
        (n y sieveLevel sieveQ : ℕ) (ratio : ℝ),
        (∀ i < k,
          IsCFPUnsaturatedPhase hb R₀ E hE hdiverse phaseQ sat i →
          CFPInverseSievePhaseConditions A C n y sieveLevel sieveQ ratio
            (modularPhaseSums hb R₀ E hE hdiverse i)
            (cfpRemainder hb R₀ E hE hdiverse i)
            (modularPhasePick hb R₀ E hE hdiverse
              (cfpRemainder hb R₀ E hE hdiverse i))
            (D - 1)) →
        (∀ i < k,
          IsCFPUnsaturatedPhase hb R₀ E hE hdiverse phaseQ sat i →
          ∀ j, 2 ≤ j →
            j < Nat.log 2
              ((modularPhaseSums hb R₀ E hE hdiverse i).card /
                (2 * (D - 1))) →
            1000000000 *
                (dyadicFinsetSum
                  (almostPeriods
                    (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1)) j).card ≤
              b →
            25 *
                (dyadicFinsetSum
                  (almostPeriods
                    (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1))
                  (j + 1)).card ≤
              51 *
                (dyadicFinsetSum
                  (almostPeriods
                    (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1)) j).card →
            CFPLocalDyadicInverseAlternative
              (modularPhaseSums hb R₀ E hE hdiverse i) (D - 1) j) →
        CFPPickedShiftEscapesAlmostPeriods
          hb R₀ E hE hdiverse phaseQ D sat k := by
  obtain ⟨A, C, hA, hC, hsieve⟩ :=
    exists_growth_gt_of_stepBoundedLongProgressionCover_absorbed
  refine ⟨A, C, hA, hC, ?_⟩
  intro b _ hb R₀ E hE hdiverse phaseQ D sat k n y sieveLevel sieveQ
    ratio hconditions hlocalDF
  exact cfpPickedShiftEscapesAlmostPeriods_of_phasewise_sparse_localDF
    A C hsieve hb R₀ E hE hdiverse phaseQ D sat k n y sieveLevel sieveQ
    ratio hconditions hlocalDF

end Erdos360
