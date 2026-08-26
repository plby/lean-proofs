import ErdosProblems.Erdos67b.MRFiniteHalaszBandL2
import ErdosProblems.Erdos67b.MRHalaszDistancePropagation

/-!
# A fixed finite-Halasz Euler band

Frequency-dependent selection among three Euler factors cannot be inserted
inside a smoothing integral.  Instead, take the selected band to contain
every prime up to a lower cutoff `Y`.  Its pretentious distance at `Y` is
then exactly the distance of the original coefficient, uniformly in the
frequency.  Distance propagation from `X` supplies the Euler suppression,
while both complementary finite factors avoid this same large prime packet
and therefore receive the strong missing-block sieve saving.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b Erdos67b.EulerResidue Erdos67b.MRHalaszEuler
  Erdos67b.MRMultiplicativeEuler

/-- Restricting to a band which contains all primes through `Y` does not
change the pretentious distance at that cutoff. -/
theorem pretentiousDistSq_primeBandCoefficient_eq_of_primesUpTo
    (f g : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {Y : ℕ} (hP : ∀ p, p.Prime → p ≤ Y → P p) :
    pretentiousDistSq (primeBandCoefficient f P) g Y =
      pretentiousDistSq f g Y := by
  unfold pretentiousDistSq
  apply Finset.sum_congr rfl
  intro p hp
  have hpdata := mem_primesUpTo.mp hp
  rw [pretentiousTerm_primeBandCoefficient f g P hpdata.1,
    if_pos (hP p hpdata.1 hpdata.2)]

/-- Uniform Euler suppression for one fixed selected band containing every
prime through the lower cutoff.  This is the finite-Halasz `L∞` factor;
the other two factors may remain genuinely finite. -/
theorem exists_uniform_norm_fixedBand_LSeries_lower_halaszPoint_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A X Y : ℕ}
        (P : ℕ → Prop) [DecidablePred P],
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        (∀ p, p.Prime → p ≤ Y → P p) →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖LSeries (primeBandCoefficient f P) (halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ)) +
                3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
  obtain ⟨C, hC, hprop⟩ :=
    Erdos67b.MRHalaszDistancePropagation.exists_uniform_archimedean_distance_ge_at_lower_cutoff
  refine ⟨C, hC, ?_⟩
  intro f A X Y P _ hmul hbound hY hYX hP hnonpret t ht
  let fP := primeBandCoefficient f P
  have hmP : IsMultiplicativeOnPositiveNat fP :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P
  have hbP : ∀ n, 0 < n → ‖fP n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound P hn
  have hbase :=
    norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hmP hbP (show 1 < Y by omega) t
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  have hdist := hprop hY hYX
    (fun p hp ↦ hbound p hp.pos) hnonpret t ht
  have hdistP :
      (A : ℝ) -
            2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
              Real.log (Y + 1 : ℝ) ≤
        pretentiousDistSq fP (archimedeanTwist t) Y := by
    rw [pretentiousDistSq_primeBandCoefficient_eq_of_primesUpTo
      f (archimedeanTwist t) P hP]
    exact hdist
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  dsimp [fP] at hbase ⊢
  nlinarith

end

end Erdos67b.MRHalaszBands
