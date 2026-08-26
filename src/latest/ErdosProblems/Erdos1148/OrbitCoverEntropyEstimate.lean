import ErdosProblems.Erdos1148.RegularWordCoverFamilies
import ErdosProblems.Erdos1148.FiniteEntropyGapAlgebra
import ErdosProblems.Erdos1148.FiniteOrbitEntropy

/-! # A finite-time entropy estimate from a strict-rate orbit cover -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem orbitEntropy_le_of_two_covers {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι)
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ)
    (C : ι → Set ModularOrbitSpace) (hCsub : ∀ i, C i ⊆ P.atom i)
    {η τ β d Mg Ma : ℝ} {n Ng Na : ℕ} (hn : 0 < n) (hτ : 0 < τ)
    (hd : 0 ≤ d) (hMg : 1 ≤ Mg) (hMa : 0 ≤ Ma) (hβ : β ≤ 1 / 4)
    (hβq : 2 * β * Real.log (Fintype.card ι) ≤ d / 16)
    (hQ : MeasurableSet (⋃ i, C i)ᶜ) (hQmass : μ.real (⋃ i, C i)ᶜ / τ ≤ β)
    (hstable : ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ),
      EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i)
    (hwords : ∀ (v : Fin n → ι) (F : Finset (Fin n → ι)),
      (∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) →
      (F.card : ℝ) ≤ Real.exp (d / 16 * n))
    (Bg : Fin Ng → Set SL(2, ℝ)) (Ba : Fin Na → Set SL(2, ℝ))
    (hBg : ∀ i, LiftForwardClose η n (Bg i)) (hBa : ∀ i, LiftForwardClose η n (Ba i))
    (hNg : (Ng : ℝ) ≤ Mg * Real.exp ((1 - d) * n))
    (hNa : (Na : ℝ) ≤ Ma * Real.exp n)
    (hgmass : (3 / 4 : ℝ) ≤ μ.real (⋃ i, modularMk '' Bg i))
    (hamass : 1 - β ≤ μ.real (⋃ i, modularMk '' Ba i)) :
    P.orbitEntropy μ modularTimeOne n ≤ Real.log 3 + Real.log Mg + Real.log (Mg + Ma) +
      (1 - 3 * d / 8) * n := by
  classical
  obtain ⟨G, H, hGH, hGcard, hHcard, hGmass, hHmass⟩ := regular_word_families_of_covers
    P μ hf C hCsub hn hτ hQ hQmass hstable hwords Bg Ba hBg hBa hgmass hamass
  have hq : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hGbound : (G.card : ℝ) ≤ Mg * Real.exp ((1 - d + d / 16) * n) := by
    calc
      _ ≤ (Ng : ℝ) * Real.exp (d / 16 * n) := hGcard
      _ ≤ (Mg * Real.exp ((1 - d) * n)) * Real.exp (d / 16 * n) :=
        mul_le_mul_of_nonneg_right hNg (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hNg' : (Ng : ℝ) ≤ Mg * Real.exp n := hNg.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith only [hd, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (by linarith only [hMg]))
  have hHbound : (H.card : ℝ) ≤ (Mg + Ma) * Real.exp ((1 + d / 16) * n) := by
    calc
      _ ≤ ((Ng : ℝ) + Na) * Real.exp (d / 16 * n) := hHcard
      _ ≤ ((Mg + Ma) * Real.exp n) * Real.exp (d / 16 * n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith only [hNg', hNa]
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hcard : (Fintype.card (Fin n → ι) : ℝ) ≤
      Real.exp (Real.log (Fintype.card ι) * n) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by positivity)]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, le_refl]
  have hbad : (1 - ∑ w ∈ H, μ.real (P.orbitAtom modularTimeOne n w)) *
      Real.log (Fintype.card ι) ≤ d / 16 := by
    apply le_trans _ hβq
    exact mul_le_mul_of_nonneg_right (by linarith only [hHmass]) hq
  exact finiteEntropy_le_gap_of_word_families G H hGH
    (p := fun w => μ.real (P.orbitAtom modularTimeOne n w)) (fun _ => measureReal_nonneg)
    ((P.orbitPartition hf.measurable n).sum_mass μ) (Nat.cast_nonneg n) hd hMg
    (by linarith only [hMg, hMa]) hGbound hHbound hcard
    (by linarith only [hGmass, hβ]) hbad

end Erdos1148.DukeArithmetic
