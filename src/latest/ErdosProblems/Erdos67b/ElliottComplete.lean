import ErdosProblems.Erdos67b.MRTComplete
import ErdosProblems.Erdos67b.PrimeGraphFourierUpper
import ErdosProblems.Erdos67b.ElliottFourierMoment

/-! # The unconditional unit-circle logarithmically averaged Elliott theorem

The graph criterion and MRT are both proved inputs. Only finite maxima,
the exact Fourier convention, and the harmonic normalization are assembled here.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter

namespace Erdos67b

open FiniteEntropy

noncomputable section

theorem elliottExists_finalThreshold (L₀ N : ℕ) (M₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℕ, 4 ≤ A₀ ∧ N ≤ A₀ ∧ 2 * L₀ ≤ A₀ ∧
      ∀ W : ℕ, A₀ ≤ W →
        2 * ((L₀ : ℝ) + 1) ≤ Real.log W ∧
        M₀ ≤ Real.log W / 2 ∧ (L₀ : ℝ) ≤ (ε / 2) * Real.log W := by
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop
      (max (2 * ((L₀ : ℝ) + 1)) (max (2 * M₀) (2 * L₀ / ε)))))
  let A₀ := max 4 (max N (max (2 * L₀) A₁))
  have h4 : 4 ≤ A₀ := le_max_left _ _
  have hN : N ≤ A₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL : 2 * L₀ ≤ A₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hA : A₁ ≤ A₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨A₀, h4, hN, hL, ?_⟩
  intro W hW
  have hh := hA₁ W (hA.trans hW)
  have hfirst := (le_max_left _ _).trans hh
  have hlast := (le_max_right _ _).trans hh
  have hmass := (le_max_left _ _).trans hlast
  have herror := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hlast)
  exact ⟨hfirst, by linarith only [hmass], by nlinarith only [herror]⟩

theorem unitCircleLogElliott : UnitCircleLogElliott := by
  intro ε hε h hh
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ζ, hζ, hgraph⟩ := exists_logPairCorrelation_small_of_fourier_first_moments hh hη
  let δ : ℝ := ζ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Hmin, hHmin, hmrt⟩ := mrtModulatedShortIntervalUnrestricted δ hδ
  obtain ⟨H₀, J, L₀, M₀, hH₀min, hH₀, hJ, hL₀, hM₀, hgraphMain⟩ := hgraph Hmin
  let Hmax := max H₀ ((range J).sup (entropyScale H₀))
  have hHmax : Hmin ≤ Hmax := hH₀min.trans (le_max_left _ _)
  obtain ⟨N, hN, hmrtMain⟩ := hmrt Hmax hHmax
  obtain ⟨A₀, hA₀4, hA₀N, hA₀L, hthreshold⟩ := elliottExists_finalThreshold L₀ N M₀ hε
  refine ⟨A₀, by omega, ?_⟩
  intro A X W hA hAW hWX f hmul hunit hpret
  have hA₀W : A₀ ≤ W := hA.trans hAW
  have hW4 : 4 ≤ W := hA₀4.trans hA₀W
  have hW : 0 < W := by omega
  obtain ⟨hlog, hmassThreshold, herror⟩ := hthreshold W hA₀W
  let L := elliottTrimmedLower X W L₀
  obtain ⟨hL, hLL, hLX⟩ := elliottTrimmedLower_geometry hW4 hWX
    (hA₀L.trans (hA₀W.trans hWX))
  obtain ⟨hMlo, hMhi⟩ := elliottTrimmedMass_bounds hW hWX hlog
  have hM : 0 < (logProbMassNN L X : ℝ) := by
    exact_mod_cast logProbMassNN_pos hL (by omega)
  have hcorr : ‖logPairCorrelation L X f h‖ < η := by
    apply hgraphMain L X hL hLX hLL (hmassThreshold.trans hMlo) f hmul hunit
    intro j hj t _ht
    have hHlo : Hmin ≤ entropyScale H₀ j := hH₀min.trans (le_entropyScale H₀ j)
    have hHhi : entropyScale H₀ j ≤ Hmax :=
      (Finset.le_sup (f := entropyScale H₀) (mem_range.2 hj)).trans (le_max_right _ _)
    have hfirst := hmrtMain A X W (entropyScale H₀ j) (hA₀N.trans hA) hAW hWX
      hHlo hHhi f hmul hunit hpret ((t : ℝ) / (4 * h * entropyScale H₀ j + 1))
    have hbound := logProb_fourier_firstMoment_of_MRT hW
      (show 0 < entropyScale H₀ j by omega) hM hMlo hδ.le f
      (4 * h * entropyScale H₀ j + 1) (t : ℤ) (by
        simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          using hfirst)
    exact hbound.trans (by dsimp [δ]; nlinarith [Nat.cast_nonneg (α := ℝ) (entropyScale H₀ j)])
  rw [logPairCorrelation, logProbExpectation_eq_mass_inv_smul_sum,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), inv_mul_eq_div] at hcorr
  have hsum := (div_lt_iff₀ hM).1 hcorr
  have htrim := norm_shiftedLogCorrelation_le_trimmed (X := X) hW L₀ h f hunit
  calc
    ‖shiftedLogCorrelation f h X W‖ ≤
        ‖∑ n ∈ Icc L X, (n : ℝ)⁻¹ • (f n * conj (f (n + h)))‖ + L₀ := htrim
    _ ≤ η * (logProbMassNN L X : ℝ) + L₀ := add_le_add hsum.le le_rfl
    _ ≤ η * (2 * Real.log W) + (ε / 2) * Real.log W :=
      add_le_add (mul_le_mul_of_nonneg_left hMhi hη.le) herror
    _ = ε * Real.log W := by dsimp [η]; ring

end

end Erdos67b
