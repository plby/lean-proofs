import ErdosProblems.Erdos1148.RealFormOrbit
import ErdosProblems.Erdos1148.FlowStabilizer
import ErdosProblems.Erdos1148.SignedFlow
import ErdosProblems.Erdos1148.BaseChange

/-!
# Real flow frames for integral pairs of forms

Each integral pair of positive discriminant admits real special-linear
lifts. Its integral mixed coefficient controls the close-flow parameter
area for these lifts, independently of their choice.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

structure IntegralPairFrame {d ℓ : ℤ} (p : FormPair ℤ d ℓ) where
  first : SL(2, ℝ)
  second : SL(2, ℝ)
  first_form : Real.sqrt (d : ℝ) • formAction first (splitForm ℝ) =
    mapCoeffs (Int.castRingHom ℝ) p.1.1
  second_form : Real.sqrt (d : ℝ) • formAction second (splitForm ℝ) =
    mapCoeffs (Int.castRingHom ℝ) p.1.2

lemma nonempty_integralPairFrame {d ℓ : ℤ} (hd : 0 < d) (p : FormPair ℤ d ℓ) :
    Nonempty (IntegralPairFrame p) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : discr (mapCoeffs (Int.castRingHom ℝ) p.1.1) = (d : ℝ) := by
    rw [discr_mapCoeffs, p.2.1]
    rfl
  have hu : discr (mapCoeffs (Int.castRingHom ℝ) p.1.2) = (d : ℝ) := by
    rw [discr_mapCoeffs, p.2.2.1]
    rfl
  obtain ⟨g, hg⟩ := exists_formAction_sqrt_discr hdR ht
  obtain ⟨h, hh⟩ := exists_formAction_sqrt_discr hdR hu
  exact ⟨⟨g, h, hg, hh⟩⟩

noncomputable def chooseIntegralPairFrame {d ℓ : ℤ} (hd : 0 < d)
    (p : FormPair ℤ d ℓ) : IntegralPairFrame p :=
  Classical.choice (nonempty_integralPairFrame hd p)

lemma IntegralPairFrame.relative_pairing {d ℓ : ℤ} (hd : 0 < d)
    {p : FormPair ℤ d ℓ} (f : IntegralPairFrame p) :
    (ℓ : ℝ) = (d : ℝ) *
      (2 + 4 * (f.first⁻¹ * f.second) 0 1 * (f.first⁻¹ * f.second) 1 0) := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
  calc
    (ℓ : ℝ) = pairing (mapCoeffs (Int.castRingHom ℝ) p.1.1)
        (mapCoeffs (Int.castRingHom ℝ) p.1.2) := by
      rw [pairing_mapCoeffs, p.2.2.2]
      rfl
    _ = (Real.sqrt (d : ℝ)) ^ 2 *
        (2 + 4 * (f.first⁻¹ * f.second) 0 1 * (f.first⁻¹ * f.second) 1 0) := by
      rw [← f.first_form, ← f.second_form, pairing_scaled_relative_action]
    _ = _ := by rw [Real.sq_sqrt hdR]

theorem IntegralPairFrame.volume_close_times_le {d ℓ : ℤ}
    (hd : 0 < d) (hℓ : ℓ ≠ 2 * d) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    {p : FormPair ℤ d ℓ} (f : IntegralPairFrame p) :
    volume (signedCloseDiagonalFlowTimes (f.first⁻¹ * f.second) η) ≤
      ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) :=
  volume_signedCloseDiagonalFlowTimes_le hd hℓ hη0 hη _ (f.relative_pairing hd)

end Erdos1148.DukeArithmetic
