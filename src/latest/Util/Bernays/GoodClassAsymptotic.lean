import Util.Bernays.SharpCancellation
import Util.Bernays.FiniteGroupDistribution
import Util.Bernays.GoodClassCounts

/-!
# The same positive leading constant for all coprime ideal classes
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem genusLocal_character_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ goodLocalValues d b hD.ne N, ψ (Additive.ofMul (genusValue hD n))) / (scale N : ℂ))
        atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := genusLocal_sharp_norm_cancellation hD ψ hψ
  apply h.congr'
  filter_upwards [] with N
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg
    (show 0 ≤ scale N from div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)), genusLocalAF_sum]

noncomputable def goodClassConstant {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ℝ :=
  letI := quadraticOrderIsDomain hD
  goodLocalConstant d b hD.ne / Nat.card (GenusGroup (QuadraticAlgebra ℤ d b))

theorem goodClassConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : 0 < goodClassConstant hD := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  change 0 < goodLocalConstant d b hD.ne / (Nat.card (GenusGroup (QuadraticAlgebra ℤ d b)) : ℝ)
  exact div_pos (goodLocalConstant_pos hD) (Nat.cast_pos.mpr Nat.card_pos)

theorem genusValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ g : GenusGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ((genusValues hD g N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (GenusGroup (QuadraticAlgebra ℤ d b)) := Fintype.ofFinite _
  intro g
  have h := fiber_card_limit_of_character_cancellation (goodLocalValues d b hD.ne)
    (genusValue hD) (fun N : ℕ => scale N) (goodLocalValues_card_limit hD)
    (genusLocal_character_cancellation hD) g
  have hcount (N : ℕ) : eventCount (goodLocalValues d b hD.ne N) (fun n => genusValue hD n = g) =
      (genusValues hD g N).card := by
    unfold eventCount goodLocalValues genusValues
    rw [Finset.filter_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter]
  simpa only [hcount, goodClassConstant, Nat.card_eq_fintype_card] using h

theorem goodClassValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ((goodClassValues hD C N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  intro C
  have h := (genusValues_card_limit hD (genusMap C)).sub (goodClass_genus_count_error_limit hD C)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  change ((genusValues hD (genusMap C) N).card : ℝ) / scale N -
    (((genusValues hD (genusMap C) N).card : ℝ) - (goodClassValues hD C N).card) / scale N = _
  ring

end Bernays
