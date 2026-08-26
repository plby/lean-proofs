import ErdosProblems.Erdos1148.PacketRefinedGlobalMass
import ErdosProblems.Erdos1148.RefinedMassScale
import ErdosProblems.Erdos1148.CuspVisitExceedance
import ErdosProblems.Erdos1148.PacketPowerHeightEscape

/-! # Long high-cusp visit fractions have vanishing normalized packet mass -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem exists_packet_high_cusp_visit_power_bound {α : ℝ} (hαpos : 0 < α) (hα : α ≤ 1) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)), IntegralDiscrForm d →
        (normalizedDiscriminantPacket hd hns).real
          (modularHighCuspVisits H ((d : ℝ) ^ (α / 176)) (packetObservationTime (d : ℝ))
            (α * (packetObservationTime (d : ℝ) : ℝ))) ^ 2 ≤ C * (d : ℝ) ^ (-α / 16) := by
  obtain ⟨H₀, hH₀, hbound⟩ := exists_unconditional_packet_global_high_cusp_mass_bound
    (η := 1 / 256) (ε := α / 8) (σ := α / 16) (by norm_num) (by norm_num)
    (by positivity) (by positivity)
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨C, hC, hmass⟩ := hbound H hH
  refine ⟨C * (2 ^ 11 * (1 + Real.exp 1)), by positivity, ?_⟩
  intro d hd hns base
  have hd1 : 1 ≤ d := by omega
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hY : 1 ≤ (d : ℝ) ^ (α / 176) := Real.one_le_rpow hD (by positivity)
  have hm := hmass ((d : ℝ) ^ (α / 176)) hY d hd hns base (packetObservationTime (d : ℝ))
    (α * (packetObservationTime (d : ℝ) : ℝ))
  have hs := refined_global_mass_scale_decay hD hαpos hα
  have hscaled := mul_le_mul_of_nonneg_left hs hC.le
  calc
    _ ≤ C * ((d : ℝ) ^ (α / 176) + 1) ^ 11 *
        Real.exp ((1 + α / 8) * (packetObservationTime (d : ℝ) : ℝ) -
          (α * (packetObservationTime (d : ℝ) : ℝ)) / 2) *
        ((d : ℝ) ^ (-1 / 2 + α / 16) + (d : ℝ) ^ (α / 16) *
          Real.exp (-(packetObservationTime (d : ℝ) : ℝ))) := hm
    _ = C * (((d : ℝ) ^ (α / 176) + 1) ^ 11 *
        Real.exp ((1 + α / 8) * (packetObservationTime (d : ℝ) : ℝ) -
          (α * (packetObservationTime (d : ℝ) : ℝ)) / 2) *
        ((d : ℝ) ^ (-1 / 2 + α / 16) + (d : ℝ) ^ (α / 16) *
          Real.exp (-(packetObservationTime (d : ℝ) : ℝ)))) := by ring
    _ ≤ C * ((2 ^ 11 * (1 + Real.exp 1)) * (d : ℝ) ^ (-α / 16)) := hscaled
    _ = _ := by ring

theorem normalizedPacket_cusp_visit_exceedance_tendsto_zero
    {ι : Type*} {l : Filter ι} {d : ι → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d l atTop)
    {α : ℝ} (hαpos : 0 < α) (hα : α ≤ 1) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      Tendsto (fun i => (normalizedDiscriminantPacket (hd i) (hns i)).real
        (modularCuspVisitExceedance H (packetObservationTime (d i : ℝ))
          (α * (packetObservationTime (d i : ℝ) : ℝ)))) l (𝓝 0) := by
  obtain ⟨H₀, hH₀, hbound⟩ := exists_packet_high_cusp_visit_power_bound hαpos hα
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨C, hC, hmass⟩ := hbound H hH
  have hdRlim : Tendsto (fun i => (d i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hlim
  have hp : Tendsto (fun i => (d i : ℝ) ^ (-α / 16)) l (𝓝 0) := by
    have heq : -α / 16 = -(α / 16) := by ring
    rw [heq]
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < α / 16)).comp hdRlim
  have hupp : Tendsto (fun i => C * (d i : ℝ) ^ (-α / 16)) l (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul C
  have hsquared := squeeze_zero'
    (Eventually.of_forall (fun i => sq_nonneg ((normalizedDiscriminantPacket (hd i) (hns i)).real
      (modularHighCuspVisits H ((d i : ℝ) ^ (α / 176)) (packetObservationTime (d i : ℝ))
        (α * (packetObservationTime (d i : ℝ) : ℝ))))))
    (Eventually.of_forall (fun i => hmass (d i) (hd i) (hns i) (base i))) hupp
  have hlow : Tendsto (fun i => (normalizedDiscriminantPacket (hd i) (hns i)).real
      (modularHighCuspVisits H ((d i : ℝ) ^ (α / 176)) (packetObservationTime (d i : ℝ))
        (α * (packetObservationTime (d i : ℝ) : ℝ)))) l (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsquared
    simpa only [Function.comp_def, Real.sqrt_sq measureReal_nonneg, Real.sqrt_zero] using h
  have hheight := normalizedPacket_cusp_power_tendsto_zero hd hns base hlim
    (by positivity : 0 < α / 176)
  have hsum := hheight.add hlow
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  apply Eventually.of_forall
  intro i
  let μ := normalizedDiscriminantPacket (hd i) (hns i)
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability (hd i) (hns i) (base i)
  exact cusp_visit_exceedance_mass_le μ H ((d i : ℝ) ^ (α / 176))
    (packetObservationTime (d i : ℝ)) (α * (packetObservationTime (d i : ℝ) : ℝ))

end Erdos1148.DukeArithmetic
