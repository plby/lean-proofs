import ErdosProblems.Erdos1148.BoundedFrameInjectivity
import ErdosProblems.Erdos1148.PacketClosePairs

/-! # Upgrading nearby lifts using quotient closeness in an injective neighborhood -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_close_lift_over_fixed_base {η : ℝ} (g : SL(2, ℝ))
    {y : ModularOrbitSpace} (hpair : (modularMk g, y) ∈ modularClosePairs η) :
    ∃ h : SL(2, ℝ), modularMk h = y ∧ EntryCloseOne η (g⁻¹ * h) := by
  obtain ⟨g', h', hpair', hclose⟩ := hpair
  have hfirst : modularMk g' = modularMk g := (congrArg Prod.fst hpair').symm
  have hsecond : modularMk h' = y := (congrArg Prod.snd hpair').symm
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff g' g).mp hfirst
  refine ⟨(γ : SL(2, ℝ)) * h', (modularMk_integral_mul γ h').trans hsecond, ?_⟩
  rw [← hγ]
  have heq : ((γ : SL(2, ℝ)) * g')⁻¹ * ((γ : SL(2, ℝ)) * h') = g'⁻¹ * h' := by group
  rwa [heq]

theorem entryCloseOne_of_close_lifts_and_modularClosePairs {A α η : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hαone : α ≤ 1) (hηα : η ≤ α)
    (hscale : 16 * A ^ 2 * α < 1) (g h : SL(2, ℝ))
    (hg : ∀ i j : Fin 2, |g i j| ≤ A) (hclose : EntryCloseOne α (g⁻¹ * h))
    (hpair : (modularMk g, modularMk h) ∈ modularClosePairs η) :
    EntryCloseOne η (g⁻¹ * h) := by
  obtain ⟨h', hmk, hnear⟩ := exists_close_lift_over_fixed_base g hpair
  have heq : modularMk (g * (g⁻¹ * h)) = modularMk (g * (g⁻¹ * h')) := by
    simpa only [mul_inv_cancel_left] using hmk.symm
  have hlift := modularMk_injective_on_small_right_neighborhood hA hα hαone hscale g hg
    hclose (entryCloseOne_mono hnear hηα) heq
  rw [hlift]
  exact hnear

end Erdos1148.DukeArithmetic
