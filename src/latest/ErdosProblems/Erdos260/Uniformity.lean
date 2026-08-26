import ErdosProblems.Erdos260.Exterior

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Uniformity and the constant hierarchy

This module corresponds to Appendix D of the manuscript.
-/

noncomputable section

open Filter Set Topology

namespace Erdos260

def normalizationScale (W : WindowSystem) : ℝ :=
  W.m * W.X * thresholdLength W

def boundaryLossRatio (W : WindowSystem) : ℝ :=
  ((W.s + 1 : ℕ) : ℝ) * (W.L : ℝ) ^ 2 / (W.m * W.X)

def rareMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  rareLargePairsMass W Z0 / normalizationScale W

def exteriorMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  exteriorPairsMass W Z0 / normalizationScale W

def interiorMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  interiorPairsMass W Z0 / normalizationScale W

/-- Paper label: `prop:uniform-errors` (Appendix D).  One cutoff and one
nonnegative interior coefficient function are selected from the
denominator-level context before the rational numerator/support family.  The
rare, exterior, and interior conclusions are asserted uniformly for every
cutoff beyond that common threshold; their eventual scales may still depend
on the compatible family and cutoff. -/
theorem prop_uniform_errors (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ interiorBound : ℕ → ℝ,
      (∀ Z0, 0 ≤ interiorBound Z0) ∧
      Tendsto interiorBound atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        Tendsto (fun L => boundaryLossRatio (F.system L)) atTop (𝓝 0) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => rareLargePairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => exteriorPairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        ∀ Z0, Zmin ≤ Z0 → ∀ᶠ L : ℕ in atTop,
          interiorMassRatio (F.system L) Z0 ≤ interiorBound Z0 := by
  obtain ⟨Zstrict, ηQ, hηQ_nonneg, hηQ_zero, hstrict⟩ :=
    thm_strict_mass context
  obtain ⟨Zoff, hoff⟩ := thm_off_mass context
  let Zrare := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zmin := max Zstrict (max Zrare Zoff)
  refine ⟨Zmin, ηQ, hηQ_nonneg, hηQ_zero, ?_⟩
  intro F hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hlim :=
      tendsto_pow_const_div_const_pow_of_one_lt 2
        (by norm_num : (1 : ℝ) < 2)
    convert hlim using 1
    funext L
    simp only [boundaryLossRatio, WindowSystem.m, WindowSystem.X,
      dyadicScale, F.level_eq, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat]
    have hm : (0 : ℝ) < (F.system L).s + 1 := by positivity
    field_simp
  · intro Z0 hZ0
    have hrare : Zrare ≤ Z0 :=
      le_trans
        (le_trans (le_max_left Zrare Zoff)
          (le_max_right Zstrict (max Zrare Zoff))) hZ0
    simpa [normalizationScale] using
      (prop_low_firstdeep context Z0 hrare F hF)
  · intro Z0 hZ0
    have hZoff : Zoff ≤ Z0 :=
      le_trans
        (le_trans (le_max_right Zrare Zoff)
          (le_max_right Zstrict (max Zrare Zoff))) hZ0
    simpa [normalizationScale] using
      (hoff Z0 hZoff F hF)
  · intro Z0 hZ0
    have hZstrict : Zstrict ≤ Z0 :=
      le_trans (le_max_left Zstrict (max Zrare Zoff)) hZ0
    filter_upwards [hstrict Z0 hZstrict F hF, eventually_ge_atTop 1] with L hL hLpos
    obtain ⟨_refinement, hmass⟩ := hL
    have hnormalization : 0 < normalizationScale (F.system L) := by
      rw [normalizationScale, thresholdLength, F.level_eq]
      have hm : (0 : ℝ) < (F.system L).m := by
        exact_mod_cast Nat.succ_pos (F.system L).s
      have hX : (0 : ℝ) < (F.system L).X := by
        exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
      have hcI : 0 < (F.system L).structural.cI :=
        (F.system L).structural.cI_pos
      have hLreal : (0 : ℝ) < L := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hLpos)
      positivity
    rw [interiorMassRatio, div_le_iff₀ hnormalization]
    simpa [normalizationScale, mul_assoc] using hmass

end Erdos260
