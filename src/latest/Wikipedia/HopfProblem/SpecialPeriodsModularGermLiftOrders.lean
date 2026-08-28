import Wikipedia.HopfProblem.SpecialPeriodsModularRamification

/-!
# Exact orders of actual analytic modular lifts

The order formula for composition applies to any actual local lift through
the normalized modular function.  It divides the source order by three over
zero and by two over `1728`, without choosing coordinates or a modular orbit
representative.  The corresponding pulled-back Eisenstein series has the
same order as the local lift at its elliptic value.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularForm
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

private theorem enat_eq_nat_of_mul_eq {x : ℕ∞} {m n : ℕ} (hm : 0 < m)
    (h : (m : ℕ∞) * x = (m * n : ℕ)) : x = n := by
  have hm0 : (m : ℕ∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hfin : x ≠ ⊤ := by
    intro hx
    rw [hx, ENat.mul_top hm0] at h
    exact ENat.top_ne_natCast _ h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at h
  have hkn : k = n := by
    have hmul : m * k = m * n := by exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hm hmul
  rw [← hk, hkn]

/-- The composition-order identity for a genuine analytic lift. -/
theorem modularJ_lift_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => modularJ (ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt F a =
      analyticOrderAt (modularJ ∘ ofComplex) (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hj : AnalyticAt ℂ (modularJ ∘ ofComplex) (τ a) := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      modularJ_analyticAt (ofComplex (τ a))
  exact (analyticOrderAt_congr hJ).symm.trans (hj.analyticOrderAt_comp hτ)

/-- The shifted composition formula at the other elliptic value. -/
theorem modularJ_lift_sub_1728_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => modularJ (ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt (fun z => F z - 1728) a =
      analyticOrderAt (fun z => modularJ (ofComplex z) - 1728) (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hjbase : AnalyticAt ℂ (modularJ ∘ ofComplex) (τ a) := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      modularJ_analyticAt (ofComplex (τ a))
  have hj : AnalyticAt ℂ (fun z => modularJ (ofComplex z) - 1728) (τ a) :=
    hjbase.sub analyticAt_const
  have he : (fun z => modularJ (ofComplex (τ z)) - 1728) =ᶠ[𝓝 a]
      (fun z => F z - 1728) := hJ.sub (Filter.EventuallyEq.rfl)
  exact (analyticOrderAt_congr he).symm.trans (hj.analyticOrderAt_comp hτ)

/-- Every local lift at a zero of source order `3n` has exact order `n`. -/
theorem modularJ_lift_order_of_zero {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => modularJ (ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 0) (horder : analyticOrderAt F a = (3 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj0 : modularJ (ofComplex (τ a)) = 0 := hJ.self_of_nhds.trans ha
  have hjord : analyticOrderAt (modularJ ∘ ofComplex) (τ a) = 3 := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      analyticOrderAt_modularJ_of_eq_zero (ofComplex (τ a)) hj0
  have hmul := modularJ_lift_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq (by decide : 0 < 3) hmul.symm

/-- Every local lift at a `1728`-point of source order `2n` has exact order `n`. -/
theorem modularJ_lift_order_of_1728 {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => modularJ (ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 1728)
    (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj1728 : modularJ (ofComplex (τ a)) = 1728 := hJ.self_of_nhds.trans ha
  have hjord : analyticOrderAt (fun z => modularJ (ofComplex z) - 1728) (τ a) = 2 := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      analyticOrderAt_modularJ_sub_1728_of_eq (ofComplex (τ a)) hj1728
  have hmul := modularJ_lift_sub_1728_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq (by decide : 0 < 2) hmul.symm

/-- Pulling back the simple zero of `E₄` gives the exact order of the lift. -/
theorem E₄_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : E₄ (ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => E₄ (ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (E₄ ∘ ofComplex) (τ a) := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      modularForm_analyticAt E₄ (ofComplex (τ a))
  have ho : analyticOrderAt (E₄ ∘ ofComplex) (τ a) = 1 := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      analyticOrderAt_E₄_of_eq_zero (ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => E₄ (ofComplex (τ z))) a =
        analyticOrderAt (E₄ ∘ ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a := hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

/-- Pulling back the simple zero of `E₆` gives the exact order of the lift. -/
theorem E₆_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : E₆ (ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => E₆ (ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (E₆ ∘ ofComplex) (τ a) := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      modularForm_analyticAt E₆ (ofComplex (τ a))
  have ho : analyticOrderAt (E₆ ∘ ofComplex) (τ a) = 1 := by
    simpa only [ofComplex_apply_of_im_pos hpos] using
      analyticOrderAt_E₆_of_eq_zero (ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => E₆ (ofComplex (τ z))) a =
        analyticOrderAt (E₆ ∘ ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a := hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
