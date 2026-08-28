import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftNativeOrders

/-!
# Fixed-point derivative data determine a modular action

The actual centered Cayley coordinate shows that real determinant-one
actions fixing the same interior point agree if their complex derivatives
agree there.  The resulting integral-matrix statement identifies the
modular action of a global lift from its local ramification data.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularGroup Matrix
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Two real Möbius actions fixing the same interior point are determined
by their complex derivatives at that point. -/
theorem realSL_actions_eq_of_fixed_deriv (g h : SL(2, ℝ)) (a : ℍ)
    (hg : g • a = a) (hh : h • a = a)
    (hd : deriv (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) (a : ℂ) =
      deriv (fun z : ℂ => ((h • ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  have hm : Triangle.slMultiplier g a = Triangle.slMultiplier h a := by
    simpa only [Triangle.sl_deriv_smul] using hd
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a (h • z)
  rw [Triangle.cayleyCoordinate_smul g a z hg,
    Triangle.cayleyCoordinate_smul h a z hh, hm]

/-- The same uniqueness statement for the actual integral modular action,
with its possible central sign already absorbed in the action. -/
theorem modularSL_actions_eq_of_fixed_deriv (g h : SL(2, ℤ)) (a : ℍ)
    (hg : g • a = a) (hh : h • a = a)
    (hd : deriv (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) (a : ℂ) =
      deriv (fun z : ℂ => ((h • ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  simpa only [integerSL_real_action] using
    realSL_actions_eq_of_fixed_deriv
      (SpecialLinearGroup.map (Int.castRingHom ℝ) g)
      (SpecialLinearGroup.map (Int.castRingHom ℝ) h) a
      (by simpa only [integerSL_real_action] using hg)
      (by simpa only [integerSL_real_action] using hh)
      (by simpa only [integerSL_real_action] using hd)

/-- A complex formula for a modular action agrees with its actual ambient
germ at every upper-half-plane point, hence has the same derivative. -/
theorem modularSL_ambient_deriv_eq (g : SL(2, ℤ)) (f : ℂ → ℂ)
    (hf : ∀ z : ℍ, f z = ((g • z : ℍ) : ℂ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) (a : ℂ) = deriv f (a : ℂ) := by
  apply Filter.EventuallyEq.deriv_eq
  have hpos : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    isOpen_upperHalfPlaneSet.mem_nhds a.im_pos
  filter_upwards [hpos] with z hz
  simpa only [ofComplex_apply_of_im_pos hz] using (hf (ofComplex z)).symm

theorem modularRho_ambient_deriv :
    deriv (fun z : ℂ => (((T * S) • ofComplex z : ℍ) : ℂ)) (rhoPoint : ℂ) = -rho :=
  (modularSL_ambient_deriv_eq (T * S) modularRhoAction modularRhoAction_coe rhoPoint).trans
    modularRhoAction_deriv_rho

theorem modularI_ambient_deriv :
    deriv (fun z : ℂ => ((S • ofComplex z : ℍ) : ℂ)) (UpperHalfPlane.I : ℂ) = -1 :=
  (modularSL_ambient_deriv_eq S modularIAction modularIAction_coe UpperHalfPlane.I).trans
    modularIAction_deriv_I

/-- Invariance of the modular equation under one source automorphism gives
one fixed integral Möbius transformation on the entire lift.  The regular
value is an actual point, not an orbit-separation hypothesis. -/
theorem modularJ_invariant_lift_action {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (A : SL(2, ℝ))
    (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z))
    (x : ℍ) (hx : modularJ (τ x) ∈ modularRegularValues) :
    ∃ γ : SL(2, ℤ), ∀ z : ℍ, γ • τ z = τ (A • z) := by
  exact modularJ_equal_lifts_differ_by_SL hτ
    (hτ.comp (Triangle.specialLinear_holomorphic A)) (fun z => (hJ z).symm) x hx

end Wikipedia.HopfProblem.SpecialPeriods
