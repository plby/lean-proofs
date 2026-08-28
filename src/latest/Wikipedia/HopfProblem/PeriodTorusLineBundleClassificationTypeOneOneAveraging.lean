import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarClosed

/-!
# Constants cannot be derivatives of smooth periodic data

This is an actual averaging statement on the period torus. It uses the
proved zero Fourier coefficient of the genuine Dolbeault derivative, and
descends arbitrary smooth lattice-periodic functions through the actual
period marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open UnitAddTorus
open scoped ContDiff

theorem constant_eq_zero_of_torus_dbar_difference (p : PeriodDomain)
    (f g : SmoothTorusFunction (Fin 4)) (i j : Fin 2) (c : ℂ)
    (h : ∀ t, torusDbar p g i t - torusDbar p f j t = c) : c = 0 := by
  have he : (torusDbar p g i).toContinuousMap - (torusDbar p f j).toContinuousMap =
      ContinuousMap.const _ c := ContinuousMap.ext h
  have hc := congrArg (fun F : C(UnitAddTorus (Fin 4), ℂ) => mFourierCoeff F 0) he
  rw [torusFourierCoeff_sub] at hc
  have hconst : mFourierCoeff (ContinuousMap.const (UnitAddTorus (Fin 4)) c) 0 = c := by
    change mFourierCoeff (fun _ : UnitAddTorus (Fin 4) => c) 0 = c
    rw [mFourierCoeff_const]
    simp
  change torusFourierMean (torusDbar p g i) - torusFourierMean (torusDbar p f j) = _ at hc
  rw [torusFourierMean_torusDbar, torusFourierMean_torusDbar, sub_self, hconst] at hc
  exact hc.symm

/-- A literal constant mixed derivative of actual periodic functions is zero. -/
theorem constant_eq_zero_of_periodic_dbar_difference (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (i j : Fin 2) (c : ℂ)
    (h : ∀ z, dbarCoordinate g i z - dbarCoordinate f j z = c) : c = 0 := by
  let fT := smoothTorusOfLatticePeriodic p f hf hpf
  let gT := smoothTorusOfLatticePeriodic p g hg hpg
  have heF : periodTorusLift p fT = f :=
    funext (periodTorusLift_smoothTorusOfLatticePeriodic p f hf hpf)
  have heG : periodTorusLift p gT = g :=
    funext (periodTorusLift_smoothTorusOfLatticePeriodic p g hg hpg)
  apply constant_eq_zero_of_torus_dbar_difference p fT gT i j c
  intro t
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  have hx := h (PeriodTorusTypeOneOne.periodEquiv p x)
  rw [← heF, ← heG, dbarCoordinate_periodTorusLift, dbarCoordinate_periodTorusLift,
    periodTorusLift_periodEquiv, periodTorusLift_periodEquiv] at hx
  exact hx

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
