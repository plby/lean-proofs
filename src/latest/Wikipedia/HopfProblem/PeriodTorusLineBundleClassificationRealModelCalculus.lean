import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierPeriodCoordinates

/-!
# Native coordinate calculus for the logarithmic normal-form construction

These statements concern the literal coordinate-update antiholomorphic
derivative on `ComplexPlane₂`. Smoothness and mixed commutation are
consequences of the actual real differential, not formal derivative rules.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex
open scoped ContDiff

def dbarCoordinateLinear (i : Fin 2) : (ComplexPlane₂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1) +
    I • ContinuousLinearMap.apply ℝ ℂ (I • Pi.single i 1))

@[simp]
theorem dbarCoordinateLinear_apply (i : Fin 2) (L : ComplexPlane₂ →L[ℝ] ℂ) :
    dbarCoordinateLinear i L = (L (Pi.single i 1) + I * L (I • Pi.single i 1)) / 2 := by
  simp only [dbarCoordinateLinear, smul_apply,
    add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem dbarCoordinate_eq_linear {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    dbarCoordinate f i z = dbarCoordinateLinear i (fderiv ℝ f z) := by
  rw [dbarCoordinate_eq_fderiv hf, dbarCoordinateLinear_apply]

theorem dbarCoordinateLinear_complex_smul (i : Fin 2) (c : ℂ)
    (L : ComplexPlane₂ →L[ℝ] ℂ) :
    dbarCoordinateLinear i (c • L) = c * dbarCoordinateLinear i L := by
  simp only [dbarCoordinateLinear_apply, smul_apply, smul_eq_mul]
  ring

theorem contDiff_dbarCoordinate {f : ComplexPlane₂ → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ContDiff ℝ ∞ (dbarCoordinate f i) := by
  have he : dbarCoordinate f i = dbarCoordinateLinear i ∘ fderiv ℝ f :=
    funext (fun z => dbarCoordinate_eq_linear (hf.differentiable (by simp) z) i)
  rw [he]
  exact (dbarCoordinateLinear i).contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

@[simp]
theorem dbarCoordinate_const (c : ℂ) (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (fun _ => c) i z = 0 := by
  simp [dbarCoordinate, HolomorphicCousin.dbar]

theorem dbarCoordinate_add {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    dbarCoordinate (fun x => f x + g x) i z = dbarCoordinate f i z + dbarCoordinate g i z := by
  have hfg : DifferentiableAt ℝ (fun x => f x + g x) z := hf.add hg
  rw [dbarCoordinate_eq_linear hfg, fderiv_fun_add hf hg, map_add,
    ← dbarCoordinate_eq_linear hf, ← dbarCoordinate_eq_linear hg]

theorem dbarCoordinate_sub {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    dbarCoordinate (fun x => f x - g x) i z = dbarCoordinate f i z - dbarCoordinate g i z := by
  have hfg : DifferentiableAt ℝ (fun x => f x - g x) z := hf.sub hg
  rw [dbarCoordinate_eq_linear hfg, fderiv_fun_sub hf hg, map_sub,
    ← dbarCoordinate_eq_linear hf, ← dbarCoordinate_eq_linear hg]

theorem dbarCoordinate_const_mul {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) (i : Fin 2) :
    dbarCoordinate (fun x => c * f x) i z = c * dbarCoordinate f i z := by
  have hcf : DifferentiableAt ℝ (fun x => c * f x) z := hf.const_mul c
  rw [dbarCoordinate_eq_linear hcf, (hf.hasFDerivAt.const_mul c).fderiv,
    dbarCoordinateLinear_complex_smul, ← dbarCoordinate_eq_linear hf]

/-- The literal coordinate operator commutes with a translation in the cover. -/
theorem dbarCoordinate_translate {f : ComplexPlane₂ → ℂ} {z a : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f (z + a)) (i : Fin 2) :
    dbarCoordinate (fun x => f (x + a)) i z = dbarCoordinate f i (z + a) := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) z).add_const a
  have hd : HasFDerivAt (fun x => f (x + a)) (fderiv ℝ f (z + a)) z := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hf.hasFDerivAt.comp z ht
  rw [dbarCoordinate_eq_linear hd.differentiableAt, hd.fderiv,
    ← dbarCoordinate_eq_linear hf]

theorem dbarCoordinate_zero_of_differentiableAt {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℂ f z) (i : Fin 2) : dbarCoordinate f i z = 0 := by
  have hf' : DifferentiableAt ℂ f (Function.update z i (z i)) := by simpa using hf
  exact HolomorphicCousin.dbar_eq_zero_of_differentiableAt
    (hf'.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt)

open PeriodTorusLineBundleClassificationPolydiscAnalytic (complexPairEquiv)

/-- Actual mixed derivatives commute in the native coordinate model. -/
theorem dbarCoordinate_zero_one_commute {f : ComplexPlane₂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z : ComplexPlane₂) :
    dbarCoordinate (dbarCoordinate f 1) 0 z = dbarCoordinate (dbarCoordinate f 0) 1 z := by
  let g := f ∘ complexPairEquiv.symm
  have h0 : dbarCoordinate f 0 = dbarFirst g ∘ complexPairEquiv :=
    funext (dbarCoordinate_zero_eq_pair f)
  have h1 : dbarCoordinate f 1 = dbarSecond g ∘ complexPairEquiv :=
    funext (dbarCoordinate_one_eq_pair f)
  rw [h1, h0, dbarCoordinate_pair_zero, dbarCoordinate_pair_one]
  exact dbarFirst_dbarSecond (hf.comp (complexPairEquiv.symm.contDiff.restrict_scalars ℝ)) _

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
