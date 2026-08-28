import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierHermitianBasic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth dependence of the Hermitian Fourier inverses

The scalar primitive and the top-degree inverse are jointly real smooth on the
nonzero-symbol locus. The same statements hold after composition with smooth
families on any subset of a real normed space; no choice of a nonzero component
is made.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian

open Complex
open scoped ComplexConjugate ContDiff

/-- The Hermitian energy is a globally smooth real polynomial. -/
theorem energy_contDiff : ContDiff ℝ ∞ energy := by
  have hn : ContDiff ℝ ∞ (normSq : ℂ → ℝ) := by
    change ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (hn.comp (contDiff_apply ℝ ℂ (0 : Fin 2))).add
    (hn.comp (contDiff_apply ℝ ℂ (1 : Fin 2)))

/-- The energy, regarded as a complex-valued function, is real smooth. -/
theorem energy_coe_contDiff :
    ContDiff ℝ ∞ (fun s : ComplexPlane₂ => (energy s : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp energy_contDiff

section Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Set E}

/-- Smooth families of nonzero symbols give smooth scalar primitives. -/
theorem potential_contDiffOn_comp {s a : E → ComplexPlane₂}
    (hs : ContDiffOn ℝ ∞ s U) (ha : ContDiffOn ℝ ∞ a U)
    (hne : ∀ x ∈ U, s x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => potential (s x) (a x)) U := by
  have hc (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => conj (s x i)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hs i)
  have hd : ContDiffOn ℝ ∞ (fun x => (energy (s x) : ℂ)⁻¹) U :=
    (energy_coe_contDiff.comp_contDiffOn hs).fun_inv
      (fun x hx => energy_coe_ne_zero (hne x hx))
  simpa only [potential, div_eq_mul_inv] using
    (((hc 0).mul (contDiffOn_pi.mp ha 0)).add
      ((hc 1).mul (contDiffOn_pi.mp ha 1))).mul hd

/-- Smooth families of nonzero symbols give smooth top-degree inverses. -/
theorem topInverse_contDiffOn_comp {s : E → ComplexPlane₂} {h : E → ℂ}
    (hs : ContDiffOn ℝ ∞ s U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ x ∈ U, s x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => topInverse (s x) (h x)) U := by
  have hc (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => conj (s x i)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hs i)
  have hd : ContDiffOn ℝ ∞ (fun x => (energy (s x) : ℂ)⁻¹) U :=
    (energy_coe_contDiff.comp_contDiffOn hs).fun_inv
      (fun x hx => energy_coe_ne_zero (hne x hx))
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ ∞
      (fun x => -conj (s x 1) * h x / (energy (s x) : ℂ)) U
    simpa only [div_eq_mul_inv] using ((hc 1).neg.mul hh).mul hd
  · change ContDiffOn ℝ ∞
      (fun x => conj (s x 0) * h x / (energy (s x) : ℂ)) U
    simpa only [div_eq_mul_inv] using ((hc 0).mul hh).mul hd

end Families

/-- Joint real smoothness of the scalar inverse away from the zero symbol. -/
theorem potential_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ComplexPlane₂ × ComplexPlane₂ => potential p.1 p.2)
      {p | p.1 ≠ 0} :=
  potential_contDiffOn_comp contDiffOn_fst contDiffOn_snd (fun _ hp => hp)

/-- Joint real smoothness of the top-degree inverse away from the zero symbol. -/
theorem topInverse_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ComplexPlane₂ × ℂ => topInverse p.1 p.2)
      {p | p.1 ≠ 0} :=
  topInverse_contDiffOn_comp contDiffOn_fst contDiffOn_snd (fun _ hp => hp)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierHermitian
