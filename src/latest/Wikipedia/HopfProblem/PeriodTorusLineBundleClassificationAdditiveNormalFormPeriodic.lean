import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus

/-!
# Periodic antiholomorphic derivatives of an additive lattice primitive

If the actual lattice differences of a smooth function on the cover
are holomorphic, its actual coordinate antiholomorphic derivatives are
lattice periodic.  This follows by differentiating the given function
identity, using the ordinary translation and subtraction rules.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open scoped ContDiff

/-- Holomorphic lattice differences force the actual coordinate
antiholomorphic derivatives of the primitive to be periodic. -/
theorem dbarCoordinate_periodic_of_holomorphic_lattice_differences (p : PeriodDomain)
    {h : ComplexPlane₂ → ℂ} {k : p.lattice → ComplexPlane₂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hk : ∀ l, ContDiff ℂ ω (k l))
    (hshift : ∀ l : p.lattice, ∀ z, h (z + l) - h z = k l z)
    (i : Fin 2) (z : ComplexPlane₂) (l : p.lattice) :
    dbarCoordinate h i (z + l) = dbarCoordinate h i z := by
  have he : (fun x : ComplexPlane₂ => h (x + l) - h x) = k l :=
    funext (hshift l)
  have hd := congrArg (fun v : ComplexPlane₂ → ℂ => dbarCoordinate v i z) he
  have ht : DifferentiableAt ℝ (fun x : ComplexPlane₂ => h (x + l)) z :=
    (hh.differentiable (by simp) (z + l)).comp z (differentiableAt_id.add_const _)
  rw [dbarCoordinate_sub ht (hh.differentiable (by simp) z),
    dbarCoordinate_translate (hh.differentiable (by simp) (z + l)),
    dbarCoordinate_zero_of_differentiableAt ((hk l).differentiable (by simp) z)] at hd
  exact sub_eq_zero.mp hd

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
