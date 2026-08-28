import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationAdditiveNormalFormCorrection
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationAdditiveNormalFormPeriodic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarNative

/-!
# Holomorphic normal form of an actual additive lattice cocycle

Every entire additive cocycle for the actual period lattice is the
lattice difference of an entire function plus the restriction of an
actual antilinear functional.  The proof constructs a smooth primitive,
proves that its native Dolbeault coefficients are periodic and closed,
solves the resulting periodic equations by the proved Fourier solver,
and removes the actual constant Fourier modes explicitly.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- An entire additive cocycle on the actual period lattice has a
holomorphic coboundary plus an explicitly antilinear constant part.
No smooth primitive, periodic solver, partition, or normal form is
assumed in this theorem. -/
theorem exists_holomorphic_additive_normal_form (p : PeriodDomain)
    {k : p.lattice → ComplexPlane₂ → ℂ}
    (hk : ∀ l, ContDiff ℂ ω (k l))
    (hcocycle : ∀ l m z, k (l + m) z = k l (z + m) + k m z) :
    ∃ (c : Fin 2 → ℂ) (g : ComplexPlane₂ → ℂ), ContDiff ℂ ω g ∧
      ∀ l : p.lattice, ∀ z, k l z = g (z + l) - g z +
        antiholomorphicLinear c (l : ComplexPlane₂) := by
  have hkR (l : p.lattice) : ContDiff ℝ ∞ (k l) :=
    ((hk l).of_le le_top).restrict_scalars ℝ
  obtain ⟨h, hh, hshift⟩ :=
    PeriodTorusLineBundleClassificationLatticeCochain.exists_smooth_lattice_coboundary
      p hkR hcocycle
  let a : ComplexPlane₂ → ℂ := dbarCoordinate h 0
  let b : ComplexPlane₂ → ℂ := dbarCoordinate h 1
  have ha : ContDiff ℝ ∞ a := contDiff_dbarCoordinate hh 0
  have hb : ContDiff ℝ ∞ b := contDiff_dbarCoordinate hh 1
  have hap : ∀ z : ComplexPlane₂, ∀ l : p.lattice, a (z + l) = a z :=
    fun z l => dbarCoordinate_periodic_of_holomorphic_lattice_differences
      p hh hk hshift 0 z l
  have hbp : ∀ z : ComplexPlane₂, ∀ l : p.lattice, b (z + l) = b z :=
    fun z l => dbarCoordinate_periodic_of_holomorphic_lattice_differences
      p hh hk hshift 1 z l
  have hclosed : ∀ z, dbarCoordinate b 0 z = dbarCoordinate a 1 z :=
    dbarCoordinate_zero_one_commute hh
  obtain ⟨u, hu, hpu, hdu₀, hdu₁⟩ :=
    exists_periodic_dbar_primitive p a b ha hb hap hbp hclosed
  let c : Fin 2 → ℂ :=
    ![torusFourierMean (smoothTorusOfLatticePeriodic p a ha hap),
      torusFourierMean (smoothTorusOfLatticePeriodic p b hb hbp)]
  have hdu : ∀ i z, dbarCoordinate u i z = dbarCoordinate h i z - c i := by
    intro i z
    fin_cases i
    · simpa [c, a, b] using hdu₀ z
    · simpa [c, a, b] using hdu₁ z
  refine ⟨c, additiveHolomorphicCorrection h u c,
    additiveHolomorphicCorrection_contDiff_complex hh hu c hdu, ?_⟩
  intro l z
  exact (hshift l z).symm.trans
    (additiveHolomorphicCorrection_lattice_increment p h u c hpu l z).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
