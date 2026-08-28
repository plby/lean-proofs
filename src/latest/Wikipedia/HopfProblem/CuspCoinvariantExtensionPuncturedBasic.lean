import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCusp
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology

/-!
# The original gamma coordinate on the entire punctured cusp

The first real period coordinate descends through the original cusp
monodromy quotient. Transport through the proved whole-family
homeomorphism gives a continuous map on the actual punctured toric
quotient. Its formula is retained on every original logarithmic-cover
representative, not only on a selected boundary or fibre.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open CuspUniformization SpecialPeriods.CuspFamily
open ThreefoldOverlapMappingTorus.Cusp TrianglePeriodFamily.GammaZero

/-- Every original integer cusp monodromy fixes the first circle coordinate. -/
theorem fibreGamma_cuspTorusHomeomorph (k : ℤ) (x : RealTorus₄) :
    fibreGamma (cuspTorusHomeomorph k x) = fibreGamma x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, fibreGamma_mkQ, fibreGamma_mkQ]
  rfl

/-- Gamma on the original integer quotient of the actual varying cusp family. -/
def cuspFamilyGamma (D : Data) : C(D.Space, AddCircle (1 : ℝ)) := by
  letI := D.totalAction
  exact {
    toFun := Quotient.lift (fun x : D.TotalSpace => fibreGamma x.2) (by
      rintro x y ⟨k, hk⟩
      have he : cuspTorusHomeomorph k.toAdd y.2 = x.2 := congrArg Prod.snd hk
      rw [← he, fibreGamma_cuspTorusHomeomorph])
    continuous_toFun := by
      apply (familyQuotient_isQuotientMap D).continuous_iff.mpr
      exact fibreGamma.continuous.comp continuous_snd }

@[simp] theorem cuspFamilyGamma_quotient (D : Data) (x : D.TotalSpace) :
    cuspFamilyGamma D (D.quotient x) = fibreGamma x.2 := rfl

@[simp] theorem cuspFamilyGamma_quotient_mkQ (D : Data)
    (s : LogBase D.radius) (x : RealPlane₄) :
    cuspFamilyGamma D (D.quotient (s, standardLattice.mkQ x)) =
      (x 0 : AddCircle (1 : ℝ)) := fibreGamma_mkQ x

/-- The continuous original gamma coordinate on the entire actual punctured cusp. -/
def puncturedGamma (D : Data) :
    C(PuncturedQuotient D.correction D.radius, AddCircle (1 : ℝ)) :=
  (cuspFamilyGamma D).comp
    ⟨(puncturedFamilyHomeomorph D).symm, (puncturedFamilyHomeomorph D).symm.continuous⟩

/-- Compatibility with the actual whole-family homeomorphism. -/
theorem puncturedGamma_family (D : Data) (q : D.Space) :
    puncturedGamma D (puncturedFamilyHomeomorph D q) = cuspFamilyGamma D q := by
  change cuspFamilyGamma D
    ((puncturedFamilyHomeomorph D).symm (puncturedFamilyHomeomorph D q)) = _
  rw [Homeomorph.symm_apply_apply]

/-- The exact gamma formula on every original logarithmic-cover representative. -/
theorem puncturedGamma_cover (D : Data) (p : LogCover D.radius) :
    puncturedGamma D (puncturedCuspCover D.correction D.radius p) =
      (((D.periods.periodEquiv ⟨p.1.1, p.2⟩).symm p.1.2) 0 : AddCircle (1 : ℝ)) := by
  rw [← puncturedFamilyHomeomorph_iteratedCover D p, puncturedGamma_family]
  change fibreGamma
    (standardLattice.mkQ ((D.periods.periodEquiv ⟨p.1.1, p.2⟩).symm p.1.2)) = _
  exact fibreGamma_mkQ _

/-- On every original real-period representative, gamma is literally its first coordinate. -/
theorem puncturedGamma_realCoordinates (D : Data) (s : LogBase D.radius)
    (x : RealPlane₄) :
    puncturedGamma D (puncturedCuspCover D.correction D.radius
      ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩) =
        (x 0 : AddCircle (1 : ℝ)) := by
  rw [puncturedGamma_cover]
  change (((D.periods.periodEquiv s).symm (D.periods.periodEquiv s x)) 0 :
    AddCircle (1 : ℝ)) = _
  rw [LinearEquiv.symm_apply_apply]

end Wikipedia.HopfProblem.CuspCoinvariantExtension
