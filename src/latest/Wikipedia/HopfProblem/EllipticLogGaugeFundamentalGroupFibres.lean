import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupDeck
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupCentralMap
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupMarking
import Wikipedia.HopfProblem.EllipticLogGaugeSource
import Wikipedia.HopfProblem.EllipticLogGaugeQuotients

/-!
# Actual fibre-translation loops in the logarithmic filling

The loop is defined by its flat-coordinate formula in the actual filling
quotient.  Its endpoint closes because the translating vector is an
integral period.  We identify the same loop in complex period coordinates
and retract it pointwise to the genuine central surface.  The resulting
deck marking is translation by the negative lattice vector, as required
by the proved monodromy convention.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

variable {j : Kind} (D : Equivariant.Data j)

/-- An integral lattice vector vanishes in the actual flat torus. -/
theorem standardLattice_mkQ_realCast (w : Lattice) :
    standardLattice.mkQ (realCast w) = 0 :=
  (Submodule.Quotient.mk_eq_zero standardLattice).mpr
    ((standardLattice_mem_iff _).mpr ⟨w, rfl⟩)

/-- The literal straight translation in one fibre of the period family. -/
def fibreTranslationFamily (z : Disc) (x : RealCoordinates) (w : Lattice) (t : I) :
    D.TotalSpace := (z, standardLattice.mkQ (x + (t : ℝ) • realCast w))

theorem fibreTranslationFamily_continuous (z : Disc) (x : RealCoordinates) (w : Lattice) :
    Continuous (fibreTranslationFamily D z x w) :=
  continuous_const.prodMk (standardLattice.continuous_mkQ.comp
    (continuous_const.add (continuous_subtype_val.smul continuous_const)))

@[simp] theorem fibreTranslationFamily_zero (z : Disc) (x : RealCoordinates) (w : Lattice) :
    fibreTranslationFamily D z x w 0 = (z, standardLattice.mkQ x) := by
  simp [fibreTranslationFamily]

@[simp] theorem fibreTranslationFamily_one (z : Disc) (x : RealCoordinates) (w : Lattice) :
    fibreTranslationFamily D z x w 1 = (z, standardLattice.mkQ x) := by
  change (z, standardLattice.mkQ (x + (1 : ℝ) • realCast w)) =
    (z, standardLattice.mkQ x)
  rw [one_smul, map_add, standardLattice_mkQ_realCast, add_zero]

/-- Real translation has exactly the displayed complex period-vector formula. -/
theorem periodEquiv_fibreTranslation (z : Disc) (x : RealCoordinates) (w : Lattice)
    (t : I) :
    D.periods.periodEquiv z (x + (t : ℝ) • realCast w) =
      D.periods.periodEquiv z x + (t : ℂ) • periodVector D.periods w z := by
  simp only [map_add, map_smul, periodVector, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem fibreTranslationFamily_complex_formula (z : Disc) (x : RealCoordinates)
    (w : Lattice) (t : I) :
    fibreTranslationFamily D z x w t =
      D.periods.quotientMap
        (z, D.periods.periodEquiv z x + (t : ℂ) • periodVector D.periods w z) := by
  rw [← periodEquiv_fibreTranslation]
  change (z, standardLattice.mkQ (x + (t : ℝ) • realCast w)) =
    (z, standardLattice.mkQ ((D.periods.periodEquiv z).symm
      (D.periods.periodEquiv z (x + (t : ℝ) • realCast w))))
  rw [LinearEquiv.symm_apply_apply]

/-- The honest filling loop given by positive translation by the integral
vector `w` in the fibre over the fixed root coordinate `z`. -/
def fibreTranslationLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) :
    Path (D.quotient v hv (z, standardLattice.mkQ x))
      (D.quotient v hv (z, standardLattice.mkQ x)) where
  toFun t := D.quotient v hv (fibreTranslationFamily D z x w t)
  continuous_toFun := (D.quotient_continuous v hv).comp
    (fibreTranslationFamily_continuous D z x w)
  source' := congrArg (D.quotient v hv) (fibreTranslationFamily_zero D z x w)
  target' := congrArg (D.quotient v hv) (fibreTranslationFamily_one D z x w)

@[simp] theorem fibreTranslationLoop_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) (t : I) :
    fibreTranslationLoop D v hv z x w t =
      D.quotient v hv (z, standardLattice.mkQ (x + (t : ℝ) • realCast w)) := rfl

theorem fibreTranslationLoop_complex_formula (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) (t : I) :
    fibreTranslationLoop D v hv z x w t =
      D.quotient v hv (D.periods.quotientMap
        (z, D.periods.periodEquiv z x + (t : ℂ) • periodVector D.periods w z)) :=
  congrArg (D.quotient v hv) (fibreTranslationFamily_complex_formula D z x w t)

/-- The loop remains over one point of the actual powered base map. -/
theorem fibreTranslationLoop_projection (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) (t : I) :
    D.projection v hv (fibreTranslationLoop D v hv z x w t) =
      discPower j.order j.order_pos z := by
  rw [fibreTranslationLoop_apply, D.projection_quotient]

theorem fibreTranslationLoop_projection_norm (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) (t : I) :
    ‖(D.projection v hv (fibreTranslationLoop D v hv z x w t) : ℂ)‖ =
      ‖(z : ℂ)‖ ^ j.order := by
  rw [fibreTranslationLoop_projection, discPower_coe, norm_pow]

theorem fibreTranslationLoop_projection_ne_zero (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (hz : (z : ℂ) ≠ 0) (x : RealCoordinates) (w : Lattice) (t : I) :
    (D.projection v hv (fibreTranslationLoop D v hv z x w t) : ℂ) ≠ 0 := by
  rw [fibreTranslationLoop_projection, discPower_coe]
  exact pow_ne_zero _ hz

/-- Retraction of the actual filling loop, with both endpoints changed
only along the proved equality of its retracted basepoint. -/
def fibreTranslationSurfaceLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) :
    Path (affineCoverProjection j D.centralPeriod v hv x)
      (affineCoverProjection j D.centralPeriod v hv x) :=
  retractedFlatLoop D v hv z x (fibreTranslationLoop D v hv z x w)

/-- The retracted path is exactly the projected straight affine path. -/
theorem fibreTranslationSurfaceLoop_eq (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) :
    fibreTranslationSurfaceLoop D v hv z x w =
      affineTranslationLoop j D.centralPeriod v hv x w := by
  ext t
  change D.fillingSurfaceRetraction v hv
      (D.quotient v hv (z, standardLattice.mkQ (x + (t : ℝ) • realCast w))) =
    affineTranslationLoop j D.centralPeriod v hv x w t
  rw [fillingSurfaceRetraction_quotient_flat, affineTranslationLoop_apply]

/-- The actual fibre-attaching loop has the native negative-translation marking. -/
theorem fibreTranslationSurfaceLoop_deck (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) :
    surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv x
      (FundamentalGroup.fromPath ⟦fibreTranslationSurfaceLoop D v hv z x w⟧) =
        deckTranslationHom j v (Multiplicative.ofAdd (-w)) := by
  rw [fibreTranslationSurfaceLoop_eq]
  exact surfaceFundamentalGroupDeckEquiv_affineTranslationLoop j D.centralPeriod v hv x w

theorem fibreTranslationSurfaceLoop_eq_marked (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) (w : Lattice) :
    FundamentalGroup.fromPath ⟦fibreTranslationSurfaceLoop D v hv z x w⟧ =
      surfaceTranslationHom j D.centralPeriod v hv x (Multiplicative.ofAdd (-w)) := by
  rw [fibreTranslationSurfaceLoop_eq]
  exact affineTranslationLoop_eq_marked j D.centralPeriod v hv x w

/-- The computed image is that of the actual retraction-induced group homomorphism. -/
theorem fillingRetractionDeckHom_fibreTranslationLoop (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (x : RealCoordinates) (w : Lattice) :
    fillingRetractionDeckHom D v hv z x
      (FundamentalGroup.fromPath ⟦fibreTranslationLoop D v hv z x w⟧) =
        deckTranslationHom j v (Multiplicative.ofAdd (-w)) :=
  (fillingRetractionDeckHom_fromPath D v hv z x (fibreTranslationLoop D v hv z x w)).trans
    (fibreTranslationSurfaceLoop_deck D v hv z x w)

/-- Exact cancellation in complex coordinates holds for every real parameter. -/
theorem gaugeMap_project_negativeLog_add_period (v : Lattice) (z : BaseStar)
    (w : Lattice) (s : ℂ) (hs : exponential s = (z.1 : ℂ)) (t : ℝ) :
    gaugeMap D.periods v (project D.periods
      ⟨(z.1, -s • periodVector D.periods v z.1 + (t : ℂ) • periodVector D.periods w z.1),
        z.2⟩) =
      project D.periods ⟨(z.1, (t : ℂ) • periodVector D.periods w z.1), z.2⟩ := by
  apply Subtype.ext
  rw [gaugeMap_project_of_exponential D.periods v _ s hs]
  change D.periods.quotientMap _ = D.periods.quotientMap _
  apply congrArg D.periods.quotientMap
  apply congrArg (fun u : ComplexPlane₂ => (z.1, u))
  simp only [neg_smul]
  abel

/-- The same fibre translation on the actual punctured period family. -/
def fibreTranslationFamilyStar (z : BaseStar) (x : RealCoordinates) (w : Lattice) (t : I) :
    FamilyStar D.periods := ⟨fibreTranslationFamily D z.1 x w t, z.2⟩

theorem fibreTranslationFamilyStar_continuous (z : BaseStar)
    (x : RealCoordinates) (w : Lattice) :
    Continuous (fibreTranslationFamilyStar D z x w) :=
  (fibreTranslationFamily_continuous D z.1 x w).subtype_mk _

/-- Any genuine logarithm gives the exact gauge formula on the fibre path. -/
theorem gaugeMap_fibreTranslationFamilyStar_formula (v : Lattice) (z : BaseStar)
    (x : RealCoordinates) (w : Lattice) (s : ℂ) (hs : exponential s = (z.1 : ℂ)) (t : I) :
    (gaugeMap D.periods v (fibreTranslationFamilyStar D z x w t) : D.TotalSpace) =
      D.periods.quotientMap (z.1,
        D.periods.periodEquiv z.1 x + (t : ℂ) • periodVector D.periods w z.1 +
          s • periodVector D.periods v z.1) := by
  let a : CoverStar := ⟨(z.1,
    D.periods.periodEquiv z.1 x + (t : ℂ) • periodVector D.periods w z.1), z.2⟩
  have ha : fibreTranslationFamilyStar D z x w t = project D.periods a :=
    Subtype.ext (fibreTranslationFamily_complex_formula D z.1 x w t)
  rw [ha]
  exact gaugeMap_project_of_exponential D.periods v a s hs

/-- Starting at the actual negative-logarithmic vector makes the gauge
send the entire fibre path to the zero-origin period path, pointwise. -/
theorem gaugeMap_fibreTranslationFamilyStar_negativeLog (v : Lattice) (z : BaseStar)
    (w : Lattice) (s : ℂ) (hs : exponential s = (z.1 : ℂ)) (t : I) :
    gaugeMap D.periods v (fibreTranslationFamilyStar D z
      ((D.periods.periodEquiv z.1).symm (-s • periodVector D.periods v z.1)) w t) =
        fibreTranslationFamilyStar D z 0 w t := by
  apply Subtype.ext
  rw [gaugeMap_fibreTranslationFamilyStar_formula D v z _ w s hs]
  change D.periods.quotientMap _ = fibreTranslationFamily D z.1 0 w t
  rw [fibreTranslationFamily_complex_formula]
  congr 1
  apply congrArg (fun u : ComplexPlane₂ => (z.1, u))
  simp only [LinearEquiv.apply_symm_apply, map_zero, zero_add, neg_smul]
  abel

/-- The pointwise fibre loop in the actual punctured filling. -/
def fibreTranslationFillingPoint (v : Lattice) (hv : AdmissibleTwist j v)
    (z : BaseStar) (x : RealCoordinates) (w : Lattice) (t : I) : FillingStar D v hv :=
  fillingStarProject D v hv (fibreTranslationFamilyStar D z x w t)

@[simp] theorem fibreTranslationFillingPoint_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (z : BaseStar) (x : RealCoordinates) (w : Lattice) (t : I) :
    (fibreTranslationFillingPoint D v hv z x w t : D.Space v hv) =
      fibreTranslationLoop D v hv z.1 x w t := rfl

theorem fibreTranslationFillingPoint_continuous (v : Lattice) (hv : AdmissibleTwist j v)
    (z : BaseStar) (x : RealCoordinates) (w : Lattice) :
    Continuous (fibreTranslationFillingPoint D v hv z x w) :=
  ((D.quotient_continuous v hv).comp
    (fibreTranslationFamily_continuous D z.1 x w)).subtype_mk _

/-- An actual loop in the punctured filling, not merely in the whole filling. -/
def fibreTranslationFillingLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (z : BaseStar) (x : RealCoordinates) (w : Lattice) :
    Path (fibreTranslationFillingPoint D v hv z x w 0)
      (fibreTranslationFillingPoint D v hv z x w 0) where
  toFun := fibreTranslationFillingPoint D v hv z x w
  continuous_toFun := fibreTranslationFillingPoint_continuous D v hv z x w
  source' := rfl
  target' := Subtype.ext ((fibreTranslationLoop D v hv z.1 x w).target.trans
    (fibreTranslationLoop D v hv z.1 x w).source.symm)

/-- The actual filling gauge sends the translated logarithmic fibre path
to the untwisted zero-origin period path. -/
theorem fillingToTautological_fibreTranslation (v : Lattice) (hv : AdmissibleTwist j v)
    (z : BaseStar) (w : Lattice) (s : ℂ) (hs : exponential s = (z.1 : ℂ)) (t : I) :
    fillingToTautologicalBiholomorph D v hv (fibreTranslationFillingPoint D v hv z
      ((D.periods.periodEquiv z.1).symm (-s • periodVector D.periods v z.1)) w t) =
        starProject D 0 (Matrix.mulVec_zero j.matrix) (fibreTranslationFamilyStar D z 0 w t) := by
  rw [fibreTranslationFillingPoint, fillingToTautologicalBiholomorph_project,
    gaugeMap_fibreTranslationFamilyStar_negativeLog D v z w s hs]

end Wikipedia.HopfProblem.Elliptic.LogGauge
