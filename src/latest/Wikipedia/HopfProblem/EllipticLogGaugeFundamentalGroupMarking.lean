import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupPath
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupCentralMap
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupDeck

/-!
# The marked image of the actual logarithmic meridian

The attaching loop is mapped by the actual radial retraction, with only
the proved equality of its retracted basepoint used as a cast.  Its real
lift ends at the affine generator, so the native deck-group convention
sends the clockwise logarithmic meridian to the inverse generator.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods

/-- A change by equality of basepoints is precisely an endpoint cast of loops. -/
theorem fundamentalGroup_cast_loop {Y : Type*} [TopologicalSpace Y]
    {a b : Y} (h : a = b) (γ : Path a a) :
    MulEquiv.cast (M := FundamentalGroup Y) h (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.cast h.symm h.symm⟧ := by
  cases h
  rfl

variable {j : Kind} (D : Equivariant.Data j)

/-- The genuine retraction on a loop, at the exactly equal affine-cover basepoint. -/
def retractedFlatLoop (v : Lattice) (hv : AdmissibleTwist j v) (z : Disc)
    (x : RealCoordinates)
    (γ : Path (D.quotient v hv (z, standardLattice.mkQ x))
      (D.quotient v hv (z, standardLattice.mkQ x))) :
    Path (affineCoverProjection j D.centralPeriod v hv x)
      (affineCoverProjection j D.centralPeriod v hv x) :=
  (γ.map (D.fillingSurfaceRetraction v hv).continuous).cast
    (fillingSurfaceRetraction_quotient_flat D v hv z x).symm
    (fillingSurfaceRetraction_quotient_flat D v hv z x).symm

@[simp] theorem retractedFlatLoop_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates)
    (γ : Path (D.quotient v hv (z, standardLattice.mkQ x))
      (D.quotient v hv (z, standardLattice.mkQ x))) (t : I) :
    retractedFlatLoop D v hv z x γ t = D.fillingSurfaceRetraction v hv (γ t) := rfl

/-- The actual retraction-induced homomorphism followed by affine-cover monodromy. -/
def fillingRetractionDeckHom (v : Lattice) (hv : AdmissibleTwist j v) (z : Disc)
    (x : RealCoordinates) :
    FundamentalGroup (D.Space v hv) (D.quotient v hv (z, standardLattice.mkQ x)) →*
      AffineDeckGroup j v :=
  (surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv x).toMonoidHom.comp
    ((MulEquiv.cast (M := FundamentalGroup (Surface j D.centralPeriod v hv))
      (fillingSurfaceRetraction_quotient_flat D v hv z x)).toMonoidHom.comp
        (FundamentalGroup.map (D.fillingSurfaceRetraction v hv)
          (D.quotient v hv (z, standardLattice.mkQ x))))

theorem fillingRetractionDeckHom_fromPath (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates)
    (γ : Path (D.quotient v hv (z, standardLattice.mkQ x))
      (D.quotient v hv (z, standardLattice.mkQ x))) :
    fillingRetractionDeckHom D v hv z x (FundamentalGroup.fromPath ⟦γ⟧) =
      surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv x
        (FundamentalGroup.fromPath ⟦retractedFlatLoop D v hv z x γ⟧) := by
  change surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv x
    (MulEquiv.cast (M := FundamentalGroup (Surface j D.centralPeriod v hv))
      (fillingSurfaceRetraction_quotient_flat D v hv z x)
      (FundamentalGroup.fromPath ⟦γ.map (D.fillingSurfaceRetraction v hv).continuous⟧)) = _
  rw [fundamentalGroup_cast_loop]
  rfl

/-- The actual retracted logarithmic loop on the genuine central surface. -/
def logMeridianSurfaceLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0))
      (affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0)) :=
  retractedFlatLoop D v hv (logMeridianRoot j s₀ hs₀ 0) (logMeridianFlat D v s₀ hs₀ 0)
    (logMeridianLoop D v hv s₀ hs₀)

@[simp] theorem logMeridianSurfaceLoop_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianSurfaceLoop D v hv s₀ hs₀ t =
      affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ t) :=
  fillingSurfaceRetraction_quotient_flat D v hv (logMeridianRoot j s₀ hs₀ t)
    (logMeridianFlat D v s₀ hs₀ t)

/-- The retracted path is exactly the projected affine-endpoint path. -/
theorem logMeridianSurfaceLoop_eq_affineGeneratorPathLoop
    (v : Lattice) (hv : AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    logMeridianSurfaceLoop D v hv s₀ hs₀ =
      affineGeneratorPathLoop j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0)
        (logMeridianFlatPath D v hv.1 s₀ hs₀) := by
  ext t
  exact logMeridianSurfaceLoop_apply D v hv s₀ hs₀ t

/-- Clockwise root continuation has the inverse native affine marking. -/
theorem surfaceFundamentalGroupDeckEquiv_logMeridian
    (v : Lattice) (hv : AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0)
      (FundamentalGroup.fromPath ⟦logMeridianSurfaceLoop D v hv s₀ hs₀⟧) =
        (deckGenerator j v)⁻¹ := by
  rw [logMeridianSurfaceLoop_eq_affineGeneratorPathLoop]
  exact surfaceFundamentalGroupDeckEquiv_affineGeneratorPathLoop j D.centralPeriod v hv _ _

theorem logMeridianSurfaceLoop_eq_marked_inverse
    (v : Lattice) (hv : AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    FundamentalGroup.fromPath ⟦logMeridianSurfaceLoop D v hv s₀ hs₀⟧ =
      (surfaceAffineGenerator j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0))⁻¹ := by
  rw [logMeridianSurfaceLoop_eq_affineGeneratorPathLoop]
  exact affineGeneratorPathLoop_eq_marked_inverse j D.centralPeriod v hv _ _

/-- The induced map on the actual noncentral filling loop has the same computed sign. -/
theorem fillingRetractionDeckHom_logMeridian
    (v : Lattice) (hv : AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    fillingRetractionDeckHom D v hv (logMeridianRoot j s₀ hs₀ 0)
      (logMeridianFlat D v s₀ hs₀ 0)
      (FundamentalGroup.fromPath ⟦logMeridianLoop D v hv s₀ hs₀⟧) =
        (deckGenerator j v)⁻¹ := by
  exact (fillingRetractionDeckHom_fromPath D v hv (logMeridianRoot j s₀ hs₀ 0)
    (logMeridianFlat D v s₀ hs₀ 0) (logMeridianLoop D v hv s₀ hs₀)).trans
      (surfaceFundamentalGroupDeckEquiv_logMeridian D v hv s₀ hs₀)

end Wikipedia.HopfProblem.Elliptic.LogGauge
