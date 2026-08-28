import Wikipedia.HopfProblem.EllipticFirstHomologyGroups

/-!
# Compatibility with the actual central-surface inclusion

The abelianization isomorphism induced by the actual surface inclusion
into its filling agrees with the computed affine-group coordinates.
In particular, the marked lattice and affine-generator classes are
preserved. This is the abelianized form of the already proved strong
deformation retraction in Lemma 7.3(i), without a singular-homology assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- The abelianization isomorphism induced by the actual central-surface inclusion. -/
def centralSurfaceAbelianizationEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SurfaceAbelianization j (centralPeriod j) v hv y ≃ₗ[ℤ] FillingAbelianization j v hv y :=
  abelianizationLinearCongr (fillingSurfaceFundamentalGroupEquiv j v hv
    (affineCoverProjection j (centralPeriod j) v hv y))

/-- The map is literally induced by `FundamentalGroup.map` of the actual
continuous central-surface embedding. -/
theorem centralSurfaceAbelianizationEquiv_toLinearMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (centralSurfaceAbelianizationEquiv j v hv y).toLinearMap =
      (Abelianization.map (FundamentalGroup.map (surfaceIntoFilling j v hv)
        (affineCoverProjection j (centralPeriod j) v hv y))).toAdditive.toIntLinearMap := rfl

theorem centralSurfaceAbelianizationEquiv_deck (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (x : SurfaceAbelianization j (centralPeriod j) v hv y) :
    fillingAbelianizationDeckEquiv j v hv y (centralSurfaceAbelianizationEquiv j v hv y x) =
      surfaceAbelianizationDeckEquiv j (centralPeriod j) v hv y x := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep x.toMul
  have hx : Additive.ofMul (Abelianization.of g) = x := congrArg Additive.ofMul hg
  rw [← hx]
  change Additive.ofMul (Abelianization.of
      (fillingFundamentalGroupDeckEquiv j v hv y
        (fillingSurfaceFundamentalGroupEquiv j v hv
          (affineCoverProjection j (centralPeriod j) v hv y) g))) =
    Additive.ofMul (Abelianization.of
      (surfaceFundamentalGroupDeckEquiv j (centralPeriod j) v hv y g))
  have he : fillingFundamentalGroupDeckEquiv j v hv y
      (fillingSurfaceFundamentalGroupEquiv j v hv
        (affineCoverProjection j (centralPeriod j) v hv y) g) =
      surfaceFundamentalGroupDeckEquiv j (centralPeriod j) v hv y g := by
    change surfaceFundamentalGroupDeckEquiv j (centralPeriod j) v hv y
      ((fillingSurfaceFundamentalGroupEquiv j v hv
        (affineCoverProjection j (centralPeriod j) v hv y)).symm
          (fillingSurfaceFundamentalGroupEquiv j v hv
            (affineCoverProjection j (centralPeriod j) v hv y) g)) = _
    rw [MulEquiv.symm_apply_apply]
  exact congrArg (fun k => Additive.ofMul (Abelianization.of k)) he

@[simp] theorem centralSurfaceAbelianizationEquiv_translation (j : Kind) (v w : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    centralSurfaceAbelianizationEquiv j v hv y
        (surfaceAbelianTranslation j (centralPeriod j) v hv y w) =
      fillingAbelianTranslation j v hv y w := by
  apply (fillingAbelianizationDeckEquiv j v hv y).injective
  rw [centralSurfaceAbelianizationEquiv_deck, surfaceAbelianizationDeckEquiv_translation,
    fillingAbelianizationDeckEquiv_translation]

@[simp] theorem centralSurfaceAbelianizationEquiv_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    centralSurfaceAbelianizationEquiv j v hv y
        (surfaceAbelianGenerator j (centralPeriod j) v hv y) =
      fillingAbelianGenerator j v hv y := by
  apply (fillingAbelianizationDeckEquiv j v hv y).injective
  rw [centralSurfaceAbelianizationEquiv_deck, surfaceAbelianizationDeckEquiv_generator,
    fillingAbelianizationDeckEquiv_generator]

/-- The source's main rank-two marking is unchanged by actual inclusion
of the central surface into the filling. -/
theorem mainFillingAbelianizationEquiv_centralSurface (j : Kind) (y : RealCoordinates)
    (x : SurfaceAbelianization j (centralPeriod j) j.twist (mainTwist_admissible j) y) :
    mainFillingAbelianizationEquiv j y
        (centralSurfaceAbelianizationEquiv j j.twist (mainTwist_admissible j) y x) =
      mainSurfaceAbelianizationEquiv j (centralPeriod j) y x := by
  change mainDeckAbelianizationEquiv j (fillingAbelianizationDeckEquiv j j.twist
      (mainTwist_admissible j) y
        (centralSurfaceAbelianizationEquiv j j.twist (mainTwist_admissible j) y x)) =
    mainDeckAbelianizationEquiv j (surfaceAbelianizationDeckEquiv j (centralPeriod j) j.twist
      (mainTwist_admissible j) y x)
  rw [centralSurfaceAbelianizationEquiv_deck]

end Wikipedia.HopfProblem.Elliptic
