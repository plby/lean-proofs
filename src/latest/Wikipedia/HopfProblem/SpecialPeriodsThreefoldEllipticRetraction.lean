import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibreTopology
import Wikipedia.HopfProblem.EllipticFillingTopologyTubes

/-!
# Retraction of the actual small elliptic pieces onto their central surfaces

The original radial homotopy decreases the norm of the filling parameter,
so it preserves the exact selected small-radius piece.  Restricting that
homotopy gives a strong deformation retraction through the actual central
surface inclusion.  The genuine full-patch homeomorphism carries the same
retraction to the corresponding open subset of the global threefold.

The resulting fundamental-group equivalences concern these local pieces
and lifted patches, not the whole global threefold.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

attribute [local instance] specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace Threefold.chartedSpace

/-- The original open filling domain, regarded as a set in the full filling. -/
abbrev pieceFullDomain (j : Elliptic.Kind) : Set (SpecialFullFilling j) :=
  pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j

/-- The actual central-surface inclusion with its unchanged small-piece target. -/
def centralSurfaceIntoPiece (j : Elliptic.Kind) :
    C(SpecialCentralSurface j, LocalSpace j) :=
  ⟨pieceCentralInclusion j, pieceCentralInclusion_continuous j⟩

@[simp] theorem centralSurfaceIntoPiece_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) : centralSurfaceIntoPiece j x = pieceCentralInclusion j x :=
  rfl

theorem fullCentralSurface_subset_piece (j : Elliptic.Kind) :
    range (specialCentralSurfaceIntoFilling j) ⊆ pieceFullDomain j := by
  rintro _ ⟨a, rfl⟩
  exact (pieceCentralInclusion j a).property

/-- The actual full-family deformation preserves the chosen small-radius domain. -/
theorem fullCentralHomotopy_preserves_piece (j : Elliptic.Kind) (t : unitInterval)
    (x : SpecialFullFilling j) (hx : x ∈ pieceFullDomain j) :
    specialCentralSurfaceStrongDeformationRetraction j (t, x) ∈ pieceFullDomain j :=
  (Elliptic.fillingRadial_projection_norm_le j j.twist
    (Elliptic.mainTwist_admissible j) t x).trans_lt hx

/-- Restriction of the genuine full-family central retraction to the small piece. -/
def pieceSurfaceRetraction (j : Elliptic.Kind) :
    C(LocalSpace j, SpecialCentralSurface j) :=
  restrictedRetraction (specialCentralSurfaceRetraction j) (pieceFullDomain j)

@[simp] theorem pieceSurfaceRetraction_apply (j : Elliptic.Kind) (x : LocalSpace j) :
    pieceSurfaceRetraction j x = specialCentralSurfaceRetraction j x.val := rfl

@[simp] theorem pieceSurfaceRetraction_comp_inclusion (j : Elliptic.Kind) :
    (pieceSurfaceRetraction j).comp (centralSurfaceIntoPiece j) = ContinuousMap.id _ :=
  restrictedRetraction_comp_inclusion (specialCentralSurfaceIntoFilling j)
    (specialCentralSurfaceRetraction j)
    ((specialLocalData j).fillingSurfaceRetraction_comp_inclusion
      j.twist (Elliptic.mainTwist_admissible j))
    (pieceFullDomain j) (fullCentralSurface_subset_piece j)

/-- The genuine radial strong deformation restricted to the actual small piece. -/
def pieceStrongDeformationRetraction (j : Elliptic.Kind) :
    (ContinuousMap.id (LocalSpace j)).HomotopyRel
      ((centralSurfaceIntoPiece j).comp (pieceSurfaceRetraction j))
      (range (centralSurfaceIntoPiece j)) :=
  restrictedRetractionHomotopy (specialCentralSurfaceIntoFilling j)
    (specialCentralSurfaceRetraction j) (specialCentralSurfaceStrongDeformationRetraction j)
    (pieceFullDomain j) (fullCentralSurface_subset_piece j)
    (fullCentralHomotopy_preserves_piece j)

@[simp] theorem pieceStrongDeformationRetraction_coe (j : Elliptic.Kind)
    (t : unitInterval) (x : LocalSpace j) :
    (pieceStrongDeformationRetraction j (t, x) : SpecialFullFilling j) =
      specialCentralSurfaceStrongDeformationRetraction j (t, x.val) := rfl

/-- The unchanged ramified base coordinate contracts by the actual order power. -/
theorem parameter_pieceStrongDeformationRetraction (j : Elliptic.Kind)
    (t : unitInterval) (x : LocalSpace j) :
    parameter j (pieceStrongDeformationRetraction j (t, x)) =
      (((1 - (t : ℝ) : ℝ) : ℂ) ^ j.order) * parameter j x :=
  Elliptic.fillingRadial_projection_coe j j.twist (Elliptic.mainTwist_admissible j) t x.val

/-- The actual central-surface inclusion is a homotopy equivalence with the small piece. -/
def pieceSurfaceHomotopyEquiv (j : Elliptic.Kind) :
    SpecialCentralSurface j ≃ₕ LocalSpace j :=
  retractionHomotopyEquiv (centralSurfaceIntoPiece j) (pieceSurfaceRetraction j)
    (pieceSurfaceRetraction_comp_inclusion j) (pieceStrongDeformationRetraction j)

@[simp] theorem pieceSurfaceHomotopyEquiv_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    pieceSurfaceHomotopyEquiv j x = pieceCentralInclusion j x := rfl

/-- The actual inclusion into the chosen small piece induces the pointed π₁ isomorphism. -/
def pieceSurfaceFundamentalGroupEquiv (j : Elliptic.Kind) (a : SpecialCentralSurface j) :
    FundamentalGroup (SpecialCentralSurface j) a ≃*
      FundamentalGroup (LocalSpace j) (pieceCentralInclusion j a) :=
  retractionFundamentalGroupEquiv (centralSurfaceIntoPiece j) (pieceSurfaceRetraction j)
    (pieceSurfaceRetraction_comp_inclusion j) (pieceStrongDeformationRetraction j) a

@[simp] theorem pieceSurfaceFundamentalGroupEquiv_toMonoidHom (j : Elliptic.Kind)
    (a : SpecialCentralSurface j) :
    (pieceSurfaceFundamentalGroupEquiv j a).toMonoidHom =
      FundamentalGroup.map (centralSurfaceIntoPiece j) a := rfl

/-- The central surface maps into the full actual lifted elliptic patch. -/
def centralSurfaceIntoLiftedPatch (j : Elliptic.Kind) :
    C(SpecialCentralSurface j, Threefold.liftedPatch (some (some j))) :=
  ContinuousMap.comp
    ⟨nativePatchBiholomorph j, (nativePatchBiholomorph j).toHomeomorph.continuous⟩
    (centralSurfaceIntoPiece j)

@[simp] theorem centralSurfaceIntoLiftedPatch_coe (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    (centralSurfaceIntoLiftedPatch j x : Threefold.Space) = centralSurfaceInclusion j x := rfl

/-- The same retraction on the genuine open patch inside the global threefold. -/
def liftedPatchSurfaceRetraction (j : Elliptic.Kind) :
    C(Threefold.liftedPatch (some (some j)), SpecialCentralSurface j) :=
  (pieceSurfaceRetraction j).comp
    ⟨(nativePatchBiholomorph j).symm, (nativePatchBiholomorph j).symm.toHomeomorph.continuous⟩

@[simp] theorem liftedPatchSurfaceRetraction_comp_inclusion (j : Elliptic.Kind) :
    (liftedPatchSurfaceRetraction j).comp (centralSurfaceIntoLiftedPatch j) =
      ContinuousMap.id _ := by
  ext a
  change pieceSurfaceRetraction j
    ((nativePatchBiholomorph j).symm (nativePatchBiholomorph j (pieceCentralInclusion j a))) = a
  rw [Diffeomorph.symm_apply_apply]
  exact congrArg (fun f : C(SpecialCentralSurface j, SpecialCentralSurface j) => f a)
    (pieceSurfaceRetraction_comp_inclusion j)

/-- The radial strong deformation on the whole actual lifted elliptic patch. -/
def liftedPatchStrongDeformationRetraction (j : Elliptic.Kind) :
    (ContinuousMap.id (Threefold.liftedPatch (some (some j)))).HomotopyRel
      ((centralSurfaceIntoLiftedPatch j).comp (liftedPatchSurfaceRetraction j))
      (range (centralSurfaceIntoLiftedPatch j)) where
  toFun p := nativePatchBiholomorph j
    (pieceStrongDeformationRetraction j (p.1, (nativePatchBiholomorph j).symm p.2))
  continuous_toFun := (nativePatchBiholomorph j).toHomeomorph.continuous.comp
    ((pieceStrongDeformationRetraction j).continuous.comp
      (continuous_fst.prodMk
        ((nativePatchBiholomorph j).symm.toHomeomorph.continuous.comp continuous_snd)))
  map_zero_left x :=
    (congrArg (nativePatchBiholomorph j)
      ((pieceStrongDeformationRetraction j).map_zero_left
        ((nativePatchBiholomorph j).symm x))).trans
      ((nativePatchBiholomorph j).apply_symm_apply x)
  map_one_left x := congrArg (nativePatchBiholomorph j)
    ((pieceStrongDeformationRetraction j).map_one_left ((nativePatchBiholomorph j).symm x))
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    change nativePatchBiholomorph j
        (pieceStrongDeformationRetraction j
          (t, (nativePatchBiholomorph j).symm
            (nativePatchBiholomorph j (pieceCentralInclusion j a)))) =
      nativePatchBiholomorph j (pieceCentralInclusion j a)
    rw [Diffeomorph.symm_apply_apply]
    exact congrArg (nativePatchBiholomorph j)
      ((pieceStrongDeformationRetraction j).eq_fst t ⟨a, rfl⟩)

/-- The actual central-surface inclusion is a homotopy equivalence onto its full lifted patch. -/
def liftedPatchSurfaceHomotopyEquiv (j : Elliptic.Kind) :
    SpecialCentralSurface j ≃ₕ Threefold.liftedPatch (some (some j)) :=
  retractionHomotopyEquiv (centralSurfaceIntoLiftedPatch j) (liftedPatchSurfaceRetraction j)
    (liftedPatchSurfaceRetraction_comp_inclusion j) (liftedPatchStrongDeformationRetraction j)

@[simp] theorem liftedPatchSurfaceHomotopyEquiv_apply (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    liftedPatchSurfaceHomotopyEquiv j x = centralSurfaceIntoLiftedPatch j x := rfl

/-- The actual inclusion induces an isomorphism on pointed π₁ of the full lifted patch. -/
def liftedPatchSurfaceFundamentalGroupEquiv (j : Elliptic.Kind)
    (a : SpecialCentralSurface j) :
    FundamentalGroup (SpecialCentralSurface j) a ≃*
      FundamentalGroup (Threefold.liftedPatch (some (some j)))
        (centralSurfaceIntoLiftedPatch j a) :=
  retractionFundamentalGroupEquiv (centralSurfaceIntoLiftedPatch j) (liftedPatchSurfaceRetraction j)
    (liftedPatchSurfaceRetraction_comp_inclusion j) (liftedPatchStrongDeformationRetraction j) a

@[simp] theorem liftedPatchSurfaceFundamentalGroupEquiv_toMonoidHom (j : Elliptic.Kind)
    (a : SpecialCentralSurface j) :
    (liftedPatchSurfaceFundamentalGroupEquiv j a).toMonoidHom =
      FundamentalGroup.map (centralSurfaceIntoLiftedPatch j) a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
