import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# Changing the radius and phase of the genuine elliptic boundary

Translation in the real cylinder descends to a jointly continuous flow on
the actual mapping torus.  Combining this flow with the explicit positive
radius segment gives a homotopy between the original boundary inclusion
and the inclusion at any permitted radius and real phase.  The real-period
coordinate is unchanged on every cylinder representative, throughout the
homotopy.  Composing with the literal overlap maps preserves both actual
attachment coefficients on integral singular homology.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

section TimeTranslation

variable {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)

/-- Translation in the actual real-cylinder coordinate. -/
def timeShift (θ : ℝ) : C(MappingTorus.Torus f, MappingTorus.Torus f) where
  toFun := Quotient.lift (fun p : ℝ × X => MappingTorus.mk f (p.1 + θ, p.2)) (by
    rintro p q ⟨k, rfl⟩
    simpa only [MappingTorus.deck, add_assoc, add_left_comm, add_comm] using
      (MappingTorus.mk_deck f k (p.1 + θ, p.2)).symm)
  continuous_toFun := ((MappingTorus.mk_continuous f).comp
    ((continuous_fst.add continuous_const).prodMk continuous_snd)).quotient_lift _

@[simp] theorem timeShift_mk (θ t : ℝ) (x : X) :
    timeShift f θ (MappingTorus.mk f (t, x)) = MappingTorus.mk f (t + θ, x) := rfl

@[simp] theorem timeShift_zero (x : MappingTorus.Torus f) : timeShift f 0 x = x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := MappingTorus.mk_surjective f x
  simp only [timeShift_mk, add_zero]

/-- The cylinder translation is jointly continuous in phase and quotient point. -/
theorem timeShift_jointly_continuous :
    Continuous (fun p : ℝ × MappingTorus.Torus f => timeShift f p.1 p.2) := by
  have hq : IsOpenQuotientMap (MappingTorus.mk f) :=
    ⟨MappingTorus.mk_surjective f, MappingTorus.mk_continuous f, MappingTorus.mk_open f⟩
  apply (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp
  change Continuous (fun p : ℝ × (ℝ × X) => MappingTorus.mk f (p.2.1 + p.1, p.2.2))
  exact (MappingTorus.mk_continuous f).comp
    (((continuous_fst.comp continuous_snd).add continuous_fst).prodMk
      (continuous_snd.comp continuous_snd))

end TimeTranslation

namespace Elliptic

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.EllipticFilling
open Wikipedia.HopfProblem.Elliptic
open SingularMayerVietoris PeriodTorusHigherHomology

section GenericBoundary

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (r : ℝ)

/-- The genuine punctured-filling inclusion at a specified radius and phase. -/
def boundaryInclusionAt (a : Radius j.order r) (θ : ℝ) :
    C(Boundary j v, PuncturedFilling j v hv r) :=
  ⟨fun x => (puncturedProductHomeomorph j v hv r).symm
      (a, timeShift (flatTorusAffine j v) θ x),
    (puncturedProductHomeomorph j v hv r).symm.continuous.comp
      (continuous_const.prodMk (timeShift (flatTorusAffine j v) θ).continuous)⟩

@[simp] theorem boundaryInclusionAt_mk (a : Radius j.order r) (θ t : ℝ) (x : RealTorus₄) :
    boundaryInclusionAt j v hv r a θ (MappingTorus.mk (flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r (a, ((((t + θ) / j.order : ℝ) : Circle), x)) := by
  change (puncturedProductHomeomorph j v hv r).symm
    (a, timeShift (flatTorusAffine j v) θ (MappingTorus.mk _ (t, x))) = _
  rw [timeShift_mk, puncturedProductHomeomorph_symm_mk]

@[simp] theorem boundaryInclusionAt_zero (a : Radius j.order r) :
    boundaryInclusionAt j v hv r a 0 = boundaryInclusion j v hv r a := by
  apply ContinuousMap.ext
  intro x
  change (puncturedProductHomeomorph j v hv r).symm
    (a, timeShift (flatTorusAffine j v) 0 x) =
      (puncturedProductHomeomorph j v hv r).symm (a, x)
  rw [timeShift_zero]

/-- Both the radius and the real phase can vary without changing the actual
boundary inclusion up to homotopy. -/
def boundaryRadiusPhaseHomotopy (a b : Radius j.order r) (θ : ℝ) :
    (boundaryInclusion j v hv r a).Homotopy (boundaryInclusionAt j v hv r b θ) where
  toFun p := (puncturedProductHomeomorph j v hv r).symm
    (radiusSegment a b p.1, timeShift (flatTorusAffine j v) ((p.1 : ℝ) * θ) p.2)
  continuous_toFun := (puncturedProductHomeomorph j v hv r).symm.continuous.comp
    (((radiusSegment_continuous a).comp
      (continuous_fst.prodMk continuous_const)).prodMk
        ((timeShift_jointly_continuous (flatTorusAffine j v)).comp
          (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
            continuous_snd)))
  map_zero_left x := by
    change (puncturedProductHomeomorph j v hv r).symm
      (radiusSegment a b 0, timeShift (flatTorusAffine j v) ((0 : unitInterval) * θ) x) =
        (puncturedProductHomeomorph j v hv r).symm (a, x)
    simp
  map_one_left x := by
    change (puncturedProductHomeomorph j v hv r).symm
      (radiusSegment a b 1, timeShift (flatTorusAffine j v) ((1 : unitInterval) * θ) x) =
        (puncturedProductHomeomorph j v hv r).symm (b, timeShift (flatTorusAffine j v) θ x)
    simp

/-- Every point of the homotopy keeps its original real-period coordinate. -/
theorem boundaryRadiusPhaseHomotopy_mk (a b : Radius j.order r) (θ : ℝ)
    (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    boundaryRadiusPhaseHomotopy j v hv r a b θ
        (s, MappingTorus.mk (flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (radiusSegment a b s, ((((t + (s : ℝ) * θ) / j.order : ℝ) : Circle), x)) := by
  change (puncturedProductHomeomorph j v hv r).symm
    (radiusSegment a b s,
      timeShift (flatTorusAffine j v) ((s : ℝ) * θ) (MappingTorus.mk _ (t, x))) = _
  rw [timeShift_mk, puncturedProductHomeomorph_symm_mk]

end GenericBoundary

section SpecialBoundary

variable (j : Kind) (a : Radius j.order (specialBaseCover.radius (some j))) (θ : ℝ)

/-- The actual original punctured small piece, at any allowed radius and phase. -/
def specialBoundaryInclusionAt : C(SpecialBoundary j, PuncturedPiece (some j)) :=
  ((specialPuncturedHomeomorph j).symm : C(_, _)).comp
    (boundaryInclusionAt j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) a θ)

/-- The radius-and-phase homotopy takes values in the literal original small piece. -/
def specialBoundaryRadiusPhaseHomotopy :
    (specialBoundaryInclusion j).Homotopy (specialBoundaryInclusionAt j a θ) :=
  (ContinuousMap.Homotopy.refl ((specialPuncturedHomeomorph j).symm :
    C(PuncturedFilling j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)), PuncturedPiece (some j)))).comp
    (boundaryRadiusPhaseHomotopy j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) (specialRootRadius j) a θ)

/-- The varied boundary is still the original varying-period quotient on every representative. -/
theorem specialBoundaryInclusionAt_mk (t : ℝ) (x : RealTorus₄) :
    ((specialBoundaryInclusionAt j a θ
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))).val : SpecialEllipticPiece j).val =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (root j.order (specialBaseCover.radius (some j)) a
          (((t + θ) / j.order : ℝ) : Circle), x) := by
  change (((specialPuncturedHomeomorph j).symm
    (boundaryInclusionAt j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) a θ (MappingTorus.mk _ (t, x)))).val :
        SpecialEllipticPiece j).val = _
  rw [boundaryInclusionAt_mk]
  rfl

/-- The original real-period coordinate is unchanged throughout the special homotopy. -/
theorem specialBoundaryRadiusPhaseHomotopy_mk (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    ((specialBoundaryRadiusPhaseHomotopy j a θ
      (s, MappingTorus.mk (flatTorusAffine j j.twist) (t, x))).val : SpecialEllipticPiece j).val =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (root j.order (specialBaseCover.radius (some j))
          (radiusSegment (specialRootRadius j) a s)
          (((t + (s : ℝ) * θ) / j.order : ℝ) : Circle), x) := by
  change (((specialPuncturedHomeomorph j).symm
    (boundaryRadiusPhaseHomotopy j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) (specialRootRadius j) a θ
      (s, MappingTorus.mk _ (t, x)))).val : SpecialEllipticPiece j).val = _
  rw [boundaryRadiusPhaseHomotopy_mk]
  rfl

/-- The original regular-family inclusion at the specified radius and phase. -/
def specialBoundaryToRegularFamilyAt : C(SpecialBoundary j, SpecialRegularFamily) :=
  (puncturedPieceToRegular (some j)).comp (specialBoundaryInclusionAt j a θ)

/-- The original small-filling inclusion at the specified radius and phase. -/
def specialBoundaryToPieceAt : C(SpecialBoundary j, SpecialEllipticPiece j) :=
  (puncturedPieceInclusion (some j)).comp (specialBoundaryInclusionAt j a θ)

theorem boundaryToRegularFamily_homotopic_at :
    (boundaryToRegularFamily (some j)).Homotopic (specialBoundaryToRegularFamilyAt j a θ) := by
  change ((puncturedPieceToRegular (some j)).comp (specialBoundaryInclusion j)).Homotopic _
  exact ⟨(ContinuousMap.Homotopy.refl (puncturedPieceToRegular (some j))).comp
    (specialBoundaryRadiusPhaseHomotopy j a θ)⟩

theorem specialBoundaryToPiece_homotopic_at :
    (specialBoundaryToPiece j).Homotopic (specialBoundaryToPieceAt j a θ) :=
  ⟨(ContinuousMap.Homotopy.refl (puncturedPieceInclusion (some j))).comp
    (specialBoundaryRadiusPhaseHomotopy j a θ)⟩

theorem boundaryToFilling_homotopic_at :
    (ThreefoldOverlapMappingTorus.boundaryToFilling (some j)).Homotopic
      (specialBoundaryToPieceAt j a θ) := by
  rw [boundaryToFilling_elliptic]
  exact specialBoundaryToPiece_homotopic_at j a θ

/-- The actual regular attachment coefficient is independent of this radius-and-phase choice. -/
theorem boundaryRegularHomologyMap_at (n : ℕ) :
    boundaryRegularHomologyMap (some j) n =
      singularHomologyMap (specialBoundaryToRegularFamilyAt j a θ) n :=
  homotopic_homologyMap (boundaryToRegularFamily_homotopic_at j a θ) n

/-- The actual filling attachment coefficient is independent of the same choice. -/
theorem boundaryFillingHomologyMap_at (n : ℕ) :
    boundaryFillingHomologyMap (some j) n =
      singularHomologyMap (specialBoundaryToPieceAt j a θ) n :=
  homotopic_homologyMap (boundaryToFilling_homotopic_at j a θ) n

end SpecialBoundary
end Elliptic
end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
