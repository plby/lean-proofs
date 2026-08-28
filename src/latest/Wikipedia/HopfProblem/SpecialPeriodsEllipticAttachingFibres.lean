import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMarking
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupFibres

/-!
# Lattice-translation attaching loops in the actual elliptic pieces

At the same logarithmic basepoint as the meridian, every integral period
gives a literal fibre loop in the chosen small elliptic filling. The
unchanged radial retraction identifies its deck marking with translation
by the negative period vector. No basepoint tail is introduced.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticFilling CuspUniformization

/-- Translation by an integral period at the actual logarithmic basepoint. -/
abbrev attachingFibreFullLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (w : Lattice) :=
  fibreTranslationLoop (specialLocalData j) j.twist (mainTwist_admissible j)
    (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w

theorem attachingFibreFullLoop_projection (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (w : Lattice) (t : I) :
    (specialFullFillingProjection j (attachingFibreFullLoop j s₀ hs₀ w t) : ℂ) =
      exponential s₀ ^ j.order := by
  change (logMeridianRoot j s₀ hs₀ 0 : ℂ) ^ j.order = _
  rw [logMeridianRoot_zero]

theorem attachingFibreFullLoop_mem_piece (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    attachingFibreFullLoop j s₀ hs₀ w t ∈
      pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
        specialBaseCover j := by
  change ‖(specialFullFillingProjection j (attachingFibreFullLoop j s₀ hs₀ w t) : ℂ)‖ < _
  rw [attachingFibreFullLoop_projection, norm_pow]
  exact hr

/-- The fibre translation remains in the actual selected small piece. -/
def attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr) where
  toFun t := ⟨attachingFibreFullLoop j s₀ hs₀ w t,
    attachingFibreFullLoop_mem_piece j s₀ hs₀ hr w t⟩
  continuous_toFun := (attachingFibreFullLoop j s₀ hs₀ w).continuous.subtype_mk _
  source' := Subtype.ext (attachingFibreFullLoop j s₀ hs₀ w).source
  target' := Subtype.ext (attachingFibreFullLoop j s₀ hs₀ w).target

@[simp] theorem attachingFibreLoop_coe (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    (attachingFibreLoop j s₀ hs₀ hr w t : SpecialFullFilling j) =
      attachingFibreFullLoop j s₀ hs₀ w t := rfl

/-- Mapping into the whole filling recovers the genuine generic fibre loop. -/
theorem attachingFibreLoop_map_full (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    (attachingFibreLoop j s₀ hs₀ hr w).map
        (continuous_subtype_val : Continuous (Subtype.val : LocalSpace j → SpecialFullFilling j)) =
      fibreTranslationLoop (specialLocalData j) j.twist (mainTwist_admissible j)
        (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w := by
  ext t
  rfl

theorem attachingFibreLoop_quotient (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    (attachingFibreLoop j s₀ hs₀ hr w t : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (logMeridianRoot j s₀ hs₀ 0,
          standardLattice.mkQ (attachingFlatBase j s₀ hs₀ + (t : ℝ) • realCast w)) := rfl

/-- The loop has the original period-vector formula in varying complex coordinates. -/
theorem attachingFibreLoop_complex_formula (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    (attachingFibreLoop j s₀ hs₀ hr w t : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        ((specialLocalData j).periods.quotientMap (logMeridianRoot j s₀ hs₀ 0,
          (specialLocalData j).periods.periodEquiv (logMeridianRoot j s₀ hs₀ 0)
              (attachingFlatBase j s₀ hs₀) +
            (t : ℂ) • periodVector (specialLocalData j).periods w
              (logMeridianRoot j s₀ hs₀ 0))) :=
  fibreTranslationLoop_complex_formula (specialLocalData j) j.twist (mainTwist_admissible j)
    (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w t

@[simp] theorem parameter_attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    parameter j (attachingFibreLoop j s₀ hs₀ hr w t) = exponential s₀ ^ j.order :=
  attachingFibreFullLoop_projection j s₀ hs₀ w t

theorem parameter_attachingFibreLoop_norm (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    ‖parameter j (attachingFibreLoop j s₀ hs₀ hr w t)‖ = ‖exponential s₀‖ ^ j.order := by
  rw [parameter_attachingFibreLoop, norm_pow]

theorem parameter_attachingFibreLoop_ne_zero (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    parameter j (attachingFibreLoop j s₀ hs₀ hr w t) ≠ 0 := by
  rw [parameter_attachingFibreLoop]
  exact pow_ne_zero j.order (exponential_ne_zero s₀)

theorem projectionToBase_attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    specialEllipticPieceProjectionToBase j (attachingFibreLoop j s₀ hs₀ hr w t) =
      (punctureChart (some j)).symm (exponential s₀ ^ j.order) := by
  change (punctureChart (some j)).symm
    (parameter j (attachingFibreLoop j s₀ hs₀ hr w t)) = _
  rw [parameter_attachingFibreLoop]

theorem projectionToBase_attachingFibreLoop_mem_regular (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    specialEllipticPieceProjectionToBase j (attachingFibreLoop j s₀ hs₀ hr w t) ∈ regularPatch :=
  (pieceProjectionToBase_mem_regular_iff specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _).mpr
      (parameter_attachingFibreLoop_ne_zero j s₀ hs₀ hr w t)

/-- The actual retracted path with only its proved basepoint equality cast. -/
def attachingFibreRetractionLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    Path (affineCoverProjection j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀))
      (affineCoverProjection j (specialLocalData j).centralPeriod j.twist
        (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)) :=
  ((attachingFibreLoop j s₀ hs₀ hr w).map (pieceSurfaceRetraction j).continuous).cast
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm

theorem attachingFibreRetractionLoop_eq (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    attachingFibreRetractionLoop j s₀ hs₀ hr w =
      fibreTranslationSurfaceLoop (specialLocalData j) j.twist (mainTwist_admissible j)
        (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w := by
  ext t
  rfl

/-- The actual fibre-attaching loop has the native negative lattice-translation marking. -/
theorem attachingDeckEquiv_attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    attachingDeckEquiv j s₀ hs₀ hr
        (FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr w⟧) =
      deckTranslationHom j j.twist (Multiplicative.ofAdd (-w)) := by
  change surfaceFundamentalGroupDeckEquiv j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
      (MulEquiv.cast (M := FundamentalGroup (SpecialCentralSurface j))
        (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)
        (FundamentalGroup.fromPath
          ⟦(attachingFibreLoop j s₀ hs₀ hr w).map (pieceSurfaceRetraction j).continuous⟧)) = _
  rw [fundamentalGroup_cast_loop]
  change surfaceFundamentalGroupDeckEquiv j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
      (FundamentalGroup.fromPath ⟦attachingFibreRetractionLoop j s₀ hs₀ hr w⟧) = _
  rw [attachingFibreRetractionLoop_eq]
  exact fibreTranslationSurfaceLoop_deck (specialLocalData j) j.twist (mainTwist_admissible j)
    (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
