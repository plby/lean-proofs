import Wikipedia.HopfProblem.CuspControlledRetractionCollapseEquivariance
import Wikipedia.HopfProblem.CuspControlledRetractionStraightenedCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProjection
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelCollapse

/-!
# Equivariance of the prescribed collapse independent of the ambient radius

The explicit varying-twist straightening intertwines the original deck
action with the frozen one. The independently prescribed frozen collapse
is equivariant, and on its central target the frozen and varying actions
agree. Thus the actual representative formula descends at every ambient
quotient radius containing the chosen level, independently of any chosen
retraction endpoint. Small drift is required only at an auxiliary radius.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- The genuine varying-twist translation on the literal punctured tube. -/
def puncturedTwistedTranslate (η : ℝ) (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨closedTranslate C η v x.1, by
    change time (twistedTranslate C v (x.1 : Space)) ≠ 0
    rw [time_twistedTranslate]
    exact x.2⟩

@[simp] theorem puncturedTwistedTranslate_coe (η : ℝ) (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) :
    ((puncturedTwistedTranslate C η v x).1 : Space) =
      twistedTranslate C v (x.1 : Space) := rfl

theorem puncturedStraightening_twistedTranslate {ε η : ℝ} (hε1 : ε < 1)
    (hRC : SmallDrift C ε) (hηε : η < ε) (v : Fin 2 → ℤ) (x : PuncturedClosedTube η) :
    puncturedStraightening C η (puncturedTwistedTranslate C η v x) =
      puncturedFrozenTranslate (C 0) η v (puncturedStraightening C η x) := by
  apply Subtype.ext
  apply Subtype.ext
  exact changeTwist_frozen_equivariant C hε1 hRC v (x.1.2.trans_lt hηε)

/-- The original and frozen actions coincide on every actual central stratum. -/
theorem twistedTranslate_frozen_central (v : Fin 2 → ℤ) (x : CentralFibre) :
    twistedTranslate (frozen C) v (x : Space) = twistedTranslate C v (x : Space) := by
  rw [twistedTranslate_eq_expFibreAction, twistedTranslate_eq_expFibreAction, x.2]
  rfl

@[simp] theorem levelToPunctured_levelTranslate (η : ℝ) (t : ℂ) (ht : t ≠ 0)
    (v : Fin 2 → ℤ) (x : ToricLevel η t) :
    levelToPunctured η t ht (levelTranslate C η t v x) =
      puncturedTwistedTranslate C η v (levelToPunctured η t ht x) := rfl

variable {ε η : ℝ} (hε1 : ε < 1) (hRC : SmallDrift C ε)
    (hRD : SmallDrift (frozen C) ε) (hηε : η < ε)

include hε1 hRC hRD hηε

/-- The independently prescribed straightened collapse commutes with the
original varying-twist action, without any continuity or endpoint assumption. -/
theorem straightenedPrescribedCollapse_equivariant (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) :
    (straightenedPrescribedCollapse C η (puncturedTwistedTranslate C η v x) : Space) =
      twistedTranslate C v (straightenedPrescribedCollapse C η x : Space) := by
  change (prescribedCollapse (C 0) η
      (puncturedStraightening C η (puncturedTwistedTranslate C η v x)) : Space) =
    twistedTranslate C v (prescribedCollapse (C 0) η (puncturedStraightening C η x) : Space)
  rw [puncturedStraightening_twistedTranslate C hε1 hRC hηε,
    prescribedCollapse_frozen_equivariant (C 0) hε1
      (CuspPositive.smallDrift_positiveTwist (C 0) hRD) hηε]
  exact twistedTranslate_frozen_central C v
    (prescribedCollapse (C 0) η (puncturedStraightening C η x))

/-- Invariance after projection holds at any positive ambient radius;
the small-drift estimates are imposed only at the auxiliary radius `ε`. -/
theorem prescribedFibreUpstairs_invariant (r : ℝ) (hr : 0 < r) (t : ℂ) (ht : t ≠ 0)
    (v : Fin 2 → ℤ) (x : ToricLevel η t) :
    prescribedFibreUpstairs C r hr η t ht (levelTranslate C η t v x) =
      prescribedFibreUpstairs C r hr η t ht x := by
  unfold prescribedFibreUpstairs
  rw [levelToPunctured_levelTranslate]
  apply (centralProject_eq_iff C r hr _ _).mpr
  exact ⟨v, (straightenedPrescribedCollapse_equivariant C hε1 hRC hRD hηε v
    (levelToPunctured η t ht x)).symm⟩

/-- Compatibility is deduced from the original orbit relation, not supplied
as an extra hypothesis on the prescribed collapse. -/
theorem prescribedFibreUpstairs_compatible (r : ℝ) (hr : 0 < r) (hηr : η < r)
    (t : ℂ) (ht : t ≠ 0) :
    ∀ x y : ToricLevel η t, levelProjection C hηr t x = levelProjection C hηr t y →
      prescribedFibreUpstairs C r hr η t ht x = prescribedFibreUpstairs C r hr η t ht y :=
  levelProjection_fibre_compatible_of_invariant C hηr t
    (prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_invariant C hε1 hRC hRD hηε r hr t ht)

/-- Exact evaluation of the independently defined descent on every literal
toric level representative. -/
theorem prescribedFibreCollapse_levelProjection (r : ℝ) (hr : 0 < r) (hηr : η < r)
    (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    prescribedFibreCollapse C r hr hηr t ht (levelProjection C hηr t x) =
      prescribedFibreUpstairs C r hr η t ht x :=
  levelDescend_levelProjection C hηr t (prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_compatible C hε1 hRC hRD hηε r hr hηr t ht) x

/-- The independently defined collapse on an actual quotient fibre has its
displayed straightened representative formula at every containing ambient
radius. No chosen endpoint, continuity, or separate compatibility premise is used. -/
theorem prescribedActualFibreCollapse_fibreProjection
    (r : ℝ) (hr : 0 < r) (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) :
    prescribedActualFibreCollapse C r hr hηr t ht htη
      (fibreProjection C r t (htη.trans_lt hηr) x) =
        centralProject C r hr
          (straightenedPrescribedCollapse C η (toricFibrePunctured η t ht htη x)) := by
  rw [fibreProjection_eq_levelProjection C r t (htη.trans_lt hηr) η hηr htη x]
  change prescribedFibreCollapse C r hr hηr t ht
    ((quotientLevelFibreHomeomorph C r η t htη).symm
      (quotientLevelFibreHomeomorph C r η t htη
        (levelProjection C hηr t (toricFibreLevelHomeomorph η t htη x)))) = _
  rw [Homeomorph.symm_apply_apply]
  exact prescribedFibreCollapse_levelProjection C hε1 hRC hRD hηε r hr hηr t ht
    (toricFibreLevelHomeomorph η t htη x)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
