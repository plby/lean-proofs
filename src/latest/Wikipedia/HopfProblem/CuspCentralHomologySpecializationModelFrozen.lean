import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelPolar
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelPositive
import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspControlledRetractionCoordinates

/-!
# Frozen phase-plane coordinates on a positive-real toric fibre

The inverse normalized positive coordinates, together with the actual
compact fibre action, identify the phase plane with the original nonzero
toric fibre. The genuine constant-twist action becomes precisely the
previously defined honeycomb lattice-and-phase action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspPositive CuspCollapse CuspControlledRetraction
open CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The actual positive-twist action on the literal fixed-height fibre. -/
def positiveFibreTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) : PositiveFibre ρ :=
  ⟨⟨twistedTranslate (positiveTwist C₀) v (q.1 : Space),
      twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [time_twistedTranslate, q.2]⟩

@[simp] theorem positiveFibreTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) :
    ((positiveFibreTranslate C₀ ρ v q).1 : Space) =
      twistedTranslate (positiveTwist C₀) v (q.1 : Space) := rfl

@[simp] theorem positiveFibreTranslate_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (q : PositiveFibre ρ) : positiveFibreTranslate C₀ ρ 0 q = q :=
  Subtype.ext (Subtype.ext (twistedTranslate_zero (positiveTwist C₀) (q.1 : Space)))

theorem positiveFibreTranslate_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v w : Fin 2 → ℤ) (q : PositiveFibre ρ) :
    positiveFibreTranslate C₀ ρ v (positiveFibreTranslate C₀ ρ w q) =
      positiveFibreTranslate C₀ ρ (v + w) q :=
  Subtype.ext (Subtype.ext (twistedTranslate_add (positiveTwist C₀) v w (q.1 : Space)))

/-- The original positive action is ordinary lattice translation in the
proved normalized position coordinates. -/
theorem normalizedPosition_positiveFibreTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) :
    normalizedPosition C₀ ((positiveFibreTranslate C₀ ρ v q).1 : Space) =
      normalizedPosition C₀ (q.1 : Space) + latticePoint (cuspVector v) := by
  have hq : time (q.1 : Space) ≠ 0 := by
    rw [q.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have ht : ‖time (q.1 : Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact normalizedPosition_twistedTranslate C₀ hε1 hR v hq ht

/-- Polar multiplication has the exact frozen deck covariance before
taking any lattice quotient. -/
theorem positiveFibrePolarMap_phaseDeck
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (v : Fin 2 → ℤ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    (positiveFibrePolarMap ρ (deckFibrePhase C₀ v * p.1,
      positiveFibreTranslate C₀ ρ v p.2) : Space) =
      twistedTranslate (fun _ => C₀) v (positiveFibrePolarMap ρ p : Space) := by
  rw [positiveFibrePolarMap_coe, positiveFibrePolarMap_coe]
  change compactFibreAction (deckFibrePhase C₀ v * p.1)
      (twistedTranslate (positiveTwist C₀) v (p.2.1 : Space)) =
    twistedTranslate (fun _ => C₀) v (compactFibreAction p.1 (p.2.1 : Space))
  rw [compactFibreAction_eq_compact, compactFibreAction_eq_compact,
    twistedTranslate_constant_polar, phaseTransform_compactFibrePhase]

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- The actual inverse normalized coordinates are equivariant because
their inverse is the already proved normalized position. -/
theorem normalizedPositiveHomeomorph_equivariant (v : Fin 2 → ℤ) (y : Plane) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR
      (y + latticePoint (cuspVector v)) =
      positiveFibreTranslate C₀ ρ v
        (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y) := by
  apply (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm.injective
  rw [Homeomorph.symm_apply_apply, normalizedPositiveHomeomorph_symm_apply,
    normalizedPosition_positiveFibreTranslate C₀ ρ hρ ε hε1 hρε hR]
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply y
  rw [normalizedPositiveHomeomorph_symm_apply] at hy
  rw [hy]

include hε1 hρε hR in
theorem normalizedPositivePoint_equivariant (v : Fin 2 → ℤ) (y : Plane) :
    normalizedPositivePoint C₀ ρ hρ (y + latticePoint (cuspVector v)) =
      positiveFibreTranslate C₀ ρ v (normalizedPositivePoint C₀ ρ hρ y) := by
  simpa only [normalizedPositiveHomeomorph_apply] using
    normalizedPositiveHomeomorph_equivariant C₀ ρ hρ ε hε1 hρε hR v y

/-- The genuine compact-phase and normalized-plane coordinates on the
literal positive-real nonzero toric fibre. -/
def frozenPhaseHomeomorph : PhasePlane ≃ₜ ToricFibre (ρ : ℂ) :=
  ((Homeomorph.refl CompactFibreTorus).prodCongr
    (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans
      (positiveFibrePolarHomeomorph ρ hρ)

@[simp] theorem frozenPhaseHomeomorph_apply (p : PhasePlane) :
    frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p = positiveFibrePolarMap ρ
      (p.1, normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2) := rfl

theorem frozenPhaseHomeomorph_coe_homeomorph (p : PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : Space) =
      compactFibreAction p.1
        ((normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2).1 : Space) := rfl

@[simp] theorem frozenPhaseHomeomorph_coe (p : PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : Space) =
      compactFibreAction p.1 ((normalizedPositivePoint C₀ ρ hρ p.2).1 : Space) := by
  rw [frozenPhaseHomeomorph_coe_homeomorph, normalizedPositiveHomeomorph_apply]

@[simp] theorem frozenPhaseHomeomorph_symm_fst (x : ToricFibre (ρ : ℂ)) :
    ((frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm x).1 =
      ((positiveFibrePolarHomeomorph ρ hρ).symm x).1 := rfl

/-- The actual modulus supplies the positive coordinate of the inverse. -/
@[simp] theorem frozenPhaseHomeomorph_symm_snd (x : ToricFibre (ρ : ℂ)) :
    ((frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm x).2 =
      normalizedPosition C₀ (modulus (x : Space)) := by
  change (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm
    (((positiveFibrePolarHomeomorph ρ hρ).symm x).2) = _
  rw [normalizedPositiveHomeomorph_symm_apply,
    positiveFibrePolarHomeomorph_symm_positive_coe]

/-- The original frozen deck action is exactly the previously constructed
honeycomb phase-and-lattice action in these genuine fibre coordinates. -/
theorem frozenPhaseHomeomorph_deck (v : Fin 2 → ℤ) (p : PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR (honeycombDeckMap C₀ v p) : Space) =
      twistedTranslate (fun _ => C₀) v
        (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : Space) := by
  change (positiveFibrePolarMap ρ (deckFibrePhase C₀ v * p.1,
      normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR
        (p.2 + latticePoint (cuspVector v))) : Space) =
    twistedTranslate (fun _ => C₀) v (positiveFibrePolarMap ρ
      (p.1, normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2) : Space)
  rw [normalizedPositiveHomeomorph_equivariant]
  exact positiveFibrePolarMap_phaseDeck C₀ ρ v
    (p.1, normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
