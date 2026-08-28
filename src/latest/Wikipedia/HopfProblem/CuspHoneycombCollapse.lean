import Wikipedia.HopfProblem.CuspHoneycombHomeomorph
import Wikipedia.HopfProblem.CuspCollapseCentralQuotient

/-!
# The actual central cusp collapse in honeycomb coordinates

The constructed equivariant honeycomb homeomorphism replaces the positive
central coordinate by the literal real plane. The polar map then gives
an actual quotient map from the compact fibre torus times that plane to
the toric central fibre. Its further quotient is the original cusp central
fibre, with explicit lattice translations and stratum-dependent phase
stabilizers describing exactly its fibres.

These are maps of the actual central spaces. This file does not claim that
the previously constructed neighborhood retraction has been modified to
have this prescribed collapse on a selected nonzero fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

abbrev PhasePlane := CompactFibreTorus × Plane

/-- Genuine honeycomb coordinates on compact phases and positive central points. -/
def phaseCoordinatesHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane ≃ₜ PhasePositiveSpace :=
  (Homeomorph.refl CompactFibreTorus).prodCongr (honeycombHomeomorph C₀)

@[simp] theorem phaseCoordinatesHomeomorph_apply
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    phaseCoordinatesHomeomorph C₀ p = (p.1, honeycombHomeomorph C₀ p.2) := rfl

/-- The actual polar collapse over the literal honeycomb plane. -/
def honeycombPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : PhasePlane → CentralFibre :=
  centralPolarMap ∘ phaseCoordinatesHomeomorph C₀

theorem honeycombPolarMap_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (honeycombPolarMap C₀) :=
  centralPolarMap_continuous.comp (phaseCoordinatesHomeomorph C₀).continuous

theorem honeycombPolarMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (honeycombPolarMap C₀) :=
  centralPolarMap_surjective.comp (phaseCoordinatesHomeomorph C₀).surjective

theorem honeycombPolarMap_isProperMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    IsProperMap (honeycombPolarMap C₀) :=
  centralPolarMap_isProperMap.comp (phaseCoordinatesHomeomorph C₀).isProperMap

theorem honeycombPolarMap_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    IsQuotientMap (honeycombPolarMap C₀) :=
  centralPolarMap_isQuotientMap.comp (phaseCoordinatesHomeomorph C₀).isQuotientMap

/-- The base point is unique; only its actual phase stabilizer is collapsed. -/
theorem honeycombPolarMap_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p q : PhasePlane) :
    honeycombPolarMap C₀ p = honeycombPolarMap C₀ q ↔ p.2 = q.2 ∧
      p.1⁻¹ * q.1 ∈ MulAction.stabilizer CompactFibreTorus
        ((honeycombHomeomorph C₀ p.2).1 : Space) := by
  change centralPolarMap (phaseCoordinatesHomeomorph C₀ p) =
    centralPolarMap (phaseCoordinatesHomeomorph C₀ q) ↔ _
  rw [centralPolarMap_eq_iff]
  change honeycombHomeomorph C₀ p.2 = honeycombHomeomorph C₀ q.2 ∧ _ ↔ _
  rw [(honeycombHomeomorph C₀).injective.eq_iff]
  rfl

/-- The explicit lattice action in compact-phase and planar coordinates. -/
def honeycombDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : PhasePlane) : PhasePlane :=
  (deckFibrePhase C₀ v * p.1, p.2 + latticePoint (cuspVector v))

theorem phaseCoordinatesHomeomorph_deck
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (p : PhasePlane) :
    phaseCoordinatesHomeomorph C₀ (honeycombDeckMap C₀ v p) =
      phaseDeckMap C₀ v (phaseCoordinatesHomeomorph C₀ p) := by
  apply Prod.ext
  · rfl
  · exact honeycombHomeomorph_equivariant C₀ v p.2

/-- This displayed action is the original central deck action, including
the compact phases contributed by the frozen correction. -/
theorem honeycombPolarMap_deck
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (p : PhasePlane) :
    (honeycombPolarMap (C 0) (honeycombDeckMap (C 0) v p) : Space) =
      twistedTranslate C v (honeycombPolarMap (C 0) p : Space) := by
  change (centralPolarMap (phaseCoordinatesHomeomorph (C 0)
    (honeycombDeckMap (C 0) v p)) : Space) = _
  rw [phaseCoordinatesHomeomorph_deck]
  exact centralPolarMap_phaseDeckMap C v (phaseCoordinatesHomeomorph (C 0) p)

/-- The actual map to the literal central fibre of the original cusp quotient. -/
def honeycombCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePlane → QuotientCentralFibre C ε :=
  centralCollapseMap C ε hε ∘ phaseCoordinatesHomeomorph (C 0)

theorem honeycombCollapseMap_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (honeycombCollapseMap C ε hε) :=
  (centralCollapseMap_continuous C ε hε).comp (phaseCoordinatesHomeomorph (C 0)).continuous

theorem honeycombCollapseMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Function.Surjective (honeycombCollapseMap C ε hε) :=
  (centralCollapseMap_surjective C ε hε).comp (phaseCoordinatesHomeomorph (C 0)).surjective

theorem honeycombCollapseMap_isQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    IsQuotientMap (honeycombCollapseMap C ε hε) :=
  (centralCollapseMap_isQuotientMap C ε hε hC).comp
    (phaseCoordinatesHomeomorph (C 0)).isQuotientMap

/-- Integral translation and the indicated phase stabilizer give the
entire relation, without a further equivalence closure. -/
def honeycombCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : PhasePlane) : Prop :=
  ∃ v : Fin 2 → ℤ, p.2 = q.2 + latticePoint (cuspVector v) ∧
    p.1⁻¹ * (deckFibrePhase C₀ v * q.1) ∈
      MulAction.stabilizer CompactFibreTorus ((honeycombHomeomorph C₀ p.2).1 : Space)

theorem honeycombCollapseMap_eq_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p q : PhasePlane) :
    honeycombCollapseMap C ε hε p = honeycombCollapseMap C ε hε q ↔
      honeycombCollapseRelation (C 0) p q := by
  change centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) p) =
    centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) q) ↔ _
  rw [centralCollapseMap_eq_iff]
  unfold centralCollapseRelation honeycombCollapseRelation
  apply exists_congr
  intro v
  change honeycombHomeomorph (C 0) p.2 =
    positiveCentralTranslate (C 0) v (honeycombHomeomorph (C 0) q.2) ∧ _ ↔ _
  rw [← honeycombHomeomorph_equivariant,
    (honeycombHomeomorph (C 0)).injective.eq_iff]
  rfl

def honeycombCollapseSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Setoid PhasePlane where
  r := honeycombCollapseRelation C₀
  iseqv := by
    let f := honeycombCollapseMap (fun _ => C₀) 1 zero_lt_one
    have he (p q : PhasePlane) : f p = f q ↔ honeycombCollapseRelation C₀ p q :=
      honeycombCollapseMap_eq_iff (fun _ => C₀) 1 zero_lt_one p q
    exact
      { refl := fun p => (he p p).mp rfl
        symm := fun {p q} h => (he q p).mp ((he p q).mpr h).symm
        trans := fun {p q r} hpq hqr =>
          (he p r).mp (((he p q).mpr hpq).trans ((he q r).mpr hqr)) }

abbrev HoneycombCollapseModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (honeycombCollapseSetoid C₀)

/-- A genuine homeomorphism from the displayed planar phase-collapse
quotient to the original central cusp fibre. -/
def honeycombCollapseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    HoneycombCollapseModel (C 0) ≃ₜ QuotientCentralFibre C ε :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (Quotient.mk (honeycombCollapseSetoid (C 0))) (honeycombCollapseMap C ε hε)
    isQuotientMap_quotient_mk' (honeycombCollapseMap_isQuotientMap C ε hε hC)
    (fun p q => ⟨fun h => (honeycombCollapseMap_eq_iff C ε hε p q).mpr (Quotient.exact h),
      fun h => Quotient.sound ((honeycombCollapseMap_eq_iff C ε hε p q).mp h)⟩)

theorem honeycombCollapseHomeomorph_mk
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (p : PhasePlane) :
    honeycombCollapseHomeomorph C ε hε hC
      (Quotient.mk (honeycombCollapseSetoid (C 0)) p) = honeycombCollapseMap C ε hε p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

end Wikipedia.HopfProblem.CuspHoneycomb
