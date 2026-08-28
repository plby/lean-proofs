import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelBasic

/-!
# The phase-plane source quotient for a positive real level

Before any phase stabilizers are collapsed, the source relation consists
only of the displayed integral deck translations. This is the relation
of the positive-real frozen fibre. Its canonical map to the actual central
fibre is the existing honeycomb collapse, descended through these translations.
The additional base phase at a nonreal level is not discarded here.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

@[simp] theorem sourceDeck_zero (p : PhasePlane) : honeycombDeckMap C₀ 0 p = p := by
  simp only [honeycombDeckMap, deckFibrePhase_zero, one_mul, cuspVector_zero,
    latticePoint_zero, add_zero, Prod.eta]

theorem sourceDeck_add (v w : Fin 2 → ℤ) (p : PhasePlane) :
    honeycombDeckMap C₀ v (honeycombDeckMap C₀ w p) = honeycombDeckMap C₀ (v + w) p := by
  apply Prod.ext
  · change deckFibrePhase C₀ v * (deckFibrePhase C₀ w * p.1) =
      deckFibrePhase C₀ (v + w) * p.1
    rw [deckFibrePhase_add, mul_assoc]
  · change (p.2 + latticePoint (cuspVector w)) + latticePoint (cuspVector v) =
      p.2 + latticePoint (cuspVector (v + w))
    rw [cuspVector_add, latticePoint_add]
    abel

/-- The original integral deck transformation in normalized source coordinates. -/
def sourceDeckHomeomorph (v : Fin 2 → ℤ) : PhasePlane ≃ₜ PhasePlane where
  toFun := honeycombDeckMap C₀ v
  invFun := honeycombDeckMap C₀ (-v)
  left_inv p := by rw [sourceDeck_add, neg_add_cancel, sourceDeck_zero]
  right_inv p := by rw [sourceDeck_add, add_neg_cancel, sourceDeck_zero]
  continuous_toFun := (continuous_const.mul continuous_fst).prodMk
    (continuous_snd.add continuous_const)
  continuous_invFun := (continuous_const.mul continuous_fst).prodMk
    (continuous_snd.add continuous_const)

/-- Only genuine deck translations are identified in the nonzero-fibre source model. -/
def sourceDeckSetoid : Setoid PhasePlane where
  r p q := ∃ v : Fin 2 → ℤ, honeycombDeckMap C₀ v q = p
  iseqv :=
    { refl := fun p => ⟨0, sourceDeck_zero C₀ p⟩
      symm := by
        rintro p q ⟨v, hv⟩
        refine ⟨-v, ?_⟩
        rw [← hv, sourceDeck_add, neg_add_cancel, sourceDeck_zero]
      trans := by
        rintro p q r ⟨v, hv⟩ ⟨w, hw⟩
        refine ⟨v + w, ?_⟩
        rw [← sourceDeck_add, hw, hv] }

abbrev SourceModel := Quotient (sourceDeckSetoid C₀)

def sourceProjection : PhasePlane → SourceModel C₀ := Quotient.mk (sourceDeckSetoid C₀)

theorem sourceProjection_continuous : Continuous (sourceProjection C₀) := continuous_quotient_mk'

theorem sourceProjection_surjective : Function.Surjective (sourceProjection C₀) :=
  Quotient.mk_surjective

theorem sourceProjection_isQuotientMap : IsQuotientMap (sourceProjection C₀) :=
  isQuotientMap_quotient_mk'

theorem sourceProjection_eq_iff (p q : PhasePlane) :
    sourceProjection C₀ p = sourceProjection C₀ q ↔
      ∃ v : Fin 2 → ℤ, honeycombDeckMap C₀ v q = p :=
  ⟨Quotient.exact, fun h => @Quotient.sound PhasePlane (sourceDeckSetoid C₀) p q h⟩

@[simp] theorem sourceProjection_deck (v : Fin 2 → ℤ) (p : PhasePlane) :
    sourceProjection C₀ (honeycombDeckMap C₀ v p) = sourceProjection C₀ p :=
  (sourceProjection_eq_iff C₀ _ p).mpr ⟨v, rfl⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem honeycombCollapseMap_sourceDeck (v : Fin 2 → ℤ) (p : PhasePlane) :
    honeycombCollapseMap C ε hε (honeycombDeckMap (C 0) v p) =
      honeycombCollapseMap C ε hε p := by
  apply (honeycombCollapseMap_eq_iff C ε hε _ p).mpr
  refine ⟨v, rfl, ?_⟩
  change (deckFibrePhase (C 0) v * p.1)⁻¹ * (deckFibrePhase (C 0) v * p.1) ∈ _
  rw [inv_mul_cancel]
  exact Subgroup.one_mem _

/-- The actual central collapse of the free phase-plane source quotient. -/
def sourceCollapse : C(SourceModel (C 0), QuotientCentralFibre C ε) where
  toFun := Quotient.lift (honeycombCollapseMap C ε hε) (by
    rintro p q ⟨v, hv⟩
    rw [← hv]
    exact honeycombCollapseMap_sourceDeck C ε hε v q)
  continuous_toFun := (honeycombCollapseMap_continuous C ε hε).quotient_lift _

@[simp] theorem sourceCollapse_projection (p : PhasePlane) :
    sourceCollapse C ε hε (sourceProjection (C 0) p) = honeycombCollapseMap C ε hε p := rfl

theorem sourceCollapse_surjective : Function.Surjective (sourceCollapse C ε hε) := by
  intro q
  obtain ⟨p, rfl⟩ := honeycombCollapseMap_surjective C ε hε q
  exact ⟨sourceProjection (C 0) p, rfl⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
