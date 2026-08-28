import Wikipedia.HopfProblem.CuspCollapseCentralPolar
import Wikipedia.HopfProblem.CuspPositiveRetractionPhases
import Wikipedia.HopfProblem.ToricCentralAction

/-!
# The genuine central deck action in phase coordinates

On the central fibre, a varying correction acts through its value at zero.
In the actual phase presentation its action is positive translation on the
positive coordinate and multiplication by a fixed compact fibre phase.
These formulas include boundary points and commute with phase collapse.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCollapse

open ToricSpace CuspRetraction CuspPositiveRetraction

/-- The frozen multiplier's two compact phases. -/
def deckFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) : CompactFibreTorus :=
  fun i => CuspPositive.frozenPhaseCoordinate C₀ v i

@[simp] theorem deckFibrePhase_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    deckFibrePhase C₀ 0 = 1 := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe,
    exponentialMultiplier_zero, Pi.one_apply, Units.val_one, one_div, inv_one, Circle.coe_one]

theorem deckFibrePhase_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ) :
    deckFibrePhase C₀ (v + w) = deckFibrePhase C₀ v * deckFibrePhase C₀ w := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe, Pi.mul_apply, Circle.coe_mul]
  rw [exponentialMultiplier_add, exponentialMultiplier_add]
  simp only [Pi.mul_apply, Units.val_mul, div_mul_div_comm]

theorem phaseTransform_compactFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : CompactFibreTorus) :
    CuspPositive.phaseTransform C₀ v (ToricSpace.compactFibrePhase u) =
      ToricSpace.compactFibrePhase (deckFibrePhase C₀ v * u) := by
  funext i
  fin_cases i <;>
    simp [CuspPositive.phaseTransform, CuspPositive.frozenPhase, phaseShear,
      ToricSpace.compactFibrePhase, deckFibrePhase]

/-- Positive translation on the literal positive central fibre. -/
def positiveCentralTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (q : PositiveCentralFibre) : PositiveCentralFibre :=
  ⟨⟨twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : Space),
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [time_twistedTranslate, q.2]⟩

@[simp] theorem positiveCentralTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (q : PositiveCentralFibre) :
    ((positiveCentralTranslate C₀ v q).1 : Space) =
      twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : Space) := rfl

@[simp] theorem positiveCentralTranslate_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (q : PositiveCentralFibre) : positiveCentralTranslate C₀ 0 q = q :=
  Subtype.ext (Subtype.ext (twistedTranslate_zero (CuspPositive.positiveTwist C₀) q.1))

theorem positiveCentralTranslate_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (q : PositiveCentralFibre) :
    positiveCentralTranslate C₀ v (positiveCentralTranslate C₀ w q) =
      positiveCentralTranslate C₀ (v + w) q :=
  Subtype.ext (Subtype.ext (twistedTranslate_add (CuspPositive.positiveTwist C₀) v w q.1))

theorem positiveCentralTranslate_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : Continuous (positiveCentralTranslate C₀ v) :=
  (((centralTranslationHomeomorph (CuspPositive.positiveTwist C₀) v).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

def positiveCentralHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : PositiveCentralFibre ≃ₜ PositiveCentralFibre where
  toFun := positiveCentralTranslate C₀ v
  invFun := positiveCentralTranslate C₀ (-v)
  left_inv q := by
    rw [positiveCentralTranslate_add, neg_add_cancel, positiveCentralTranslate_zero]
  right_inv q := by
    rw [positiveCentralTranslate_add, add_neg_cancel, positiveCentralTranslate_zero]
  continuous_toFun := positiveCentralTranslate_continuous C₀ v
  continuous_invFun := positiveCentralTranslate_continuous C₀ (-v)

/-- The explicit diagonal deck action on the central phase presentation. -/
def phaseDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CompactFibreTorus × PositiveCentralFibre) : CompactFibreTorus × PositiveCentralFibre :=
  (deckFibrePhase C₀ v * p.1, positiveCentralTranslate C₀ v p.2)

@[simp] theorem phaseDeckMap_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CompactFibreTorus × PositiveCentralFibre) : phaseDeckMap C₀ 0 p = p := by
  simp only [phaseDeckMap, deckFibrePhase_zero, one_mul, positiveCentralTranslate_zero, Prod.eta]

theorem phaseDeckMap_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (p : CompactFibreTorus × PositiveCentralFibre) :
    phaseDeckMap C₀ v (phaseDeckMap C₀ w p) = phaseDeckMap C₀ (v + w) p := by
  simp only [phaseDeckMap, positiveCentralTranslate_add, deckFibrePhase_add, mul_assoc]

theorem phaseDeckMap_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    Continuous (phaseDeckMap C₀ v) :=
  (continuous_const.mul continuous_fst).prodMk
    ((positiveCentralTranslate_continuous C₀ v).comp continuous_snd)

def phaseDeckHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    (CompactFibreTorus × PositiveCentralFibre) ≃ₜ
      (CompactFibreTorus × PositiveCentralFibre) where
  toFun := phaseDeckMap C₀ v
  invFun := phaseDeckMap C₀ (-v)
  left_inv p := by rw [phaseDeckMap_add, neg_add_cancel, phaseDeckMap_zero]
  right_inv p := by rw [phaseDeckMap_add, add_neg_cancel, phaseDeckMap_zero]
  continuous_toFun := phaseDeckMap_continuous C₀ v
  continuous_invFun := phaseDeckMap_continuous C₀ (-v)

/-- The original central translation uses only the central correction. -/
theorem twistedTranslate_central_eq_constant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : time x = 0) :
    twistedTranslate C v x = twistedTranslate (fun _ => C 0) v x := by
  simp only [twistedTranslate, variableMultiplier, time_translate, hx]
  rfl

/-- The actual varying-twist action commutes with the phase presentation
through the explicit diagonal transformation above. -/
theorem centralPolarMap_phaseDeckMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : CompactFibreTorus × PositiveCentralFibre) :
    (centralPolarMap (phaseDeckMap (C 0) v p) : Space) =
      twistedTranslate C v (centralPolarMap p : Space) := by
  rw [twistedTranslate_central_eq_constant C v (centralPolarMap p).2]
  change compactFibreAction (deckFibrePhase (C 0) v * p.1)
      ((positiveCentralTranslate (C 0) v p.2).1 : Space) =
    twistedTranslate (fun _ => C 0) v (compactFibreAction p.1 (p.2.1 : Space))
  rw [compactFibreAction_eq_compact, compactFibreAction_eq_compact,
    CuspPositive.twistedTranslate_constant_polar, phaseTransform_compactFibrePhase]
  rfl

end Wikipedia.HopfProblem.CuspCollapse
