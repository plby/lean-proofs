import Wikipedia.HopfProblem.CuspControlledRetractionPuncturedPolar
import Wikipedia.HopfProblem.CuspControlledRetractionCoordinates
import Wikipedia.HopfProblem.CuspHoneycombHomeomorph

/-!
# The prescribed collapse map on the actual punctured closed tube

The punctured polar homeomorphism gives unique compact phases and a
positive point.  The prescribed collapse keeps those phases and sends
the positive point's normalized position through the already constructed
equivariant honeycomb homeomorphism.  This definition uses no retraction
homotopy or endpoint map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse CuspHoneycomb CuspPositive

/-- The full compact torus acting on a positive central point, with
codomain restricted to the literal central fibre. -/
def centralCompactPolar (p : CompactTorus × PositiveCentralFibre) : CentralFibre :=
  ⟨compactTorusAction p.1 (p.2.1 : Space), by
    simp only [compactTorusAction, time_torusAction, p.2.2, mul_zero]⟩

@[simp] theorem centralCompactPolar_coe (p : CompactTorus × PositiveCentralFibre) :
    (centralCompactPolar p : Space) = compactTorusAction p.1 (p.2.1 : Space) := rfl

theorem centralCompactPolar_continuous : Continuous centralCompactPolar :=
  (compactTorusAction_continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_subtype_val).comp
      continuous_snd))).subtype_mk _

@[simp] theorem centralModulus_centralCompactPolar (p : CompactTorus × PositiveCentralFibre) :
    centralModulus (centralCompactPolar p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change modulus (compactTorusAction p.1 (p.2.1 : Space)) = (p.2.1 : Space)
  rw [modulus_compactTorusAction]
  exact p.2.1.2

/-- The prescribed positive endpoint is defined directly from normalized
coordinates and the actual honeycomb homeomorphism. -/
def prescribedPositiveCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (q : PuncturedPositiveTube η) : PositiveCentralFibre :=
  honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : Space))

/-- The explicit prescribed map in the unique punctured polar coordinates. -/
def prescribedPolarCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) : CentralFibre :=
  centralCompactPolar (p.1, prescribedPositiveCollapse C₀ η p.2)

/-- The actual prescribed collapse, defined independently of any
deformation or retraction. -/
def prescribedCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : CentralFibre :=
  prescribedPolarCollapse C₀ η ((puncturedPolarHomeomorph η).symm x)

@[simp] theorem prescribedCollapse_puncturedPolarMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : CompactTorus × PuncturedPositiveTube η) :
    prescribedCollapse C₀ η (puncturedPolarMap η p) = prescribedPolarCollapse C₀ η p := by
  unfold prescribedCollapse
  rw [puncturedPolarHomeomorph_symm_map]

/-- The exact source formula on every nonzero closed-tube polar
representative, not only on a selected radius. -/
theorem prescribedCollapse_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (u : CompactTorus) (q : PuncturedPositiveTube η) :
    (prescribedCollapse C₀ η (puncturedPolarMap η (u, q)) : Space) =
      compactTorusAction u
        ((honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : Space))).1 : Space) := by
  rw [prescribedCollapse_puncturedPolarMap]
  rfl

@[simp] theorem prescribedCollapse_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) :
    centralModulus (prescribedCollapse C₀ η x) =
      prescribedPositiveCollapse C₀ η ((puncturedPolarHomeomorph η).symm x).2 :=
  centralModulus_centralCompactPolar _

section Continuity

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε) (hηε : η < ε)

include hε1 hR hηε

theorem normalizedPosition_puncturedPositive_continuous :
    Continuous (fun q : PuncturedPositiveTube η => normalizedPosition C₀ (q.1.1 : Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε q.2).comp
    continuous_subtype_val.continuousAt

theorem prescribedPositiveCollapse_continuous : Continuous (prescribedPositiveCollapse C₀ η) :=
  (honeycombHomeomorph C₀).continuous.comp
    (normalizedPosition_puncturedPositive_continuous C₀ hε1 hR hηε)

theorem prescribedPolarCollapse_continuous : Continuous (prescribedPolarCollapse C₀ η) :=
  centralCompactPolar_continuous.comp
    (continuous_fst.prodMk ((prescribedPositiveCollapse_continuous C₀ hε1 hR hηε).comp
      continuous_snd))

theorem prescribedCollapse_continuous : Continuous (prescribedCollapse C₀ η) :=
  (prescribedPolarCollapse_continuous C₀ hε1 hR hηε).comp
    (puncturedPolarHomeomorph η).symm.continuous

end Continuity

end Wikipedia.HopfProblem.CuspControlledRetraction
