import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyPhase

/-!
# The actual central rotation and the free-source unipotent shear

The compact phase covariance is applied to the genuine positive central
point given by the honeycomb homeomorphism.  Thus the resulting homotopy
takes values in the literal central toric fibre, even at a boundary or
triple point.  Its full-turn source map is descended through the original
free integral deck relation.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling CuspPositive

/-- The integral unipotent shear before taking the original free deck quotient. -/
def phasePlaneShear (p : PhasePlane) : PhasePlane :=
  (p.1 * planarPhase p.2, p.2)

theorem phasePlaneShear_continuous : Continuous phasePlaneShear :=
  (continuous_fst.mul (planarPhase_continuous.comp continuous_snd)).prodMk continuous_snd

theorem phasePlaneShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : PhasePlane) :
    phasePlaneShear (honeycombDeckMap C₀ v p) =
      honeycombDeckMap C₀ v (phasePlaneShear p) := by
  apply Prod.ext
  · change (deckFibrePhase C₀ v * p.1) *
        planarPhase (p.2 + latticePoint (cuspVector v)) =
      deckFibrePhase C₀ v * (p.1 * planarPhase p.2)
    rw [planarPhase_add_latticePoint, mul_assoc]
  · rfl

/-- The literal descended shear on the free phase-plane quotient. -/
def sourceShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : C(SourceModel C₀, SourceModel C₀) where
  toFun := Quotient.map phasePlaneShear (by
    rintro p q ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [← phasePlaneShear_deck, hv])
  continuous_toFun :=
    ((sourceProjection_continuous C₀).comp phasePlaneShear_continuous).quotient_lift _

@[simp] theorem sourceShear_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    sourceShear C₀ (sourceProjection C₀ p) = sourceProjection C₀ (phasePlaneShear p) := rfl

/-- The genuine compact-three-torus action on a positive central point,
with the shear-compensating planar phase. -/
def rotatingCentralPoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (p : PhasePlane) : CentralFibre :=
  ⟨compactTorusAction (compensatingPhase r p)
      ((honeycombHomeomorph C₀ p.2).1 : Space), by
    apply norm_eq_zero.mp
    rw [norm_time_compactTorusAction, (honeycombHomeomorph C₀ p.2).2, norm_zero]⟩

theorem rotatingCentralPoint_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun p : ℝ × PhasePlane => rotatingCentralPoint C₀ p.1 p.2) := by
  have hθ : Continuous (fun p : ℝ × PhasePlane => honeycombHomeomorph C₀ p.2.2) :=
    (honeycombHomeomorph C₀).continuous.comp (continuous_snd.comp continuous_snd)
  have hθp : Continuous (fun p : ℝ × PhasePlane => (honeycombHomeomorph C₀ p.2.2).1) :=
    continuous_subtype_val.comp hθ
  have hθx : Continuous (fun p : ℝ × PhasePlane =>
      ((honeycombHomeomorph C₀ p.2.2).1 : Space)) := continuous_subtype_val.comp hθp
  apply Continuous.subtype_mk
  change Continuous (fun p : ℝ × PhasePlane =>
    compensatingPhase p.1 p.2 • ((honeycombHomeomorph C₀ p.2.2).1 : Space))
  exact compensatingPhase_continuous.smul hθx

@[simp] theorem rotatingCentralPoint_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) : rotatingCentralPoint C₀ 0 p = honeycombPolarMap C₀ p := by
  apply Subtype.ext
  change compactTorusAction (compensatingPhase 0 p) _ = _
  rw [compensatingPhase_zero]
  rfl

@[simp] theorem rotatingCentralPoint_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : PhasePlane) :
    rotatingCentralPoint C₀ 1 p = honeycombPolarMap C₀ (phasePlaneShear p) := by
  apply Subtype.ext
  change compactTorusAction (compensatingPhase 1 p) _ = _
  rw [compensatingPhase_one]
  rfl

/-- All intermediate stages intertwine the actual deck translations on
the central toric fibre; there is no assumption that its point is dense. -/
theorem rotatingCentralPoint_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (r : ℝ) (p : PhasePlane) :
    (rotatingCentralPoint (C 0) r (honeycombDeckMap (C 0) v p) : Space) =
      twistedTranslate C v (rotatingCentralPoint (C 0) r p : Space) := by
  rw [twistedTranslate_central_eq_constant C v (rotatingCentralPoint (C 0) r p).2]
  change compactTorusAction (compensatingPhase r (honeycombDeckMap (C 0) v p))
      ((honeycombHomeomorph (C 0) (p.2 + latticePoint (cuspVector v))).1 : Space) =
    twistedTranslate (fun _ => C 0) v
      (compactTorusAction (compensatingPhase r p) ((honeycombHomeomorph (C 0) p.2).1 : Space))
  rw [compensatingPhase_deck, honeycombHomeomorph_equivariant,
    positiveCentralTranslate_coe, twistedTranslate_constant_polar]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
