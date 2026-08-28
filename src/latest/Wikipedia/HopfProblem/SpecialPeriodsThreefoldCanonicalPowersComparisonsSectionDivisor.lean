import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsSectionDivisorLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleLocalGluing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartierSections

/-!
# Global native bundle comparison from actual local section equations

If two actual sections have locally equal native coefficients up to a
holomorphic unit, and the source section is nonzero on a dense set,
those local comparisons glue to a genuine holomorphic bundle
isomorphism.  On overlaps equality follows first by cancellation at
the dense nonzero points and then by continuity.  Thus no compatibility
or bundle isomorphism is assumed in addition to the local equations.
-/

noncomputable section

open Set Topology Bundle TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ}
  {sA : ∀ x, A.core.Fiber x} {sB : ∀ x, B.core.Fiber x}
  [A.IsHolomorphic I] [B.IsHolomorphic I]

namespace LocalSectionComparison

/-- The exact section equations imply agreement wherever the source
section is nonzero; density and actual continuity extend it over the zeros. -/
theorem localValue_eq_of_dense (G : Set M) (hG : Dense G)
    (hsA : ∀ x ∈ G, sA x ≠ 0) (D D' : LocalSectionComparison I A B sA sB)
    (i : ι × κ) {x : M} (hi : x ∈ A.baseSet i.1 ∩ B.baseSet i.2)
    (hx : x ∈ D.domain) (hx' : x ∈ D'.domain) : D.localValue i x = D'.localValue i x := by
  let V : Set M := ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ D.domain) ∩ D'.domain
  have hV : IsOpen V :=
    (((A.isOpen_baseSet i.1).inter (B.isOpen_baseSet i.2)).inter D.domain.isOpen).inter
      D'.domain.isOpen
  have hD : ContinuousOn (fun y => (D.localValue i y : ℂ)) V :=
    (D.localValue_holomorphicOn i).continuousOn.mono (fun _ hy => hy.1)
  have hD' : ContinuousOn (fun y => (D'.localValue i y : ℂ)) V :=
    (D'.localValue_holomorphicOn i).continuousOn.mono (fun _ hy => ⟨hy.1.1, hy.2⟩)
  have he : EqOn (fun y => (D.localValue i y : ℂ))
      (fun y => (D'.localValue i y : ℂ)) (V ∩ G) := by
    intro y hy
    have hn : A.localCoefficient sA i.1 y ≠ 0 :=
      mul_ne_zero (A.transition_ne_zero _ _ _) (hsA y hy.2)
    apply mul_right_cancel₀ hn
    exact (D.localValue_equation i hy.1.1.1 hy.1.1.2).trans
      (D'.localValue_equation i hy.1.1.1 hy.1.2).symm
  exact Units.ext ((CanonicalGlobal.eqOn_of_dense_open hG hV hD hD' he) ⟨⟨hi, hx⟩, hx'⟩)

end LocalSectionComparison

namespace SectionDivisorComparison

variable (I) (A B) (sA sB)
  (G : Set M) (hG : Dense G) (hsA : ∀ x ∈ G, sA x ≠ 0)
  (D : M → LocalSectionComparison I A B sA sB)
  (hmem : ∀ x, x ∈ (D x).domain)

/-- Every point's proved local equation supplies a genuine open coarse
chart; all gluing conditions are derived from those equations. -/
def localGauge : LocalCrossGauge I A B M where
  cover x := (D x).domain
  indexAt := id
  mem_cover := hmem
  value x := (D x).localValue
  holomorphicOn x := (D x).localValue_holomorphicOn
  agreement k l i _x hi hk hl :=
    LocalSectionComparison.localValue_eq_of_dense G hG hsA (D k) (D l) i hi hk hl
  compatible k i j _x hi hk := (D k).localValue_compatible i j hi hk

/-- The resulting genuine cross-cover comparison of the original bundles. -/
def crossGauge : CrossGauge I A B := (localGauge I A B sA sB G hG hsA D hmem).toCrossGauge

/-- The actual fibre map sends the actual source section to the actual
target section at all points, including every zero of either section. -/
theorem crossGauge_fiberEquiv_section (x : M) :
    (crossGauge I A B sA sB G hG hsA D hmem).fiberEquiv x (sA x) = sB x := by
  rw [CrossGauge.fiberEquiv_apply]
  change ((D x).localValue (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) (sA x) =
    id (α := ℂ) (sB x)
  have he := (D x).localValue_equation (A.indexAt x, B.indexAt x)
    ⟨A.mem_baseSet_at x, B.mem_baseSet_at x⟩ (hmem x)
  simpa only [A.localCoefficient_indexAt, B.localCoefficient_indexAt] using he

theorem crossGauge_diffeomorph_section (x : M) :
    (crossGauge I A B sA sB G hG hsA D hmem).diffeomorph ⟨x, sA x⟩ = ⟨x, sB x⟩ :=
  congrArg (fun v : B.core.Fiber x => (⟨x, v⟩ : B.core.TotalSpace))
    (crossGauge_fiberEquiv_section I A B sA sB G hG hsA D hmem x)

variable (hloc : ∀ x, ∃ Q : LocalSectionComparison I A B sA sB, x ∈ Q.domain)

/-- Local existence is sufficient; the construction chooses actual
neighborhoods and then proves their native bundle maps agree. -/
def crossGaugeOfLocal : CrossGauge I A B :=
  crossGauge I A B sA sB G hG hsA (fun x => (hloc x).choose)
    (fun x => (hloc x).choose_spec)

theorem crossGaugeOfLocal_fiberEquiv_section (x : M) :
    (crossGaugeOfLocal I A B sA sB G hG hsA hloc).fiberEquiv x (sA x) = sB x :=
  crossGauge_fiberEquiv_section I A B sA sB G hG hsA _ _ x

theorem crossGaugeOfLocal_diffeomorph_section (x : M) :
    (crossGaugeOfLocal I A B sA sB G hG hsA hloc).diffeomorph ⟨x, sA x⟩ = ⟨x, sB x⟩ :=
  crossGauge_diffeomorph_section I A B sA sB G hG hsA _ _ x

end SectionDivisorComparison

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
