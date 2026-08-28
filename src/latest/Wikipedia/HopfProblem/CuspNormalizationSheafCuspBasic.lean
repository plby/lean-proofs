import Wikipedia.HopfProblem.CuspComponentProper
import Wikipedia.HopfProblem.CuspRationalCurves

/-!
# The actual spaces and maps in the cusp normalization resolution

The base is the actual reduced central-fibre subset of the constructed
cusp quotient. The normalization map is the actual component projection
with codomain restricted to that subset. The curve maps are literal
inclusions of the already constructed double curves.

The source convention labels the triple point with odd cyclic hexagon
vertices as `P`; for the repo's opposite cyclic ray convention this is
the upper triple point. `Q` is the lower triple point.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual central-fibre set in the cusp quotient. -/
def centralSet : Set (QuotientSpace C ε) := projection C ε ⁻¹' {0}

/-- The base of the resolution has the actual central-fibre subspace topology. -/
abbrev CentralSpace := ↥(centralSet C ε)

/-- The actual normalization map, with its codomain restricted to the central fibre. -/
def normalization (x : rayDivisor 0) : CentralSpace C ε :=
  ⟨componentProjection C ε hε x, projection_componentProjection C ε hε x⟩

@[simp] theorem normalization_val (x : rayDivisor 0) :
    (normalization C ε hε x : QuotientSpace C ε) = componentProjection C ε hε x := rfl

theorem normalization_continuous : Continuous (normalization C ε hε) :=
  (componentProjection_continuous C ε hε).subtype_mk _

theorem normalization_surjective : Function.Surjective (normalization C ε hε) := by
  intro x
  have hx : (x : QuotientSpace C ε) ∈ range (componentProjection C ε hε) := by
    rw [componentProjection_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

theorem normalization_isClosedMap : IsClosedMap (normalization C ε hε) :=
  (componentProjection_isClosedMap C ε hε).subtype_mk _

/-- The actual topological-space morphism used by sheaf pushforward. -/
def normalizationMap : TopCat.of (rayDivisor 0) ⟶ TopCat.of (CentralSpace C ε) :=
  TopCat.ofHom ⟨normalization C ε hε, normalization_continuous C ε hε⟩

@[simp] theorem normalizationMap_apply (x : rayDivisor 0) :
    normalizationMap C ε hε x = normalization C ε hε x := rfl

theorem normalization_fibre_finite (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (x : CentralSpace C ε) :
    (normalization C ε hε ⁻¹' {x}).Finite := by
  have he : normalization C ε hε ⁻¹' {x} =
      componentProjection C ε hε ⁻¹' {(x : QuotientSpace C ε)} := by
    ext y
    change normalization C ε hε y = x ↔ componentProjection C ε hε y = x.val
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [he]
  exact componentProjection_fibre_finite C ε hε hε1 hC hR x

/-- The actual inclusion of a double curve into the central fibre. -/
def curveInclusion (i : Fin 3) (x : doubleCurve C ε hε i) : CentralSpace C ε :=
  ⟨x, doubleCurve_subset_central C ε hε i x.property⟩

@[simp] theorem curveInclusion_val (i : Fin 3) (x : doubleCurve C ε hε i) :
    (curveInclusion C ε hε i x : QuotientSpace C ε) = x := rfl

theorem curveInclusion_continuous (i : Fin 3) : Continuous (curveInclusion C ε hε i) :=
  continuous_subtype_val.subtype_mk _

theorem curveInclusion_injective (i : Fin 3) :
    Function.Injective (curveInclusion C ε hε i) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : CentralSpace C ε => z.val) h)

theorem curveInclusion_isClosedMap (i : Fin 3) : IsClosedMap (curveInclusion C ε hε i) :=
  ((doubleCurve_isClosed C ε hε i).isClosedMap_subtype_val).subtype_mk _

/-- The actual topological inclusion used in the curve pushforwards. -/
def curveMap (i : Fin 3) : TopCat.of (doubleCurve C ε hε i) ⟶ TopCat.of (CentralSpace C ε) :=
  TopCat.ofHom ⟨curveInclusion C ε hε i, curveInclusion_continuous C ε hε i⟩

@[simp] theorem curveMap_apply (i : Fin 3) (x : doubleCurve C ε hε i) :
    curveMap C ε hε i x = curveInclusion C ε hε i x := rfl

/-- The source's first actual triple point. -/
def pointP : CentralSpace C ε :=
  ⟨upperTriplePoint C ε hε, projection_upperTriplePoint C ε hε⟩

/-- The source's second actual triple point. -/
def pointQ : CentralSpace C ε :=
  ⟨lowerTriplePoint C ε hε, projection_lowerTriplePoint C ε hε⟩

theorem pointP_ne_pointQ : pointP C ε hε ≠ pointQ C ε hε := by
  intro h
  exact (triplePoints_distinct C ε hε) (congrArg Subtype.val h).symm

/-- The first triple point as an actual point of each double curve. -/
def curvePointP (i : Fin 3) : doubleCurve C ε hε i :=
  ⟨upperTriplePoint C ε hε, upperTriplePoint_mem_doubleCurve C ε hε i⟩

/-- The second triple point as an actual point of each double curve. -/
def curvePointQ (i : Fin 3) : doubleCurve C ε hε i :=
  ⟨lowerTriplePoint C ε hε, lowerTriplePoint_mem_doubleCurve C ε hε i⟩

@[simp] theorem curveMap_pointP (i : Fin 3) :
    curveMap C ε hε i (curvePointP C ε hε i) = pointP C ε hε := rfl

@[simp] theorem curveMap_pointQ (i : Fin 3) :
    curveMap C ε hε i (curvePointQ C ε hε i) = pointQ C ε hε := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
