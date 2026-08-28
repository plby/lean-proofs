import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspEndpoints

/-!
# Full active branch sets are actual triple points

The full coordinate branch set makes the actual point lie on two
distinct actual source double curves. Their proved set-theoretic
intersection consists precisely of the two actual triple points.
At either triple point the actual curve point selected by a chart is
the actual source-ordered triple point of that curve, by injectivity of
the actual curve inclusion.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafCurveStalk

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- Two different actual source double curves meet only at the actual
two triple points. -/
theorem exists_triplePoint_of_mem_two_sourceCurves (x : CentralSpace C ε)
    (h₀ : x.val ∈ sourceDoubleCurve C ε hε 0)
    (h₁ : x.val ∈ sourceDoubleCurve C ε hε 1) :
    ∃ t : Fin 2, x = triplePoint C ε hε t := by
  have hx : x.val ∈ doubleCurve C ε hε (sourceEdgeIndex 0) ∩
      doubleCurve C ε hε (sourceEdgeIndex 1) := ⟨h₀, h₁⟩
  rw [doubleCurve_inter_eq_pair C ε hε (sourceEdgeIndex 0) (sourceEdgeIndex 1)
    (by decide)] at hx
  rcases hx with h | h
  · exact ⟨1, Subtype.ext h⟩
  · exact ⟨0, Subtype.ext h⟩

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- A full active branch set places the actual point on each actual
source double curve; this is the proved chart membership criterion. -/
theorem mem_sourceCurve_of_full_active (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (hfull : Germs.activeBranches ((e) x.val) = Finset.univ) (k : Fin 3) :
    x.val ∈ sourceDoubleCurve C ε hε k := by
  have hk : sourcePair s k ⊆ Germs.activeBranches ((e) x.val) := by
    rw [hfull]
    exact Finset.subset_univ _
  have hm := (mem_sourceDoubleCurve_iff_pair_active C ε hε hε1 hC hR a s
    ((e) x.val) ((e).map_source hx) k).mpr hk
  rwa [(e).left_inv hx] at hm

/-- Full activity in an actual normalization chart forces the actual
point to be one of the actual two triple points. -/
theorem exists_triplePoint_of_full_active (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (hfull : Germs.activeBranches ((e) x.val) = Finset.univ) :
    ∃ t : Fin 2, x = triplePoint C ε hε t :=
  exists_triplePoint_of_mem_two_sourceCurves C ε hε x
    (mem_sourceCurve_of_full_active C ε hε hε1 hC hR a s x hx hfull 0)
    (mem_sourceCurve_of_full_active C ε hε hε1 hC hR a s x hx hfull 1)

/-- At an actual triple point, the actual chart-selected point of an
incident curve is the actual source-ordered triple point of that curve. -/
theorem chartCurvePoint_eq_curveTriplePoint (b : CoordinateSpace 3)
    (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (t : Fin 2) (hxt : x = triplePoint C ε hε t) :
    chartCurvePoint C ε hε hε1 hC hR a s b hb k hk = curveTriplePoint C ε hε k t := by
  apply sourceCurveMap_injective C ε hε k
  exact (chartCurvePoint_map C ε hε hε1 hC hR a s b hb x hxb k hk).trans
    (hxt.trans (sourceCurveMap_curveTriplePoint C ε hε k t).symm)

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation
