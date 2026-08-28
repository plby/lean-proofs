import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCompact
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspEndpoints

/-!
# Global sections of the actual double-curve direct images

Each source-ordered double curve is the actual constructed sphere with
its actual analytic atlas. Its proved sphere homeomorphism supplies
compactness and connectedness, and the compact maximum principle
identifies genuine global sections with constants by evaluation at P.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution CuspQuotient ToricCharts ToricSpace HolomorphicFunctionSheaf
open CuspQuotient.NormalizationCurves

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- Compactness is proved using the actual sphere parametrization. -/
theorem sourceCurve_compact (k : Fin 3) : CompactSpace (sourceDoubleCurve C ε hε k) :=
  (curveSphereHomeomorph C ε hε hε1 hC hR (sourceEdgeIndex k)).compactSpace

/-- Connectedness is proved using the actual sphere parametrization. -/
theorem sourceCurve_connected (k : Fin 3) : ConnectedSpace (sourceDoubleCurve C ε hε k) :=
  (curveSphereHomeomorph C ε hε hε1 hC hR (sourceEdgeIndex k)).surjective.connectedSpace
    (curveSphereHomeomorph C ε hε hε1 hC hR (sourceEdgeIndex k)).continuous

/-- Actual curve direct-image sections retain their pointwise complex module. -/
abbrev CurveFunctions (k : Fin 3) : Type :=
  @GlobalSections ℂ ℂ _ _ _ 𝓘(ℂ) (sourceDoubleCurve C ε hε k) _
    (curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k))

/-- The actual section module uses the fixed, constructed curve atlas. -/
instance curveSections_module (k : Fin 3) :
    Module ℂ (Sections (curveSheaf C ε hε hε1 hC hR k)) :=
  inferInstanceAs (Module ℂ (CurveFunctions C ε hε hε1 hC hR k))

/-- The global-section identification for actual curve pushforward
is literally the identity on functions on the top open set. -/
def curveSectionsLinearEquiv (k : Fin 3) :
    Sections (curveSheaf C ε hε hε1 hC hR k) ≃ₗ[ℂ]
      CurveFunctions C ε hε hε1 hC hR k := LinearEquiv.refl ℂ _

/-- Literal evaluation of a genuine curve direct-image global section. -/
def curveValue (k : Fin 3) (s : Sections (curveSheaf C ε hε hε1 hC hR k))
    (x : sourceDoubleCurve C ε hε k) : ℂ :=
  curveSectionsLinearEquiv C ε hε hε1 hC hR k s
    (toTopOpen (sourceDoubleCurve C ε hε k) x)

/-- Values of an actual global curve section agree at all actual points. -/
theorem curveValue_eq (k : Fin 3) (s : Sections (curveSheaf C ε hε hε1 hC hR k))
    (x y : sourceDoubleCurve C ε hε k) :
    curveValue C ε hε hε1 hC hR k s x = curveValue C ε hε hε1 hC hR k s y := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let := curve_isManifold C ε hε hε1 hC hR (sourceEdgeIndex k)
  let := sourceCurve_compact C ε hε hε1 hC hR k
  let := sourceCurve_connected C ε hε hε1 hC hR k
  exact compact_global_apply_eq 𝓘(ℂ) (sourceDoubleCurve C ε hε k)
    (curveSectionsLinearEquiv C ε hε hε1 hC hR k s) x y

/-- A literal constant holomorphic section of an actual curve pushforward. -/
def curveConstantSection (k : Fin 3) (c : ℂ) :
    Sections (curveSheaf C ε hε hε1 hC hR k) :=
  algebraMap ℂ (CurveFunctions C ε hε hε1 hC hR k) c

/-- Actual evaluation at the source-ordered endpoint P is complex linear. -/
def curveGlobalEval (k : Fin 3) : Sections (curveSheaf C ε hε hε1 hC hR k) →ₗ[ℂ] ℂ where
  toFun s := curveValue C ε hε hε1 hC hR k s (curveTriplePoint C ε hε k 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curveGlobalEval_injective (k : Fin 3) :
    Function.Injective (curveGlobalEval C ε hε hε1 hC hR k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  intro f g h
  apply (curveSectionsLinearEquiv C ε hε hε1 hC hR k).injective
  apply ContMDiffMap.ext
  intro x
  exact (curveValue_eq C ε hε hε1 hC hR k f x (curveTriplePoint C ε hε k 0)).trans
    (h.trans (curveValue_eq C ε hε hε1 hC hR k g (curveTriplePoint C ε hε k 0) x))

theorem curveGlobalEval_surjective (k : Fin 3) :
    Function.Surjective (curveGlobalEval C ε hε hε1 hC hR k) := by
  intro c
  exact ⟨curveConstantSection C ε hε hε1 hC hR k c, rfl⟩

/-- Evaluation at the actual source-ordered point P identifies the
actual curve direct-image global sections with the complex numbers. -/
def curveGlobalLinearEquiv (k : Fin 3) :
    Sections (curveSheaf C ε hε hε1 hC hR k) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (curveGlobalEval C ε hε hε1 hC hR k)
    ⟨curveGlobalEval_injective C ε hε hε1 hC hR k,
      curveGlobalEval_surjective C ε hε hε1 hC hR k⟩

@[simp] theorem curveGlobalLinearEquiv_apply (k : Fin 3)
    (s : Sections (curveSheaf C ε hε hε1 hC hR k)) :
    curveGlobalLinearEquiv C ε hε hε1 hC hR k s =
      curveValue C ε hε hε1 hC hR k s (curveTriplePoint C ε hε k 0) := rfl

/-- The scalar obtained from P is also the actual value at Q or any
other actual point of the same curve. -/
theorem curveValue_eq_scalar (k : Fin 3) (s : Sections (curveSheaf C ε hε hε1 hC hR k))
    (x : sourceDoubleCurve C ε hε k) :
    curveValue C ε hε hε1 hC hR k s x = curveGlobalLinearEquiv C ε hε hε1 hC hR k s :=
  curveValue_eq C ε hε hε1 hC hR k s x (curveTriplePoint C ε hε k 0)

@[simp] theorem curveGlobalLinearEquiv_symm_apply (k : Fin 3) (c : ℂ) :
    (curveGlobalLinearEquiv C ε hε hε1 hC hR k).symm c =
      curveConstantSection C ε hε hε1 hC hR k c := by
  apply (curveGlobalLinearEquiv C ε hε hε1 hC hR k).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
