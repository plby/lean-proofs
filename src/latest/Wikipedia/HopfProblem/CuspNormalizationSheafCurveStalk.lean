import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkAxes
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationBasic

/-!
# Actual double-curve sheaf stalks in an adapted normalization chart

An incident double curve has its actual holomorphic stalk identified
with the actual one-variable analytic-germ ring at zero. The comparison
uses the genuine curve inclusion and its genuine centered axis chart.
Its section formula is literal translated-axis composition, and scalar
evaluation agrees with evaluation of this analytic germ at zero.

A nonincident curve has a zero actual stalk. The convenient `At`
versions use the normalization-chart coordinate of the given actual
central-fibre point directly.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafGermComplex

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : CoordinateSpace 3)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

section Active

variable (hb : b ∈ (normalizationChart C ε hε hε1 hC hR a s).target)
  (x : CentralSpace C ε)
  (hxb : (x : QuotientSpace C ε) = (normalizationChart C ε hε hε1 hC hR a s).symm b)
  (k : Fin 3)
  (hk : sourcePair s k ⊆ Germs.activeBranches b)

include C ε hε hε1 hC hR a s b hb x hxb k hk

local notation "t" => b (s.axisIndex (sourceEdgeIndex k))
local notation "d" => axisSection C ε hε s (sourceEdgeIndex k) t

/-- The actual curve point selected by the normalization chart lies
over the specified actual central-fibre point. -/
theorem chartCurvePoint_map :
    sourceCurveMap C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) = x := by
  apply Subtype.ext
  exact hxb.symm

/-- The literal axis point is that same actual point of the fibre. -/
theorem axisSection_map : sourceCurveMap C ε hε k d = x :=
  (congrArg (sourceCurveMap C ε hε k)
    (chartCurvePoint_eq_axisSection C ε hε hε1 hC hR a s b hb k hk)).symm.trans
      (chartCurvePoint_map C ε hε hε1 hC hR a s b hb x hxb k hk)

/-- The actual axis centre belongs to the inverse image of every base
neighbourhood of the actual central point. -/
theorem axisPoint_mem_preimage (U : Opens (CentralSpace C ε)) (hxU : x ∈ U) :
    d ∈ (Opens.map (sourceCurveMap C ε hε k)).obj U :=
  curvePoint_mem_preimage C ε hε k d x
    (axisSection_map C ε hε hε1 hC hR a s b hb x hxb k hk) U hxU

/-- The actual additive direct-image stalk of an incident double curve
is its genuine centered one-variable analytic-germ ring. -/
def curveStalkEquiv :
    (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x ≃+ AxisGerm :=
  (curvePointStalkEquiv C ε hε hε1 hC hR k d x
    (axisSection_map C ε hε hε1 hC hR a s b hb x hxb k hk)).trans
      (axisStalkEquiv C ε hε hε1 hC hR s k t).toAddEquiv

/-- On a literal actual section germ, the representative is its literal
composition with `axisSection (t + z)`. -/
@[simp] theorem curveStalkEquiv_germ
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : CurveSection C ε hε hε1 hC hR k
      ((Opens.map (sourceCurveMap C ε hε k)).obj U)) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        ((curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU f) =
      Germs.ofAnalytic
        (axisSectionRepresentative C ε hε hε1 hC hR s k t
          ((Opens.map (sourceCurveMap C ε hε k)).obj U) f)
        (axisSectionRepresentative_analyticAt C ε hε hε1 hC hR s k t
          ((Opens.map (sourceCurveMap C ε hε k)).obj U) f
          (axisPoint_mem_preimage C ε hε hε1 hC hR a s b hb x hxb k hk U hxU)) :=
  (congrArg (axisStalkEquiv C ε hε hε1 hC hR s k t)
    (curvePointStalkEquiv_germ C ε hε hε1 hC hR k d x
      (axisSection_map C ε hε hε1 hC hR a s b hb x hxb k hk) U hxU f)).trans
    (axisStalkEquiv_germ C ε hε hε1 hC hR s k t
      ((Opens.map (sourceCurveMap C ε hε k)).obj U)
      (axisPoint_mem_preimage C ε hε hε1 hC hR a s b hb x hxb k hk U hxU) f)

/-- Analytic evaluation at zero is the actual value of the original
section at the actual axis centre. -/
@[simp] theorem curveStalkEquiv_germ_eval
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : CurveSection C ε hε hε1 hC hR k
      ((Opens.map (sourceCurveMap C ε hε k)).obj U)) :
    Germs.eval (0 : ℂ) (curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        ((curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU f)) =
      f ⟨d, axisPoint_mem_preimage C ε hε hε1 hC hR a s b hb x hxb k hk U hxU⟩ := by
  rw [curveStalkEquiv_germ, Germs.eval_ofAnalytic, axisSectionRepresentative_zero]

/-- On every actual stalk element, evaluation of the centered analytic
germ equals the genuine scalar stalk evaluation at the actual chart point. -/
@[simp] theorem eval_curveStalkEquiv
    (φ : (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    Germs.eval (0 : ℂ) (curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk φ) =
      SheafEvaluation.stalkEvaluationAt 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
        (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) x
        (chartCurvePoint_map C ε hε hε1 hC hR a s b hb x hxb k hk) φ := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  obtain ⟨U, hxU, f, rfl⟩ := (curveSheaf C ε hε hε1 hC hR k).presheaf.exists_germ_eq φ
  change CurveSection C ε hε hε1 hC hR k
    ((Opens.map (sourceCurveMap C ε hε k)).obj U) at f
  exact (curveStalkEquiv_germ_eval C ε hε hε1 hC hR a s b hb x hxb k hk U hxU f).trans
    ((congrArg f (Subtype.ext
      (chartCurvePoint_eq_axisSection C ε hε hε1 hC hR a s b hb k hk).symm)).trans
      (SheafEvaluation.stalkEvaluationAt_germ 𝓘(ℂ, ℂ) (sourceCurveMap C ε hε k)
        (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) x
        (chartCurvePoint_map C ε hε hε1 hC hR a s b hb x hxb k hk) U hxU f).symm)

end Active

/-- A source double curve not incident to the chosen chart point has a
zero actual direct-image stalk. -/
theorem curveStalk_isZero_of_not_active (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : ¬ sourcePair s k ⊆ Germs.activeBranches b) :
    IsZero ((curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) := by
  apply curveStalk_isZero_of_not_mem C ε hε hε1 hC hR k x
  intro hx
  rw [hxb] at hx
  exact hk ((mem_sourceDoubleCurve_iff_pair_active C ε hε hε1 hC hR a s b hb k).mp hx)

omit b in
/-- The incident-curve equivalence with the chart coordinate of the
actual point selected automatically. -/
def curveStalkEquivAt (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (k : Fin 3) (hk : sourcePair s k ⊆ Germs.activeBranches ((e) x.val)) :
    (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x ≃+ AxisGerm :=
  curveStalkEquiv C ε hε hε1 hC hR a s ((e) x.val) ((e).map_source hx)
    x ((e).left_inv hx).symm k hk

omit b in
/-- The nonincident zero-stalk statement in the same automatic chart
coordinates as `curveStalkEquivAt`. -/
theorem curveStalk_isZeroAt (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (k : Fin 3) (hk : ¬ sourcePair s k ⊆ Germs.activeBranches ((e) x.val)) :
    IsZero ((curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) :=
  curveStalk_isZero_of_not_active C ε hε hε1 hC hR a s ((e) x.val)
    ((e).map_source hx) x ((e).left_inv hx).symm k hk

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
