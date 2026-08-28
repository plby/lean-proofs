import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalNative
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedSmooth
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferential
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalManifoldChart
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalManifoldCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalManifoldRepresentatives

/-!
# Actual local primitives of native closed forms on a complex threefold

The actual chart representative of a native closed form satisfies the full
antiholomorphic differential equation on its original open coordinate
domain. The proved native three-dimensional Cauchy–Green theorem supplies
a scalar primitive there. Pulling that scalar function back through the
same original chart and using the actual tangent coordinate maps gives
equality with the original native differential on a smaller manifold open.

Closedness here is the genuine differential equation, not a definition
by local exactness. No Hausdorffness, compactness, acyclicity, primitive,
or coordinate-comparison hypothesis is required.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold

variable (M : Type) [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M]

/-- The actual full chartwise closedness equation gives a genuine local
smooth primitive for the original native antiholomorphic differential. -/
theorem exists_local_primitive_of_isClosed {U : Opens M}
    (s : Forms.FormSection Model M U) (hs : ClosedForms.IsClosed Model M U s.val)
    (x : U) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
      ∃ t : Functions.SmoothSection Model M V,
        NativeDifferential.differentialSection Model M V t =
          Forms.restriction Model M hVU s := by
  let D : Opens Model := ClosedForms.coordinateDomain Model M U (x : M)
  let a : Model → Model →L[ℝ] ℂ := ClosedForms.coordinateForm Model M U s.val (x : M)
  have ha : ContDiffOn ℝ ∞ a D :=
    ClosedForms.coordinateForm_contDiffOn Model M s (x : M)
  have hanti : ∀ z ∈ D, a z ∈ antiCovectors :=
    fun z hz => ClosedForms.coordinateForm_anti Model M s (x : M) z hz
  have hclosed : ∀ z ∈ D, ∀ v w : Model,
      dbar (fun y => a y w) z v = dbar (fun y => a y v) z w := hs (x : M)
  have hxD : chartAt Model (x : M) (x : M) ∈ D :=
    ClosedForms.mem_coordinateDomain_self Model M U x x.property
  obtain ⟨u, hu, he⟩ := Local.exists_native_primitive_germ D.isOpen ha hanti hclosed hxD
  have hn : {z : Model | z ∈ D ∧ dbar u z = a z} ∈
      𝓝 (chartAt Model (x : M) (x : M)) := by
    filter_upwards [D.isOpen.mem_nhds hxD, he] with z hz hez
    exact ⟨hz, hez⟩
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hn
  let W' : Opens Model := ⟨W, hWo⟩
  have hWD : W' ≤ D := fun _ hz => (hW hz).1
  have hWeq (z : Model) (hz : z ∈ W') : dbar u z = a z := (hW hz).2
  let V : Opens M := chartPreimageOpen Model M (x : M) W'
  have hVU : V ≤ U := chartPreimageOpen_le Model M U (x : M) W' hWD
  have hxV : (x : M) ∈ V := mem_chartPreimageOpen_self Model M (x : M) W' hxW
  have hVsource : ∀ y ∈ V, y ∈ (chartAt Model (x : M)).source :=
    chartPreimageOpen_subset_source Model M (x : M) W'
  let t : Functions.SmoothSection Model M V :=
    chartSmoothSection Model M V (x : M) hVsource u hu
  refine ⟨V, hVU, hxV, t, ?_⟩
  apply Forms.FormSection.ext Model M
  intro y
  have hy := hVsource (y : M) y.property
  apply eq_at_of_inCoordinates_eq Model M
    (NativeDifferential.differentialSection Model M V t).val
    (Forms.restriction Model M hVU s).val (x : M) y hy
  rw [NativeDifferential.differentialSection_inCoordinates Model M V t (x : M) y hy]
  have hzV := chart_mem_coordinateDomain Model M V (x : M) (y : M) hy y.property
  calc
    dbar (NativeDifferential.chartFunction Model M V t (x : M))
        (chartAt Model (x : M) (y : M)) =
        dbar u (chartAt Model (x : M) (y : M)) :=
      dbar_congr (chartFunction_chartSmoothSection_germ Model M V (x : M)
        hVsource u hu (chartAt Model (x : M) (y : M)) hzV)
    _ = a (chartAt Model (x : M) (y : M)) := hWeq _ y.property.2
    _ = Forms.inCoordinates Model M s.val (x : M) ⟨(y : M), hVU y.property⟩ :=
      coordinateForm_at_chart Model M U s.val (x : M)
        ⟨(y : M), hVU y.property⟩ hy
    _ = Forms.inCoordinates Model M (Forms.restriction Model M hVU s).val
        (x : M) y :=
      (inCoordinates_restriction Model M hVU s.val (x : M) y).symm

/-- Every actual native closed `(0,1)` form has, at every original point,
a smooth local primitive whose original native differential equals the
literal restriction of the given form. -/
theorem exists_local_primitive {U : Opens M}
    (s : ClosedForms.ClosedFormSection Model M U) (x : U) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
      ∃ t : Functions.SmoothSection Model M V,
        NativeDifferential.differentialSection Model M V t =
          Forms.restriction Model M hVU (ClosedForms.ClosedFormSection.toForm Model M s) :=
  exists_local_primitive_of_isClosed M (ClosedForms.ClosedFormSection.toForm Model M s)
    (ClosedForms.ClosedFormSection.isClosed Model M s) x

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold
