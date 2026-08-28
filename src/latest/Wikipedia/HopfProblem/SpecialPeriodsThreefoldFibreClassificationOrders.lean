import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationGeometry

/-!
# Exact multiplicities at all points of the literal multiple fibres

The original elliptic projection charts apply at every point of the
literal global fibres at zero and one.  Their power equations give exact
orders three and four for the actual projection along a transverse line.
The hypotheses specify only membership of the already constructed fibre.
-/

noncomputable section

open Function Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

open Triangle EllipticGeometry

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM

attribute [local instance] Threefold.chartedSpace

/-- Every point of a literal elliptic fibre lies in its actual full
elliptic patch in the glued threefold. -/
theorem elliptic_fibre_mem_liftedPatch (j : Elliptic.Kind) (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = sphereValue j) :
    y ∈ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  have hbase : Threefold.projection y = puncturePoint (some j) :=
    triangleSphereUniformization.injective hy
  change Threefold.projection y ∈ specialBaseCover.fillingPatch (some j)
  rw [hbase]
  exact specialBaseCover.point_mem_fillingPatch (some j)

/-- The exact native power chart at every point of either entire
multiple fibre of the actual sphere projection. -/
theorem elliptic_fibre_power_chart (j : Elliptic.Kind) (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = sphereValue j) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      y ∈ e.source ∧ (e y).1 = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) ∧
      ∀ u ∈ e.target,
        sphereChart j (Threefold.projectionSphere (e.symm u)) = u.1 ^ j.order :=
  exists_central_projectionChart j y (elliptic_fibre_mem_liftedPatch j y hy)
    (by rw [hy, sphereChart_value])

private theorem transverse_order_of_power_chart (j : Elliptic.Kind)
    (y : Threefold.Space) (e : PartialDiffeomorph IF IF Threefold.Space FM ω)
    (hy : y ∈ e.source) (hzero : (e y).1 = 0)
    (hpower : ∀ u ∈ e.target,
      sphereChart j (Threefold.projectionSphere (e.symm u)) = u.1 ^ j.order) :
    analyticOrderAt (fun z : ℂ => sphereChart j
      (Threefold.projectionSphere (e.symm (z, (e y).2)))) 0 = (j.order : ℕ∞) := by
  have ht : (0, (e y).2) ∈ e.target := by
    have he : (0, (e y).2) = e y := Prod.ext hzero.symm rfl
    rw [he]
    exact e.map_source' hy
  have hc : ContinuousAt (fun z : ℂ => (z, (e y).2)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have he : (fun z : ℂ => sphereChart j
      (Threefold.projectionSphere (e.symm (z, (e y).2)))) =ᶠ[𝓝 0]
      (fun z : ℂ => z ^ j.order) := by
    filter_upwards [hc (e.open_target.mem_nhds ht)] with z hz
    exact hpower (z, (e y).2) hz
  rw [analyticOrderAt_congr he]
  change analyticOrderAt ((id : ℂ → ℂ) ^ j.order) 0 = (j.order : ℕ∞)
  rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- The actual global map has exact transverse order `j.order` at every
point of the literal multiple fibre, in an analytic chart of its native atlas. -/
theorem elliptic_fibre_projection_order (j : Elliptic.Kind) (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = sphereValue j) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      y ∈ e.source ∧ (e y).1 = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) ∧
      (∀ u ∈ e.target,
        sphereChart j (Threefold.projectionSphere (e.symm u)) = u.1 ^ j.order) ∧
      analyticOrderAt (fun z : ℂ => sphereChart j
        (Threefold.projectionSphere (e.symm (z, (e y).2)))) 0 = (j.order : ℕ∞) := by
  obtain ⟨e, hes, hezero, hsource, hpower⟩ := elliptic_fibre_power_chart j y hy
  exact ⟨e, hes, hezero, hsource, hpower,
    transverse_order_of_power_chart j y e hes hezero hpower⟩

/-- Every point over zero has the actual cubic projection equation
and exact transverse multiplicity three. -/
theorem zeroFibre_order_three (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere)) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      y ∈ e.source ∧ (e y).1 = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some (some Elliptic.Kind.three)) :
        Set Threefold.Space) ∧
      (∀ u ∈ e.target,
        sphereChart .three (Threefold.projectionSphere (e.symm u)) = u.1 ^ 3) ∧
      analyticOrderAt (fun z : ℂ => sphereChart .three
        (Threefold.projectionSphere (e.symm (z, (e y).2)))) 0 = 3 := by
  simpa [Elliptic.Kind.order] using elliptic_fibre_projection_order .three y
    (hy.trans sphereValue_three.symm)

/-- Every point over one has the actual quartic projection equation
and exact transverse multiplicity four. -/
theorem oneFibre_order_four (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere)) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      y ∈ e.source ∧ (e y).1 = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some (some Elliptic.Kind.four)) :
        Set Threefold.Space) ∧
      (∀ u ∈ e.target,
        sphereChart .four (Threefold.projectionSphere (e.symm u)) = u.1 ^ 4) ∧
      analyticOrderAt (fun z : ℂ => sphereChart .four
        (Threefold.projectionSphere (e.symm (z, (e y).2)))) 0 = 4 := by
  simpa [Elliptic.Kind.order] using elliptic_fibre_projection_order .four y
    (hy.trans sphereValue_four.symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification
