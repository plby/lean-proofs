import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Real and complex calculus in the native period-torus charts

The charted space is the original `DiscreteQuotient.chartedSpace`. Restricting
the scalar field of its translation transitions gives a real smooth manifold
without changing any chart. A map out of this torus can be tested locally by
its literal lift along the quotient projection.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

local notation "IC₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂

/-- All original complex translation transitions are real differentiable to
the same order. This does not introduce a new charted-space structure. -/
theorem realManifold_of_order (p : PeriodDomain) (n : ℕ∞ω) :
    IsManifold IR₂ n p.Torus := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have h := contDiffOn_of_sub_mem_discrete p.lattice
    ((DiscreteQuotient.chart p.lattice x).symm.trans
      (DiscreteQuotient.chart p.lattice y)).continuousOn
    (DiscreteQuotient.transition_sub_mem p.lattice x y) n
  simpa using h.restrict_scalars ℝ

/-- The underlying real smooth manifold of the unchanged period torus. -/
instance realManifold (p : PeriodDomain) : IsManifold IR₂ ∞ p.Torus :=
  realManifold_of_order p ∞

/-- The actual quotient projection is real differentiable to every order. -/
theorem mkQ_contMDiff_real_of_order (p : PeriodDomain) (n : ℕ∞ω) :
    ContMDiff IR₂ IR₂ n (p.lattice.mkQ : ComplexPlane₂ → p.Torus) := by
  let := realManifold_of_order p n
  have h := contMDiff_iff.mp (DiscreteQuotient.contMDiff_mkQ p.lattice n)
  apply contMDiff_iff.mpr
  exact ⟨h.1, fun x y => (h.2 x y).restrict_scalars ℝ⟩

/-- The actual quotient projection is a smooth map of real manifolds. -/
theorem mkQ_contMDiff_real (p : PeriodDomain) :
    ContMDiff IR₂ IR₂ ∞ (p.lattice.mkQ : ComplexPlane₂ → p.Torus) :=
  mkQ_contMDiff_real_of_order p ∞

/-- The domain of the original preferred chart, as an open of the torus. -/
def chartSource (p : PeriodDomain) (x : p.Torus) : Opens p.Torus :=
  ⟨(DiscreteQuotient.chart p.lattice x).source,
    (DiscreteQuotient.chart p.lattice x).open_source⟩

/-- The range of the original preferred chart, as an open of the cover. -/
def chartTarget (p : PeriodDomain) (x : p.Torus) : Opens ComplexPlane₂ :=
  ⟨(DiscreteQuotient.chart p.lattice x).target,
    (DiscreteQuotient.chart p.lattice x).open_target⟩

@[simp] theorem mem_chartSource (p : PeriodDomain) (x : p.Torus) :
    x ∈ chartSource p x :=
  ChartedSpace.mem_chart_source (H := ComplexPlane₂) x

@[simp] theorem chart_mem_chartTarget (p : PeriodDomain) (x : p.Torus) :
    DiscreteQuotient.chart p.lattice x x ∈ chartTarget p x :=
  (DiscreteQuotient.chart p.lattice x).map_source (mem_chartSource p x)

/-- Testing a real derivative in the actual native chart is exactly testing
the derivative of the literal lift to the covering vector space. -/
theorem contMDiffAt_real_iff_lift (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : p.Torus → F} :
    ContMDiffAt IR₂ (modelWithCornersSelf ℝ F) n f x ↔
      ContDiffAt ℝ n (f ∘ p.lattice.mkQ) (DiscreteQuotient.chart p.lattice x x) := by
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have hchart : chartAt ComplexPlane₂ x = DiscreteQuotient.chart p.lattice x := rfl
  simp [extChartAt, OpenPartialHomeomorph.extend, hchart, DiscreteQuotient.chart_symm,
    contDiffWithinAt_univ]

/-- A real-smooth lift at the preferred representative gives the native
real-smooth map at the original torus point. No periodicity premise is needed. -/
theorem contMDiffAt_real_of_lift (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : p.Torus → F}
    (hf : ContDiffAt ℝ n (f ∘ p.lattice.mkQ) (DiscreteQuotient.chart p.lattice x x)) :
    ContMDiffAt IR₂ (modelWithCornersSelf ℝ F) n f x :=
  (contMDiffAt_real_iff_lift p x n).mpr hf

/-- A globally smooth literal lift gives a smooth map on the original torus. -/
theorem contMDiff_real_of_lift (p : PeriodDomain) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : p.Torus → F}
    (hf : ContDiff ℝ n (f ∘ p.lattice.mkQ)) :
    ContMDiff IR₂ (modelWithCornersSelf ℝ F) n f :=
  fun x => contMDiffAt_real_of_lift p x n hf.contDiffAt

/-- The same native chart test for complex differentiability. -/
theorem contMDiffAt_complex_iff_lift (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : p.Torus → F} :
    ContMDiffAt IC₂ (modelWithCornersSelf ℂ F) n f x ↔
      ContDiffAt ℂ n (f ∘ p.lattice.mkQ) (DiscreteQuotient.chart p.lattice x x) := by
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have hchart : chartAt ComplexPlane₂ x = DiscreteQuotient.chart p.lattice x := rfl
  simp [extChartAt, OpenPartialHomeomorph.extend, hchart, DiscreteQuotient.chart_symm,
    contDiffWithinAt_univ]

/-- A holomorphic lift at the preferred representative descends at the point. -/
theorem contMDiffAt_complex_of_lift (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : p.Torus → F}
    (hf : ContDiffAt ℂ n (f ∘ p.lattice.mkQ) (DiscreteQuotient.chart p.lattice x x)) :
    ContMDiffAt IC₂ (modelWithCornersSelf ℂ F) n f x :=
  (contMDiffAt_complex_iff_lift p x n).mpr hf

/-- Each original torus chart is real smooth on its actual domain. -/
theorem chart_contMDiffOn_real (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω) :
    ContMDiffOn IR₂ IR₂ n (DiscreteQuotient.chart p.lattice x) (chartSource p x) := by
  let := realManifold_of_order p n
  exact contMDiffOn_chart (I := IR₂) (n := n) (x := x)

/-- Each original torus chart is complex analytic on its actual domain. -/
theorem chart_contMDiffOn_complex (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω) :
    ContMDiffOn IC₂ IC₂ n (DiscreteQuotient.chart p.lattice x) (chartSource p x) :=
  contMDiffOn_chart (I := IC₂) (n := n) (x := x)

/-- Pointwise complex differentiability implies real differentiability using
the same native chart on both sides. -/
theorem contMDiffAt_real_of_complex (p : PeriodDomain) (x : p.Torus) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {f : p.Torus → F}
    (hf : ContMDiffAt IC₂ (modelWithCornersSelf ℂ F) n f x) :
    ContMDiffAt IR₂ (modelWithCornersSelf ℝ F) n f x :=
  (contMDiffAt_real_iff_lift p x n).mpr
    (((contMDiffAt_complex_iff_lift p x n).mp hf).restrict_scalars ℝ)

/-- A complex differentiable map out of the native torus is real differentiable
to the same order, with its original domain atlas unchanged. -/
theorem contMDiff_real_of_complex (p : PeriodDomain) (n : ℕ∞ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {f : p.Torus → F}
    (hf : ContMDiff IC₂ (modelWithCornersSelf ℂ F) n f) :
    ContMDiff IR₂ (modelWithCornersSelf ℝ F) n f :=
  fun x => contMDiffAt_real_of_complex p x n (hf x)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
