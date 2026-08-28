import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The two actual affine coordinates of a sphere open cover

Open subsets of the constructed Riemann sphere pull back to genuine
open subsets of the finite and reciprocal complex planes. An actual
open neighbourhood of infinity contains the complement of a sufficiently
large ball in the finite coordinate. These are the geometric cover
inputs for applying the proved holomorphic Cousin solver to the function
sheaf; no cohomological vanishing is assumed here.
-/

noncomputable section

open Set TopologicalSpace Metric
open scoped OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- Pullback of an actual sphere open set in the finite affine chart. -/
def finiteOpen (U : Opens RiemannSphere) : Opens ℂ :=
  ⟨((↑) : ℂ → RiemannSphere) ⁻¹' (U : Set RiemannSphere),
    U.isOpen.preimage OnePoint.continuous_coe⟩

/-- Pullback in the actual reciprocal chart, whose origin is infinity. -/
def infinityOpen (U : Opens RiemannSphere) : Opens ℂ :=
  ⟨RiemannSphere.infinityParametrization ⁻¹' (U : Set RiemannSphere),
    U.isOpen.preimage RiemannSphere.infinityParametrization_continuous⟩

@[simp] theorem mem_finiteOpen (U : Opens RiemannSphere) (z : ℂ) :
    z ∈ finiteOpen U ↔ (z : RiemannSphere) ∈ U := Iff.rfl

@[simp] theorem mem_infinityOpen (U : Opens RiemannSphere) (z : ℂ) :
    z ∈ infinityOpen U ↔ RiemannSphere.infinityParametrization z ∈ U := Iff.rfl

@[simp] theorem finiteOpen_inf (U V : Opens RiemannSphere) :
    finiteOpen (U ⊓ V) = finiteOpen U ⊓ finiteOpen V := rfl

@[simp] theorem infinityOpen_inf (U V : Opens RiemannSphere) :
    infinityOpen (U ⊓ V) = infinityOpen U ⊓ infinityOpen V := rfl

/-- Any sphere cover is a cover after pullback to the finite plane. -/
theorem finiteOpen_cover {ι : Type*} (U : ι → Opens RiemannSphere)
    (hU : ∀ p : RiemannSphere, ∃ i, p ∈ U i) :
    ∀ z : ℂ, ∃ i, z ∈ finiteOpen (U i) :=
  fun z => hU (z : RiemannSphere)

/-- The distinguished patch required by the Cousin theorem is provided
by any actual member of the cover which contains infinity. -/
theorem exists_positive_tail_radius (U : Opens RiemannSphere)
    (hU : (∞ : RiemannSphere) ∈ U) :
    ∃ R : ℝ, 0 < R ∧ (ball (0 : ℂ) R)ᶜ ⊆ finiteOpen U := by
  have hc : IsCompact (finiteOpen U : Set ℂ)ᶜ :=
    ((OnePoint.isOpen_iff_of_mem' hU).mp U.isOpen).1
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, ?_⟩
  intro z hz
  by_contra hn
  exact hz (hbound hn)

/-- A neighbourhood of infinity contains an actual reciprocal-coordinate
disc, with a positive radius. -/
theorem exists_positive_infinity_radius (U : Opens RiemannSphere)
    (hU : (∞ : RiemannSphere) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : ℂ) r ⊆ infinityOpen U := by
  have hzero : (0 : ℂ) ∈ infinityOpen U := by
    simpa only [mem_infinityOpen, RiemannSphere.infinityParametrization_zero] using hU
  exact Metric.mem_nhds_iff.mp ((infinityOpen U).isOpen.mem_nhds hzero)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
