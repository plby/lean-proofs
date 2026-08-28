import Wikipedia.HopfProblem.HolomorphicCousinWirtinger

/-!
# The global forcing term of a smooth additive cochain

Local smooth representatives with holomorphic differences have a common
antiholomorphic derivative.  We construct this global function, prove its
smoothness, and prove compact support whenever the local representatives are
holomorphic near infinity.  Thus no triviality on a whole affine chart is
assumed when passing from local torsor data to the Cauchy--Green equation.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- Smooth local representatives whose pairwise differences are holomorphic.
The representatives need not themselves be holomorphic. -/
structure LocalPotential (ι : Type*) where
  domain : ι → Set ℂ
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ z : ℂ, ∃ i, z ∈ domain i
  potential : ι → ℂ → ℂ
  smooth : ∀ i, ContDiffOn ℝ ∞ (potential i) (domain i)
  analytic_difference : ∀ i j,
    AnalyticOnNhd ℂ (fun z => potential i z - potential j z) (domain i ∩ domain j)

namespace LocalPotential

variable {ι : Type*} (P : LocalPotential ι)

/-- Select a local representative at the given point.  The resulting forcing
term is proved independent of this choice. -/
def indexAt (z : ℂ) : ι := (P.cover z).choose

theorem mem_domain_indexAt (z : ℂ) : z ∈ P.domain (P.indexAt z) :=
  (P.cover z).choose_spec

theorem smoothAt {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    ContDiffAt ℝ ∞ (P.potential i) z :=
  (P.smooth i z hz).contDiffAt ((P.isOpen_domain i).mem_nhds hz)

/-- The globally defined coefficient of the antiholomorphic differential. -/
def forcing (z : ℂ) : ℂ := dbar (P.potential (P.indexAt z)) z

/-- Each local representative computes exactly the same forcing term. -/
theorem forcing_eq {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing z = dbar (P.potential i) z := by
  exact dbar_eq_of_sub_differentiableAt
    ((P.smoothAt (P.mem_domain_indexAt z)).differentiableAt (by simp))
    ((P.smoothAt hz).differentiableAt (by simp))
    (P.analytic_difference (P.indexAt z) i z ⟨P.mem_domain_indexAt z, hz⟩).differentiableAt

theorem forcing_eventuallyEq {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing =ᶠ[𝓝 z] dbar (P.potential i) := by
  filter_upwards [(P.isOpen_domain i).mem_nhds hz] with w hw
  exact P.forcing_eq hw

theorem forcing_contDiff : ContDiff ℝ ∞ P.forcing := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (contDiffAt_dbar (P.smoothAt (P.mem_domain_indexAt z))).congr_of_eventuallyEq
    (P.forcing_eventuallyEq (P.mem_domain_indexAt z))

/-- A holomorphic local representative makes the forcing term vanish. -/
theorem forcing_eq_zero {i : ι} {z : ℂ} (hz : z ∈ P.domain i)
    (hs : DifferentiableAt ℂ (P.potential i) z) : P.forcing z = 0 := by
  rw [P.forcing_eq hz]
  exact dbar_eq_zero_of_differentiableAt hs

/-- Holomorphic local representatives outside a bounded set give an actual
compactly supported global forcing term. -/
theorem forcing_hasCompactSupport {R : ℝ}
    (hR : ∀ z : ℂ, R < ‖z‖ →
      ∃ i, z ∈ P.domain i ∧ DifferentiableAt ℂ (P.potential i) z) :
    HasCompactSupport P.forcing := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
  intro z hz
  by_contra hzn
  have hzR : R < ‖z‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hzn
  obtain ⟨i, hi, hs⟩ := hR z hzR
  exact hz (P.forcing_eq_zero hi hs)

/-- Subtracting a common global correction does not change the original
additive transition functions. -/
theorem corrected_difference (u : ℂ → ℂ) (i j : ι) (z : ℂ) :
    (P.potential i z - u z) - (P.potential j z - u z) =
      P.potential i z - P.potential j z := by ring

/-- A solution of the constructed global `∂̄` equation corrects every local
representative to a genuine holomorphic function. -/
theorem corrected_analytic {u : ℂ → ℂ} (hu : Differentiable ℝ u)
    (hsolve : ∀ z, dbar u z = P.forcing z) (i : ι) :
    AnalyticOnNhd ℂ (fun z => P.potential i z - u z) (P.domain i) := by
  apply analyticOnNhd_of_dbar_eq_zero (P.isOpen_domain i)
  · exact ((P.smooth i).differentiableOn (by simp)).sub hu.differentiableOn
  · intro z hz
    rw [dbar_sub ((P.smoothAt hz).differentiableAt (by simp)) (hu z), hsolve,
      P.forcing_eq hz, sub_self]

end LocalPotential

end Wikipedia.HopfProblem.HolomorphicCousin
