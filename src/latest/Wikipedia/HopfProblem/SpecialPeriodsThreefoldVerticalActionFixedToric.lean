import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricScaling
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricLocus

/-!
# The fixed locus of the actual vertical flow on the toric cusp space

The literal scaling in every affine toric chart shows that any nonidentity
vertical scalar fixes precisely its middle axis. The existing chart-independent
edge-direction locus identifies these axes with the curves of direction `e₂`.
Surjectivity of the actual normalized exponential gives the same description
for the points fixed by every time of the constructed additive flow.

These are statements on the actual upstairs toric space. Quotient descent,
global gluing, and the projective-line identification are not assumed here.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric

open ToricCharts ToricFan ToricFan.Triangle ToricSpace

/-- Every nonidentity vertical torus parameter fixes exactly the existing
edge-direction-one locus in the actual glued toric space. -/
theorem torusAction_vertical_fixed_iff (u : ℂˣ) (hu : u ≠ 1) (x : Space) :
    torusAction (fibreMultiplier ![1, u]) x = x ↔ x ∈ edgeDirectionLocus 1 := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_vertical_inclusion_fixed_iff u hu,
    inclusion_mem_edgeDirectionLocus_one_iff]

/-- The literal fixed-point set of any nonidentity vertical scalar. -/
theorem torusAction_vertical_fixed_set (u : ℂˣ) (hu : u ≠ 1) :
    {x : Space | torusAction (fibreMultiplier ![1, u]) x = x} =
      edgeDirectionLocus 1 := by
  ext x
  exact torusAction_vertical_fixed_iff u hu x

/-- Being fixed by all vertical multiplicative parameters is equivalent
to lying on the same geometric edge-direction locus. -/
theorem all_vertical_scalars_fixed_iff (x : Space) :
    (∀ u : ℂˣ, torusAction (fibreMultiplier ![1, u]) x = x) ↔
      x ∈ edgeDirectionLocus 1 := by
  constructor
  · intro hx
    let u : ℂˣ := Units.mk0 (2 : ℂ) (by norm_num)
    have hu : u ≠ 1 := by
      intro h
      have he := congrArg Units.val h
      change (2 : ℂ) = 1 at he
      norm_num at he
    exact (torusAction_vertical_fixed_iff u hu x).mp (hx u)
  · intro hx u
    obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
    exact torusAction_vertical_inclusion_fixed u a z
      ((inclusion_mem_edgeDirectionLocus_one_iff a z).mp hx)

/-- The actual exponential is surjective, so its additive flow and the
vertical multiplicative subgroup have identical common fixed points. -/
theorem toricFlow_fixed_iff_all_vertical_scalars (x : Space) :
    (∀ s : ℂ, Cusp.toricFlow s x = x) ↔
      ∀ u : ℂˣ, torusAction (fibreMultiplier ![1, u]) x = x := by
  constructor
  · intro hx u
    obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
    exact hx s
  · intro hx s
    exact hx (Exponential.normalizedExponential s)

/-- The fixed locus of the constructed additive flow on the actual
toric space is exactly the union of the curves of direction `e₂`. -/
theorem toricFlow_fixed_iff (x : Space) :
    (∀ s : ℂ, Cusp.toricFlow s x = x) ↔ x ∈ edgeDirectionLocus 1 := by
  rw [toricFlow_fixed_iff_all_vertical_scalars, all_vertical_scalars_fixed_iff]

/-- The common fixed-point condition in every native affine toric chart. -/
theorem toricFlow_fixed_inclusion_iff (a : Triangle) (z : CoordinateSpace 3) :
    (∀ s : ℂ, Cusp.toricFlow s (inclusion a z) = inclusion a z) ↔
      z 0 = 0 ∧ z 2 = 0 := by
  rw [toricFlow_fixed_iff, inclusion_mem_edgeDirectionLocus_one_iff]

/-- The actual global upstairs fixed set, stated as equality of subsets. -/
theorem toricFlow_fixed_set :
    {x : Space | ∀ s : ℂ, Cusp.toricFlow s x = x} = edgeDirectionLocus 1 := by
  ext x
  exact toricFlow_fixed_iff x

/-- No noncentral toric point is fixed by the whole vertical flow. -/
theorem toricFlow_fixed_time_eq_zero {x : Space}
    (hx : ∀ s : ℂ, Cusp.toricFlow s x = x) : time x = 0 :=
  time_eq_zero_of_mem_edgeDirectionLocus_one ((toricFlow_fixed_iff x).mp hx)

/-- Any nonintegral additive parameter already has the entire common
fixed locus on the upstairs toric model. -/
theorem toricFlow_noninteger_fixed_iff (s : ℂ)
    (hs : ¬ ∃ n : ℤ, s = (n : ℂ)) (x : Space) :
    Cusp.toricFlow s x = x ↔ x ∈ edgeDirectionLocus 1 := by
  have hu : Exponential.normalizedExponential s ≠ 1 :=
    fun h => hs ((Exponential.normalizedExponential_eq_one_iff s).mp h)
  exact torusAction_vertical_fixed_iff (Exponential.normalizedExponential s) hu x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric
