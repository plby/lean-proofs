import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnectionCovariant

/-!
# Constructed smooth connection coefficients for arbitrary torus line bundles

For an arbitrary native holomorphic complex line bundle on an actual period
torus, the native universal-cover pullback has an actual convex trivializing
cover. A subordinate smooth partition is constructed from that cover and its
logarithmic scalar derivatives give real-smooth connection coefficients.
Their change-of-coordinate law, and the covariance of `ds + Aᵢ s`, are proved.

This does not assume or assert a global frame of the pullback. Smooth parallel
transport and the subsequent holomorphic correction remain further tasks.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection

open PeriodTorusLineBundleClassificationTopological

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- The actual constructed connection coefficient on a ball of the native
universal-cover pullback, not an assumed connection. -/
def pullbackConnectionForm (i x : ComplexPlane₂) : ComplexPlane₂ →L[ℝ] ℂ :=
  connectionForm (pullbackBallData p V) i x

theorem pullbackConnectionForm_contDiffOn (i : ComplexPlane₂) :
    ContDiffOn ℝ ∞ (pullbackConnectionForm p V i) ((pullbackBallData p V).baseSet i) :=
  connectionForm_contDiffOn (pullbackBallData p V) i

theorem pullbackConnectionForm_change (i j : ComplexPlane₂) {x : ComplexPlane₂}
    (hi : x ∈ (pullbackBallData p V).baseSet i)
    (hj : x ∈ (pullbackBallData p V).baseSet j) :
    pullbackConnectionForm p V j x = pullbackConnectionForm p V i x -
      ((pullbackBallData p V).transition i j x : ℂ)⁻¹ •
        fderiv ℝ (fun y => ((pullbackBallData p V).transition i j y : ℂ)) x :=
  connectionForm_change (pullbackBallData p V) i j hi hj

/-- For every arbitrary native holomorphic line bundle, there really exist
smooth local real one-forms with the connection transformation law for its
actual pullback transitions. -/
theorem exists_pullback_connection_forms :
    ∃ C : ComplexPlane₂ → ComplexPlane₂ → (ComplexPlane₂ →L[ℝ] ℂ),
      (∀ i, ContDiffOn ℝ ∞ (C i) ((pullbackBallData p V).baseSet i)) ∧
      ∀ i j x, x ∈ (pullbackBallData p V).baseSet i ∩ (pullbackBallData p V).baseSet j →
        C j x = C i x - ((pullbackBallData p V).transition i j x : ℂ)⁻¹ •
          fderiv ℝ (fun y => ((pullbackBallData p V).transition i j y : ℂ)) x :=
  ⟨pullbackConnectionForm p V, pullbackConnectionForm_contDiffOn p V,
    fun i j _ hx => pullbackConnectionForm_change p V i j hx.1 hx.2⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
