import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected

/-!
# Actual period parameters above every regular sphere value

The normalized biholomorphism of the compact triangle quotient identifies
its regular part with the complement of infinity, zero, and one.  The
actual regular triangle covering therefore supplies a period parameter
above every such sphere point.  The parameter is chosen from this proved
surjectivity, not included as additional data.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- Every unmarked sphere value has an actual regular upper-half-plane
representative for the original triangle action. -/
theorem exists_regularPoint_over (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere)) :
    ∃ z : TriangleRegularPoint,
      triangleSphereUniformization (triangleCompactifiedProjection z.val) = b := by
  let c := triangleSphereUniformization.symm b
  have hc : triangleSphereUniformization c = b :=
    triangleSphereUniformization.apply_symm_apply b
  have hreg : c ∈ regularPatch := by
    apply (mem_regularPatch c).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have he := congrArg triangleSphereUniformization h
      rw [hc, triangleSphereUniformization_cusp] at he
      exact h_inf he
    · intro h
      have he := congrArg triangleSphereUniformization h
      change triangleSphereUniformization c =
        triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterOne) at he
      rw [hc, triangleSphereUniformization_centerOne] at he
      exact h₀ he
    · intro h
      have he := congrArg triangleSphereUniformization h
      change triangleSphereUniformization c =
        triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterTwo) at he
      rw [hc, triangleSphereUniformization_centerTwo] at he
      exact h₁ he
  obtain ⟨z, hz⟩ := regularProjection_surjective ⟨c, hreg⟩
  have he : triangleCompactifiedProjection z.val = c :=
    congrArg (fun x : regularPatch => (x : TriangleCompactifiedOrbitSpace)) hz
  exact ⟨z, (congrArg triangleSphereUniformization he).trans hc⟩

/-- A genuine period parameter, selected from the proved actual
regular-covering surjectivity above an unmarked sphere value. -/
def regularPointOver (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere)) : TriangleRegularPoint :=
  (exists_regularPoint_over b h_inf h₀ h₁).choose

@[simp] theorem regularPointOver_value (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere)) :
    triangleSphereUniformization
      (triangleCompactifiedProjection (regularPointOver b h_inf h₀ h₁).val) = b :=
  (exists_regularPoint_over b h_inf h₀ h₁).choose_spec

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
