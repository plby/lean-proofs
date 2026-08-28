import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat

/-!
# Holomorphic native Jacobians with point-independent preferred charts

The given complex atlases are retained throughout. When their preferred
charts are independent of the point, the actual tangent coordinate changes
are identities. The general holomorphic derivative theorem therefore gives
holomorphic variation of the literal native manifold derivative, viewed as
a continuous linear map on the original model. Evaluating that derivative
at one gives the genuine scalar Jacobian.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.FlatDerivative

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

/-- The actual manifold derivative in the original preferred model coordinates. -/
def nativeDerivative (f : M → N) (x : M) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ) 𝓘(ℂ) f x

@[simp] theorem nativeDerivative_apply (f : M → N) (x : M) (v : ℂ) :
    nativeDerivative f x v = mfderiv 𝓘(ℂ) 𝓘(ℂ) f x v := rfl

variable [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N]

/-- Actual tangent-coordinate changes disappear when the supplied preferred
charts are independent of the point. This holds for every field of linear maps. -/
theorem inTangentCoordinates_eq_of_constant_charts
    (hM : ∀ x y : M, chartAt ℂ x = chartAt ℂ y)
    (hN : ∀ x y : N, chartAt ℂ x = chartAt ℂ y)
    (f : M → N) (A : M → ℂ →L[ℂ] ℂ) (x₀ x : M) :
    inTangentCoordinates 𝓘(ℂ) 𝓘(ℂ) id f A x₀ x = A x := by
  have hx : x ∈ (chartAt ℂ x₀).source := by
    rw [hM x₀ x]
    exact mem_chart_source ℂ x
  have hy : f x ∈ (chartAt ℂ (f x₀)).source := by
    rw [hN (f x₀) (f x)]
    exact mem_chart_source ℂ (f x)
  have haM : achart ℂ x₀ = achart ℂ x := Subtype.ext (hM x₀ x)
  have haN : achart ℂ (f x₀) = achart ℂ (f x) := Subtype.ext (hN (f x₀) (f x))
  rw [inTangentCoordinates_eq id f A hx hy]
  simp only [id_eq]
  rw [haM, haN]
  apply ContinuousLinearMap.ext
  intro v
  change (tangentBundleCore 𝓘(ℂ) N).coordChange (achart ℂ (f x)) (achart ℂ (f x)) (f x)
    (A x ((tangentBundleCore 𝓘(ℂ) M).coordChange (achart ℂ x) (achart ℂ x) x v)) = A x v
  rw [(tangentBundleCore 𝓘(ℂ) M).coordChange_self
    (achart ℂ x) x (mem_chart_source ℂ x) v]
  exact (tangentBundleCore 𝓘(ℂ) N).coordChange_self
    (achart ℂ (f x)) (f x) (mem_chart_source ℂ (f x)) (A x v)

/-- In particular, the literal native derivative equals its tangent-coordinate
expression around every chosen center. -/
theorem inTangentCoordinates_nativeDerivative
    (hM : ∀ x y : M, chartAt ℂ x = chartAt ℂ y)
    (hN : ∀ x y : N, chartAt ℂ x = chartAt ℂ y)
    (f : M → N) (x₀ x : M) :
    inTangentCoordinates 𝓘(ℂ) 𝓘(ℂ) id f (nativeDerivative f) x₀ x =
      nativeDerivative f x :=
  inTangentCoordinates_eq_of_constant_charts hM hN f (nativeDerivative f) x₀ x

/-- The actual native continuous-linear derivative of a holomorphic map
varies holomorphically in the same point-independent complex atlases. -/
theorem nativeDerivative_holomorphic_of_constant_charts
    (hM : ∀ x y : M, chartAt ℂ x = chartAt ℂ y)
    (hN : ∀ x y : N, chartAt ℂ x = chartAt ℂ y)
    (f : M → N) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω (nativeDerivative f) := by
  intro x₀
  have hd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (inTangentCoordinates 𝓘(ℂ) 𝓘(ℂ) id f (nativeDerivative f) x₀) x₀ :=
    (hf x₀).mfderiv_const (m := ω) (by simp)
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x =>
    (inTangentCoordinates_nativeDerivative hM hN f x₀ x).symm

/-- Evaluation on any fixed original model vector is holomorphic. -/
theorem mfderiv_apply_holomorphic_of_constant_charts
    (hM : ∀ x y : M, chartAt ℂ x = chartAt ℂ y)
    (hN : ∀ x y : N, chartAt ℂ x = chartAt ℂ y)
    (f : M → N) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (v : ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : M => (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x v : ℂ)) :=
  (nativeDerivative_holomorphic_of_constant_charts hM hN f hf).clm_apply contMDiff_const

/-- The actual scalar native Jacobian is holomorphic, with no substituted atlas. -/
theorem mfderiv_apply_one_holomorphic_of_constant_charts
    (hM : ∀ x y : M, chartAt ℂ x = chartAt ℂ y)
    (hN : ∀ x y : N, chartAt ℂ x = chartAt ℂ y)
    (f : M → N) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : M => (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x (1 : ℂ) : ℂ)) :=
  mfderiv_apply_holomorphic_of_constant_charts hM hN f hf 1

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.FlatDerivative
