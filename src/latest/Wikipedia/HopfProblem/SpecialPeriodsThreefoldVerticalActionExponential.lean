import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionExponentialLocal
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# The genuine complex parameter group `ℂ / ℤ ≃ ℂˣ`

The normalized exponential identifies the ordinary additive quotient
topology with the topology on the nonzero complex numbers. Integer
translations act freely and holomorphically on the complex plane, and
their actual quotient projection is a covering map. Local lifts through
this projection construct the quotient complex atlas. The exponential
then gives a biholomorphism to the existing open-submanifold atlas on
`ℂˣ`, compatible with the group equivalence from the core file.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Exponential

/-- The actual additive integer translations of the complex parameter. -/
@[instance_reducible] def integerTranslationAction : MulAction (Multiplicative ℤ) ℂ where
  smul g s := s + (g.toAdd : ℂ)
  one_smul s := by
    change s + ((0 : ℤ) : ℂ) = s
    simp only [Int.cast_zero, add_zero]
  mul_smul g h s := by
    change s + ((g.toAdd + h.toAdd : ℤ) : ℂ) =
      (s + (h.toAdd : ℂ)) + (g.toAdd : ℂ)
    push_cast
    abel

@[simp] theorem integerTranslation_smul (g : Multiplicative ℤ) (s : ℂ) :
    letI := integerTranslationAction
    g • s = s + (g.toAdd : ℂ) := rfl

theorem integerTranslation_holomorphic :
    letI := integerTranslationAction
    ∀ g : Multiplicative ℤ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun s : ℂ => g • s) := by
  let := integerTranslationAction
  intro g
  exact contMDiff_id.add contMDiff_const

theorem integerTranslation_continuousConstSMul :
    letI := integerTranslationAction
    ContinuousConstSMul (Multiplicative ℤ) ℂ := by
  let := integerTranslationAction
  exact ⟨fun g => (integerTranslation_holomorphic g).continuous⟩

theorem integerTranslation_free :
    letI := integerTranslationAction
    IsCancelSMul (Multiplicative ℤ) ℂ := by
  let := integerTranslationAction
  constructor
  intro g h s he
  apply Multiplicative.toAdd.injective
  have hc : (g.toAdd : ℂ) = (h.toAdd : ℂ) := add_left_cancel he
  exact_mod_cast hc

theorem normalizedExponential_eq_iff_orbit (s t : ℂ) :
    letI := integerTranslationAction
    normalizedExponential s = normalizedExponential t ↔
      s ∈ MulAction.orbit (Multiplicative ℤ) t := by
  let := integerTranslationAction
  constructor
  · intro he
    obtain ⟨n, hn⟩ := (normalizedExponential_eq_iff s t).mp he
    exact ⟨Multiplicative.ofAdd n, hn.symm⟩
  · rintro ⟨g, rfl⟩
    change normalizedExponential (t + (g.toAdd : ℂ)) = normalizedExponential t
    rw [normalizedExponential_add, normalizedExponential_int, mul_one]

/-- The literal normalized exponential is the quotient covering by the
free integer-translation action. -/
theorem normalizedExponential_covering :
    letI := integerTranslationAction
    IsQuotientCoveringMap normalizedExponential (Multiplicative ℤ) := by
  let := integerTranslationAction
  let := integerTranslation_continuousConstSMul
  let := integerTranslation_free
  exact quotientCoveringMap_of_localHomeomorph
    normalizedExponential_isLocalDiffeomorph.isLocalHomeomorph
    normalizedExponential_surjective normalizedExponential_eq_iff_orbit

theorem parameterExponential_continuous : Continuous parameterExponential := by
  apply parameterProjection_isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, parameterExponential_projection] using
    normalizedExponential_continuous

theorem parameterExponential_isOpenMap : IsOpenMap parameterExponential := by
  apply IsOpenMap.of_comp parameterProjection_continuous parameterProjection_surjective
  simpa only [Function.comp_def, parameterExponential_projection] using
    normalizedExponential_isOpenMap

/-- The underlying bijection of the actual exponential on `ℂ / ℤ`. -/
def parameterEquiv : Parameter ≃ ℂˣ :=
  Equiv.ofBijective parameterExponential parameterExponential_bijective

/-- The quotient topology, not a topology transported along a bijection,
makes the normalized exponential a homeomorphism. -/
def parameterHomeomorph : Parameter ≃ₜ ℂˣ :=
  parameterEquiv.toHomeomorphOfContinuousOpen parameterExponential_continuous
    parameterExponential_isOpenMap

@[simp] theorem parameterHomeomorph_projection (s : ℂ) :
    parameterHomeomorph (parameterProjection s) = normalizedExponential s := rfl

@[simp] theorem parameterHomeomorph_eq_mulEquiv (p : Parameter) :
    parameterHomeomorph p = parameterMulEquiv (Multiplicative.ofAdd p) := rfl

@[simp] theorem parameterHomeomorph_symm_exponential (s : ℂ) :
    parameterHomeomorph.symm (normalizedExponential s) = parameterProjection s := by
  simpa only [parameterHomeomorph_projection] using
    parameterHomeomorph.symm_apply_apply (parameterProjection s)

/-- The ordinary group-quotient projection is itself the actual
integer-translation covering. -/
theorem parameterProjection_covering :
    letI := integerTranslationAction
    IsQuotientCoveringMap (parameterProjection : ℂ → Parameter) (Multiplicative ℤ) := by
  let := integerTranslationAction
  have h := normalizedExponential_covering.homeomorph_comp parameterHomeomorph.symm
  have he : parameterHomeomorph.symm ∘ normalizedExponential = parameterProjection :=
    funext parameterHomeomorph_symm_exponential
  rwa [he] at h

/-- The complex charts are actual local lifts of the quotient covering,
followed by the original complex-plane chart. -/
@[instance_reducible] def parameterChartedSpace : ChartedSpace ℂ Parameter :=
  letI := integerTranslationAction
  CoveringQuotient.chartedSpace (E := ℂ) parameterProjection_covering

theorem parameter_isManifold :
    letI := parameterChartedSpace
    IsManifold 𝓘(ℂ) ω Parameter := by
  let := integerTranslationAction
  exact CoveringQuotient.isManifold parameterProjection_covering ω
    integerTranslation_holomorphic

theorem parameterProjection_holomorphic :
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (parameterProjection : ℂ → Parameter) := by
  let := integerTranslationAction
  exact CoveringQuotient.contMDiff_project parameterProjection_covering ω
    integerTranslation_holomorphic

theorem parameterProjection_isLocalDiffeomorph :
    letI := parameterChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (parameterProjection : ℂ → Parameter) := by
  let := integerTranslationAction
  exact CoveringQuotient.project_isLocalDiffeomorph parameterProjection_covering
    integerTranslation_holomorphic

theorem parameterExponential_holomorphic :
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω parameterExponential := by
  let := integerTranslationAction
  let := parameterChartedSpace
  apply CoveringQuotient.contMDiff_of_comp parameterProjection_covering 𝓘(ℂ) ω
  simpa only [Function.comp_def, parameterExponential_projection] using
    normalizedExponential_holomorphic

theorem parameterHomeomorph_symm_holomorphic :
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω parameterHomeomorph.symm := by
  let := parameterChartedSpace
  apply contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
    normalizedExponential_isLocalDiffeomorph normalizedExponential_surjective
  have he : parameterHomeomorph.symm ∘ normalizedExponential = parameterProjection :=
    funext parameterHomeomorph_symm_exponential
  rw [he]
  exact parameterProjection_holomorphic

/-- The actual quotient covering atlas and the inherited units atlas
make normalized exponentiation a genuine biholomorphism. -/
def parameterBiholomorph :
    letI := parameterChartedSpace
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Parameter ℂˣ ω := by
  letI := parameterChartedSpace
  exact
    { toEquiv := parameterHomeomorph.toEquiv
      contMDiff_toFun := parameterExponential_holomorphic
      contMDiff_invFun := parameterHomeomorph_symm_holomorphic }

@[simp] theorem parameterBiholomorph_projection (s : ℂ) :
    letI := parameterChartedSpace
    parameterBiholomorph (parameterProjection s) = normalizedExponential s := rfl

@[simp] theorem parameterBiholomorph_eq_mulEquiv (p : Parameter) :
    letI := parameterChartedSpace
    parameterBiholomorph p = parameterMulEquiv (Multiplicative.ofAdd p) := rfl

@[simp] theorem parameterBiholomorph_symm_exponential (s : ℂ) :
    letI := parameterChartedSpace
    parameterBiholomorph.symm (normalizedExponential s) = parameterProjection s :=
  parameterHomeomorph_symm_exponential s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Exponential
