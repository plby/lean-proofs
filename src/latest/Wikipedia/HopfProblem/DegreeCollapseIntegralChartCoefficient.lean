import Wikipedia.HopfProblem.DegreeCollapseIntegralFundamentalClass
import Mathlib.Topology.LocallyConstant.Basic

/-!
# One integral comparison sign on a connected original chart

For any original absolute top class, its coordinate in a supplied actual
partial chart is locally constant. If the class is primitive at every
point, the coordinate is one or minus one. On a connected chart source
one fixed sign therefore applies at every point. No chart orientation
agreement or cap-duality premise is supplied.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralChartCoefficient

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology
open IntegralLocalNormalization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M]

/-- The actual integer coordinate of the original localization in the specified chart. -/
def coefficient (a : SingularHomology M (n + 2)) (e : OpenPartialHomeomorph M E)
    (x : e.source) : ℤ :=
  chartMark n e (x : M) x.property (fromAbsolute (ModuleCat.of ℤ ℤ) {(x : M)} (n + 2) a)

theorem localization_eq_coefficient_smul (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) (x : e.source) :
    fromAbsolute (ModuleCat.of ℤ ℤ) {(x : M)} (n + 2) a =
      coefficient n a e x • (chartMark n e (x : M) x.property).symm 1 := by
  apply (chartMark n e (x : M) x.property).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  change coefficient n a e x = coefficient n a e x • (1 : ℤ)
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

/-- The integer coordinate is locally constant in the supplied chart, not a newly chosen chart. -/
theorem coefficient_isLocallyConstant (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) : IsLocallyConstant (coefficient n a e) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨U, hU, hxU, hUs, k, hk⟩ :=
    exists_local_coefficient_in_chart n a e (x : M) x.property
  have he (y : e.source) (hy : (y : M) ∈ U) : coefficient n a e y = k := by
    have h := congrArg (chartMark n e (y : M) y.property) (hk (y : M) hy)
    rw [map_zsmul, LinearEquiv.apply_symm_apply] at h
    simpa only [coefficient, zsmul_eq_mul, Int.cast_id, mul_one] using h
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU, ?_⟩
  intro y hy
  exact (he y hy).trans (he x hxU).symm

theorem coefficient_eq (a : SingularHomology M (n + 2)) (e : OpenPartialHomeomorph M E)
    [PreconnectedSpace e.source] (x y : e.source) : coefficient n a e x = coefficient n a e y :=
  (coefficient_isLocallyConstant n a e).apply_eq_of_preconnectedSpace x y

/-- A primitive original localization has actual integer coordinate one or minus one. -/
theorem coefficient_eq_one_or_neg_one (a : SingularHomology M (n + 2))
    (ha : IntegralManifoldFundamentalClass.IsFundamental (n + 2) a)
    (e : OpenPartialHomeomorph M E) (x : e.source) :
    coefficient n a e x = 1 ∨ coefficient n a e x = -1 := by
  obtain ⟨k, hk⟩ := ha (x : M) ((chartMark n e (x : M) x.property).symm 1)
  have he := congrArg (chartMark n e (x : M) x.property) hk
  rw [map_zsmul, LinearEquiv.apply_symm_apply] at he
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := k)
  simpa only [coefficient, zsmul_eq_mul, Int.cast_id, mul_comm] using he

/-- One fixed integral sign compares the primitive class with the entire connected chart. -/
theorem exists_sign (a : SingularHomology M (n + 2))
    (ha : IntegralManifoldFundamentalClass.IsFundamental (n + 2) a)
    (e : OpenPartialHomeomorph M E) [PreconnectedSpace e.source] :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : e.source, coefficient n a e x = ε := by
  rcases isEmpty_or_nonempty e.source with h | h
  · exact ⟨1, Or.inl rfl, fun x => h.elim x⟩
  · let x : e.source := Classical.choice h
    exact ⟨coefficient n a e x, coefficient_eq_one_or_neg_one n a ha e x,
      fun y => coefficient_eq n a e y x⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralChartCoefficient
