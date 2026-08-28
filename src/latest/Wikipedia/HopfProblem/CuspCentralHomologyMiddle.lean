import Wikipedia.HopfProblem.CuspCentralHomologyMiddleAdmissible
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesRadius

/-!
# The actual central cusp has middle homology `ℤ⁴` and `ℤ²`

These statements concern the literal central fibre at the original
positive ambient radius. An admissible smaller radius is derived from
the holomorphic coefficients, the actual Mayer–Vietoris calculation is
performed there, and the actual radius homeomorphism transports it back.
No attaching-map vanishing, model equivalence, or splitting is assumed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The literal central fibre has four integral degree-two classes. -/
def centralSingularH2Equiv :
    SingularHomology (QuotientCentralFibre C r) 2 ≃ₗ[ℤ] (Fin 4 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs : 0 < δ ∧ δ < r ∧ δ < 1 ∧ SmallDrift C δ ∧
      ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact (homeomorphHomologyEquiv
    (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 2).trans
      (centralSingularH2Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

/-- The literal central fibre has two integral degree-three classes. -/
def centralSingularH3Equiv :
    SingularHomology (QuotientCentralFibre C r) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs : 0 < δ ∧ δ < r ∧ δ < 1 ∧ SmallDrift C δ ∧
      ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact (homeomorphHomologyEquiv
    (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 3).trans
      (centralSingularH3Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

include hr hC

theorem centralSingularH2_free :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) 2) :=
  Module.Free.of_equiv (centralSingularH2Equiv C r hr hC).symm

theorem centralSingularH3_free :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) 3) :=
  Module.Free.of_equiv (centralSingularH3Equiv C r hr hC).symm

theorem centralSingularH2_finite :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) 2) :=
  Module.Finite.of_surjective (centralSingularH2Equiv C r hr hC).symm.toLinearMap
    (centralSingularH2Equiv C r hr hC).symm.surjective

theorem centralSingularH3_finite :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) 3) :=
  Module.Finite.of_surjective (centralSingularH3Equiv C r hr hC).symm.toLinearMap
    (centralSingularH3Equiv C r hr hC).symm.surjective

theorem centralSingularH2_finrank :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) 2) = 4 := by
  rw [(centralSingularH2Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem centralSingularH3_finrank :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) 3) = 2 := by
  rw [(centralSingularH3Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem centralSingularH2_torsionFree :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) 2) := by
  let := centralSingularH2_free C r hr hC
  infer_instance

theorem centralSingularH3_torsionFree :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) 3) := by
  let := centralSingularH3_free C r hr hC
  infer_instance

end Wikipedia.HopfProblem.CuspCentralHomology
