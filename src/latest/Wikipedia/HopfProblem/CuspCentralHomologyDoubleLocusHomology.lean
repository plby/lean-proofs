import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusHomeomorph

/-!
# Integral singular homology of the actual central double locus

The explicit geometric homeomorphism to the suspension of three circles
transports the already proved singular-homology calculation to the literal
central boundary in the original cusp quotient.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

/-- Actual integral homology in every degree, transported by the constructed map. -/
def centralBoundaryHomologyEquiv (n : ℕ) :
    SingularHomology (centralBoundary C ε hε) n ≃ₗ[ℤ]
      (Fin (threeCircleSuspensionBetti n) → ℤ) :=
  (homeomorphHomologyEquiv (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) n).trans
    (threeCircleSuspensionHomologyEquiv n)

def centralBoundaryHomologyZeroEquiv :
    SingularHomology (centralBoundary C ε hε) 0 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) 0).trans
    threeCircleSuspensionHomologyZeroEquiv

def centralBoundaryHomologyOneEquiv :
    SingularHomology (centralBoundary C ε hε) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (homeomorphHomologyEquiv (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) 1).trans
    threeCircleSuspensionHomologyOneEquiv

def centralBoundaryHomologyTwoEquiv :
    SingularHomology (centralBoundary C ε hε) 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (homeomorphHomologyEquiv (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) 2).trans
    threeCircleSuspensionHomologyTwoEquiv

theorem centralBoundary_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (centralBoundary C ε hε) (n + 3)) := by
  let := threeCircleSuspension_homology_subsingleton n
  exact (homeomorphHomologyEquiv
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) (n + 3)).injective.subsingleton

theorem centralBoundary_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (centralBoundary C ε hε) n) :=
  Module.Free.of_equiv (centralBoundaryHomologyEquiv C ε hε hε1 hC hR n).symm

theorem centralBoundary_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology (centralBoundary C ε hε) n) :=
  Module.Finite.of_surjective (centralBoundaryHomologyEquiv C ε hε hε1 hC hR n).symm.toLinearMap
    (centralBoundaryHomologyEquiv C ε hε hε1 hC hR n).symm.surjective

theorem centralBoundary_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (centralBoundary C ε hε) n) =
      threeCircleSuspensionBetti n := by
  rw [(centralBoundaryHomologyEquiv C ε hε hε1 hC hR n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem centralBoundary_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (centralBoundary C ε hε) n) := by
  let := centralBoundary_homology_free C ε hε hε1 hC hR n
  infer_instance

theorem centralBoundary_homology :
    Nonempty (SingularHomology (centralBoundary C ε hε) 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology (centralBoundary C ε hε) 1 ≃ₗ[ℤ] (Fin 2 → ℤ)) ∧
      Nonempty (SingularHomology (centralBoundary C ε hε) 2 ≃ₗ[ℤ] (Fin 3 → ℤ)) ∧
      ∀ n, Subsingleton (SingularHomology (centralBoundary C ε hε) (n + 3)) :=
  ⟨⟨centralBoundaryHomologyZeroEquiv C ε hε hε1 hC hR⟩,
    ⟨centralBoundaryHomologyOneEquiv C ε hε hε1 hC hR⟩,
    ⟨centralBoundaryHomologyTwoEquiv C ε hε hε1 hC hR⟩,
    centralBoundary_homology_subsingleton C ε hε hε1 hC hR⟩

end Wikipedia.HopfProblem.CuspCentralHomology
