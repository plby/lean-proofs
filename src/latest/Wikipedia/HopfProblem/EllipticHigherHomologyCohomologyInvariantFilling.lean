import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantCokernel
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantIndices
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInjective

/-!
# Actual filling cohomology pullback into deck invariants

The genuine central-surface cohomology equivalence followed by the actual
central covering pullback gives the full-filling pullback into the same
deck-invariant cohomology of the original period torus.  Its underlying
value is the native pullback of the literal period-torus map into the
filling.  Surjectivity of the central equivalence gives equality of the
two actual image submodules and an identity-on-representatives cokernel
comparison, before any numerical index calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual full-filling pullback with codomain restricted to all deck invariants. -/
def periodTorusIntoFillingCohomologyToInvariants (n : ℕ) :
    SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n →ₗ[ℤ]
      periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) n :=
  (periodCoverCohomologyToInvariants j D.centralPeriod j.twist
    (mainTwist_admissible j) n).comp (centralSurfaceCohomologyEquiv D n).toLinearMap

/-- Forgetting the invariant subtype gives the original native cohomology pullback. -/
@[simp] theorem periodTorusIntoFillingCohomologyToInvariants_coe (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    (periodTorusIntoFillingCohomologyToInvariants D n a :
        SingularCohomology D.centralPeriod.val.Torus n) =
      singularCohomologyPullback
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n a :=
  centralSurfaceCohomologyEquiv_periodCover D n a

/-- Every actual filling pullback is fixed by every actual deck transformation. -/
theorem periodTorusIntoFilling_cohomology_deck_invariant (n : ℕ)
    (g : CyclicGroup j)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    singularCohomologyPullback
        (surfaceDeckMap j D.centralPeriod j.twist (mainTwist_admissible j) g) n
        (singularCohomologyPullback
          (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n a) =
      singularCohomologyPullback
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n a := by
  have h := (mem_periodCohomologyInvariants_iff j D.centralPeriod j.twist
    (mainTwist_admissible j) n
    (periodTorusIntoFillingCohomologyToInvariants D n a)).mp
      (periodTorusIntoFillingCohomologyToInvariants D n a).property g
  simpa only [periodTorusIntoFillingCohomologyToInvariants_coe] using h

theorem periodTorusIntoFillingCohomologyToInvariants_injective (n : ℕ) :
    Function.Injective (periodTorusIntoFillingCohomologyToInvariants D n) :=
  (periodCoverCohomologyToInvariants_injective j D.centralPeriod n).comp
    (centralSurfaceCohomologyEquiv D n).injective

/-- The restricted map preserves the actual evaluation/pushforward pairing. -/
theorem periodTorusIntoFillingCohomologyToInvariants_evaluate (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n)
    (b : SingularHomology D.centralPeriod.val.Torus n) :
    singularEvaluation D.centralPeriod.val.Torus n
        (periodTorusIntoFillingCohomologyToInvariants D n a) b =
      singularEvaluation (D.Space j.twist (mainTwist_admissible j)) n a
        (singularHomologyMap
          (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n b) := by
  rw [periodTorusIntoFillingCohomologyToInvariants_coe, singularEvaluation_naturality]

/-- The filling and central covering have literally equal image submodules. -/
theorem periodTorusIntoFillingCohomologyToInvariants_range (n : ℕ) :
    LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D n) =
      LinearMap.range (periodCoverCohomologyToInvariants j D.centralPeriod j.twist
        (mainTwist_admissible j) n) :=
  LinearMap.range_comp_of_range_eq_top _ (centralSurfaceCohomologyEquiv D n).range

/-- The actual invariant cohomology modulo the actual full-filling pullback. -/
abbrev PeriodTorusIntoFillingInvariantCohomologyCokernel (n : ℕ) :=
  periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) n ⧸
    LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D n)

/-- Equality of actual images gives the genuine cokernel comparison,
with the identity map on the ambient invariant cohomology. -/
def periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral (n : ℕ) :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D n ≃ₗ[ℤ]
      PeriodCoverInvariantCohomologyCokernel j D.centralPeriod n :=
  CohomologyDualComparison.cokernelEquivOfIntertwining
    (periodTorusIntoFillingCohomologyToInvariants D n)
    (periodCoverCohomologyToInvariants j D.centralPeriod j.twist
      (mainTwist_admissible j) n)
    (centralSurfaceCohomologyEquiv D n) (LinearEquiv.refl ℤ _) (fun _ => rfl)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk
    (n : ℕ)
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) n) :
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D n
        (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := rfl

@[simp] theorem periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_symm_apply_mk
    (n : ℕ)
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) n) :
    (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D n).symm
        (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := rfl

/-- The two actual covering images have the same integral index in every degree. -/
theorem periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central (n : ℕ) :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D n)).toAddSubgroup.index =
      (LinearMap.range (periodCoverCohomologyToInvariants j D.centralPeriod j.twist
        (mainTwist_admissible j) n)).toAddSubgroup.index := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range]


/-! ## The actual degree-zero through degree-four invariant-image quotients -/

/-- The actual degree-0 filling invariant-cohomology image quotient. -/
def periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D 0 ≃ₗ[ℤ] ZMod 1 :=
  (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D 0).trans
    (periodCoverInvariantCohomologyH0CokernelEquivZMod j D.centralPeriod)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod_apply_mk
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 0) :
    periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod D (Submodule.Quotient.mk a) =
      0 := by
  rw [periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod, LinearEquiv.trans_apply,
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk,
    periodCoverInvariantCohomologyH0CokernelEquivZMod_apply_mk]

/-- The actual degree-0 filling pullback image has the central covering's index. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h0_range_index :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 0)).toAddSubgroup.index =
      1 := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central,
    periodCoverCohomologyToInvariants_h0_range_index]

theorem periodTorusIntoFillingCohomologyToInvariants_h0_range_finiteIndex :
    (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D 0)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFillingCohomologyToInvariants_h0_range_index]
  exact Nat.one_ne_zero

/-- The actual degree-1 filling invariant-cohomology image quotient. -/
def periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D 1 ≃ₗ[ℤ] ZMod j.order :=
  (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D 1).trans
    (periodCoverInvariantCohomologyH1CokernelEquivZMod j D.centralPeriod)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod_apply_mk
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 1) :
    periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod D (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH1Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH1Shear j D.centralPeriod *
          periodInvariantCohomologyH1Coordinates j D.centralPeriod a 0 : ℤ) :
            ZMod j.order) := by
  rw [periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod, LinearEquiv.trans_apply,
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk,
    periodCoverInvariantCohomologyH1CokernelEquivZMod_apply_mk]

/-- The actual degree-1 filling pullback image has the central covering's index. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h1_range_index :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 1)).toAddSubgroup.index =
      j.order := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central,
    periodCoverCohomologyToInvariants_h1_range_index]

theorem periodTorusIntoFillingCohomologyToInvariants_h1_range_finiteIndex :
    (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D 1)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFillingCohomologyToInvariants_h1_range_index]
  exact j.order_pos.ne'

/-- The actual degree-2 filling invariant-cohomology image quotient. -/
def periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D 2 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D 2).trans
    (periodCoverInvariantCohomologyH2CokernelEquivZMod j D.centralPeriod)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod_apply_mk
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 2) :
    periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod D (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH2Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH2Shear j D.centralPeriod *
          periodInvariantCohomologyH2Coordinates j D.centralPeriod a 0 : ℤ) :
            ZMod (fibreNormIndex j)) := by
  rw [periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod, LinearEquiv.trans_apply,
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk,
    periodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk]

/-- The actual degree-2 filling pullback image has the central covering's index. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h2_range_index :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 2)).toAddSubgroup.index =
      (fibreNormIndex j) := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central,
    periodCoverCohomologyToInvariants_h2_range_index]

theorem periodTorusIntoFillingCohomologyToInvariants_h2_range_finiteIndex :
    (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D 2)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFillingCohomologyToInvariants_h2_range_index]
  exact (fibreNormIndex_pos j).ne'

/-- The actual degree-3 filling invariant-cohomology image quotient. -/
def periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D 3 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D 3).trans
    (periodCoverInvariantCohomologyH3CokernelEquivZMod j D.centralPeriod)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod_apply_mk
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 3) :
    periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod D (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH3Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH3Shear j D.centralPeriod *
          periodInvariantCohomologyH3Coordinates j D.centralPeriod a 0 : ℤ) :
            ZMod (fibreNormIndex j)) := by
  rw [periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod, LinearEquiv.trans_apply,
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk,
    periodCoverInvariantCohomologyH3CokernelEquivZMod_apply_mk]

/-- The actual degree-3 filling pullback image has the central covering's index. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h3_range_index :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 3)).toAddSubgroup.index =
      (fibreNormIndex j) := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central,
    periodCoverCohomologyToInvariants_h3_range_index]

theorem periodTorusIntoFillingCohomologyToInvariants_h3_range_finiteIndex :
    (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D 3)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFillingCohomologyToInvariants_h3_range_index]
  exact (fibreNormIndex_pos j).ne'

/-- The actual degree-4 filling invariant-cohomology image quotient. -/
def periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod :
    PeriodTorusIntoFillingInvariantCohomologyCokernel D 4 ≃ₗ[ℤ] ZMod j.order :=
  (periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral D 4).trans
    (periodCoverInvariantCohomologyH4CokernelEquivZMod j D.centralPeriod)

@[simp] theorem periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod_apply_mk
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 4) :
    periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod D (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH4Coordinates j D.centralPeriod a : ℤ) : ZMod j.order) := by
  rw [periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod, LinearEquiv.trans_apply,
    periodTorusIntoFillingInvariantCohomologyCokernelEquivCentral_apply_mk,
    periodCoverInvariantCohomologyH4CokernelEquivZMod_apply_mk]

/-- The actual degree-4 filling pullback image has the central covering's index. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h4_range_index :
    (LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 4)).toAddSubgroup.index =
      j.order := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range_index_eq_central,
    periodCoverCohomologyToInvariants_h4_range_index]

theorem periodTorusIntoFillingCohomologyToInvariants_h4_range_finiteIndex :
    (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D 4)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFillingCohomologyToInvariants_h4_range_index]
  exact j.order_pos.ne'

/-- The complete actual cohomological image-index profile inside all deck invariants. -/
theorem periodTorusIntoFillingCohomologyToInvariants_range_index_vector :
    (fun n : Fin 5 => (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D n)).toAddSubgroup.index) =
      ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact periodTorusIntoFillingCohomologyToInvariants_h0_range_index D
  · exact periodTorusIntoFillingCohomologyToInvariants_h1_range_index D
  · exact periodTorusIntoFillingCohomologyToInvariants_h2_range_index D
  · exact periodTorusIntoFillingCohomologyToInvariants_h3_range_index D
  · exact periodTorusIntoFillingCohomologyToInvariants_h4_range_index D

/-- Literal cohomological indices for every actual order-three filling. -/
theorem periodTorusIntoFillingCohomologyToInvariants_range_index_vector_three
    (D : Equivariant.Data .three) :
    (fun n : Fin 5 => (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D n)).toAddSubgroup.index) =
      ![1, 3, 1, 1, 3] :=
  periodTorusIntoFillingCohomologyToInvariants_range_index_vector D

/-- Literal cohomological indices for every actual order-four filling. -/
theorem periodTorusIntoFillingCohomologyToInvariants_range_index_vector_four
    (D : Equivariant.Data .four) :
    (fun n : Fin 5 => (LinearMap.range
      (periodTorusIntoFillingCohomologyToInvariants D n)).toAddSubgroup.index) =
      ![1, 4, 2, 2, 4] :=
  periodTorusIntoFillingCohomologyToInvariants_range_index_vector D

/-- The actual filling has the same degree-one integral descent obstruction. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h1_mem_range
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 1) :
    a ∈ LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 1) ↔
      (j.order : ℤ) ∣ periodInvariantCohomologyH1Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH1Shear j D.centralPeriod *
          periodInvariantCohomologyH1Coordinates j D.centralPeriod a 0 := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range]
  exact periodCoverCohomologyToInvariants_h1_mem_range j D.centralPeriod a

/-- Degree-two descent is tested on the actual marked invariant cohomology class. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h2_mem_range
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 2) :
    a ∈ LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 2) ↔
      (fibreNormIndex j : ℤ) ∣ periodInvariantCohomologyH2Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH2Shear j D.centralPeriod *
          periodInvariantCohomologyH2Coordinates j D.centralPeriod a 0 := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range]
  exact periodCoverCohomologyToInvariants_h2_mem_range j D.centralPeriod a

/-- Degree-three descent is tested on the actual marked invariant cohomology class. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h3_mem_range
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 3) :
    a ∈ LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 3) ↔
      (fibreNormIndex j : ℤ) ∣ periodInvariantCohomologyH3Coordinates j D.centralPeriod a 1 -
        periodCoverDeckDualH3Shear j D.centralPeriod *
          periodInvariantCohomologyH3Coordinates j D.centralPeriod a 0 := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range]
  exact periodCoverCohomologyToInvariants_h3_mem_range j D.centralPeriod a

/-- Top-degree filling descent is literal divisibility of the actual evaluation coordinate. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h4_mem_range
    (a : periodCohomologyInvariants j D.centralPeriod j.twist (mainTwist_admissible j) 4) :
    a ∈ LinearMap.range (periodTorusIntoFillingCohomologyToInvariants D 4) ↔
      (j.order : ℤ) ∣ periodInvariantCohomologyH4Coordinates j D.centralPeriod a := by
  rw [periodTorusIntoFillingCohomologyToInvariants_range]
  exact periodCoverCohomologyToInvariants_h4_mem_range j D.centralPeriod a

theorem periodTorusIntoFillingCohomologyToInvariants_h0_surjective :
    Function.Surjective (periodTorusIntoFillingCohomologyToInvariants D 0) :=
  (periodCoverCohomologyToInvariants_h0_surjective j D.centralPeriod).comp
    (centralSurfaceCohomologyEquiv D 0).surjective

/-- Every order-three invariant degree-two class comes from the actual full filling. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h2_surjective_three
    (D : Equivariant.Data .three) :
    Function.Surjective (periodTorusIntoFillingCohomologyToInvariants D 2) :=
  (periodCoverCohomologyToInvariants_h2_surjective_three D.centralPeriod).comp
    (centralSurfaceCohomologyEquiv D 2).surjective

/-- Every order-three invariant degree-three class comes from the actual full filling. -/
theorem periodTorusIntoFillingCohomologyToInvariants_h3_surjective_three
    (D : Equivariant.Data .three) :
    Function.Surjective (periodTorusIntoFillingCohomologyToInvariants D 3) :=
  (periodCoverCohomologyToInvariants_h3_surjective_three D.centralPeriod).comp
    (centralSurfaceCohomologyEquiv D 3).surjective

end Wikipedia.HopfProblem.Elliptic.HigherHomology
