import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndices
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesTop

/-!
# Actual period-cover indices in the entire elliptic filling

The actual central inclusion is a homology equivalence and its composite
with the finite period cover is the literal period-torus map into the
whole filling.  It therefore identifies their actual image quotients
in every degree.  The calculated surface cokernels and indices transfer
to the actual filling, preserving the established homology coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

section QuotientComparison

variable {M N P : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]

/-- A commuting actual codomain equivalence identifies the two actual
image quotients, with the original representative map. -/
def coverCokernelEquivOfIntertwining (f : M →ₗ[ℤ] N) (g : M →ₗ[ℤ] P)
    (e : N ≃ₗ[ℤ] P) (h : ∀ x, e (f x) = g x) :
    (N ⧸ LinearMap.range f) ≃ₗ[ℤ] (P ⧸ LinearMap.range g) := by
  letI := Submodule.Quotient.module (LinearMap.range f)
  letI := Submodule.Quotient.module (LinearMap.range g)
  have he : e.toLinearMap.comp f = g := LinearMap.ext h
  exact (Submodule.Quotient.equiv _ _ e
    (by rw [← LinearMap.range_comp, he])).toAddEquiv.toIntLinearEquiv

@[simp] theorem coverCokernelEquivOfIntertwining_mk
    (f : M →ₗ[ℤ] N) (g : M →ₗ[ℤ] P) (e : N ≃ₗ[ℤ] P)
    (h : ∀ x, e (f x) = g x) (a : N) :
    coverCokernelEquivOfIntertwining f g e h (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (e a) := rfl

end QuotientComparison

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual deformation retraction identifies the cokernel of the
period-torus map into the full filling with the actual surface-cover cokernel. -/
def periodTorusIntoFillingCokernelSurfaceEquiv (n : ℕ) :
    (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n ⧸
      LinearMap.range (singularHomologyMap
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n)) ≃ₗ[ℤ]
    (SingularHomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) n ⧸
      LinearMap.range (singularHomologyMap
        (periodCover j D.centralPeriod j.twist (mainTwist_admissible j)) n)) :=
  coverCokernelEquivOfIntertwining
    (singularHomologyMap (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n)
    (singularHomologyMap (periodCover j D.centralPeriod j.twist (mainTwist_admissible j)) n)
    (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n).symm
    (fun a => by
      rw [← centralSurfaceHomologyEquiv_periodCover, LinearEquiv.symm_apply_apply])

@[simp] theorem periodTorusIntoFillingCokernelSurfaceEquiv_mk (n : ℕ)
    (a : SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) :
    periodTorusIntoFillingCokernelSurfaceEquiv D n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n).symm a) := rfl

/-- The two actual maps have exactly the same image index in every degree. -/
theorem periodTorusIntoFilling_homology_range_index (n : ℕ) :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n)).toAddSubgroup.index =
    (LinearMap.range (singularHomologyMap
      (periodCover j D.centralPeriod j.twist (mainTwist_admissible j)) n)).toAddSubgroup.index := by
  change Nat.card (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n ⧸
    LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n)) = _
  exact Nat.card_congr (periodTorusIntoFillingCokernelSurfaceEquiv D n).toEquiv

/-- The actual degree-two cokernel in the whole filling is `ℤ/dℤ`,
where `d` is one for order three and two for order four. -/
def fillingPeriodCoverH2CokernelEquivZMod :
    (SingularHomology (D.Space j.twist (mainTwist_admissible j)) 2 ⧸
      LinearMap.range (singularHomologyMap
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 2)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  (periodTorusIntoFillingCokernelSurfaceEquiv D 2).trans
    (surfacePeriodCoverH2CokernelEquivZMod j D.centralPeriod)

/-- The same actual residue cokernel occurs in degree three. -/
def fillingPeriodCoverH3CokernelEquivZMod :
    (SingularHomology (D.Space j.twist (mainTwist_admissible j)) 3 ⧸
      LinearMap.range (singularHomologyMap
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 3)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  (periodTorusIntoFillingCokernelSurfaceEquiv D 3).trans
    (surfacePeriodCoverH3CokernelEquivZMod j D.centralPeriod)

/-- In degree four the actual cokernel is reduction modulo the elliptic order. -/
def fillingPeriodCoverH4CokernelEquivZMod :
    (SingularHomology (D.Space j.twist (mainTwist_admissible j)) 4 ⧸
      LinearMap.range (singularHomologyMap
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 4)) ≃ₗ[ℤ]
      ZMod j.order :=
  (periodTorusIntoFillingCokernelSurfaceEquiv D 4).trans
    (surfacePeriodCoverH4CokernelEquivZMod j D.centralPeriod)

@[simp] theorem fillingPeriodCoverH2CokernelEquivZMod_mk
    (a : SingularHomology (D.Space j.twist (mainTwist_admissible j)) 2) :
    fillingPeriodCoverH2CokernelEquivZMod D (Submodule.Quotient.mk a) =
      (fillingH2Equiv D a 1 : ZMod (fibreNormIndex j)) := rfl

@[simp] theorem fillingPeriodCoverH3CokernelEquivZMod_mk
    (a : SingularHomology (D.Space j.twist (mainTwist_admissible j)) 3) :
    fillingPeriodCoverH3CokernelEquivZMod D (Submodule.Quotient.mk a) =
      (fillingH3Equiv D a 1 : ZMod (fibreNormIndex j)) := rfl

@[simp] theorem fillingPeriodCoverH4CokernelEquivZMod_mk
    (a : SingularHomology (D.Space j.twist (mainTwist_admissible j)) 4) :
    fillingPeriodCoverH4CokernelEquivZMod D (Submodule.Quotient.mk a) =
      (fillingH4Equiv D a : ZMod j.order) := rfl

theorem periodTorusIntoFilling_h2_range_index :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 2)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [periodTorusIntoFilling_homology_range_index, surfacePeriodCover_h2_range_index]

theorem periodTorusIntoFilling_h3_range_index :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 3)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [periodTorusIntoFilling_homology_range_index, surfacePeriodCover_h3_range_index]

theorem periodTorusIntoFilling_h4_range_index :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 4)).toAddSubgroup.index =
      j.order := by
  rw [periodTorusIntoFilling_homology_range_index, surfacePeriodCover_h4_range_index]

theorem periodTorusIntoFilling_h2_range_finiteIndex :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist
        (mainTwist_admissible j)) 2)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFilling_h2_range_index]
  exact (fibreNormIndex_pos j).ne'

theorem periodTorusIntoFilling_h3_range_finiteIndex :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist
        (mainTwist_admissible j)) 3)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFilling_h3_range_index]
  exact (fibreNormIndex_pos j).ne'

theorem periodTorusIntoFilling_h4_range_finiteIndex :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist
        (mainTwist_admissible j)) 4)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFilling_h4_range_index]
  exact j.order_pos.ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
