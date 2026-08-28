import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionKernel
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Integral singular homology of the suspension of three circles

The space is the actual quotient of the cylinder on three disjoint unit
complex circles, collapsing its two end slices separately. Its two actual
open cones are contractible, and their intersection is genuinely homotopy
equivalent to the original three circles. The proved singular
Mayer–Vietoris sequence therefore computes the homology as `ℤ`, `ℤ²`,
`ℤ³`, and zero in all higher degrees.

No CW structure, suspension homology formula, or desired homology
equivalence is supplied as an assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual unreduced suspension of three disjoint unit complex circles. -/
abbrev ThreeCircleSuspension := Suspension ThreeCircles

local notation "U" => (Suspension.northOpen : Set ThreeCircleSuspension)
local notation "V" => (Suspension.southOpen : Set ThreeCircleSuspension)

/-- The canonical augmentation computes degree zero of the actual,
path-connected suspension. -/
def threeCircleSuspensionHomologyZeroEquiv :
    SingularHomology ThreeCircleSuspension 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv ThreeCircleSuspension

/-- The two first-homology generators are the two independent
differences of the three components of the actual open intersection. -/
def threeCircleSuspensionHomologyOneEquiv :
    SingularHomology ThreeCircleSuspension 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (contractibleCoverHomologyOneEquivKernel U V
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover).trans
      (threeCirclesIntersectionKernelEquiv U V
        (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)))

/-- The actual connecting map identifies degree two with the three
circle generators of the open belt. -/
def threeCircleSuspensionHomologyTwoEquiv :
    SingularHomology ThreeCircleSuspension 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (contractibleCoverHomologyHigherEquiv U V
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 0).trans
      ((homotopyEquivHomologyEquiv (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
        threeCirclesHomologyOneEquiv)

/-- All actual integral singular homology above degree two vanishes. -/
theorem threeCircleSuspension_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology ThreeCircleSuspension (n + 3)) := by
  let := threeCircles_homology_subsingleton n
  exact ((contractibleCoverHomologyHigherEquiv U V
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover (n + 1)).trans
      (homotopyEquivHomologyEquiv
        (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) (n + 2))).injective.subsingleton

/-- The Betti numbers are ranks of the proved actual homology groups. -/
def threeCircleSuspensionBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 0

/-- A finite integral coordinate model for every actual homology degree. -/
def threeCircleSuspensionHomologyEquiv (n : ℕ) :
    SingularHomology ThreeCircleSuspension n ≃ₗ[ℤ]
      (Fin (threeCircleSuspensionBetti n) → ℤ) := by
  cases n with
  | zero =>
      exact threeCircleSuspensionHomologyZeroEquiv.trans
        (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | succ n =>
      cases n with
      | zero => exact threeCircleSuspensionHomologyOneEquiv
      | succ n =>
          cases n with
          | zero => exact threeCircleSuspensionHomologyTwoEquiv
          | succ n =>
              change SingularHomology ThreeCircleSuspension (n + 3) ≃ₗ[ℤ] (Fin 0 → ℤ)
              letI := threeCircleSuspension_homology_subsingleton n
              exact LinearEquiv.ofSubsingleton _ _

theorem threeCircleSuspension_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology ThreeCircleSuspension n) :=
  Module.Free.of_equiv (threeCircleSuspensionHomologyEquiv n).symm

theorem threeCircleSuspension_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology ThreeCircleSuspension n) :=
  Module.Finite.of_surjective (threeCircleSuspensionHomologyEquiv n).symm.toLinearMap
    (threeCircleSuspensionHomologyEquiv n).symm.surjective

theorem threeCircleSuspension_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology ThreeCircleSuspension n) =
      threeCircleSuspensionBetti n := by
  rw [(threeCircleSuspensionHomologyEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

/-- No torsion appears in any degree of the actual suspension homology. -/
theorem threeCircleSuspension_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology ThreeCircleSuspension n) := by
  let := threeCircleSuspension_homology_free n
  infer_instance

theorem threeCircleSuspension_homology :
    Nonempty (SingularHomology ThreeCircleSuspension 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology ThreeCircleSuspension 1 ≃ₗ[ℤ] (Fin 2 → ℤ)) ∧
      Nonempty (SingularHomology ThreeCircleSuspension 2 ≃ₗ[ℤ] (Fin 3 → ℤ)) ∧
      ∀ n, Subsingleton (SingularHomology ThreeCircleSuspension (n + 3)) :=
  ⟨⟨threeCircleSuspensionHomologyZeroEquiv⟩, ⟨threeCircleSuspensionHomologyOneEquiv⟩,
    ⟨threeCircleSuspensionHomologyTwoEquiv⟩, threeCircleSuspension_homology_subsingleton⟩

end Wikipedia.HopfProblem.CuspCentralHomology
