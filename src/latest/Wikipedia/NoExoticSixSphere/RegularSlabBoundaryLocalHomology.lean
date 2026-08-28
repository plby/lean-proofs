import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryPuncture
import Wikipedia.NoExoticSixSphere.RegularSlabInteriorEquivalence
import Wikipedia.NoExoticSixSphere.RelativeHomologyAcyclic
import Wikipedia.NoExoticSixSphere.RelativeCoefficientSequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Original local homology vanishes at the actual slab boundary

The constructed boundary-puncture equivalence has the original inclusion
as its forward map. The actual pair sequence annihilates integral local
homology, and the actual coefficient sequence gives finite-cyclic local
vanishing in every degree.
-/

noncomputable section

open scoped Manifold ContDiff ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (w : BoundaryPush.ends d.map z s t)

def boundaryPunctureHomotopyEquiv :
    ({w.val}ᶜ : Set (slab d.map z s t)) ≃ₕ slab d.map z s t :=
  let a := d.exists_inner_times.choose
  let b := d.exists_inner_times.choose_spec.choose
  let h := d.exists_inner_times.choose_spec.choose_spec
  InteriorPush.boundaryPunctureHomotopyEquiv d.map z s t a b h.1 h.2.1 h.2.2.1
    (fun r hr x ↦ (d.left_eq r (h.2.2.2.1 hr) x).trans (d.left_eq s d.left_mem x).symm)
    (fun r hr x ↦ (d.right_eq r (h.2.2.2.2 hr) x).trans (d.right_eq t d.right_mem x).symm)
    w.val w.property

theorem boundaryPunctureHomotopyEquiv_toFun :
    (d.boundaryPunctureHomotopyEquiv w).toFun =
      subtypeInclusion ({w.val}ᶜ : Set (slab d.map z s t)) := rfl

theorem exists_interior_mem_open (O : Set (slab d.map z s t)) (hO : IsOpen O)
    (p : slab d.map z s t) (hp : p ∈ O) :
    ∃ y : slab d.map z s t, y ∈ O ∧ y ∈ interiorDomain d.map z s t := by
  obtain ⟨a, b, hsa, hab, hbt, hL, hR⟩ := d.exists_inner_times
  exact InteriorPush.exists_interior_mem_open d.map z s t a b hsa hab hbt
    (fun r hr x ↦ (d.left_eq r (hL hr) x).trans (d.left_eq s d.left_mem x).symm)
    (fun r hr x ↦ (d.right_eq r (hR hr) x).trans (d.right_eq t d.right_mem x).symm) O hO p hp

theorem boundaryLocalIntegralHomology_subsingleton (n : ℕ) :
    Subsingleton (RelativeSingularHomology.Homology ({w.val}ᶜ : Set (slab d.map z s t)) n) :=
  RelativeSingularHomology.subsingleton_of_inclusion_bijective
    ({w.val}ᶜ : Set (slab d.map z s t))
    (fun q ↦ (homotopyEquivHomologyEquiv (d.boundaryPunctureHomotopyEquiv w) q).bijective) n

theorem boundaryLocalModHomology_subsingleton (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    Subsingleton (RelativeCoefficients.ModHomology p ({w.val}ᶜ : Set (slab d.map z s t)) n) := by
  let := d.boundaryLocalIntegralHomology_subsingleton w n
  cases n with
  | zero => exact (RelativeCoefficients.reductionMap_zero_surjective p hp
      ({w.val}ᶜ : Set (slab d.map z s t))).subsingleton
  | succ n =>
    let := d.boundaryLocalIntegralHomology_subsingleton w n
    exact (RelativeCoefficients.reductionMap_surjective_of_subsingleton p hp
      ({w.val}ᶜ : Set (slab d.map z s t)) n).subsingleton

end NoExoticSixSphere.RegularCollaredCylinder
