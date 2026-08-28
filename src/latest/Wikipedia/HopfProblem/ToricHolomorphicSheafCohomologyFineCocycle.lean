import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineExtensionLinear
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1
import Mathlib.Topology.Compactness.Compact

/-!
# Solving actual one-cocycles by finite fine decompositions

Each term is the actual extension by zero of a supported sheaf
endomorphism applied to a cocycle section. Their finite sum has precisely
the prescribed differences. On a compact space a finite subcover makes
this construction apply to every open cover, so the previously proved
degree-one comparison gives genuine Ext-defined H¹ vanishing.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι J : Type} [Fintype J] {U : ι → Opens X}
  (σ : J → ι) (d : FiniteDecomposition F (fun j => U (σ j)))
  (c : CechOneCocycle F U)

/-- An actual supported cocycle section extended to a member of the cover. -/
def weightedSection (i : ι) (j : J) : Section F (U i) :=
  supportedExtension F (d.support j) (d.support_closed j) (U (σ j))
    (d.subordinate j) (d.operator j) (d.zeroOutside j) (U i) (c.value i (σ j))

/-- The difference of the two actual weighted sections is the supported
endomorphism applied to the original transition section. -/
theorem weightedSection_difference (i k : ι) (j : J) :
    res F inf_le_left (weightedSection σ d c i j) -
      res F inf_le_right (weightedSection σ d c k j) =
        (d.operator j).hom.app (op (U i ⊓ U k)) (c.value i k) := by
  dsimp only [weightedSection]
  have hi := supportedExtension_restrict F (d.support j) (d.support_closed j)
    (U (σ j)) (d.subordinate j) (d.operator j) (d.zeroOutside j)
    (U i) (U i ⊓ U k) inf_le_left (c.value i (σ j))
  have hk := supportedExtension_restrict F (d.support j) (d.support_closed j)
    (U (σ j)) (d.subordinate j) (d.operator j) (d.zeroOutside j)
    (U k) (U i ⊓ U k) inf_le_right (c.value k (σ j))
  have hc :
      res F (V := (U i ⊓ U k) ⊓ U (σ j))
          (inf_le_inf inf_le_left le_rfl) (c.value i (σ j)) -
        res F (V := (U i ⊓ U k) ⊓ U (σ j))
          (inf_le_inf inf_le_right le_rfl) (c.value k (σ j)) =
      res F (V := (U i ⊓ U k) ⊓ U (σ j)) inf_le_left (c.value i k) :=
    sub_eq_iff_eq_add.mpr (c.condition i k (σ j)).symm
  exact (congrArg₂ (fun a b : Section F (U i ⊓ U k) => a - b) hi hk).trans
    ((supportedExtension_sub F (d.support j) (d.support_closed j)
      (U (σ j)) (d.subordinate j) (d.operator j) (d.zeroOutside j)
      (U i ⊓ U k) _ _).symm.trans
      ((congrArg (supportedExtension F (d.support j) (d.support_closed j)
        (U (σ j)) (d.subordinate j) (d.operator j) (d.zeroOutside j)
        (U i ⊓ U k)) hc).trans
        (supportedExtension_restriction_eq_action F (d.support j) (d.support_closed j)
          (U (σ j)) (d.subordinate j) (d.operator j) (d.zeroOutside j)
          (U i ⊓ U k) (c.value i k))))

include σ d

/-- Every actual cocycle is solved by the literal finite sum of its
supported extensions. The original cover need not be finite. -/
theorem solvable_of_finiteDecomposition : c.Solvable := by
  classical
  refine ⟨fun i => ∑ j, weightedSection σ d c i j, ?_⟩
  intro i k
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  simp only [weightedSection_difference]
  let ev : (F ⟶ F) →+ Section F (U i ⊓ U k) :=
    { toFun := fun φ => φ.hom.app (op (U i ⊓ U k)) (c.value i k)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ∑ j, ev (d.operator j) = c.value i k
  rw [← map_sum, d.total]
  rfl

omit σ d

/-- On a compact space, finite fineness solves actual one-cocycles on
every open cover, using an actual finite subcover. -/
theorem FiniteFine.cechOneVanishing [CompactSpace X] (hF : FiniteFine F) :
    CechOneVanishing F := by
  classical
  intro ι U hU c
  have hc : Set.univ ⊆ ⋃ i, (U i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) hc
  let σ : ↥s → ι := Subtype.val
  have hσ : ∀ x : X, ∃ j : ↥s, x ∈ U (σ j) := by
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨d⟩ := hF ↥s (fun j => U (σ j)) hσ
  exact solvable_of_finiteDecomposition σ d c

/-- Genuine Ext-defined first sheaf cohomology vanishes for an actual
finite-fine sheaf on a compact space. -/
theorem FiniteFine.h1_subsingleton [CompactSpace X] (hF : FiniteFine F) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) :=
  subsingleton_h1_of_cechOneVanishing F hF.cechOneVanishing

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
