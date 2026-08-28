import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineSummation
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1

/-!
# Actual locally fine sheaves solve arbitrary-cover one-cocycles

Supported extensions of the original cocycle sections form a locally
finite family on every member of the cover.  Their genuine sheaf sum
has the prescribed differences, as verified on actual finite-support
neighborhoods.  The proved one-cocycle comparison gives actual Ext H¹
vanishing, with no compactness or cohomological vanishing hypothesis.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1

namespace LocallyFiniteDecomposition

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (d : LocallyFiniteDecomposition F U)

/-- The actual local endomorphism identity evaluated on a literal section. -/
theorem localTotal_apply (V : Opens X) (s : Finset ι)
    (hs : ∀ i ∉ s, Disjoint (V : Set X) (d.support i)) (a : Section F V) :
    (s.sum d.operator).hom.app (op V) a = a := by
  have h := ConcreteCategory.congr_hom (d.localTotal V s hs V le_rfl) a
  change (s.sum d.operator).hom.app (op V) a - a = 0 at h
  exact sub_eq_zero.mp h

variable (c : CechOneCocycle F U)

/-- The actual supported cocycle contribution on one member of the cover. -/
def weightedSection (i j : ι) : Section F (U i) :=
  supportedExtension F (d.support j) (d.support_closed j) (U j)
    (d.subordinate j) (d.operator j) (d.zeroOutside j) (U i) (c.value i j)

/-- The literal difference of supported extensions is the original
cocycle section acted on by the actual supported endomorphism. -/
theorem weightedSection_difference (i k j : ι) :
    res F inf_le_left (d.weightedSection c i j) -
      res F inf_le_right (d.weightedSection c k j) =
        (d.operator j).hom.app (op (U i ⊓ U k)) (c.value i k) := by
  dsimp only [weightedSection]
  have hi := supportedExtension_restrict F (d.support j) (d.support_closed j)
    (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j)
    (U i) (U i ⊓ U k) inf_le_left (c.value i j)
  have hk := supportedExtension_restrict F (d.support j) (d.support_closed j)
    (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j)
    (U k) (U i ⊓ U k) inf_le_right (c.value k j)
  have hc :
      res F (V := (U i ⊓ U k) ⊓ U j)
          (inf_le_inf inf_le_left le_rfl) (c.value i j) -
        res F (V := (U i ⊓ U k) ⊓ U j)
          (inf_le_inf inf_le_right le_rfl) (c.value k j) =
      res F (V := (U i ⊓ U k) ⊓ U j) inf_le_left (c.value i k) :=
    sub_eq_iff_eq_add.mpr (c.condition i k j).symm
  exact (congrArg₂ (fun a b : Section F (U i ⊓ U k) => a - b) hi hk).trans
    ((supportedExtension_sub F (d.support j) (d.support_closed j)
      (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j)
      (U i ⊓ U k) _ _).symm.trans
      ((congrArg (supportedExtension F (d.support j) (d.support_closed j)
        (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j)
        (U i ⊓ U k)) hc).trans
        (supportedExtension_restriction_eq_action F (d.support j) (d.support_closed j)
          (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j)
          (U i ⊓ U k) (c.value i k))))

/-- The actual weighted sections have the original closed locally finite supports. -/
def weightedFamily (i : ι) : SupportedSectionFamily F (U i) ι where
  value := d.weightedSection c i
  support := d.support
  support_closed := d.support_closed
  locallyFinite := d.locallyFinite
  zeroOutside j := supportedExtension_off F (d.support j) (d.support_closed j)
    (U j) (d.subordinate j) (d.operator j) (d.zeroOutside j) (U i) (c.value i j)

/-- The genuine locally finite sum on a member of the original cover. -/
def primitive (i : ι) : Section F (U i) := (d.weightedFamily c i).sum

/-- Actual finite-support restrictions of the constructed primitive. -/
theorem primitive_restrict (i : ι) (V : Opens X) (hV : V ≤ U i) (s : Finset ι)
    (hs : ∀ j ∉ s, Disjoint (V : Set X) (d.support j)) :
    res F hV (d.primitive c i) = s.sum (fun j => res F hV (d.weightedSection c i j)) :=
  (d.weightedFamily c i).sum_restrict V hV s hs

include d in
/-- Every actual cocycle is solved by the constructed locally finite
sum of actual supported extensions, without compactness. -/
theorem solvable : c.Solvable := by
  classical
  refine ⟨d.primitive c, ?_⟩
  intro i k
  apply section_ext_of_local F
  intro x hx
  let N := Classical.choice (exists_summationNeighborhood d.locallyFinite x)
  let V : Opens X := (U i ⊓ U k) ⊓ N.openSet
  have hV : V ≤ U i ⊓ U k := inf_le_left
  have hsupport : ∀ j ∉ N.indices, Disjoint (V : Set X) (d.support j) :=
    fun j hj => (N.avoids j hj).mono_left (fun _ h => h.2)
  refine ⟨V, hV, ⟨hx, N.mem_openSet⟩, ?_⟩
  simp only [map_sub, res_trans]
  rw [d.primitive_restrict c i V (hV.trans inf_le_left) N.indices hsupport,
    d.primitive_restrict c k V (hV.trans inf_le_right) N.indices hsupport,
    ← Finset.sum_sub_distrib]
  have hd (j : ι) :
      res F (hV.trans inf_le_left) (d.weightedSection c i j) -
        res F (hV.trans inf_le_right) (d.weightedSection c k j) =
      res F hV ((d.operator j).hom.app (op (U i ⊓ U k)) (c.value i k)) := by
    simpa only [map_sub, res_trans] using
      congrArg (res F hV) (d.weightedSection_difference c i k j)
  simp only [hd, res_map]
  let ev : (F ⟶ F) →+ Section F V :=
    { toFun := fun φ => φ.hom.app (op V) (res F hV (c.value i k))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change N.indices.sum (fun j => ev (d.operator j)) = res F hV (c.value i k)
  rw [← map_sum]
  exact d.localTotal_apply V N.indices hsupport (res F hV (c.value i k))

end LocallyFiniteDecomposition

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}

/-- Actual local fineness solves one-cocycles on every original open cover. -/
theorem LocallyFine.cechOneVanishing (hF : LocallyFine F) : CechOneVanishing F := by
  intro ι U hU c
  obtain ⟨d⟩ := hF ι U hU
  exact d.solvable c

/-- Genuine Ext-defined H¹ vanishes for an actual locally fine sheaf,
with no compactness hypothesis. -/
theorem LocallyFine.h1_subsingleton (hF : LocallyFine F) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) :=
  subsingleton_h1_of_cechOneVanishing F hF.cechOneVanishing

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
