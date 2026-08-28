import Wikipedia.NoExoticSixSphere.JamesSphereSecondStage
import Wikipedia.NoExoticSixSphere.CollapsedSubspace
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The actual quotient of the second James stage by the first stage

The equivalence relation is specified independently: two words are
identified precisely when they are equal or both lie in the first stage.
The original second-stage collapse induces a homeomorphism from this
quotient, with its quotient topology, to the actual sphere of dimension
`n + n`. Its composite with the quotient map is exactly the collapse.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.JamesSphere.SecondStage

def collapseRelation (n : ℕ) : Setoid (Space n) :=
  CollapsedSubspace.relation (StageAttachment.lower n 1)

theorem collapseRelation_iff (n : ℕ) (w z : Space n) :
    collapseRelation n w z ↔ collapse n w = collapse n z := by
  constructor
  · rintro (rfl | ⟨hw, hz⟩)
    · rfl
    · exact ((collapse_eq_pole_iff n w).mpr hw).trans
        ((collapse_eq_pole_iff n z).mpr hz).symm
  · intro h
    rcases collapse_fiber_condition n w z h with hw | hwz
    · exact Or.inr ⟨hw, (collapse_eq_pole_iff n z).mp
        (h.symm.trans ((collapse_eq_pole_iff n w).mpr hw))⟩
    · exact Or.inl hwz

abbrev QuotientSpace (n : ℕ) := Quotient (collapseRelation n)

def quotientMap (n : ℕ) : C(Space n, QuotientSpace n) :=
  ⟨Quotient.mk (collapseRelation n), continuous_quotient_mk' (s := collapseRelation n)⟩

def quotientHomeomorph (n : ℕ) : QuotientSpace n ≃ₜ Sphere (n + n) :=
  (Homeomorph.Quotient.congrRight (r := collapseRelation n) (r' := Setoid.ker (collapse n))
    (collapseRelation_iff n)).trans (isQuotientMap_collapse n).homeomorph

theorem quotientHomeomorph_quotientMap (n : ℕ) (w : Space n) :
    quotientHomeomorph n (quotientMap n w) = collapse n w := rfl

theorem quotientHomeomorph_lower (n : ℕ) (w : Space n)
    (hw : w ∈ StageAttachment.lower n 1) :
    quotientHomeomorph n (quotientMap n w) = spherePole (n + n) :=
  (collapse_eq_pole_iff n w).mpr hw

theorem quotientMap_eq_iff (n : ℕ) (w z : Space n) :
    quotientMap n w = quotientMap n z ↔
      w = z ∨ (w ∈ StageAttachment.lower n 1 ∧ z ∈ StageAttachment.lower n 1) :=
  Quotient.eq

theorem hopf_quotient_factor (n : ℕ) (w : Space n) :
    hopf n w.val =
      James.letter (spherePole (n + n)) (quotientHomeomorph n (quotientMap n w)) :=
  hopf_factor n w

end NoExoticSixSphere.JamesSphere.SecondStage
