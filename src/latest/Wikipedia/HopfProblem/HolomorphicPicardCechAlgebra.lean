import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingCocycle
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual additive Čech cocycles and their cover cohomology group

This file equips the existing literal-section Čech cocycles with their
pointwise additive group structure. Cover cohomology is the quotient by
actual local coboundaries. It is an intermediate Čech object, not a
redefinition of native sheaf cohomology or of holomorphic line bundles.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.Cech

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {ι : Type} (U : ι → Opens X)

abbrev OneCochain := ∀ i j : ι, Section F (U i ⊓ U j)
abbrev ZeroCochain := ∀ i : ι, Section F (U i)

/-- The actual cocycle condition cuts out an additive subgroup of the
literal families of overlap sections. -/
def cocycleSubgroup : AddSubgroup (OneCochain F U) where
  carrier c := ∀ i j k : ι,
    res F (V := (U i ⊓ U j) ⊓ U k) inf_le_left (c i j) +
      res F (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_right le_rfl) (c j k) =
      res F (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_left le_rfl) (c i k)
  zero_mem' := by intro i j k; simp
  add_mem' := by
    intro c d hc hd i j k
    simp only [Pi.add_apply, map_add]
    calc
      _ = (res F inf_le_left (c i j) +
          res F (inf_le_inf inf_le_right le_rfl) (c j k)) +
          (res F inf_le_left (d i j) +
          res F (inf_le_inf inf_le_right le_rfl) (d j k)) := by abel
      _ = _ := congrArg₂ (· + ·) (hc i j k) (hd i j k)
  neg_mem' := by
    intro c hc i j k
    simpa only [Pi.neg_apply, map_neg, neg_add] using congrArg Neg.neg (hc i j k)

/-- This equivalence retains the actual sections and their actual
triple-overlap identity. -/
def cocycleSubgroupEquiv : CechOneCocycle F U ≃ cocycleSubgroup F U where
  toFun c := ⟨c.value, c.condition⟩
  invFun c := ⟨c.val, c.property⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

instance cocycleAddCommGroup : AddCommGroup (CechOneCocycle F U) :=
  (cocycleSubgroupEquiv F U).addCommGroup

@[ext] theorem cocycle_ext {c d : CechOneCocycle F U}
    (h : ∀ i j, c.value i j = d.value i j) : c = d := by
  cases c
  cases d
  congr
  exact funext fun i => funext (h i)

@[simp] theorem zero_value (i j : ι) : (0 : CechOneCocycle F U).value i j = 0 := rfl

@[simp] theorem add_value (c d : CechOneCocycle F U) (i j : ι) :
    (c + d).value i j = c.value i j + d.value i j := rfl

@[simp] theorem neg_value (c : CechOneCocycle F U) (i j : ι) :
    (-c).value i j = -c.value i j := rfl

@[simp] theorem sub_value (c d : CechOneCocycle F U) (i j : ι) :
    (c - d).value i j = c.value i j - d.value i j := rfl

@[simp] theorem zsmul_value (n : ℤ) (c : CechOneCocycle F U) (i j : ι) :
    (n • c).value i j = n • c.value i j := rfl

variable {F U}

/-- The genuine cocycle identity restricted to any common smaller open. -/
theorem restrict_condition (c : CechOneCocycle F U) {V : Opens X}
    {i j k : ι} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    res F (le_inf hi hj) (c.value i j) + res F (le_inf hj hk) (c.value j k) =
      res F (le_inf hi hk) (c.value i k) := by
  have h := congrArg (res F (le_inf (le_inf hi hj) hk)) (c.condition i j k)
  simpa only [map_add, res_trans] using h

@[simp] theorem value_self (c : CechOneCocycle F U) (i : ι) : c.value i i = 0 := by
  have h := restrict_condition c (V := U i ⊓ U i) inf_le_left inf_le_left inf_le_left
  have h' : c.value i i + c.value i i = c.value i i := by
    simpa only [res_refl] using h
  exact (add_eq_left).mp h'

theorem restrict_symm (c : CechOneCocycle F U) {V : Opens X}
    {i j : ι} (hi : V ≤ U i) (hj : V ≤ U j) :
    res F (le_inf hi hj) (c.value i j) = -res F (le_inf hj hi) (c.value j i) := by
  have h := restrict_condition c hi hj hi
  rw [value_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

variable (F U)

/-- The actual local coboundary, with its telescoping identity proved. -/
def coboundary : ZeroCochain F U →+ CechOneCocycle F U where
  toFun b := ⟨overlapDifference F U b, overlapDifference_condition F U b⟩
  map_zero' := by
    apply cocycle_ext
    intro i j
    simp [overlapDifference]
  map_add' b d := by
    apply cocycle_ext
    intro i j
    simp only [add_value, overlapDifference, Pi.add_apply, map_add]
    abel

@[simp] theorem coboundary_value (b : ZeroCochain F U) (i j : ι) :
    (coboundary F U b).value i j =
      res F inf_le_left (b i) - res F inf_le_right (b j) := rfl

/-- Actual Čech cohomology on this cover, not native derived sheaf cohomology. -/
abbrev CoverCohomology := CechOneCocycle F U ⧸ (coboundary F U).range

def classOf : CechOneCocycle F U →+ CoverCohomology F U :=
  QuotientAddGroup.mk' (coboundary F U).range

theorem class_eq_zero_iff (c : CechOneCocycle F U) :
    classOf F U c = 0 ↔ c.Solvable := by
  change (QuotientAddGroup.mk c : CoverCohomology F U) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun i j => congrArg (fun d : CechOneCocycle F U => d.value i j) hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, cocycle_ext F U hb⟩

theorem class_eq_class_iff (c d : CechOneCocycle F U) :
    classOf F U c = classOf F U d ↔ (c - d).Solvable := by
  rw [← sub_eq_zero, ← map_sub, class_eq_zero_iff]

end Wikipedia.HopfProblem.HolomorphicPicard.Cech
