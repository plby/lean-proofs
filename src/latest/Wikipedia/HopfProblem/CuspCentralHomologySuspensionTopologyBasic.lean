import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual unreduced suspension quotient

Only the two end slices of the cylinder are collapsed.  In particular the
two poles remain distinct, and no points in the open cylinder are identified.
The cover used below is defined by the descended, continuous height coordinate.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspCentralHomology

/-- The cylinder equivalence relation defining the unreduced suspension. -/
def suspensionSetoid (X : Type*) : Setoid (unitInterval × X) where
  r p q := p.1 = q.1 ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = q.2)
  iseqv := {
    refl := fun _ => ⟨rfl, Or.inr (Or.inr rfl)⟩
    symm := by
      rintro p q ⟨ht, h | h | h⟩
      · exact ⟨ht.symm, Or.inl (ht.symm.trans h)⟩
      · exact ⟨ht.symm, Or.inr (Or.inl (ht.symm.trans h))⟩
      · exact ⟨ht.symm, Or.inr (Or.inr h.symm)⟩
    trans := by
      rintro p q r ⟨hpq, hp | hp | hp⟩ ⟨hqr, hq⟩
      · exact ⟨hpq.trans hqr, Or.inl hp⟩
      · exact ⟨hpq.trans hqr, Or.inr (Or.inl hp)⟩
      · rcases hq with hq | hq | hq
        · exact ⟨hpq.trans hqr, Or.inl (hpq.trans hq)⟩
        · exact ⟨hpq.trans hqr, Or.inr (Or.inl (hpq.trans hq))⟩
        · exact ⟨hpq.trans hqr, Or.inr (Or.inr (hp.trans hq))⟩ }

/-- The genuine unreduced suspension of a space, with its quotient topology. -/
def Suspension (X : Type*) := Quotient (suspensionSetoid X)

instance {X : Type*} [TopologicalSpace X] : TopologicalSpace (Suspension X) :=
  inferInstanceAs (TopologicalSpace (Quotient (suspensionSetoid X)))

namespace Suspension

variable {X : Type*}

/-- The suspension quotient map. -/
def mk (t : unitInterval) (x : X) : Suspension X :=
  Quotient.mk (suspensionSetoid X) (t, x)

theorem mk_eq_mk_iff (t s : unitInterval) (x y : X) :
    mk t x = mk s y ↔ t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) :=
  Quotient.eq

theorem mk_surjective : Function.Surjective (fun p : unitInterval × X => mk p.1 p.2) :=
  Quotient.mk_surjective

theorem isQuotientMap_mk [TopologicalSpace X] :
    IsQuotientMap (fun p : unitInterval × X => mk p.1 p.2) :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop] theorem continuous_mk [TopologicalSpace X] :
    Continuous (fun p : unitInterval × X => mk p.1 p.2) :=
  isQuotientMap_mk.continuous

/-- Height descends because the quotient never identifies different levels. -/
def height : Suspension X → unitInterval :=
  Quotient.lift Prod.fst (fun _ _ h => h.1)

@[simp] theorem height_mk (t : unitInterval) (x : X) : height (mk t x) = t := rfl

@[continuity, fun_prop] theorem continuous_height [TopologicalSpace X] :
    Continuous (height : Suspension X → _) :=
  isQuotientMap_mk.continuous_iff.mpr continuous_fst

@[continuity, fun_prop] theorem continuous_realHeight [TopologicalSpace X] :
    Continuous (fun p : Suspension X => (height p : ℝ)) :=
  continuous_subtype_val.comp continuous_height

theorem mk_injective_of_interior (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Injective (mk t : X → Suspension X) := by
  intro x y h
  rcases (mk_eq_mk_iff t t x y).mp h with ⟨_, h | h | h⟩
  · exact (ht0 h).elim
  · exact (ht1 h).elim
  · exact h

theorem mk_zero_eq (x y : X) : mk 0 x = mk 0 y :=
  Quotient.sound ⟨rfl, Or.inl rfl⟩

theorem mk_one_eq (x y : X) : mk 1 x = mk 1 y :=
  Quotient.sound ⟨rfl, Or.inr (Or.inl rfl)⟩

/-- The open northern cone, with height strictly less than three quarters. -/
def northOpen : Set (Suspension X) := {p | (height p : ℝ) < 3 / 4}

/-- The open southern cone, with height strictly greater than one quarter. -/
def southOpen : Set (Suspension X) := {p | 1 / 4 < (height p : ℝ)}

@[simp] theorem mem_northOpen (p : Suspension X) :
    p ∈ northOpen ↔ (height p : ℝ) < 3 / 4 := Iff.rfl

@[simp] theorem mem_southOpen (p : Suspension X) :
    p ∈ southOpen ↔ 1 / 4 < (height p : ℝ) := Iff.rfl

theorem northOpen_isOpen [TopologicalSpace X] : IsOpen (northOpen : Set (Suspension X)) :=
  isOpen_lt continuous_realHeight continuous_const

theorem southOpen_isOpen [TopologicalSpace X] : IsOpen (southOpen : Set (Suspension X)) :=
  isOpen_lt continuous_const continuous_realHeight

/-- These actual open subsets cover the suspension. -/
theorem open_cover : (northOpen ∪ southOpen : Set (Suspension X)) = univ := by
  ext p
  simp only [mem_union, mem_northOpen, mem_southOpen, mem_univ, iff_true]
  by_cases h : (height p : ℝ) < 3 / 4
  · exact Or.inl h
  · exact Or.inr (by linarith)

variable [Nonempty X]

/-- The height-zero pole. -/
def north : Suspension X := mk 0 (Classical.choice ‹Nonempty X›)

/-- The height-one pole. -/
def south : Suspension X := mk 1 (Classical.choice ‹Nonempty X›)

@[simp] theorem mk_zero (x : X) : mk 0 x = north := mk_zero_eq _ _

@[simp] theorem mk_one (x : X) : mk 1 x = south := mk_one_eq _ _

@[simp] theorem height_north : height (north : Suspension X) = 0 := rfl

@[simp] theorem height_south : height (south : Suspension X) = 1 := rfl

theorem north_ne_south : (north : Suspension X) ≠ south := by
  intro h
  have := congrArg (fun p : Suspension X => (height p : ℝ)) h
  norm_num at this

theorem north_mem_northOpen : (north : Suspension X) ∈ northOpen := by
  simp [northOpen]

theorem south_mem_southOpen : (south : Suspension X) ∈ southOpen := by
  norm_num [southOpen]

theorem north_not_mem_southOpen : (north : Suspension X) ∉ southOpen := by
  simp [southOpen]

theorem south_not_mem_northOpen : (south : Suspension X) ∉ northOpen := by
  norm_num [northOpen]

instance : Nonempty (Suspension X) := ⟨north⟩

end Suspension
end Wikipedia.HopfProblem.CuspCentralHomology
