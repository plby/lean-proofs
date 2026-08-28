import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The abelian extension defined by a symmetric integer cocycle

The group law on the actual pairs `(a,l)` is
`(a,l) + (b,m) = (a+b+c(l,m),l+m)`.  The cocycle identity proves
associativity, normalization proves the identity laws, and symmetry
proves commutativity.  The projection onto the second coordinate is
therefore a genuine surjective additive homomorphism.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable (Λ : Type*) [AddCommGroup Λ]

/-- A normalized symmetric integer-valued two-cocycle. -/
structure SymmetricIntegerCocycle where
  value : Λ → Λ → ℤ
  cocycle : ∀ l m k, value l m + value (l + m) k = value m k + value l (m + k)
  zero_left : ∀ l, value 0 l = 0
  zero_right : ∀ l, value l 0 = 0
  symmetric : ∀ l m, value l m = value m l

namespace SymmetricIntegerCocycle

variable {Λ} (c : SymmetricIntegerCocycle Λ)

/-- Pairs with the addition twisted by the specified cocycle. -/
@[ext] structure Extension (c : SymmetricIntegerCocycle Λ) where
  integer : ℤ
  lattice : Λ

instance : Add c.Extension where
  add x y := ⟨x.integer + y.integer + c.value x.lattice y.lattice, x.lattice + y.lattice⟩

instance : Zero c.Extension where
  zero := ⟨0, 0⟩

instance : Neg c.Extension where
  neg x := ⟨-x.integer - c.value (-x.lattice) x.lattice, -x.lattice⟩

instance : AddCommGroup c.Extension where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc x y z := by
    apply Extension.ext
    · change (x.integer + y.integer + c.value x.lattice y.lattice) + z.integer +
          c.value (x.lattice + y.lattice) z.lattice =
        x.integer + (y.integer + z.integer + c.value y.lattice z.lattice) +
          c.value x.lattice (y.lattice + z.lattice)
      linear_combination c.cocycle x.lattice y.lattice z.lattice
    · exact add_assoc _ _ _
  zero_add x := by
    apply Extension.ext
    · change 0 + x.integer + c.value 0 x.lattice = x.integer
      rw [c.zero_left, zero_add, add_zero]
    · exact zero_add _
  add_zero x := by
    apply Extension.ext
    · change x.integer + 0 + c.value x.lattice 0 = x.integer
      rw [c.zero_right, add_zero, add_zero]
    · exact add_zero _
  neg_add_cancel x := by
    apply Extension.ext
    · change (-x.integer - c.value (-x.lattice) x.lattice) + x.integer +
          c.value (-x.lattice) x.lattice = 0
      ring
    · exact neg_add_cancel _
  add_comm x y := by
    apply Extension.ext
    · change x.integer + y.integer + c.value x.lattice y.lattice =
        y.integer + x.integer + c.value y.lattice x.lattice
      rw [c.symmetric, add_comm x.integer y.integer]
    · exact add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem zero_integer : (0 : c.Extension).integer = 0 := rfl

@[simp] theorem zero_lattice : (0 : c.Extension).lattice = 0 := rfl

@[simp] theorem add_integer (x y : c.Extension) :
    (x + y).integer = x.integer + y.integer + c.value x.lattice y.lattice := rfl

@[simp] theorem add_lattice (x y : c.Extension) :
    (x + y).lattice = x.lattice + y.lattice := rfl

/-- The projection of the cocycle extension onto its lattice coordinate. -/
def projection : c.Extension →+ Λ where
  toFun x := x.lattice
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem projection_apply (x : c.Extension) : c.projection x = x.lattice := rfl

theorem projection_surjective : Function.Surjective c.projection := by
  intro l
  exact ⟨⟨0, l⟩, rfl⟩

/-- The integer coordinate of an additive section has precisely the requested coboundary. -/
theorem coboundary_of_section (s : Λ →+ c.Extension)
    (hs : c.projection.comp s = AddMonoidHom.id Λ) :
    (s 0).integer = 0 ∧ ∀ l m,
      c.value l m = (s (l + m)).integer - (s l).integer - (s m).integer := by
  have hproj (l : Λ) : (s l).lattice = l := DFunLike.congr_fun hs l
  constructor
  · rw [map_zero]
    rfl
  · intro l m
    rw [map_add, add_integer, hproj, hproj]
    ring

end SymmetricIntegerCocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
