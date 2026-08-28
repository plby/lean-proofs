import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleCochains
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Actual singular-cohomology classes of integral edge cocycles

The closed two-cochain constructed from genuine singular-edge labels
defines a class in the actual integral singular cohomology object.
This class is additive, natural under continuous pullback, and unchanged
by an integral group coboundary. Its vanishing and equality criteria use
the actual incoming singular-cochain differential.

These results do not identify the construction with a line bundle's
first Chern class or with a Čech-cohomology comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle

open FirstHurewicz SingularCohomologyFree

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- The literal closed singular two-cochain as a cocycle in the native complex. -/
def twoCocycle (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    Cocycle (singularCochainComplex X) 2 :=
  mkCocycle (singularCochainComplex X) 2 (twoCochain ℓ k) (twoCochain_closed ℓ k)

@[simp] theorem twoCocycle_val (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    (twoCocycle ℓ k).1 = twoCochain ℓ k := rfl

/-- The associated class in actual integral singular cohomology. -/
def twoClass (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    SingularCohomology X 2 :=
  cocycleClass (singularCochainComplex X) 2 (twoCocycle ℓ k)

@[simp] theorem twoCocycle_zero (ℓ : EdgeCocycle X A) : twoCocycle ℓ 0 = 0 := by
  apply Subtype.ext
  exact twoCochain_zero ℓ

@[simp] theorem twoCocycle_add (ℓ : EdgeCocycle X A) (k l : IntegralTwoCocycle A) :
    twoCocycle ℓ (k + l) = twoCocycle ℓ k + twoCocycle ℓ l := by
  apply Subtype.ext
  exact twoCochain_add ℓ k l

@[simp] theorem twoCocycle_neg (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    twoCocycle ℓ (-k) = -twoCocycle ℓ k := by
  apply Subtype.ext
  exact twoCochain_neg ℓ k

@[simp] theorem twoClass_zero (ℓ : EdgeCocycle X A) : twoClass ℓ 0 = 0 := by
  simp only [twoClass, twoCocycle_zero, map_zero]

@[simp] theorem twoClass_add (ℓ : EdgeCocycle X A) (k l : IntegralTwoCocycle A) :
    twoClass ℓ (k + l) = twoClass ℓ k + twoClass ℓ l := by
  simp only [twoClass, twoCocycle_add, map_add]

@[simp] theorem twoClass_neg (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    twoClass ℓ (-k) = -twoClass ℓ k := by
  simp only [twoClass, twoCocycle_neg, map_neg]

/-- The actual cochain map acts on the literal cocycle representative. -/
@[simp] theorem twoCocycle_pullback (ℓ : EdgeCocycle Y A) (k : IntegralTwoCocycle A)
    (f : C(X, Y)) :
    mapCocycles (singularPullback f) 2 (twoCocycle ℓ k) =
      twoCocycle (ℓ.pullback f) k := by
  apply Subtype.ext
  rw [mapCocycles_val, twoCocycle_val, twoCocycle_val]
  exact twoCochain_pullback ℓ k f

/-- Naturality uses the native induced map on singular cohomology. -/
@[simp] theorem twoClass_pullback (ℓ : EdgeCocycle Y A) (k : IntegralTwoCocycle A)
    (f : C(X, Y)) :
    singularCohomologyPullback f 2 (twoClass ℓ k) = twoClass (ℓ.pullback f) k := by
  exact (homologyMap_cocycleClass (singularPullback f) 2 (twoCocycle ℓ k)).trans
    (congrArg (cocycleClass (singularCochainComplex X) 2) (twoCocycle_pullback ℓ k f))

@[simp] theorem twoCocycle_comap (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle B)
    (f : A →+ B) : twoCocycle ℓ (k.comap f) = twoCocycle (ℓ.map f) k := by
  apply Subtype.ext
  exact twoCochain_comap ℓ k f

/-- Changing the label group and pulling back its group cocycle give the same actual class. -/
@[simp] theorem twoClass_comap (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle B)
    (f : A →+ B) : twoClass ℓ (k.comap f) = twoClass (ℓ.map f) k := by
  simp only [twoClass, twoCocycle_comap]

/-- An integral group coboundary becomes an actual singular coboundary. -/
@[simp] theorem twoCocycle_coboundary (ℓ : EdgeCocycle X A) (b : A → ℤ) :
    twoCocycle ℓ (IntegralTwoCocycle.coboundary b) =
      coboundaryCocycle (singularCochainComplex X) 2 (oneCochain ℓ b) := by
  apply Subtype.ext
  exact twoCochain_coboundary ℓ b

@[simp] theorem twoClass_coboundary (ℓ : EdgeCocycle X A) (b : A → ℤ) :
    twoClass ℓ (IntegralTwoCocycle.coboundary b) = 0 := by
  rw [twoClass, twoCocycle_coboundary]
  exact cocycleClass_coboundary (singularCochainComplex X) 2 (oneCochain ℓ b)

/-- Adding any integral group coboundary leaves the actual singular class unchanged. -/
@[simp] theorem twoClass_add_coboundary (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A)
    (b : A → ℤ) :
    twoClass ℓ (k + IntegralTwoCocycle.coboundary b) = twoClass ℓ k := by
  rw [twoClass_add, twoClass_coboundary, add_zero]

/-- The pointwise coboundary-change convention gives equality of the actual classes. -/
theorem twoClass_eq_of_pointwise_coboundary (ℓ : EdgeCocycle X A)
    (k l : IntegralTwoCocycle A) (b : A → ℤ)
    (h : ∀ a c, k a c - l a c = b a + b c - b (a + c)) :
    twoClass ℓ k = twoClass ℓ l := by
  have hk : k = l + IntegralTwoCocycle.coboundary b := by
    apply IntegralTwoCocycle.ext
    intro a c
    change k a c = l a c + (b a + b c - b (a + c))
    calc
      k a c = (k a c - l a c) + l a c := (sub_add_cancel _ _).symm
      _ = l a c + (b a + b c - b (a + c)) := by rw [h, add_comm]
  rw [hk, twoClass_add_coboundary]

/-- Vanishing is equivalent to being an actual singular coboundary. -/
theorem twoClass_eq_zero_iff (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    twoClass ℓ k = 0 ↔ ∃ b : Chains X 1 →ₗ[ℤ] ℤ,
      ((singularCochainComplex X).d 1 2).hom b = twoCochain ℓ k :=
  cocycleClass_eq_zero_iff (singularCochainComplex X) 2 (twoCocycle ℓ k)

/-- Equality is measured in the actual singular cochain complex, with no replacement model. -/
theorem twoClass_eq_iff (ℓ μ : EdgeCocycle X A) (k l : IntegralTwoCocycle A) :
    twoClass ℓ k = twoClass μ l ↔ ∃ b : Chains X 1 →ₗ[ℤ] ℤ,
      ((singularCochainComplex X).d 1 2).hom b = twoCochain ℓ k - twoCochain μ l :=
  cocycleClass_eq_iff (singularCochainComplex X) 2 (twoCocycle ℓ k) (twoCocycle μ l)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle
