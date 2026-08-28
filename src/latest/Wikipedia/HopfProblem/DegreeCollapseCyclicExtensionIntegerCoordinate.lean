import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionExponentTwo
import Wikipedia.HopfProblem.DegreeCollapsePrimitiveIntegerCoordinate

/-!
# The primitive integral coordinate of the original exponent-two exterior

The coefficient of twice an exterior element is additive and defines an
integer coordinate taking the meridian to two and a half-meridian to one.
Its literal kernel consists exactly of the elements killed by two. The
original old quotient has twice that kernel's cardinality.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  (μ : G) (q : G →+ H) (hker : q.ker = AddSubgroup.zmultiples μ)
  (h2 : ∀ x : H, (2 : ℤ) • x = 0)

def doubleCoefficient (g : G) : ℤ := (exists_double_coefficient μ q hker h2 g).choose

theorem doubleCoefficient_spec (g : G) :
    doubleCoefficient μ q hker h2 g • μ = (2 : ℤ) • g :=
  (exists_double_coefficient μ q hker h2 g).choose_spec

variable (hμ : Injective (fun n : ℤ ↦ n • μ))

def doubleCoordinate : G →+ ℤ where
  toFun := doubleCoefficient μ q hker h2
  map_zero' := by
    apply hμ
    change doubleCoefficient μ q hker h2 0 • μ = (0 : ℤ) • μ
    rw [doubleCoefficient_spec, smul_zero, zero_zsmul]
  map_add' x y := by
    apply hμ
    change doubleCoefficient μ q hker h2 (x + y) • μ =
      (doubleCoefficient μ q hker h2 x + doubleCoefficient μ q hker h2 y) • μ
    rw [add_zsmul, doubleCoefficient_spec, doubleCoefficient_spec,
      doubleCoefficient_spec, smul_add]

theorem doubleCoordinate_spec (g : G) :
    doubleCoordinate μ q hker h2 hμ g • μ = (2 : ℤ) • g :=
  doubleCoefficient_spec μ q hker h2 g

theorem doubleCoordinate_meridian : doubleCoordinate μ q hker h2 hμ μ = 2 :=
  hμ (doubleCoordinate_spec μ q hker h2 hμ μ)

theorem doubleCoordinate_half (h : G) (hh : (2 : ℤ) • h = μ) :
    doubleCoordinate μ q hker h2 hμ h = 1 := by
  apply hμ
  change doubleCoordinate μ q hker h2 hμ h • μ = (1 : ℤ) • μ
  rw [doubleCoordinate_spec, hh, one_zsmul]

theorem doubleCoordinate_eq_zero_iff (g : G) :
    doubleCoordinate μ q hker h2 hμ g = 0 ↔ (2 : ℤ) • g = 0 := by
  constructor
  · intro hg
    rw [← doubleCoordinate_spec μ q hker h2 hμ g, hg, zero_zsmul]
  · intro hg
    apply hμ
    change doubleCoordinate μ q hker h2 hμ g • μ = (0 : ℤ) • μ
    rw [doubleCoordinate_spec, hg, zero_zsmul]

theorem doubleCoordinate_kernel_two (x : (doubleCoordinate μ q hker h2 hμ).ker) :
    (2 : ℤ) • x = 0 := by
  apply Subtype.ext
  exact (doubleCoordinate_eq_zero_iff μ q hker h2 hμ x.val).1 x.property

include h2 hμ in
theorem doubleCoordinate_kernel_card (hq : Surjective q) (h : G) (hh : (2 : ℤ) • h = μ) :
    Nat.card H = 2 * Nat.card (doubleCoordinate μ q hker h2 hμ).ker := by
  apply IntegerSplit.double_quotient_card (doubleCoordinate μ q hker h2 hμ) h
    (doubleCoordinate_half μ q hker h2 hμ h hh) q hq
  rw [hh]
  exact hker

theorem doubleCoordinate_kernel_finite [Finite H]
    (hq : Surjective q) (h : G) (hh : (2 : ℤ) • h = μ) :
    Finite (doubleCoordinate μ q hker h2 hμ).ker := by
  apply Nat.finite_of_card_ne_zero
  intro hz
  have he := doubleCoordinate_kernel_card μ q hker h2 hμ hq h hh
  rw [hz, mul_zero] at he
  exact Nat.card_pos.ne' he

end Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter
