import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionExponentTwo
import Wikipedia.HopfProblem.DegreeCollapseCyclicSurgeryIndex

/-!
# The two useful quotient cases after an even twist

If the meridian is twice an exterior element, killing a two-torsion
section leaves an infinite-order class. If twice the section is twice the
meridian, the same exterior element becomes a class of exact order four.
In the second case the old and new quotient cardinalities agree. These
facts use the actual quotient homomorphisms, not a classification of finite
abelian groups or a supplied group decomposition.
-/

noncomputable section

open Function AddSubgroup

namespace Wikipedia.HopfProblem.DegreeCollapse.ExponentTwoSurgeryQuotient

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
  (μ β h : G) (hμ : Injective (fun n : ℤ ↦ n • μ))
  (hh : (2 : ℤ) • h = μ) (r : G →+ K) (hr : r.ker = zmultiples β)

include hμ hh hr in
theorem infinite_order_of_double_section_zero (hβ : (2 : ℤ) • β = 0) :
    Injective (fun n : ℤ ↦ n • r h) := by
  intro a b hab
  change a • r h = b • r h at hab
  have hz : (a - b) • h ∈ r.ker := by
    change r ((a - b) • h) = 0
    rw [map_zsmul, sub_zsmul, hab]
    abel
  rw [hr] at hz
  obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hz
  have he : (a - b) • μ = (0 : ℤ) • μ := by
    calc
      (a - b) • μ = (2 : ℤ) • ((a - b) • h) := by rw [smul_comm, hh]
      _ = (2 : ℤ) • (k • β) := congrArg (fun x : G ↦ (2 : ℤ) • x) hk.symm
      _ = 0 := by rw [smul_comm, hβ, smul_zero]
      _ = (0 : ℤ) • μ := (zero_zsmul μ).symm
  have hn := hμ he
  omega

include hμ hh hr in
theorem order_four_of_double_section_eq_double_meridian
    (q : G →+ H) (hqμ : q μ = 0) (hqβ : q β ≠ 0)
    (hβ : (2 : ℤ) • β = (2 : ℤ) • μ) :
    (4 : ℤ) • r h = 0 ∧ (2 : ℤ) • r h ≠ 0 := by
  have hrβ : r β = 0 := by
    change β ∈ r.ker
    rw [hr]
    exact mem_zmultiples β
  constructor
  · calc
      (4 : ℤ) • r h = r ((2 : ℤ) • ((2 : ℤ) • h)) := by
        rw [map_zsmul, map_zsmul, ← mul_zsmul]
        norm_num
      _ = r ((2 : ℤ) • μ) := by rw [hh]
      _ = r ((2 : ℤ) • β) := congrArg r hβ.symm
      _ = 0 := by rw [map_zsmul, hrβ, smul_zero]
  · intro hz
    have hm : μ ∈ r.ker := by
      change r μ = 0
      rw [← hh, map_zsmul]
      exact hz
    rw [hr] at hm
    obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hm
    have he : (2 * k) • μ = (2 : ℤ) • μ := by
      calc
        (2 * k) • μ = k • ((2 : ℤ) • β) := by
          rw [hβ, ← mul_zsmul, mul_comm]
        _ = (2 : ℤ) • (k • β) := by rw [smul_comm]
        _ = (2 : ℤ) • μ := congrArg (fun x : G ↦ (2 : ℤ) • x) hk
    have hk1 : k = 1 := by have he' := hμ he; omega
    rw [hk1, one_zsmul] at hk
    exact hqβ ((congrArg q hk).trans hqμ)

include hμ hr in
theorem card_eq_of_double_section_eq_double_meridian
    (q : G →+ H) (hq : Surjective q) (hqker : q.ker = zmultiples μ)
    (hrsurj : Surjective r) (hβ : (2 : ℤ) • β = (2 : ℤ) • μ) :
    Nat.card K = Nat.card H := by
  have hrel : (2 : ℤ) • β + (-2 : ℤ) • μ = 0 := by
    rw [hβ, neg_zsmul, add_neg_cancel]
  have he := CyclicSurgeryIndex.relation_index β μ hμ 2 (-2) (by norm_num) hrel
  have hcq : (zmultiples μ).index = Nat.card H := by
    rw [← hqker]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective q hq).toEquiv
  have hcr : (zmultiples β).index = Nat.card K := by
    rw [← hr]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective r hrsurj).toEquiv
  rw [hcq, hcr] at he
  norm_num at he
  omega

end Wikipedia.HopfProblem.DegreeCollapse.ExponentTwoSurgeryQuotient
