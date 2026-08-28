import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionIntegerCoordinate
import Wikipedia.HopfProblem.DegreeCollapseIntegerQuotient

/-!
# The exceptional free quotient has a primitive generator and one-quarter torsion

For the original exponent-two cyclic extension, suppose the meridian is
twice h and the section killed by the new quotient is a nonzero element
of order two. The new quotient has an explicit integer coordinate taking
the original image of h to one. Its finite kernel is killed by two and has
one quarter of the old quotient's cardinality.
-/

noncomputable section

open Function AddSubgroup

namespace Wikipedia.HopfProblem.DegreeCollapse.ExponentTwoFreeQuotient

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]

theorem cyclic_two_card (β : G) (hβ : (2 : ℤ) • β = 0) (hne : β ≠ 0) :
    Nat.card (zmultiples β) = 2 := by
  rw [Nat.card_zmultiples]
  apply addOrderOf_eq_prime
  · simpa only [two_zsmul, two_nsmul] using hβ
  · exact hne

theorem kernel_le_of_two_section (σ : G →+ ℤ) (r : G →+ K) (β : G)
    (hrker : r.ker = zmultiples β) (hβ : (2 : ℤ) • β = 0) : r.ker ≤ σ.ker := by
  have hσβ : σ β = 0 := by
    have he := congrArg σ hβ
    simp only [map_zsmul, map_zero, zsmul_eq_mul, Int.cast_ofNat] at he
    omega
  intro g hg
  rw [hrker] at hg
  obtain ⟨n, rfl⟩ := mem_zmultiples_iff.mp hg
  change σ (n • β) = 0
  rw [map_zsmul, hσβ, smul_zero]

theorem primitive_free_part [Finite H]
    (μ : G) (q : G →+ H) (hqker : q.ker = zmultiples μ)
    (h2 : ∀ x : H, (2 : ℤ) • x = 0)
    (hμ : Injective (fun n : ℤ ↦ n • μ)) (hq : Surjective q)
    (h : G) (hh : (2 : ℤ) • h = μ)
    (β : G) (hβ : (2 : ℤ) • β = 0) (hβne : β ≠ 0)
    (r : G →+ K) (hr : Surjective r) (hrker : r.ker = zmultiples β) :
    ∃ σ : K →+ ℤ, σ (r h) = 1 ∧ Finite σ.ker ∧
      (∀ x : σ.ker, (2 : ℤ) • x = 0) ∧ 4 * Nat.card σ.ker = Nat.card H := by
  let τ := CyclicExtensionCharacter.doubleCoordinate μ q hqker h2 hμ
  have hτh : τ h = 1 :=
    CyclicExtensionCharacter.doubleCoordinate_half μ q hqker h2 hμ h hh
  have hker : r.ker ≤ τ.ker := kernel_le_of_two_section τ r β hrker hβ
  let σ := IntegerQuotient.descend τ r hr hker
  let : Finite τ.ker :=
    CyclicExtensionCharacter.doubleCoordinate_kernel_finite μ q hqker h2 hμ hq h hh
  have hσh : σ (r h) = 1 := (IntegerQuotient.descend_apply τ r hr hker h).trans hτh
  have hfinite : Finite σ.ker := IntegerQuotient.kernel_finite τ r hr hker
  have hσ2 : ∀ x : σ.ker, (2 : ℤ) • x = 0 :=
    IntegerQuotient.kernel_two τ r hr hker
      (CyclicExtensionCharacter.doubleCoordinate_kernel_two μ q hqker h2 hμ)
  refine ⟨σ, hσh, hfinite, hσ2, ?_⟩
  have he := CyclicExtensionCharacter.doubleCoordinate_kernel_card μ q hqker h2 hμ hq h hh
  have hk : Nat.card τ.ker = 2 * Nat.card σ.ker := by
    have hk := IntegerQuotient.kernel_card τ r hr hker
    rw [hrker, cyclic_two_card β hβ hβne] at hk
    exact hk
  change Nat.card H = 2 * Nat.card τ.ker at he
  rw [hk] at he
  omega

theorem torsion_iff_kernel (σ : K →+ ℤ)
    (h2 : ∀ x : σ.ker, (2 : ℤ) • x = 0) (x : K) :
    (∃ n : ℤ, n ≠ 0 ∧ n • x = 0) ↔ σ x = 0 := by
  constructor
  · rintro ⟨n, hn, hx⟩
    have he := congrArg σ hx
    simp only [map_zsmul, map_zero, zsmul_eq_mul, Int.cast_id] at he
    exact (mul_eq_zero.mp he).resolve_left hn
  · intro hx
    refine ⟨2, by norm_num, ?_⟩
    exact congrArg Subtype.val (h2 ⟨x, hx⟩)

end Wikipedia.HopfProblem.DegreeCollapse.ExponentTwoFreeQuotient
