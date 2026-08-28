import Wikipedia.HopfProblem.DegreeCollapseCyclicSurgeryIndex

/-!
# A marked primitive integer coordinate and its finite complement

A specified integer homomorphism taking a specified element to one splits
the original abelian group. Its complement projection has kernel exactly
the multiples of that element. The original quotient by twice that element
therefore has twice the complement's cardinality. No classification or
chosen basis of a finitely generated abelian group is used.
-/

noncomputable section

open Function AddSubgroup

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegerSplit

variable {G : Type*} [AddCommGroup G] (σ : G →+ ℤ) (h : G) (hσh : σ h = 1)

include hσh in
theorem coefficient_injective : Injective (fun n : ℤ ↦ n • h) := by
  intro a b he
  have he' := congrArg σ he
  simpa only [map_zsmul, hσh, zsmul_eq_mul, Int.cast_id, mul_one] using he'

def projection : G →+ σ.ker where
  toFun g := ⟨g - σ g • h, by
    change σ (g - σ g • h) = 0
    rw [map_sub, map_zsmul, hσh, zsmul_eq_mul, Int.cast_id, mul_one, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    change (0 : G) - σ 0 • h = 0
    rw [map_zero, zero_zsmul, sub_self]
  map_add' x y := by
    apply Subtype.ext
    change x + y - σ (x + y) • h = (x - σ x • h) + (y - σ y • h)
    rw [map_add, add_zsmul]
    abel

theorem projection_apply (g : G) : (projection σ h hσh g).val = g - σ g • h := rfl

theorem projection_surjective : Surjective (projection σ h hσh) := by
  intro t
  refine ⟨t.val, Subtype.ext ?_⟩
  change t.val - σ t.val • h = t.val
  rw [show σ t.val = 0 from t.property, zero_zsmul, sub_zero]

theorem projection_kernel : (projection σ h hσh).ker = zmultiples h := by
  ext g
  constructor
  · intro hg
    have he := congrArg Subtype.val (show projection σ h hσh g = 0 from hg)
    change g - σ g • h = 0 at he
    exact mem_zmultiples_iff.mpr ⟨σ g, (sub_eq_zero.mp he).symm⟩
  · intro hg
    obtain ⟨n, rfl⟩ := mem_zmultiples_iff.mp hg
    change projection σ h hσh (n • h) = 0
    apply Subtype.ext
    change n • h - σ (n • h) • h = 0
    rw [map_zsmul, hσh, zsmul_eq_mul, Int.cast_id, mul_one, sub_self]

def equiv : G ≃+ ℤ × σ.ker where
  toFun g := (σ g, projection σ h hσh g)
  invFun p := p.1 • h + p.2.val
  left_inv g := by
    change σ g • h + (g - σ g • h) = g
    abel
  right_inv p := by
    apply Prod.ext
    · change σ (p.1 • h + p.2.val) = p.1
      rw [map_add, map_zsmul, hσh, zsmul_eq_mul, Int.cast_id, mul_one,
        show σ p.2.val = 0 from p.2.property, add_zero]
    · apply Subtype.ext
      change p.1 • h + p.2.val - σ (p.1 • h + p.2.val) • h = p.2.val
      rw [map_add, map_zsmul, hσh, zsmul_eq_mul, Int.cast_id, mul_one,
        show σ p.2.val = 0 from p.2.property, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact σ.map_add x y
    · exact (projection σ h hσh).map_add x y

theorem equiv_apply (g : G) : equiv σ h hσh g = (σ g, projection σ h hσh g) := rfl

include hσh in
theorem complement_card : Nat.card σ.ker = (zmultiples h).index := by
  rw [← projection_kernel σ h hσh]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
    (projection σ h hσh) (projection_surjective σ h hσh)).toEquiv).symm

include hσh in
theorem double_quotient_card {H : Type*} [AddCommGroup H]
    (q : G →+ H) (hq : Surjective q) (hqker : q.ker = zmultiples ((2 : ℤ) • h)) :
    Nat.card H = 2 * Nat.card σ.ker := by
  have hcard : Nat.card H = (zmultiples ((2 : ℤ) • h)).index := by
    rw [← hqker]
    exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective q hq).toEquiv).symm
  rw [hcard, CyclicSurgeryIndex.multiple_index h (coefficient_injective σ h hσh) 2,
    ← complement_card σ h hσh]
  norm_num

end Wikipedia.HopfProblem.DegreeCollapse.IntegerSplit
