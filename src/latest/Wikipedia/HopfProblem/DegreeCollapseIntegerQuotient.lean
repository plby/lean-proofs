import Wikipedia.HopfProblem.DegreeCollapsePrimitiveIntegerCoordinate

/-!
# Descend an integer coordinate through an original quotient map

The coordinate descends through a surjection whose kernel it kills.
The restriction to coordinate kernels is itself surjective, with the
same original kernel. This gives the exact complement-cardinality
formula and transfers exponent-two torsion through the genuine map.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegerQuotient

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]
  (σ : G →+ ℤ) (r : G →+ K) (hr : Surjective r) (hker : r.ker ≤ σ.ker)

def descend : K →+ ℤ :=
  (QuotientAddGroup.lift r.ker σ hker).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective r hr).symm.toAddMonoidHom

theorem descend_apply (g : G) : descend σ r hr hker (r g) = σ g := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective r hr
  have he : e (QuotientAddGroup.mk g) = r g := rfl
  change QuotientAddGroup.lift r.ker σ hker (e.symm (r g)) = σ g
  rw [← he, e.symm_apply_apply]
  rfl

def kernelMap : σ.ker →+ (descend σ r hr hker).ker where
  toFun g := ⟨r g.val, by
    change descend σ r hr hker (r g.val) = 0
    rw [descend_apply]
    exact g.property⟩
  map_zero' := by
    apply Subtype.ext
    exact r.map_zero
  map_add' x y := by
    apply Subtype.ext
    exact r.map_add x.val y.val

theorem kernelMap_apply (g : σ.ker) : (kernelMap σ r hr hker g).val = r g.val := rfl

theorem kernelMap_surjective : Surjective (kernelMap σ r hr hker) := by
  intro y
  obtain ⟨g, hg⟩ := hr y.val
  have hσg : σ g = 0 := by
    rw [← descend_apply σ r hr hker g, hg]
    exact y.property
  exact ⟨⟨g, hσg⟩, Subtype.ext hg⟩

def kernelEquiv : (kernelMap σ r hr hker).ker ≃+ r.ker where
  toFun x := ⟨x.val.val, by
    have hx := congrArg Subtype.val x.property
    exact hx⟩
  invFun y := ⟨⟨y.val, hker y.property⟩, Subtype.ext y.property⟩
  left_inv x := by rfl
  right_inv y := by rfl
  map_add' x y := by rfl

theorem kernel_card : Nat.card σ.ker =
    Nat.card r.ker * Nat.card (descend σ r hr hker).ker := by
  have hi := (kernelMap σ r hr hker).ker.card_mul_index
  have hc : Nat.card (kernelMap σ r hr hker).ker = Nat.card r.ker :=
    Nat.card_congr (kernelEquiv σ r hr hker).toEquiv
  have hq : (kernelMap σ r hr hker).ker.index = Nat.card (descend σ r hr hker).ker :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (kernelMap σ r hr hker) (kernelMap_surjective σ r hr hker)).toEquiv
  rw [hc, hq] at hi
  exact hi.symm

theorem kernel_finite [Finite σ.ker] : Finite (descend σ r hr hker).ker :=
  Finite.of_surjective (kernelMap σ r hr hker) (kernelMap_surjective σ r hr hker)

theorem kernel_two (h2 : ∀ x : σ.ker, (2 : ℤ) • x = 0)
    (y : (descend σ r hr hker).ker) : (2 : ℤ) • y = 0 := by
  obtain ⟨x, rfl⟩ := kernelMap_surjective σ r hr hker y
  rw [← map_zsmul, h2, map_zero]

end Wikipedia.HopfProblem.DegreeCollapse.IntegerQuotient
