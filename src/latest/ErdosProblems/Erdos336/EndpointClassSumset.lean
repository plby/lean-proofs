import ErdosProblems.Erdos336.EndpointVerticalIntersection
import ErdosProblems.Erdos336.VerticalStabilizer

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The pullback to the original strip of one class modulo an endpoint
quotient subgroup. -/
noncomputable def endpointClassSlice
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)) :
    Finset (ℤ × H) := by
  classical
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let r := QuotientAddGroup.mk' F
  exact T.filter fun x => r (q x) = z

/-- The corresponding class in the endpoint quotient. -/
noncomputable def endpointClassInImage
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)) :
    Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) := by
  classical
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let r := QuotientAddGroup.mk' F
  exact (T.image q).filter fun b => r b = z

@[simp] theorem mem_endpointClassSlice
    {T : Finset (ℤ × H)} {δ : ℤ × H}
    {F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ)}
    {z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)} {x : ℤ × H} :
    x ∈ endpointClassSlice T δ F z ↔
      x ∈ T ∧ (QuotientAddGroup.mk' F)
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) x) = z := by
  classical
  simp [endpointClassSlice]

/-- Quotient-class occupancy cannot exceed the number of original strip
points above that class. -/
theorem card_endpointClassInImage_le_slice
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)) :
    (endpointClassInImage T δ F z).card ≤
      (endpointClassSlice T δ F z).card := by
  classical
  let q : (ℤ × H) →+
      ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let r := QuotientAddGroup.mk' F
  have heq : (endpointClassSlice T δ F z).image q =
      endpointClassInImage T δ F z := by
    ext b
    constructor
    · intro hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      have hx' := mem_endpointClassSlice.mp hx
      change q x ∈ (T.image q).filter fun b => r b = z
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨x, hx'.1, rfl⟩, hx'.2⟩
    · intro hb
      have hb' : b ∈ T.image q ∧ r b = z := by
        simpa [endpointClassInImage, q, r] using hb
      obtain ⟨x, hxT, hxb⟩ := Finset.mem_image.mp hb'.1
      apply Finset.mem_image.mpr
      refine ⟨x, mem_endpointClassSlice.mpr ⟨hxT, ?_⟩, hxb⟩
      rw [hxb]
      exact hb'.2
  rw [← heq]
  exact Finset.card_image_le

/-- Two original quotient-class slices have the Kneser lower bound with the
vertical intersection of the endpoint subgroup. -/
theorem card_add_endpointClassSlices_ge
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z w : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F))
    (hzne : (endpointClassSlice T δ F z).Nonempty)
    (hwne : (endpointClassSlice T δ F w).Nonempty) :
    (endpointClassSlice T δ F z).card +
        (endpointClassSlice T δ F w).card -
      (addSubgroupFinset (endpointVerticalPart δ F)).card ≤
    (endpointClassSlice T δ F z + endpointClassSlice T δ F w).card := by
  classical
  let X := endpointClassSlice T δ F z
  let Y := endpointClassSlice T δ F w
  let S := X + Y
  let K := verticalStabilizer S
  let V := verticalSubgroupFinset K
  have hs_nonempty : S.Nonempty := hzne.add hwne
  have hKle : K ≤ endpointVerticalPart δ F := by
    intro k hk
    obtain ⟨s, hs⟩ := hzne.add hwne
    have hkstab : ((0 : ℤ), k) ∈ S.addStab := by
      have hiff : k ∈ verticalStabilizer S ↔ ((0 : ℤ), k) ∈ S.addStab :=
        mem_verticalStabilizer (S := S) (by exact hs_nonempty)
      exact hiff.mp (show k ∈ verticalStabilizer S from hk)
    have hshift : ((0 : ℤ), k) + s ∈ S := by
      have hact : ∀ ⦃b : ℤ × H⦄, b ∈ S → ((0 : ℤ), k) +ᵥ b ∈ S :=
        (Finset.mem_addStab' (s := S) (by exact hs_nonempty)).mp hkstab
      simpa [vadd_eq_add] using hact hs
    have hclass (u : ℤ × H) (hu : u ∈ S) :
        (QuotientAddGroup.mk' F)
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) u) = z + w := by
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hu
      rw [map_add, map_add,
        (mem_endpointClassSlice.mp hx).2,
        (mem_endpointClassSlice.mp hy).2]
    have hsclass := hclass s hs
    have hshiftclass := hclass (((0 : ℤ), k) + s) hshift
    change (verticalEndpointHom δ k) ∈ F
    apply (QuotientAddGroup.eq_zero_iff (verticalEndpointHom δ k)).mp
    let r : ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) →+
        (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F) :=
      QuotientAddGroup.mk' F
    let q : (ℤ × H) →+
        ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
    change r (verticalEndpointHom δ k) = 0
    have heq : r (verticalEndpointHom δ k) + r (q s) = r (q s) := by
      calc
        r (verticalEndpointHom δ k) + r (q s) =
            r (q (((0 : ℤ), k) + s)) := by
              rw [q.map_add, r.map_add, verticalEndpointHom_apply]
        _ = z + w := hshiftclass
        _ = r (q s) := hsclass.symm
    have hsub := congrArg (fun u => u - r (q s)) heq
    simpa using hsub
  have hKcard : (addSubgroupFinset K).card ≤
      (addSubgroupFinset (endpointVerticalPart δ F)).card := by
    exact Finset.card_le_card (fun k hk =>
      (mem_addSubgroupFinset _ _).mpr
        (hKle ((mem_addSubgroupFinset _ _).mp hk)))
  have hstab : S.addStab = V := addStab_eq_verticalSubgroupFinset S hs_nonempty
  have hkneser := Finset.add_kneser X Y
  change (X + S.addStab).card + (Y + S.addStab).card ≤
    S.card + S.addStab.card at hkneser
  rw [hstab, card_verticalSubgroupFinset] at hkneser
  have hzeroV : 0 ∈ V := by
    exact mem_verticalSubgroupFinset.mpr ⟨rfl, K.zero_mem⟩
  have hXsub : X ⊆ X + V := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroV, by simp⟩
  have hYsub : Y ⊆ Y + V := by
    intro y hy
    exact Finset.mem_add.mpr ⟨y, hy, 0, hzeroV, by simp⟩
  have hXcard := Finset.card_le_card hXsub
  have hYcard := Finset.card_le_card hYsub
  change X.card + Y.card -
      (addSubgroupFinset (endpointVerticalPart δ F)).card ≤ S.card
  omega

end Erdos336
