import ErdosProblems.Erdos336.EndpointCyclicQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Embed the vertical finite group into the endpoint quotient. -/
def verticalEndpointHom (δ : ℤ × H) :
    H →+ ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)).comp
    { toFun := fun k => (0, k)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp] theorem verticalEndpointHom_apply (δ : ℤ × H) (k : H) :
    verticalEndpointHom δ k =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) (0, k) := rfl

/-- A non-torsion endpoint displacement makes the vertical embedding injective. -/
theorem verticalEndpointHom_injective
    (δ : ℤ × H) (hδpos : 0 < δ.1) :
    Function.Injective (verticalEndpointHom δ) := by
  intro a b hab
  have hmem : (((0 : ℤ), a) - ((0 : ℤ), b)) ∈
      AddSubgroup.zmultiples δ := by
    apply (QuotientAddGroup.eq_iff_sub_mem).mp
    exact hab
  obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hfirst := congrArg Prod.fst ht
  change t * δ.1 = 0 at hfirst
  have ht0 : t = 0 := by nlinarith
  have hsecond := congrArg Prod.snd ht
  rw [ht0] at hsecond
  simp only [zero_zsmul, Prod.snd_zero, Prod.snd_sub] at hsecond
  exact sub_eq_zero.mp hsecond.symm

/-- Vertical intersection of an endpoint-quotient subgroup. -/
def endpointVerticalPart
    (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ)) : AddSubgroup H :=
  F.comap (verticalEndpointHom δ)

/-- The vertical part occupies at most half of a finite quotient subgroup as
soon as that subgroup has a nonvertical element. -/
theorem twice_card_endpointVerticalPart_le
    (δ : ℤ × H) (hδpos : 0 < δ.1)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFfin : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (hnonvertical : ∃ f ∈ Ffin,
      ∀ k : H, verticalEndpointHom δ k ≠ f) :
    2 * (addSubgroupFinset (endpointVerticalPart δ F)).card ≤ Ffin.card := by
  classical
  let K := endpointVerticalPart δ F
  let Kfin := addSubgroupFinset K
  obtain ⟨f, hfF, hfnot⟩ := hnonvertical
  have hKtoF (k : H) (hk : k ∈ Kfin) : verticalEndpointHom δ k ∈ F := by
    have hkK : k ∈ K := by
      exact (mem_addSubgroupFinset K k).mp hk
    exact hkK
  let D := Bool × ↥Kfin
  let e : D → ↥Ffin := fun u =>
    if u.1 then
      ⟨f + verticalEndpointHom δ u.2.1, (hFfin _).mpr
        (F.add_mem ((hFfin f).mp hfF) (hKtoF u.2.1 u.2.2))⟩
    else
      ⟨verticalEndpointHom δ u.2.1, (hFfin _).mpr
        (hKtoF u.2.1 u.2.2)⟩
  have he : Function.Injective e := by
    intro u v huv
    have hval := congrArg (fun x : ↥Ffin => x.1) huv
    by_cases hu : u.1 = true <;> by_cases hv : v.1 = true
    · have huBool : u.1 = v.1 := hu.trans hv.symm
      have hveq : verticalEndpointHom δ u.2.1 =
          verticalEndpointHom δ v.2.1 := by
        apply add_left_cancel (a := f)
        simpa [e, hu, hv] using hval
      have hk : u.2.1 = v.2.1 :=
        (verticalEndpointHom_injective δ hδpos) hveq
      exact Prod.ext huBool (Subtype.ext hk)
    · have hvfalse : v.1 = false := Bool.eq_false_of_not_eq_true hv
      have hcross : f + verticalEndpointHom δ u.2.1 =
          verticalEndpointHom δ v.2.1 := by
        simpa [e, hu, hvfalse] using hval
      have hfEq : f = verticalEndpointHom δ (v.2.1 - u.2.1) := by
        rw [map_sub]
        apply add_right_cancel (b := verticalEndpointHom δ u.2.1)
        simpa [hcross] using hcross
      exact (hfnot (v.2.1 - u.2.1) hfEq.symm).elim
    · have hufalse : u.1 = false := Bool.eq_false_of_not_eq_true hu
      have hcross : verticalEndpointHom δ u.2.1 =
          f + verticalEndpointHom δ v.2.1 := by
        simpa [e, hufalse, hv] using hval
      have hfEq : f = verticalEndpointHom δ (u.2.1 - v.2.1) := by
        rw [map_sub]
        apply add_right_cancel (b := verticalEndpointHom δ v.2.1)
        simpa [hcross] using hcross.symm
      exact (hfnot (u.2.1 - v.2.1) hfEq.symm).elim
    · have hufalse : u.1 = false := Bool.eq_false_of_not_eq_true hu
      have hvfalse : v.1 = false := Bool.eq_false_of_not_eq_true hv
      have huBool : u.1 = v.1 := hufalse.trans hvfalse.symm
      have hveq : verticalEndpointHom δ u.2.1 =
          verticalEndpointHom δ v.2.1 := by
        simpa [e, hufalse, hvfalse] using hval
      have hk : u.2.1 = v.2.1 :=
        (verticalEndpointHom_injective δ hδpos) hveq
      exact Prod.ext huBool (Subtype.ext hk)
  have hc := Fintype.card_le_of_injective e he
  change Fintype.card (Bool × ↥Kfin) ≤ Fintype.card ↥Ffin at hc
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe,
    Fintype.card_coe] at hc
  simpa [Kfin, K] using hc

end Erdos336
