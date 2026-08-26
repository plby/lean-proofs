import ErdosProblems.Erdos336.EndpointClassSumset
import ErdosProblems.Erdos336.ProjectionLargeFiber

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- A fixed integer fibre of one endpoint-quotient class has at most the
cardinality of the vertical part of the quotient subgroup. -/
theorem card_integerProjectionFiber_endpointClass_le
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)) (t : ℤ) :
    (integerProjectionFiber (endpointClassSlice T δ F z) t).card ≤
      (addSubgroupFinset (endpointVerticalPart δ F)).card := by
  classical
  let X := endpointClassSlice T δ F z
  let Xt := integerProjectionFiber X t
  let K := endpointVerticalPart δ F
  let Kfin := addSubgroupFinset K
  by_cases hXt : Xt.Nonempty
  · let x₀ : ℤ × H := hXt.choose
    have hx₀ : x₀ ∈ Xt := hXt.choose_spec
    have hx₀X : x₀ ∈ X := (mem_integerProjectionFiber.mp hx₀).1
    have hx₀fst : x₀.1 = t := (mem_integerProjectionFiber.mp hx₀).2
    let e : ↥Xt → ↥Kfin := fun x => ⟨x.1.2 - x₀.2, by
      apply (mem_addSubgroupFinset K _).mpr
      change verticalEndpointHom δ (x.1.2 - x₀.2) ∈ F
      have hxX : x.1 ∈ X := (mem_integerProjectionFiber.mp x.2).1
      have hxfst : x.1.1 = t := (mem_integerProjectionFiber.mp x.2).2
      have hclassx := (mem_endpointClassSlice.mp hxX).2
      have hclass0 := (mem_endpointClassSlice.mp hx₀X).2
      have hsub :
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) x.1 -
              (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) x₀ ∈ F :=
        (QuotientAddGroup.eq_iff_sub_mem).mp (hclassx.trans hclass0.symm)
      rw [← map_sub] at hsub
      convert hsub using 1
      apply congrArg (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ))
      apply Prod.ext
      · simp [hxfst, hx₀fst]
      · rfl⟩
    have he : Function.Injective e := by
      intro x y hxy
      apply Subtype.ext
      apply Prod.ext
      · rw [(mem_integerProjectionFiber.mp x.2).2,
          (mem_integerProjectionFiber.mp y.2).2]
      · have hs := congrArg (fun u : ↥Kfin => u.1) hxy
        exact sub_left_injective hs
    have hc := Fintype.card_le_of_injective e he
    change Xt.card ≤ Kfin.card
    simpa only [Fintype.card_coe] using hc
  · have hempty : Xt = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXt
    change Xt.card ≤ Kfin.card
    simp [hempty]

/-- Consequently a whole endpoint class is bounded by its number of occupied
integer fibres times the vertical fibre cardinality. -/
theorem card_endpointClassSlice_le_projection_mul_vertical
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F)) :
    (endpointClassSlice T δ F z).card ≤
      ((endpointClassSlice T δ F z).image Prod.fst).card *
        (addSubgroupFinset (endpointVerticalPart δ F)).card := by
  classical
  let X := endpointClassSlice T δ F z
  let P := X.image Prod.fst
  let k := (addSubgroupFinset (endpointVerticalPart δ F)).card
  have hpartition : X.card =
      ∑ t ∈ P, (integerProjectionFiber X t).card := by
    simpa [P, integerProjectionFiber] using
      (Finset.card_eq_sum_card_image Prod.fst X)
  rw [hpartition]
  calc
    (∑ t ∈ P, (integerProjectionFiber X t).card) ≤ ∑ _t ∈ P, k := by
      apply Finset.sum_le_sum
      intro t ht
      exact card_integerProjectionFiber_endpointClass_le T δ F z t
    _ = P.card * k := by simp

/-- The vertical-part cardinal divides the cardinal of a finite endpoint
quotient subgroup. -/
theorem card_endpointVerticalPart_dvd
    (δ : ℤ × H) (hδpos : 0 < δ.1)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFmem : ∀ x, x ∈ Ffin ↔ x ∈ F) :
    (addSubgroupFinset (endpointVerticalPart δ F)).card ∣ Ffin.card := by
  classical
  let K := endpointVerticalPart δ F
  let M := K.map (verticalEndpointHom δ)
  have hMle : M ≤ F := by
    intro y hy
    obtain ⟨x, hxK, rfl⟩ := hy
    exact hxK
  have hdvd : Nat.card M ∣ Nat.card F := AddSubgroup.card_dvd_of_le hMle
  have hKM : Nat.card K = Nat.card M :=
    Nat.card_congr (AddSubgroup.equivMapOfInjective K (verticalEndpointHom δ)
      (verticalEndpointHom_injective δ hδpos)).toEquiv
  have hKcard : Nat.card K = (addSubgroupFinset K).card := by
    let hmem : ∀ x : H, x ∈ addSubgroupFinset K ↔ x ∈ K :=
      fun x => mem_addSubgroupFinset K x
    letI : Fintype K := Fintype.ofFinset (addSubgroupFinset K) hmem
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset (addSubgroupFinset K) hmem
  have hFcard : Nat.card F = Ffin.card := by
    letI : Fintype F := Fintype.ofFinset Ffin hFmem
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset Ffin hFmem
  change (addSubgroupFinset K).card ∣ Ffin.card
  rw [← hKcard, hKM, ← hFcard]
  exact hdvd

/-- In a strip of endpoint width `l`, one quotient-subgroup class can
occupy at most one more integer fibre than the index of its vertical part.
The division-free cardinal form is `(n-1)|K| ≤ |F|`. -/
theorem projection_sub_one_mul_vertical_le_endpoint_subgroup
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l) (δ : ℤ × H)
    (hδfst : δ.1 = l)
    (hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFmem : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (z : (((ℤ × H) ⧸ AddSubgroup.zmultiples δ) ⧸ F))
    (hXne : (endpointClassSlice T δ F z).Nonempty) :
    (((endpointClassSlice T δ F z).image Prod.fst).card - 1) *
      (addSubgroupFinset (endpointVerticalPart δ F)).card ≤ Ffin.card := by
  classical
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ AddSubgroup.zmultiples δ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)
  let X := endpointClassSlice T δ F z
  let P := X.image Prod.fst
  let P0 := P.erase l
  let K := endpointVerticalPart δ F
  let Kfin := addSubgroupFinset K
  let x₀ : ℤ × H := hXne.choose
  have hx₀X : x₀ ∈ X := hXne.choose_spec
  let rep : ↥P0 → ℤ × H := fun u =>
    (Finset.mem_image.mp (Finset.mem_erase.mp u.2).2).choose
  have hrepX (u : ↥P0) : rep u ∈ X :=
    (Finset.mem_image.mp (Finset.mem_erase.mp u.2).2).choose_spec.1
  have hrepfst (u : ↥P0) : (rep u).1 = u.1 :=
    (Finset.mem_image.mp (Finset.mem_erase.mp u.2).2).choose_spec.2
  have hdiffF (u : ↥P0) : q (rep u) - q x₀ ∈ F := by
    apply (QuotientAddGroup.eq_iff_sub_mem).mp
    exact (mem_endpointClassSlice.mp (hrepX u)).2.trans
      (mem_endpointClassSlice.mp hx₀X).2.symm
  let e : (↥P0 × ↥Kfin) → ↥Ffin := fun u =>
    ⟨q (rep u.1) - q x₀ + verticalEndpointHom δ u.2.1,
      (hFmem _).mpr (F.add_mem (hdiffF u.1)
        ((mem_addSubgroupFinset K u.2.1).mp u.2.2))⟩
  have he : Function.Injective e := by
    rintro ⟨u, k⟩ ⟨v, j⟩ huv
    have hval := congrArg (fun w : ↥Ffin => w.1) huv
    have heq : q (rep u + (0, k.1)) = q (rep v + (0, j.1)) := by
      dsimp [e] at hval
      rw [q.map_add, q.map_add]
      change q (rep u) + verticalEndpointHom δ k.1 =
        q (rep v) + verticalEndpointHom δ j.1
      calc
        q (rep u) + verticalEndpointHom δ k.1 =
            (q (rep u) - q x₀ + verticalEndpointHom δ k.1) + q x₀ := by abel
        _ = (q (rep v) - q x₀ + verticalEndpointHom δ j.1) + q x₀ :=
          congrArg (fun w => w + q x₀) hval
        _ = q (rep v) + verticalEndpointHom δ j.1 := by abel
    have hmem : (rep u + (0, k.1)) - (rep v + (0, j.1)) ∈
        AddSubgroup.zmultiples δ :=
      (QuotientAddGroup.eq_iff_sub_mem).mp heq
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hfirst := congrArg Prod.fst hm
    have huT : rep u ∈ T := (mem_endpointClassSlice.mp (hrepX u)).1
    have hvT : rep v ∈ T := (mem_endpointClassSlice.mp (hrepX v)).1
    have hub := hbounds (rep u) huT
    have hvb := hbounds (rep v) hvT
    have hul : (u.1 : ℤ) ≠ l := (Finset.mem_erase.mp u.2).1
    have hvl : (v.1 : ℤ) ≠ l := (Finset.mem_erase.mp v.2).1
    have hu0 : 0 ≤ (u.1 : ℤ) := by rw [← hrepfst u]; exact hub.1
    have hv0 : 0 ≤ (v.1 : ℤ) := by rw [← hrepfst v]; exact hvb.1
    have hule : (u.1 : ℤ) ≤ l := by rw [← hrepfst u]; exact hub.2
    have hvle : (v.1 : ℤ) ≤ l := by rw [← hrepfst v]; exact hvb.2
    have humax : (u.1 : ℤ) < l := lt_of_le_of_ne hule hul
    have hvmax : (v.1 : ℤ) < l := lt_of_le_of_ne hvle hvl
    have hfirst' : m * l = (u.1 : ℤ) - (v.1 : ℤ) := by
      simpa [hδfst, hrepfst] using hfirst
    have hm0 : m = 0 := by
      by_contra hm
      rcases lt_or_gt_of_ne hm with hmneg | hmpos
      · have hm1 : m + 1 ≤ 0 := by omega
        have hp := mul_nonpos_of_nonpos_of_nonneg hm1 hlpos.le
        have hml : m * l ≤ -l := by nlinarith
        nlinarith
      · have hm1 : 0 ≤ m - 1 := by omega
        have hp := mul_nonneg hm1 hlpos.le
        have hml : l ≤ m * l := by nlinarith
        nlinarith
    have huv' : u = v := by
      apply Subtype.ext
      nlinarith [hfirst']
    subst v
    have hkj : k.1 = j.1 := by
      apply verticalEndpointHom_injective δ (by simpa [hδfst] using hlpos)
      dsimp [e] at hval
      exact add_left_cancel hval
    exact Prod.ext rfl (Subtype.ext hkj)
  have hc := Fintype.card_le_of_injective e he
  have hc' : P0.card * Kfin.card ≤ Ffin.card := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using hc
  have hP : P.card - 1 ≤ P0.card := by
    by_cases hlP : l ∈ P
    · rw [Finset.card_erase_of_mem hlP]
    · simp [P0, hlP]
  have hmul := Nat.mul_le_mul_right Kfin.card hP
  change (P.card - 1) * Kfin.card ≤ Ffin.card
  exact le_trans hmul hc'

end Erdos336
