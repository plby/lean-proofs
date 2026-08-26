import ErdosProblems.Erdos336.EndpointVerticalIntersection
import ErdosProblems.Erdos336.PrimitiveEndpointQuotientSmall

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- If every element of an endpoint subgroup is vertical, its vertical part
has exactly the same cardinality. -/
theorem card_endpointVerticalPart_eq_of_full
    (δ : ℤ × H) (hδpos : 0 < δ.1)
    (F : AddSubgroup ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (Ffin : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hFfin : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (hfull : ∀ f ∈ Ffin, ∃ k : H, verticalEndpointHom δ k = f) :
    (addSubgroupFinset (endpointVerticalPart δ F)).card = Ffin.card := by
  classical
  let K := endpointVerticalPart δ F
  let Kfin := addSubgroupFinset K
  have hKtoF (k : H) (hk : k ∈ Kfin) : verticalEndpointHom δ k ∈ F := by
    have hkK : k ∈ K := (mem_addSubgroupFinset K k).mp hk
    exact hkK
  let e : ↥Kfin → ↥Ffin := fun k =>
    ⟨verticalEndpointHom δ k.1, (hFfin _).mpr (hKtoF k.1 k.2)⟩
  have heinj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply verticalEndpointHom_injective δ hδpos
    exact congrArg (fun x : ↥Ffin => x.1) hab
  have hesurj : Function.Surjective e := by
    intro f
    obtain ⟨k, hk⟩ := hfull f.1 f.2
    have hkK : k ∈ K := by
      change verticalEndpointHom δ k ∈ F
      rw [hk]
      exact (hFfin f.1).mp f.2
    refine ⟨⟨k, (mem_addSubgroupFinset K k).mpr hkK⟩, Subtype.ext hk⟩
  have hc := Fintype.card_congr (Equiv.ofBijective e ⟨heinj, hesurj⟩)
  change Fintype.card ↥Kfin = Fintype.card ↥Ffin at hc
  change Kfin.card = Ffin.card
  simpa using hc

/-- The endpoint overlap and exact Kneser identity force the sum of endpoint
fibre sizes to be at most overlap plus stabilizer size. -/
theorem endpoint_sigma_le_overlap_add_stabilizer
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : ((0 : ℤ), 0) ∈ T) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hbounds : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let Ffin := (B + B).addStab
    (integerFiber T 0).card + (integerFiber T l).card ≤
      (endpointOverlap T l δ).card + Ffin.card := by
  classical
  dsimp
  let E := endpointOverlap T l δ
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hboundsT : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l := by
    intro x hx
    exact hbounds x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hAbarRaw := card_image_endpointQuotient T l δ hlpos hδfst hboundsT
  have hAbar : B.card + E.card = T.card := by
    simpa [B, E, q, Δ] using hAbarRaw
  have hEsub : E ⊆ T := fun _ hx =>
    (mem_integerFiber.mp (Finset.mem_inter.mp hx).1).1
  have hEne : E.Nonempty := by
    refine ⟨((0, 0) : ℤ × H), ?_⟩
    apply Finset.mem_inter.mpr
    refine ⟨mem_integerFiber.mpr ⟨hzero, rfl⟩, ?_⟩
    apply Finset.mem_vadd_finset.mpr
    refine ⟨δ, hδ, ?_⟩
    change -δ + δ = 0
    simp
  have hTE : T.card + E.card - 1 ≤ (T + E).card :=
    hexpand T E (by rfl) hEsub (Finset.union_eq_left.mpr hEsub)
      ⟨(0, 0), hzero⟩ hEne
  have hdoubleRaw := card_image_double_add_card_add_endpointOverlap_le
    T l δ (by simpa [hδfst] using hlpos)
  have hdouble : (B + B).card + (T + E).card ≤ (T + T).card := by
    change ((T + T).image q).card + (T + E).card ≤ (T + T).card at hdoubleRaw
    rw [Finset.image_add] at hdoubleRaw
    exact hdoubleRaw
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hsmallRaw := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have hKneser := add_kneser_eq_of_card_le hBne hBne (by omega)
  change (B + Ffin).card + (B + Ffin).card =
    (B + B).card + Ffin.card at hKneser
  have hzeroF : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr (hBne.add hBne)
  have hBsub : B ⊆ B + Ffin := by
    intro b hb
    exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroF, by simp⟩
  have hBle := Finset.card_le_card hBsub
  have hdef := (endpoint_fiber_deficiency_consequences T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold).1
  change (T + T).card +
      ((integerFiber T 0).card + (integerFiber T l).card) < 3 * T.card at hdef
  change (integerFiber T 0).card + (integerFiber T l).card ≤
    E.card + Ffin.card
  omega

end Erdos336
