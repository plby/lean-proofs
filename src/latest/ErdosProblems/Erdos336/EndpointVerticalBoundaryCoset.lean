import ErdosProblems.Erdos336.EndpointVerticalBoundary
import ErdosProblems.Erdos336.CosetDeficiencySum

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- In the vertical-full branch, both endpoint fibres lie in the corresponding
single vertical cosets. -/
theorem endpoint_fibers_single_vertical_cosets
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
    let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
      AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
    (∀ f ∈ Ffin, ∃ k : H, verticalEndpointHom δ k = f) →
    let K := endpointVerticalPart δ Fsub
    integerFiber T 0 ⊆ verticalSubgroupFinset K ∧
      integerFiber T l ⊆ δ +ᵥ verticalSubgroupFinset K := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
  intro hfull
  let K := endpointVerticalPart δ Fsub
  let HV := verticalEndpointFinset δ
  let QV := B ∩ HV
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hδpos : 0 < δ.1 := by rw [hδfst]; exact hlpos
  have hboundsT : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l := by
    intro x hx
    exact hbounds x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hFmem (x : (ℤ × H) ⧸ Δ) : x ∈ Ffin ↔ x ∈ Fsub := by
    change x ∈ (B + B).addStab ↔ x ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hFcard := card_endpointVerticalPart_eq_of_full δ hδpos Fsub Ffin
    hFmem hfull
  have hsigmaRaw := endpoint_sigma_le_overlap_add_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hsigma :
      (integerFiber T 0).card + (integerFiber T l).card ≤
        (endpointOverlap T l δ).card + Ffin.card := by
    simpa [B, Ffin, q, Δ] using hsigmaRaw
  have hQVcardRaw := card_inter_verticalEndpointFinset
    T l hlpos δ hδfst hboundsT
  have hQVcard : QV.card + (endpointOverlap T l δ).card =
      (integerFiber T 0).card + (integerFiber T l).card := by
    simpa [QV, HV, B, q, Δ] using hQVcardRaw
  have hQVle : QV.card ≤ Ffin.card := by omega
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let C := B.image r
  have hdefRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hF2 : 2 ≤ Ffin.card := by
    simpa [B, Ffin, q, Δ] using hdefRaw.1
  have hdef : 2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, Ffin, q, Δ] using hdefRaw.2
  have htotal := quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B
  have hfiber_large (z : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) (hz : z ∈ C) :
      Ffin.card + 2 ≤ 2 * (quotientFiberFinset Fsub B z).card := by
    have hsingle : quotientFiberDeficiency Fsub Ffin B z ≤
        quotientDeficiency Fsub Ffin B := by
      unfold quotientDeficiency
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by
        simpa [quotientImage, C, r] using hz)
    rw [htotal] at hsingle
    have hfib := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B z
    change Ffin.card - (quotientFiberFinset Fsub B z).card ≤
      (B + Ffin).card - B.card at hsingle
    have hsplit : Ffin.card - (quotientFiberFinset Fsub B z).card +
        (quotientFiberFinset Fsub B z).card = Ffin.card :=
      Nat.sub_add_cancel hfib
    omega
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroHV : 0 ∈ HV := by
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    exact (verticalEndpointHom δ).map_zero
  have hzeroQV : 0 ∈ QV := Finset.mem_inter.mpr ⟨hzeroB, hzeroHV⟩
  have hzeroC : 0 ∈ C := Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩
  have hQVsubF : QV ⊆ Ffin := by
    intro b hbQV
    by_contra hbF
    have hbB := (Finset.mem_inter.mp hbQV).1
    have hbV := (Finset.mem_inter.mp hbQV).2
    have hrbne : r b ≠ 0 := by
      intro h
      apply hbF
      apply (hFmem b).mpr
      exact (QuotientAddGroup.eq_zero_iff b).mp h
    have hrbC : r b ∈ C := Finset.mem_image.mpr ⟨b, hbB, rfl⟩
    let Z0 := quotientFiberFinset Fsub B 0
    let Zb := quotientFiberFinset Fsub B (r b)
    have hZ0large := hfiber_large 0 hzeroC
    have hZblarge := hfiber_large (r b) hrbC
    have hdisj : Disjoint Z0 Zb := by
      rw [Finset.disjoint_left]
      intro x hx0 hxb
      have hx0' : r x = 0 := by
        exact (mem_quotientFiberFinset.mp (by simpa [Z0] using hx0)).2
      have hxb' : r x = r b := by
        exact (mem_quotientFiberFinset.mp (by simpa [Zb] using hxb)).2
      exact hrbne (hxb'.symm.trans hx0')
    have hUnionSub : Z0 ∪ Zb ⊆ QV := by
      intro x hx
      have hxB : x ∈ B := by
        rcases Finset.mem_union.mp hx with hx0 | hxb
        · have hxpair : x ∈ B ∧ x ∈ Fsub := by
            simpa [Z0, quotientFiberFinset] using hx0
          exact hxpair.1
        · have hxpair : x ∈ B ∧ r x = r b := by
            simpa [Zb, quotientFiberFinset, r] using hxb
          exact hxpair.1
      apply Finset.mem_inter.mpr
      refine ⟨hxB, ?_⟩
      rcases Finset.mem_union.mp hx with hx0 | hxb
      · have hxpair : x ∈ B ∧ x ∈ Fsub := by
          simpa [Z0, quotientFiberFinset] using hx0
        have hxF : x ∈ Fsub := hxpair.2
        obtain ⟨k, hk⟩ := hfull x ((hFmem x).mpr hxF)
        apply Finset.mem_image.mpr
        exact ⟨k, Finset.mem_univ _, hk⟩
      · have hrx : r x = r b :=
          (mem_quotientFiberFinset.mp (by simpa [Zb] using hxb)).2
        have hdiffF : x - b ∈ Fsub :=
          (QuotientAddGroup.eq_iff_sub_mem).mp hrx
        obtain ⟨k, hk⟩ := hfull (x - b) ((hFmem (x - b)).mpr hdiffF)
        obtain ⟨kb, _hkb, hkbEq⟩ := Finset.mem_image.mp hbV
        apply Finset.mem_image.mpr
        refine ⟨k + kb, Finset.mem_univ _, ?_⟩
        have hk' : verticalEndpointHom δ k = x - b := by
          simpa [verticalEndpointHom] using hk
        calc
          verticalEndpointHom δ (k + kb) =
              verticalEndpointHom δ k + verticalEndpointHom δ kb := map_add _ _ _
          _ = (x - b) + b := by rw [hk', hkbEq]
          _ = x := sub_add_cancel x b
    have hcardUnion := Finset.card_le_card hUnionSub
    rw [Finset.card_union_of_disjoint hdisj] at hcardUnion
    have hZ0large' : Ffin.card + 2 ≤ 2 * Z0.card := by simpa [Z0] using hZ0large
    have hZblarge' : Ffin.card + 2 ≤ 2 * Zb.card := by simpa [Zb] using hZblarge
    omega
  refine ⟨?_, ?_⟩
  · intro x hx0
    have hxT := (mem_integerFiber.mp hx0).1
    have hxfst := (mem_integerFiber.mp hx0).2
    have hqxQV : q x ∈ QV := by
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_image.mpr ⟨x, hxT, rfl⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨x.2, Finset.mem_univ _, ?_⟩
      apply congrArg q
      exact Prod.ext hxfst.symm rfl
    have hqxF : q x ∈ Fsub := (hFmem _).mp (hQVsubF hqxQV)
    apply mem_verticalSubgroupFinset.mpr
    refine ⟨hxfst, ?_⟩
    change verticalEndpointHom δ x.2 ∈ Fsub
    convert hqxF using 1
    apply congrArg q
    exact Prod.ext hxfst.symm rfl
  · intro x hxl
    have hxT := (mem_integerFiber.mp hxl).1
    have hxfst := (mem_integerFiber.mp hxl).2
    let y := -δ + x
    have hyfst : y.1 = 0 := by
      dsimp [y]
      change -δ.1 + x.1 = 0
      rw [hxfst, hδfst]
      omega
    have hqyQV : q y ∈ QV := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        refine ⟨x, hxT, ?_⟩
        dsimp [y]
        have hqδ : q δ = 0 := (QuotientAddGroup.eq_zero_iff δ).mpr
          (AddSubgroup.mem_zmultiples δ)
        simp [hqδ]
      · apply Finset.mem_image.mpr
        refine ⟨y.2, Finset.mem_univ _, ?_⟩
        apply congrArg q
        exact Prod.ext hyfst.symm rfl
    have hqyF : q y ∈ Fsub := (hFmem _).mp (hQVsubF hqyQV)
    apply Finset.mem_vadd_finset.mpr
    refine ⟨y, mem_verticalSubgroupFinset.mpr ⟨hyfst, ?_⟩, ?_⟩
    · change verticalEndpointHom δ y.2 ∈ Fsub
      convert hqyF using 1
      apply congrArg q
      exact Prod.ext hyfst.symm rfl
    · dsimp [y]
      change δ + (-δ + x) = x
      abel

end Erdos336
