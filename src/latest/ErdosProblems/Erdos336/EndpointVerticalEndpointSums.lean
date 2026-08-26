import ErdosProblems.Erdos336.EndpointVerticalMiddle

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- If two zero-containing sets have their three pairwise sumsets covering
`V`, then the overlaps forced by the two copies of each original set give a
sharp lower bound for the aggregate cardinality of those three sumsets. -/
theorem card_union_add_card_le_three_pair_sums
    (A B V : Finset G) (hzeroA : 0 ∈ A) (hzeroB : 0 ∈ B)
    (hcover : (A ∪ B) + (A ∪ B) = V) :
    V.card + A.card + B.card ≤
      (A + A).card + (A + B).card + (B + B).card := by
  let P := A + A
  let Q := A + B
  let R := B + B
  have hAint : A ⊆ P ∩ Q := by
    intro a ha
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨a, ha, 0, hzeroA, by simp⟩
    · exact Finset.mem_add.mpr ⟨a, ha, 0, hzeroB, by simp⟩
  have hBint : B ⊆ (P ∪ Q) ∩ R := by
    intro b hb
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_union_right
      exact Finset.mem_add.mpr ⟨0, hzeroA, b, hb, by simp⟩
    · exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroB, by simp⟩
  have hAcard : A.card ≤ (P ∩ Q).card := Finset.card_le_card hAint
  have hBcard : B.card ≤ ((P ∪ Q) ∩ R).card := Finset.card_le_card hBint
  have hPQ := Finset.card_union_add_card_inter P Q
  have hPQR := Finset.card_union_add_card_inter (P ∪ Q) R
  have hunion : (P ∪ Q) ∪ R = V := by
    rw [← hcover]
    simp only [P, Q, R, Finset.union_add, Finset.add_union]
    rw [show B + A = A + B by exact add_comm B A]
    simp [Finset.union_assoc]
  rw [hunion] at hPQR
  simp only [P, Q, R] at hAcard hBcard hPQ hPQR ⊢
  omega

/-- Consequently, when all three pairwise sumsets lie in `V`, their total
number of holes is no larger than the total number of holes in the two
original sets. -/
theorem three_pair_sum_holes_le
    (A B V : Finset G) (hzeroA : 0 ∈ A) (hzeroB : 0 ∈ B)
    (hAsub : A ⊆ V) (hBsub : B ⊆ V)
    (hPsub : A + A ⊆ V) (hQsub : A + B ⊆ V) (hRsub : B + B ⊆ V)
    (hcover : (A ∪ B) + (A ∪ B) = V) :
    (V.card - (A + A).card) + (V.card - (A + B).card) +
        (V.card - (B + B).card) ≤
      (V.card - A.card) + (V.card - B.card) := by
  have hAle := Finset.card_le_card hAsub
  have hBle := Finset.card_le_card hBsub
  have hPle := Finset.card_le_card hPsub
  have hQle := Finset.card_le_card hQsub
  have hRle := Finset.card_le_card hRsub
  have hsum := card_union_add_card_le_three_pair_sums A B V hzeroA hzeroB hcover
  omega

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- In the vertical-full endpoint branch, the aligned union of the bottom and
top fibres has density greater than one half in the vertical subgroup, hence
its double is the whole vertical subgroup. -/
theorem endpointBoundaryUnion_add_self_eq_vertical
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
    endpointBoundaryUnion T l δ + endpointBoundaryUnion T l δ =
      verticalSubgroupFinset K := by
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
  let U := endpointBoundaryUnion T l δ
  let V := verticalSubgroupFinset K
  let HV := verticalEndpointFinset δ
  let QV := B ∩ HV
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
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
  have hKcard := card_endpointVerticalPart_eq_of_full δ hδpos Fsub Ffin
    hFmem hfull
  have hdefRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hF2 : 2 ≤ Ffin.card := by
    simpa [B, Ffin, q, Δ] using hdefRaw.1
  have hdef : 2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, Ffin, q, Δ] using hdefRaw.2
  have hzeroHV : 0 ∈ HV := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_univ _, (verticalEndpointHom δ).map_zero⟩
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroQV : 0 ∈ QV := Finset.mem_inter.mpr ⟨hzeroB, hzeroHV⟩
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
  have hQVsubF : QV ⊆ Ffin := by
    intro b hbQV
    obtain ⟨hbB, hbV⟩ := Finset.mem_inter.mp hbQV
    obtain ⟨k, _hk, hkb⟩ := Finset.mem_image.mp hbV
    have hkF : verticalEndpointHom δ k ∈ Fsub := by
      by_contra hknot
      have hrne : r (verticalEndpointHom δ k) ≠ 0 := by
        intro hz
        exact hknot ((QuotientAddGroup.eq_zero_iff _).mp hz)
      have hclass : r (verticalEndpointHom δ k) ∈ B.image r :=
        Finset.mem_image.mpr ⟨b, hbB, by rw [← hkb]⟩
      have htotal := quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B
      have hfib0 : quotientFiberDeficiency Fsub Ffin B 0 ≤
          (B + Ffin).card - B.card := by
        rw [← htotal]
        unfold quotientDeficiency
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by
          exact Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩)
      have hfibk : quotientFiberDeficiency Fsub Ffin B
          (r (verticalEndpointHom δ k)) ≤ (B + Ffin).card - B.card := by
        rw [← htotal]
        unfold quotientDeficiency
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hclass
      have hcard0 := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B 0
      have hcardk := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B
        (r (verticalEndpointHom δ k))
      have hdisj : Disjoint (quotientFiberFinset Fsub B 0)
          (quotientFiberFinset Fsub B (r (verticalEndpointHom δ k))) := by
        rw [Finset.disjoint_left]
        intro x hx0 hxk
        have hx0' := (mem_quotientFiberFinset.mp hx0).2
        have hxk' := (mem_quotientFiberFinset.mp hxk).2
        exact hrne (hxk'.symm.trans hx0')
      have hsub : quotientFiberFinset Fsub B 0 ∪
          quotientFiberFinset Fsub B (r (verticalEndpointHom δ k)) ⊆ QV := by
        intro x hx
        have hxB : x ∈ B := by
          rcases Finset.mem_union.mp hx with hx0 | hxk
          · exact (mem_quotientFiberFinset.mp hx0).1
          · exact (mem_quotientFiberFinset.mp hxk).1
        apply Finset.mem_inter.mpr
        refine ⟨hxB, ?_⟩
        rcases Finset.mem_union.mp hx with hx0 | hxk
        · have hxF : x ∈ Fsub :=
            (QuotientAddGroup.eq_zero_iff x).mp
              (mem_quotientFiberFinset.mp hx0).2
          obtain ⟨j, hj⟩ := hfull x ((hFmem x).mpr hxF)
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
        · have hdiff : x - verticalEndpointHom δ k ∈ Fsub :=
            (QuotientAddGroup.eq_iff_sub_mem).mp
              (mem_quotientFiberFinset.mp hxk).2
          obtain ⟨j, hj⟩ := hfull (x - verticalEndpointHom δ k)
            ((hFmem _).mpr hdiff)
          have hj' : verticalEndpointHom δ j =
              x - verticalEndpointHom δ k := by
            simpa [verticalEndpointHom] using hj
          apply Finset.mem_image.mpr
          refine ⟨j + k, Finset.mem_univ _, ?_⟩
          calc
            verticalEndpointHom δ (j + k) =
                verticalEndpointHom δ j + verticalEndpointHom δ k := map_add _ _ _
            _ = (x - verticalEndpointHom δ k) + verticalEndpointHom δ k := by rw [hj']
            _ = x := sub_add_cancel _ _
      have hcardUnion := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hcardUnion
      change Ffin.card - (quotientFiberFinset Fsub B 0).card ≤
        (B + Ffin).card - B.card at hfib0
      change Ffin.card - (quotientFiberFinset Fsub B
        (r (verticalEndpointHom δ k))).card ≤
        (B + Ffin).card - B.card at hfibk
      have hs0 := Nat.sub_add_cancel hcard0
      have hsk := Nat.sub_add_cancel hcardk
      have hlarge0 : Ffin.card + 2 ≤
          2 * (quotientFiberFinset Fsub B 0).card := by omega
      have hlargek : Ffin.card + 2 ≤
          2 * (quotientFiberFinset Fsub B
            (r (verticalEndpointHom δ k))).card := by omega
      omega
    exact (hFmem b).mpr (by simpa [hkb] using hkF)
  have hQVeq : QV = quotientFiberFinset Fsub B 0 := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ Fsub := (hFmem x).mp (hQVsubF hx)
      exact mem_quotientFiberFinset.mpr
        ⟨(Finset.mem_inter.mp hx).1, (QuotientAddGroup.eq_zero_iff x).mpr hxF⟩
    · intro hx
      have hx' := mem_quotientFiberFinset.mp hx
      have hxF : x ∈ Fsub := (QuotientAddGroup.eq_zero_iff x).mp hx'.2
      obtain ⟨k, hk⟩ := hfull x ((hFmem x).mpr hxF)
      exact Finset.mem_inter.mpr
        ⟨hx'.1, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩⟩
  have htotal := quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B
  have hdef0 : quotientFiberDeficiency Fsub Ffin B 0 ≤
      (B + Ffin).card - B.card := by
    rw [← htotal]
    unfold quotientDeficiency
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by
      exact Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩)
  have hfib0 := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B 0
  change Ffin.card - (quotientFiberFinset Fsub B 0).card ≤
    (B + Ffin).card - B.card at hdef0
  have hsplit0 := Nat.sub_add_cancel hfib0
  have hQVlarge : Ffin.card + 2 ≤ 2 * QV.card := by
    rw [hQVeq]
    omega
  have himage := image_endpointBoundaryUnion_eq_inter_vertical
    T l hlpos δ hδfst hboundsT
  have hinj := endpointQuotient_injective_on_boundary T l δ hδpos hδfst
  have hUcard : U.card = QV.card := by
    have hc := Finset.card_image_iff.mpr hinj
    rw [himage] at hc
    simpa [U, QV, HV, B, q, Δ] using hc.symm
  have hfibers := endpoint_fibers_single_vertical_cosets T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand hfull
  change integerFiber T 0 ⊆ verticalSubgroupFinset K ∧
    integerFiber T l ⊆ δ +ᵥ verticalSubgroupFinset K at hfibers
  have hUsub : U ⊆ V := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx0 | hxl
    · have hxV := hfibers.1 hx0
      simpa [V] using hxV
    · obtain ⟨y, hyl, hyx⟩ := Finset.mem_vadd_finset.mp hxl
      have hyV := hfibers.2 hyl
      obtain ⟨v, hv, hvy⟩ := Finset.mem_vadd_finset.mp hyV
      apply mem_verticalSubgroupFinset.mpr
      have hx0 : x.1 = 0 := by
        simp only [vadd_eq_add] at hyx
        rw [← hyx, Prod.fst_add, Prod.fst_neg,
          (mem_integerFiber.mp hyl).2, hδfst]
        simp
      refine ⟨hx0, ?_⟩
      have hvK := (mem_verticalSubgroupFinset.mp hv).2
      simp only [vadd_eq_add] at hyx hvy
      have hsnd := congrArg Prod.snd hyx
      have hsnd2 := congrArg Prod.snd hvy
      simp only [Prod.snd_add, Prod.snd_neg] at hsnd hsnd2
      change x.2 ∈ K
      rw [← hsnd, ← hsnd2]
      simpa [add_assoc] using hvK
  have hUlarge : V.card < U.card + U.card := by
    rw [card_verticalSubgroupFinset, hKcard, hUcard]
    omega
  have hUsub0 : U ⊆ (((0 : ℤ), (0 : H)) +ᵥ verticalSubgroupFinset K) := by
    intro x hx
    apply Finset.mem_vadd_finset.mpr
    exact ⟨x, hUsub hx, by simp⟩
  have hsum := add_eq_vadd_vertical_of_card_lt K U U
    ((0 : ℤ), (0 : H)) ((0 : ℤ), (0 : H))
    hUsub0 hUsub0 (by simpa [V] using hUlarge)
  have hzeroV :
      (((0 : ℤ), (0 : H)) + ((0 : ℤ), (0 : H))) +ᵥ
          verticalSubgroupFinset K = verticalSubgroupFinset K := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
      have hz : ((0 : ℤ), (0 : H)) + ((0 : ℤ), (0 : H)) =
          (0 : ℤ × H) := by simp
      rw [hz] at hyx
      have hyx' : y = x := by simpa using hyx
      simpa [← hyx'] using hy
    · intro hx
      exact Finset.mem_vadd_finset.mpr ⟨x, hx, by simp⟩
  rw [hzeroV] at hsum
  change U + U = V
  simpa [V] using hsum

end Erdos336
