import ErdosProblems.Erdos336.EndpointClassProjection
import ErdosProblems.Erdos336.ProgressionTwoNewArithmetic
import ErdosProblems.Erdos336.EndpointOutsideRoots
import ErdosProblems.Erdos336.EndpointCriticalRelations
import ErdosProblems.Erdos336.CosetDeficiencySum

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1800000

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The three-term-progression critical quotient is impossible in the proper
(nonvertical) endpoint-stabilizer branch.  The repair uses integer-projection
sizes of the two far classes, rather than a false balanced selector. -/
theorem endpoint_progression_proper_impossible
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
    let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
      QuotientAddGroup.mk' Fsub
    let C := B.image r
    let D := criticalNewSums C
    ∀ x : (((ℤ × H) ⧸ Δ) ⧸ Fsub),
      let x2 := x + x
      let x3 := x + x2
      let x4 := x2 + x2
      C = {0, x, x2} → x ≠ 0 → x2 ≠ 0 → x2 ≠ x →
      x3 ∈ D → x4 ∈ D → x3 ≠ x4 →
      2 * (addSubgroupFinset (endpointVerticalPart δ Fsub)).card ≤ Ffin.card →
      False := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let C := B.image r
  let D := criticalNewSums C
  intro xRaw
  let x : (((ℤ × H) ⧸ Δ) ⧸ Fsub) := xRaw
  let x2 := x + x
  let x3 := x + x2
  let x4 := x2 + x2
  intro hC hx0 hx20 hx2x hx3D hx4D hx34 hhalf
  change C = {0, x, x2} at hC
  change x ≠ 0 at hx0
  change x2 ≠ 0 at hx20
  change x2 ≠ x at hx2x
  change x3 ∈ D at hx3D
  change x4 ∈ D at hx4D
  change x3 ≠ x4 at hx34
  change 2 * (addSubgroupFinset (endpointVerticalPart δ Fsub)).card ≤
    Ffin.card at hhalf
  have hδT : δ ∈ T := (mem_integerFiber.mp hδ).1
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hδpos : 0 < δ.1 := by simpa [hδfst] using hlpos
  have hboundsT : ∀ a ∈ T, 0 ≤ a.1 ∧ a.1 ≤ l := by
    intro a ha
    exact hbounds a.1 (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hsmallRaw := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have hrelsRaw := endpoint_critical_card_relations B hBne hzeroB hsmall
  have hrels :
      (B + Ffin).card = (D.card + 1) * Ffin.card ∧
      (B + B).card = (2 * D.card + 1) * Ffin.card ∧
      C.card = D.card + 1 ∧ (C + C).card = 2 * D.card + 1 := by
    simpa [Ffin, Fsub, r, C, D] using hrelsRaw
  have hDcard : D.card = 2 := by
    have hCcard : C.card = 3 := by
      rw [hC]
      have h0not : (0 : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) ∉ ({x, x2} : Finset _) := by
        simp [hx0.symm, hx20.symm]
      rw [Finset.card_insert_of_notMem h0not]
      have hxnot : x ∉ ({x2} : Finset _) := by simpa using hx2x.symm
      rw [Finset.card_insert_of_notMem hxnot]
      simp
    omega
  have hstabRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hstab : 2 ≤ Ffin.card ∧
      2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, Ffin, q, Δ] using hstabRaw
  have hFmem (a : ((ℤ × H) ⧸ Δ)) : a ∈ Ffin ↔ a ∈ Fsub := by
    change a ∈ (B + B).addStab ↔ a ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  let K := endpointVerticalPart δ Fsub
  let Kfin := addSubgroupFinset K
  let X1 := endpointClassSlice T δ Fsub x
  let X2 := endpointClassSlice T δ Fsub x2
  let Y12 := X1 + X2
  let Y22 := X2 + X2
  have hxC : x ∈ C := by rw [hC]; simp
  have hx2C : x2 ∈ C := by rw [hC]; simp
  have hX1ne : X1.Nonempty := by
    obtain ⟨b, hbB, hbx⟩ := Finset.mem_image.mp hxC
    obtain ⟨a, haT, hab⟩ := Finset.mem_image.mp hbB
    refine ⟨a, mem_endpointClassSlice.mpr ⟨haT, ?_⟩⟩
    change r (q a) = x
    rw [hab, hbx]
  have hX2ne : X2.Nonempty := by
    obtain ⟨b, hbB, hbx⟩ := Finset.mem_image.mp hx2C
    obtain ⟨a, haT, hab⟩ := Finset.mem_image.mp hbB
    refine ⟨a, mem_endpointClassSlice.mpr ⟨haT, ?_⟩⟩
    change r (q a) = x2
    rw [hab, hbx]
  let p1 := (quotientFiberFinset Fsub B x).card
  let p2 := (quotientFiberFinset Fsub B x2).card
  let d1 := Ffin.card - p1
  let d2 := Ffin.card - p2
  let n1 := (X1.image Prod.fst).card
  let n2 := (X2.image Prod.fst).card
  have hp1le : p1 ≤ Ffin.card := card_quotient_fiber_le_subgroup
    Fsub Ffin hFmem B x
  have hp2le : p2 ≤ Ffin.card := card_quotient_fiber_le_subgroup
    Fsub Ffin hFmem B x2
  have hp1d : p1 + d1 = Ffin.card := by simp [d1, Nat.add_sub_of_le hp1le]
  have hp2d : p2 + d2 = Ffin.card := by simp [d2, Nat.add_sub_of_le hp2le]
  have hp1slice : p1 ≤ X1.card := by
    have h := card_endpointClassInImage_le_slice T δ Fsub x
    simpa [p1, X1, endpointClassInImage, quotientFiberFinset, B, q, r, Δ]
      using h
  have hp2slice : p2 ≤ X2.card := by
    have h := card_endpointClassInImage_le_slice T δ Fsub x2
    simpa [p2, X2, endpointClassInImage, quotientFiberFinset, B, q, r, Δ]
      using h
  have hX1cap := card_endpointClassSlice_le_projection_mul_vertical T δ Fsub x
  have hX2cap := card_endpointClassSlice_le_projection_mul_vertical T δ Fsub x2
  have hp1fib : p1 ≤ n1 * Kfin.card := by
    exact le_trans hp1slice (by simpa [n1, X1, Kfin, K] using hX1cap)
  have hp2fib : p2 ≤ n2 * Kfin.card := by
    exact le_trans hp2slice (by simpa [n2, X2, Kfin, K] using hX2cap)
  have hspan1 := projection_sub_one_mul_vertical_le_endpoint_subgroup
    T l hlpos δ hδfst hboundsT Fsub Ffin hFmem x hX1ne
  have hspan2 := projection_sub_one_mul_vertical_le_endpoint_subgroup
    T l hlpos δ hδfst hboundsT Fsub Ffin hFmem x2 hX2ne
  have hdiv := card_endpointVerticalPart_dvd δ hδpos Fsub Ffin hFmem
  have hkpos : 0 < Kfin.card := by
    rw [Finset.card_pos]
    exact ⟨0, (mem_addSubgroupFinset K 0).mpr K.zero_mem⟩
  have hn1 : 0 < n1 := (hX1ne.image Prod.fst).card_pos
  have hn2 : 0 < n2 := (hX2ne.image Prod.fst).card_pos
  have hcross1 := projection_large_fiber_bound X1 X2 hX1ne hX2ne
  have hcross2 := projection_large_fiber_bound X2 X1 hX2ne hX1ne
  have hdouble := projection_kneser_double_bound X2 hX2ne
  have hdefsum : d1 + d2 ≤ (B + Ffin).card - B.card := by
    let d0 := quotientFiberDeficiency Fsub Ffin B 0
    have hqdef := quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B
    have hsum : quotientDeficiency Fsub Ffin B = d0 + d1 + d2 := by
      change (∑ z ∈ quotientImage Fsub B,
        quotientFiberDeficiency Fsub Ffin B z) = d0 + d1 + d2
      have himage : quotientImage Fsub B = C := by
        rfl
      rw [himage, hC]
      simp [d0, d1, d2, p1, p2, quotientFiberDeficiency,
        hx0, hx20, hx2x, hx0.symm, hx20.symm, hx2x.symm]
      ring
    rw [← hqdef, hsum]
    omega
  have hdef12 : 2 * (d1 + d2) ≤ Ffin.card - 2 := by omega
  have hnewlower : 3 * Ffin.card ≤ 2 * (d1 + d2) + Y12.card + Y22.card := by
    apply progression_two_new_arithmetic Ffin.card Kfin.card d1 d2 p1 p2
      n1 n2 Y12.card Y22.card hkpos hn1 hn2
    · simpa [Kfin, K] using hhalf
    · simpa [Kfin, K] using hdiv
    · exact hp1d
    · exact hp2d
    · exact hdef12
    · exact hp1fib
    · exact hp2fib
    · simpa [n1, X1, Kfin, K] using hspan1
    · simpa [n2, X2, Kfin, K] using hspan2
    · have hm := Nat.mul_le_mul_left (n1 + n2 - 1) hp1slice
      exact le_trans hm (by simpa [n1, n2, X1, X2, Y12] using hcross1)
    · have hm := Nat.mul_le_mul_left (n1 + n2 - 1) hp2slice
      exact le_trans hm (by
        simpa only [n1, n2, X1, X2, Y12, add_comm] using hcross2)
    · have hm := Nat.mul_le_mul_left (2 * n2 - 1) hp2slice
      exact le_trans hm (by simpa [n2, X2, Y22] using hdouble)
  let U := Y12 ∪ Y22
  have hclass12 : ∀ a ∈ Y12, r (q a) = x3 := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp ha
    rw [q.map_add, r.map_add, (mem_endpointClassSlice.mp hu).2,
      (mem_endpointClassSlice.mp hv).2]
  have hclass22 : ∀ a ∈ Y22, r (q a) = x4 := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp ha
    rw [q.map_add, r.map_add, (mem_endpointClassSlice.mp hu).2,
      (mem_endpointClassSlice.mp hv).2]
  have hdisj : Disjoint Y12 Y22 := by
    rw [Finset.disjoint_left]
    intro a ha12 ha22
    exact hx34 ((hclass12 a ha12).symm.trans (hclass22 a ha22))
  have hUcard : U.card = Y12.card + Y22.card := by
    exact Finset.card_union_of_disjoint hdisj
  have hUoutside : U ⊆ (T + T) \ T := by
    intro a ha
    apply Finset.mem_sdiff.mpr
    rcases Finset.mem_union.mp ha with ha12 | ha22
    · refine ⟨?_, ?_⟩
      · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp ha12
        exact Finset.mem_add.mpr ⟨u, (mem_endpointClassSlice.mp hu).1,
          v, (mem_endpointClassSlice.mp hv).1, rfl⟩
      · intro haT
        have hCmem : r (q a) ∈ C := Finset.mem_image.mpr
          ⟨q a, Finset.mem_image.mpr ⟨a, haT, rfl⟩, rfl⟩
        exact (Finset.mem_sdiff.mp hx3D).2 (by simpa [hclass12 a ha12] using hCmem)
    · refine ⟨?_, ?_⟩
      · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp ha22
        exact Finset.mem_add.mpr ⟨u, (mem_endpointClassSlice.mp hu).1,
          v, (mem_endpointClassSlice.mp hv).1, rfl⟩
      · intro haT
        have hCmem : r (q a) ∈ C := Finset.mem_image.mpr
          ⟨q a, Finset.mem_image.mpr ⟨a, haT, rfl⟩, rfl⟩
        exact (Finset.mem_sdiff.mp hx4D).2 (by simpa [hclass22 a ha22] using hCmem)
  have hUsep : ∀ a ∈ U, q a ∉ B + Ffin := by
    intro a haU haBF
    obtain ⟨b, hbB, f, hfF, hbf⟩ := Finset.mem_add.mp haBF
    have hrf : r f = 0 := (QuotientAddGroup.eq_zero_iff f).mpr
      ((hFmem f).mp hfF)
    have hrC : r b ∈ C := Finset.mem_image.mpr ⟨b, hbB, rfl⟩
    have hra : r (q a) = r b := by
      rw [← hbf, r.map_add, hrf]
      exact add_zero (r b)
    have hraC : r (q a) ∈ C := by
      rw [hra]
      exact hrC
    rcases Finset.mem_union.mp haU with ha12 | ha22
    · exact (Finset.mem_sdiff.mp hx3D).2 (by simpa [hclass12 a ha12] using hraC)
    · exact (Finset.mem_sdiff.mp hx4D).2 (by simpa [hclass22 a ha22] using hraC)
  have hzeroF : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr hBBne
  have hRsub : B + Ffin ⊆ (T + T).image q := by
    intro a ha
    obtain ⟨b, hbB, f, hfF, hbf⟩ := Finset.mem_add.mp ha
    have hbBB : b ∈ B + B := Finset.mem_add.mpr ⟨b, hbB, 0, hzeroB, by simp⟩
    have hfb : f + b ∈ B + B := by
      have hact := (Finset.mem_addStab' hBBne).mp hfF hbBB
      simpa [vadd_eq_add] using hact
    have haBB : a ∈ B + B := by rw [← hbf]; simpa [add_comm] using hfb
    rw [Finset.image_add]
    exact haBB
  have hroots := card_quotient_targets_add_separated_subset_le_double_sdiff
    T δ hδT hδpos (B + Ffin) hRsub U hUoutside hUsep
  have hUlower : 3 * Ffin.card - 2 * (d1 + d2) ≤ U.card := by
    rw [hUcard]
    omega
  have hout : 2 * B.card ≤ ((T + T) \ T).card := by
    have hRcard : (B + Ffin).card = 3 * Ffin.card := by
      rw [hrels.1, hDcard]
    have hzeroFin : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr hBBne
    have hBsub : B ⊆ B + Ffin := by
      intro b hb
      exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroFin, by simp⟩
    have hBle := Finset.card_le_card hBsub
    have hsplit : ((B + Ffin).card - B.card) + B.card = (B + Ffin).card :=
      Nat.sub_add_cancel hBle
    rw [hRcard] at hroots hsplit
    omega
  let E := endpointOverlap T l δ
  have hAbarRaw := card_image_endpointQuotient T l δ hlpos hδfst hboundsT
  have hAbar : B.card + E.card = T.card := by
    simpa [B, E, q, Δ] using hAbarRaw
  have hdef := (endpoint_fiber_deficiency_consequences T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold).2
  have hTsub : T ⊆ T + T := by
    intro a ha
    exact Finset.mem_add.mpr ⟨a, ha, 0, hzero, by simp⟩
  have houtEq : ((T + T) \ T).card = (T + T).card - T.card :=
    Finset.card_sdiff_of_subset hTsub
  change (T + T).card + 2 * E.card < 3 * T.card at hdef
  rw [houtEq] at hout
  omega

end Erdos336
