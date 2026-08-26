import ErdosProblems.Erdos336.CriticalThreeClassification
import ErdosProblems.Erdos336.EndpointProperBranch
import ErdosProblems.Erdos336.EndpointProgressionBranch
import ErdosProblems.Erdos336.TwoImageThreshold

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1800000

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The last proper-stabilizer endpoint case: exactly two new critical
classes are impossible.  The three-point classification reduces it to a
balanced selector, a two/three-class quotient, or the progression branch. -/
theorem endpoint_proper_two_impossible
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
    D.card = 2 →
    (∃ f ∈ Ffin, ∀ k : H, verticalEndpointHom δ k ≠ f) →
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
  intro hD2 hnonvertical
  change D.card = 2 at hD2
  change ∃ f ∈ Ffin, ∀ k : H, verticalEndpointHom δ k ≠ f at hnonvertical
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroC : 0 ∈ C := Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩
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
  have hCcard : C.card = 3 := by omega
  have hCCcard : (C + C).card = 5 := by omega
  have hFmem (a : ((ℤ × H) ⧸ Δ)) : a ∈ Ffin ↔ a ∈ Fsub := by
    change a ∈ (B + B).addStab ↔ a ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hhalf := twice_card_endpointVerticalPart_le δ
    (by rw [(mem_integerFiber.mp hδ).2]; exact hlpos)
    Fsub Ffin hFmem hnonvertical
  rcases critical_three_representation_dichotomy C hzeroC hCcard hCCcard with
      hbalanced | hquotient | hprogression
  · obtain ⟨sel, hload2⟩ := hbalanced
    have hload : ∀ z ∈ C, selectorLoad sel z ≤ D.card := by
      intro z hz
      simpa [hD2] using hload2 z hz
    have hDtwo : 2 ≤ D.card := by rw [hD2]
    exact endpoint_balanced_proper_impossible T l hlpos hzero δ hδ h0 hl
      hbounds hthreshold hexpand sel hload
      (by simpa [D, C, r, Fsub, B, q, Δ] using hDtwo) hhalf
  · obtain ⟨L, hLC, hLCC⟩ := hquotient
    letI : L.Normal := ⟨by
      intro n hn g
      convert hn using 1 <;> abel⟩
    let Q₃ := ((((ℤ × H) ⧸ Δ) ⧸ Fsub) ⧸ L)
    let s : (((ℤ × H) ⧸ Δ) ⧸ Fsub) →+ Q₃ := QuotientAddGroup.mk' L
    let ρ : (ℤ × H) →+ Q₃ := s.comp (r.comp q)
    have hTimageEq : T.image ρ = subgroupQuotientImage L C := by
      simp [subgroupQuotientImage, ρ, s, C, B,
        Finset.image_image, AddMonoidHom.coe_comp]
      apply Finset.image_congr
      intro x hx
      exact QuotientAddGroup.mk'_apply L _
    have hTTimageEq : (T + T).image ρ = subgroupQuotientImage L (C + C) := by
      calc
        (T + T).image ρ = T.image ρ + T.image ρ := Finset.image_add ρ
        _ = subgroupQuotientImage L C + subgroupQuotientImage L C := by
          rw [hTimageEq]
        _ = subgroupQuotientImage L (C + C) := by
          simpa [subgroupQuotientImage, QuotientAddGroup.mk'_apply] using
            (Finset.image_add (QuotientAddGroup.mk' L) (s := C) (t := C)).symm
    have hTimage : (T.image ρ).card = 2 := by
      rw [hTimageEq]
      exact hLC
    have hTTimage : ((T + T).image ρ).card = 3 := by
      rw [hTTimageEq]
      exact hLCC
    exact not_two_image_three_sum_of_strict_threshold
      (H := H) (Q := Q₃) T ρ hzero hthreshold hTimage hTTimage
  · obtain ⟨x, hCx, hx0, hx20, hx2x, hx3D, hx4D, hx34⟩ := hprogression
    exact endpoint_progression_proper_impossible T l hlpos hzero δ hδ h0 hl
      hbounds hthreshold hexpand x hCx hx0 hx20 hx2x hx3D hx4D hx34 hhalf

end Erdos336
