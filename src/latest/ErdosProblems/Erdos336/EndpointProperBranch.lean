import ErdosProblems.Erdos336.EndpointBalancedBranch
import ErdosProblems.Erdos336.EndpointCriticalRelations
import ErdosProblems.Erdos336.PrimitiveEndpointQuotientSmall

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise

/-- Natural-number arithmetic behind Lev's proper-intersection branch. -/
theorem proper_branch_count_arithmetic
    (N F K S R B O : ℕ) (hN : 2 ≤ N) (hF2 : 2 ≤ F)
    (hhalf : 2 * K ≤ F) (hdef : 2 * S ≤ F - 2)
    (hR : R = (N + 1) * F) (hBle : B ≤ R) (hS : S = R - B)
    (hcount : R + N * (2 * F - K) ≤ O + N * S) :
    2 * B ≤ O := by
  have hKle : K ≤ 2 * F := by omega
  have htr : 2 * F - K + K = 2 * F := by omega
  have hSB : S + B = R := by omega
  have hFS : 2 * S + 2 ≤ F := by omega
  have hlower : 3 * N * F ≤ 2 * (N * (2 * F - K)) := by nlinarith
  have hNs : N - 2 + 2 = N := by omega
  have hFs : F - 2 * S + 2 * S = F := by omega
  have hp : 0 ≤ (N - 2) * (F - 2 * S) := Nat.zero_le _
  have harith : 4 * B + 2 * (N * S) ≤ 2 * R + 3 * N * F := by
    nlinarith
  have hc2 := Nat.mul_le_mul_left 2 hcount
  nlinarith

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- A balanced critical selector plus a proper (at-most-half) vertical
intersection contradicts the rectifiable threshold. -/
theorem endpoint_balanced_proper_impossible
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
    ∀ sel : CriticalSelector C,
      (∀ z ∈ C, selectorLoad sel z ≤ D.card) →
      2 ≤ D.card →
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
  intro sel hload hD2 hhalf
  change CriticalSelector C at sel
  change ∀ z ∈ C, selectorLoad sel z ≤ D.card at hload
  have hδT : δ ∈ T := (mem_integerFiber.mp hδ).1
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hsmallRaw := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hrelsRaw := endpoint_critical_card_relations B hBne hzeroB hsmall
  have hrels :
      (B + Ffin).card = (D.card + 1) * Ffin.card ∧
      (B + B).card = (2 * D.card + 1) * Ffin.card ∧
      C.card = D.card + 1 ∧ (C + C).card = 2 * D.card + 1 := by
    simpa [Ffin, Fsub, r, C, D] using hrelsRaw
  have hstabRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hstab : 2 ≤ Ffin.card ∧
      2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, Ffin, q, Δ] using hstabRaw
  have hcountRaw := endpoint_balanced_selector_count T δ hzero hδT
    (by simpa [hδfst] using hlpos) sel hload
  have hcount :
      (B + Ffin).card +
          D.card * (2 * Ffin.card -
            (addSubgroupFinset (endpointVerticalPart δ Fsub)).card) ≤
        ((T + T) \ T).card +
          D.card * ((B + Ffin).card - B.card) := by
    simpa [B, Ffin, Fsub, r, C, D, q, Δ] using hcountRaw
  have hzeroF : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr (hBne.add hBne)
  have hBsub : B ⊆ B + Ffin := by
    intro b hb
    exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroF, by simp⟩
  have hBle : B.card ≤ (B + Ffin).card := Finset.card_le_card hBsub
  have hout : 2 * B.card ≤ ((T + T) \ T).card :=
    proper_branch_count_arithmetic
      D.card Ffin.card
      (addSubgroupFinset (endpointVerticalPart δ Fsub)).card
      ((B + Ffin).card - B.card) (B + Ffin).card B.card
      ((T + T) \ T).card hD2 hstab.1 hhalf hstab.2 hrels.1 hBle rfl hcount
  let E := endpointOverlap T l δ
  have hboundsT : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l := by
    intro x hx
    exact hbounds x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hAbarRaw := card_image_endpointQuotient T l δ hlpos hδfst hboundsT
  have hAbar : B.card + E.card = T.card := by
    simpa [B, E, q, Δ] using hAbarRaw
  have hdef := (endpoint_fiber_deficiency_consequences T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold).2
  have hTsub : T ⊆ T + T := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have houtEq : ((T + T) \ T).card = (T + T).card - T.card :=
    Finset.card_sdiff_of_subset hTsub
  change (T + T).card + 2 * E.card < 3 * T.card at hdef
  rw [houtEq] at hout
  omega

end Erdos336
