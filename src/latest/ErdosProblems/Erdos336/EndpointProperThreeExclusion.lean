import ErdosProblems.Erdos336.EndpointBalancedExistence
import ErdosProblems.Erdos336.EndpointProperBranch

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 800000

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- In the normalized endpoint setting, at least three new stabilizer classes
and a nonvertical stabilizer element are impossible. -/
theorem endpoint_proper_three_impossible
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
    3 ≤ D.card →
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
  intro hD3 hnonvertical
  change 3 ≤ D.card at hD3
  change ∃ f ∈ Ffin, ∀ k : H, verticalEndpointHom δ k ≠ f at hnonvertical
  have hsmallRaw := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  obtain ⟨sel, hload⟩ := endpoint_exists_balanced_selector_of_three
    T δ hzero hthreshold (by simpa [B, q, Δ] using hsmall) (by simpa [D, C, r, Fsub, B, q, Δ] using hD3)
  change CriticalSelector C at sel
  change ∀ z ∈ C, selectorLoad sel z ≤ D.card at hload
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hFmem (x : (ℤ × H) ⧸ Δ) : x ∈ Ffin ↔ x ∈ Fsub := by
    change x ∈ (B + B).addStab ↔ x ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hhalf := twice_card_endpointVerticalPart_le δ
    (by rw [(mem_integerFiber.mp hδ).2]; exact hlpos)
    Fsub Ffin hFmem hnonvertical
  have hD2 : 2 ≤ D.card := by omega
  exact endpoint_balanced_proper_impossible T l hlpos hzero δ hδ h0 hl
    hbounds hthreshold hexpand sel hload hD2 hhalf

end Erdos336
