import ErdosProblems.Erdos336.EndpointCriticalRelations
import ErdosProblems.Erdos336.CriticalRepresentationDichotomy
import ErdosProblems.Erdos336.TwoImageThreshold

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 800000

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Under the strict rectifiable threshold, every critical endpoint quotient
with at least three new classes has a balanced representation selector. -/
theorem endpoint_exists_balanced_selector_of_three
    (T : Finset (ℤ × H)) (δ : ℤ × H)
    (hzero : ((0 : ℤ), 0) ∈ T)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
      AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
    let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
      QuotientAddGroup.mk' Fsub
    let C := B.image r
    let D := criticalNewSums C
    (B + B).card < 2 * B.card - 1 →
    3 ≤ D.card →
    ∃ sel : CriticalSelector C,
      ∀ z ∈ C, selectorLoad sel z ≤ D.card := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let C := B.image r
  let D := criticalNewSums C
  intro hsmallRaw hD3
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have hTne : T.Nonempty := ⟨(0, 0), hzero⟩
  have hBne : B.Nonempty := hTne.image q
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hrelsRaw := endpoint_critical_card_relations B hBne hzeroB hsmall
  have hrels : C.card = D.card + 1 ∧ (C + C).card = 2 * D.card + 1 := by
    have h := hrelsRaw.2.2
    simpa [Fsub, r, C, D] using h
  have hzeroC : 0 ∈ C := Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩
  rcases critical_representation_dichotomy C D.card hD3 hzeroC
      hrels.1 hrels.2 with hbal | hex
  · exact hbal
  · obtain ⟨L, hLC, hLCC⟩ := hex
    let : L.Normal := ⟨by
      intro n hn g
      convert hn using 1 <;> abel⟩
    let Q₃ := ((((ℤ × H) ⧸ Δ) ⧸ Fsub) ⧸ L)
    let s : (((ℤ × H) ⧸ Δ) ⧸ Fsub) →+ Q₃ := QuotientAddGroup.mk' L
    let ρ : (ℤ × H) →+ Q₃ := s.comp (r.comp q)
    have hImage : T.image ρ = subgroupQuotientImage L C := by
      simp [subgroupQuotientImage, ρ, s, C, B,
        Finset.image_image, AddMonoidHom.coe_comp]
      apply Finset.image_congr
      intro x hx
      exact QuotientAddGroup.mk'_apply L _
    have hDoubleImage : (T + T).image ρ =
        subgroupQuotientImage L (C + C) := by
      calc
        (T + T).image ρ = T.image ρ + T.image ρ := Finset.image_add ρ
        _ = subgroupQuotientImage L C + subgroupQuotientImage L C := by rw [hImage]
        _ = subgroupQuotientImage L (C + C) := by
          simpa [subgroupQuotientImage, QuotientAddGroup.mk'_apply] using
            (Finset.image_add (QuotientAddGroup.mk' L) (s := C) (t := C)).symm
    have hI : (T.image ρ).card = 2 := by rw [hImage]; exact hLC
    have hII : ((T + T).image ρ).card = 3 := by
      rw [hDoubleImage]
      exact hLCC
    exact (not_two_image_three_sum_of_strict_threshold
      (H := H) (Q := Q₃)
      T ρ hzero hthreshold hI hII).elim

end Erdos336
