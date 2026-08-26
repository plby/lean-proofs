import ErdosProblems.Erdos336.FullyPrimitiveEndpointAssembly

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 2000000

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- Relative version of the endpoint assembly: only subgroups inside a fixed
ambient subgroup `P` are assumed primitive, provided the vertical part of the
endpoint stabilizer lies in `P`. -/
theorem liftedModerate_of_normalized_relativePrimitive
    (T : Finset (ℤ × ZMod N)) (l : ℤ) (hlpos : 0 < l)
    (hzero : ((0 : ℤ), 0) ∈ T) (δ : ℤ × ZMod N)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hbounds : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) (P : AddSubgroup (ZMod N))
    (hendpoint :
      let Δ := AddSubgroup.zmultiples δ
      let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
      let B := T.image q
      let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
        AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ) (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
      endpointVerticalPart δ Fsub ≤ P)
    (hprimitive : ∀ K : AddSubgroup (ZMod N), K ≤ P → K ≠ ⊥ →
      (addSubgroupFinset K).card ≤
        (T + verticalSubgroupFinset K).card - T.card ∧
      (T + verticalSubgroupFinset K).card - T.card <
        ((T + T) + verticalSubgroupFinset K).card - (T + T).card) :
    LiftedModerateCertificate T := by
  classical
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ) (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
  let r : ((ℤ × ZMod N) ⧸ Δ) →+ (((ℤ × ZMod N) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let C := B.image r
  let D := criticalNewSums C
  have hKle : endpointVerticalPart δ Fsub ≤ P := by
    simpa [Fsub, B, q, Δ] using hendpoint
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
  by_cases hD0 : D.card = 0
  · have hzeroF : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr hBBne
    have hFsubBF : Ffin ⊆ B + Ffin := by
      intro f hf
      exact Finset.mem_add.mpr ⟨0, hzeroB, f, hf, by simp⟩
    have hcardBF : (B + Ffin).card = Ffin.card := by rw [hrels.1, hD0]; simp
    have hcollapse : B + Ffin = Ffin := by
      have heq : Ffin = B + Ffin :=
        Finset.eq_of_subset_of_card_le hFsubBF (by omega)
      exact heq.symm
    exact liftedModerate_of_endpointQuotient_collapse T l hlpos hzero δ hδ
      h0 hl hbounds hthreshold hexpand (by
        simpa [B, Ffin, q, Δ] using hcollapse)
  · by_cases hD1 : D.card = 1
    · have htwo : (B + Ffin).card = 2 * Ffin.card := by rw [hrels.1, hD1]
      exact (endpointQuotient_not_two_stabilizer_cosets T δ hzero hthreshold
        (by simpa [B, q, Δ] using hsmall)
        (by simpa [B, Ffin, q, Δ] using htwo)).elim
    · have hD2le : 2 ≤ D.card := by omega
      have hFmem (a : ((ℤ × ZMod N) ⧸ Δ)) : a ∈ Ffin ↔ a ∈ Fsub := by
        change a ∈ (B + B).addStab ↔ a ∈ Fsub
        rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
        simp [Fsub]
      by_cases hfull : ∀ f ∈ Ffin, ∃ k : ZMod N, verticalEndpointHom δ k = f
      · let K := endpointVerticalPart δ Fsub
        have hstabRaw := endpointQuotient_nontrivial_stabilizer T l hlpos hzero
          δ hδ h0 hl hbounds hthreshold hexpand
        have hF2 : 2 ≤ Ffin.card := by
          simpa [B, Ffin, q, Δ] using hstabRaw.1
        have hKcard : (addSubgroupFinset K).card = Ffin.card := by
          exact card_endpointVerticalPart_eq_of_full δ
            (by rw [(mem_integerFiber.mp hδ).2]; exact hlpos)
            Fsub Ffin hFmem hfull
        have hKne : K ≠ ⊥ := by
          intro hbot
          have hone : (addSubgroupFinset K).card = 1 := by
            rw [hbot]
            apply Finset.card_eq_one.mpr
            refine ⟨0, ?_⟩
            ext x
            simp only [mem_addSubgroupFinset, AddSubgroup.mem_bot, Finset.mem_singleton]
          omega
        have hp := hprimitive K (by simpa [K] using hKle) hKne
        have hv := vertical_full_double_defect_le T l hlpos hzero δ hδ h0 hl
          hbounds hthreshold hexpand (by
            simpa [B, Ffin, Fsub, q, Δ] using hfull)
        exact ((not_lt_of_ge (by
          simpa [K, Fsub, B, Ffin, q, Δ] using hv)) hp.2).elim
      · push_neg at hfull
        by_cases hD2 : D.card = 2
        · exact (endpoint_proper_two_impossible T l hlpos hzero δ hδ h0 hl
            hbounds hthreshold hexpand
            (by simpa [D, C, r, Fsub, B, q, Δ] using hD2)
            (by simpa [B, Ffin, q, Δ] using hfull)).elim
        · have hD3 : 3 ≤ D.card := by omega
          exact (endpoint_proper_three_impossible T l hlpos hzero δ hδ h0 hl
            hbounds hthreshold hexpand
            (by simpa [D, C, r, Fsub, B, q, Δ] using hD3)
            (by simpa [B, Ffin, q, Δ] using hfull)).elim

end Erdos336
