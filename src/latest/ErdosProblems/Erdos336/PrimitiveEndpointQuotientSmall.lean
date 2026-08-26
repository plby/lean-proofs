import ErdosProblems.Erdos336.EndpointQuotientOverlapBound
import ErdosProblems.Erdos336.IntegerFiberEndpoint
import ErdosProblems.Erdos336.KneserConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- The cover-expansion property left after all small-defect subgroup
quotients have been removed. -/
def HasCoverExpansion (T : Finset (ℤ × H)) : Prop :=
  ∀ X Y : Finset (ℤ × H), X ⊆ T → Y ⊆ T → X ∪ Y = T →
    X.Nonempty → Y.Nonempty → X.card + Y.card - 1 ≤ (X + Y).card

/-- Endpoint overlap and cover expansion force the quotient by the endpoint
displacement to have doubling strictly below `2|A|-1`. -/
theorem endpointQuotient_strict_two_minus_one
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : (0, 0) ∈ T) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hboundsImage : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    ((T.image q) + (T.image q)).card < 2 * (T.image q).card - 1 := by
  dsimp
  let E := endpointOverlap T l δ
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
  have hbounds : ∀ x ∈ T, 0 ≤ x.1 ∧ x.1 ≤ l := by
    intro x hx
    exact hboundsImage x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hEsub : E ⊆ T := by
    exact fun _ hx => (mem_integerFiber.mp (Finset.mem_inter.mp hx).1).1
  have hEne : E.Nonempty := by
    refine ⟨((0, 0) : ℤ × H), ?_⟩
    apply Finset.mem_inter.mpr
    refine ⟨mem_integerFiber.mpr ⟨hzero, rfl⟩, ?_⟩
    apply Finset.mem_vadd_finset.mpr
    refine ⟨δ, hδ, ?_⟩
    change -δ + δ = 0
    simp
  have hTE : T.card + E.card - 1 ≤ (T + E).card := by
    apply hexpand T E (by rfl) hEsub
    · exact Finset.union_eq_left.mpr hEsub
    · exact ⟨(0, 0), hzero⟩
    · exact hEne
  have hdef := (endpoint_fiber_deficiency_consequences T l hlpos
    hzero δ hδ h0 hl hboundsImage hthreshold).2
  have hAbar := card_image_endpointQuotient T l δ hlpos hδfst hbounds
  have hDbar := card_image_double_add_card_add_endpointOverlap_le
    T l δ (by simpa [hδfst] using hlpos)
  change (T.image q).card + E.card = T.card at hAbar
  change ((T + T).image q).card + (T + E).card ≤ (T + T).card at hDbar
  rw [Finset.image_add] at hDbar
  change (T + T).card + 2 * E.card < 3 * T.card at hdef
  have hspos : 0 < (T.image Prod.fst).card := by
    rw [Finset.card_pos]
    exact ⟨0, h0⟩
  have hsle : (T.image Prod.fst).card ≤ T.card := Finset.card_image_le
  have hgap : (T + T).card + 3 < 3 * T.card := by
    have hsEq : (T.image Prod.fst).card - 1 + 1 =
        (T.image Prod.fst).card := by omega
    nlinarith
  have hEpos : 0 < E.card := hEne.card_pos
  have hstrong : (T + T).card + E.card + 2 < 3 * T.card := by
    by_cases he1 : E.card = 1
    · omega
    · have he2 : 2 ≤ E.card := by omega
      omega
  change (T.image q + T.image q).card < 2 * (T.image q).card - 1
  omega

/-- The quotient double sumset therefore has a nontrivial stabilizer, and the
saturation defect of the quotient set is at most half its stabilizer minus
one. -/
theorem endpointQuotient_nontrivial_stabilizer
    (T : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : (0, 0) ∈ T) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hboundsImage : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let F := (B + B).addStab
    2 ≤ F.card ∧
      2 * ((B + F).card - B.card) ≤ F.card - 2 := by
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let F := (B + B).addStab
  change 2 ≤ F.card ∧
    2 * ((B + F).card - B.card) ≤ F.card - 2
  have hBne : B.Nonempty := by
    exact (Finset.image_nonempty.mpr ⟨(0, 0), hzero⟩)
  have hsmallRaw := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hboundsImage hthreshold hexpand
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have hsmallLe : (B + B).card ≤ B.card + B.card - 1 := by omega
  have hk := add_kneser_eq_of_card_le hBne hBne hsmallLe
  have hFeq : F = (B + B).addStab := rfl
  rw [← hFeq] at hk
  have hzeroF : 0 ∈ F := Finset.zero_mem_addStab.mpr (hBne.add hBne)
  have hBsub : B ⊆ B + F := by
    intro b hb
    exact Finset.mem_add.mpr ⟨b, hb, 0, hzeroF, by simp⟩
  have hBle := Finset.card_le_card hBsub
  have hF2 : 2 ≤ F.card := by omega
  refine ⟨hF2, ?_⟩
  omega

end Erdos336
