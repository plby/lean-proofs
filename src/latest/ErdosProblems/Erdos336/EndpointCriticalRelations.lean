import ErdosProblems.Erdos336.QuotientImageCard
import ErdosProblems.Erdos336.CriticalRepresentationDichotomy
import ErdosProblems.Erdos336.KneserConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- Exact critical cardinalities after quotienting a small-doubling set by
the stabilizer of its double sumset. -/
theorem endpoint_critical_card_relations
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (hBne : B.Nonempty) (hzero : 0 ∈ B)
    (hsmall : (B + B).card < 2 * B.card - 1) :
    let Ffin := (B + B).addStab
    let Fsub : AddSubgroup G := AddAction.stabilizer G (B + B : Set G)
    let r : G →+ (G ⧸ Fsub) := QuotientAddGroup.mk' Fsub
    let C := B.image r
    let D := criticalNewSums C
    (B + Ffin).card = (D.card + 1) * Ffin.card ∧
    (B + B).card = (2 * D.card + 1) * Ffin.card ∧
    C.card = D.card + 1 ∧
    (C + C).card = 2 * D.card + 1 := by
  classical
  dsimp
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup G := AddAction.stabilizer G (B + B : Set G)
  let r : G →+ (G ⧸ Fsub) := QuotientAddGroup.mk' Fsub
  let C := B.image r
  let D := criticalNewSums C
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroF : 0 ∈ Ffin := Finset.zero_mem_addStab.mpr hBBne
  have hFpos : 0 < Ffin.card := Finset.card_pos.mpr ⟨0, hzeroF⟩
  have hFmem (x : G) : x ∈ Ffin ↔ x ∈ Fsub := by
    change x ∈ (B + B).addStab ↔ x ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hBsat := card_add_subgroup_eq_quotient_image_mul Fsub Ffin hFmem B
  change (B + Ffin).card = C.card * Ffin.card at hBsat
  have hBBsatEq : (B + B) + Ffin = B + B := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, f, hf, rfl⟩ := Finset.mem_add.mp hx
      have hact := (Finset.mem_addStab' hBBne).mp hf hb
      simpa [vadd_eq_add, add_comm] using hact
    · intro hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroF, by simp⟩
  have hImageDouble : (B + B).image r = C + C := by
    simpa [C] using Finset.image_add r (s := B) (t := B)
  have hBBsat := card_add_subgroup_eq_quotient_image_mul Fsub Ffin hFmem (B + B)
  change ((B + B) + Ffin).card = ((B + B).image r).card * Ffin.card at hBBsat
  rw [hBBsatEq, hImageDouble] at hBBsat
  have hKneser := add_kneser_eq_of_card_le hBne hBne (by omega)
  change (B + Ffin).card + (B + Ffin).card =
    (B + B).card + Ffin.card at hKneser
  have hcrit : 2 * C.card = (C + C).card + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hFpos
    calc
      (2 * C.card) * Ffin.card =
          (B + Ffin).card + (B + Ffin).card := by rw [hBsat]; ring
      _ = (B + B).card + Ffin.card := hKneser
      _ = ((C + C).card + 1) * Ffin.card := by rw [hBBsat]; ring
  have hzeroC : 0 ∈ C := Finset.mem_image.mpr ⟨0, hzero, r.map_zero⟩
  have hCsub : C ⊆ C + C := by
    intro c hc
    exact Finset.mem_add.mpr ⟨c, hc, 0, hzeroC, by simp⟩
  have hDcard : D.card = (C + C).card - C.card := by
    dsimp [D, criticalNewSums]
    rw [Finset.card_sdiff_of_subset hCsub]
  have hCeq : C.card = D.card + 1 := by omega
  have hCCeq : (C + C).card = 2 * D.card + 1 := by omega
  change (B + Ffin).card = (D.card + 1) * Ffin.card ∧
    (B + B).card = (2 * D.card + 1) * Ffin.card ∧
    C.card = D.card + 1 ∧ (C + C).card = 2 * D.card + 1
  refine ⟨?_, ?_, hCeq, hCCeq⟩
  · rw [hBsat, hCeq]
  · rw [hBBsat, hCCeq]

end Erdos336
