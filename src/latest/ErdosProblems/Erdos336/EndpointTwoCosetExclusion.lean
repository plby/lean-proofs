import ErdosProblems.Erdos336.PrimitiveEndpointQuotientSmall
import ErdosProblems.Erdos336.QuotientImageCard
import ErdosProblems.Erdos336.TwoImageThreshold

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 800000

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- The endpoint Kneser quotient cannot occupy exactly two stabilizer cosets:
the sharp two-piece estimate would contradict the rectifiable threshold. -/
theorem endpointQuotient_not_two_stabilizer_cosets
    (T : Finset (ℤ × ZMod N)) (δ : ℤ × ZMod N)
    (hzero : (0, 0) ∈ T)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let F := (B + B).addStab
    (B + B).card < 2 * B.card - 1 →
    (B + F).card ≠ 2 * F.card := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let F := (B + B).addStab
  intro hsmallRaw htwoRaw
  have hsmall : (B + B).card < 2 * B.card - 1 := by
    simpa [B, q, Δ] using hsmallRaw
  have htwo : (B + F).card = 2 * F.card := by
    simpa [B, F, q, Δ] using htwoRaw
  have hBne : B.Nonempty := Finset.image_nonempty.mpr ⟨(0, 0), hzero⟩
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroF : 0 ∈ F := Finset.zero_mem_addStab.mpr hBBne
  have hFpos : 0 < F.card := by
    have hFne : F.Nonempty := ⟨0, hzeroF⟩
    exact hFne.card_pos
  let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ)
      (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
  have hFmem (x : (ℤ × ZMod N) ⧸ Δ) : x ∈ F ↔ x ∈ Fsub := by
    change x ∈ (B + B).addStab ↔ x ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  let r : ((ℤ × ZMod N) ⧸ Δ) →+
      (((ℤ × ZMod N) ⧸ Δ) ⧸ Fsub) := QuotientAddGroup.mk' Fsub
  let ρ : (ℤ × ZMod N) →+
      (((ℤ × ZMod N) ⧸ Δ) ⧸ Fsub) := r.comp q
  have hBsat := card_add_subgroup_eq_quotient_image_mul Fsub F hFmem B
  change (B + F).card = (B.image r).card * F.card at hBsat
  have hBimage : (B.image r).card = 2 := by
    apply Nat.eq_of_mul_eq_mul_right hFpos
    rw [← hBsat, htwo]
  have hBBsatEq : (B + B) + F = B + B := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, f, hf, rfl⟩ := Finset.mem_add.mp hx
      have hfb := (Finset.mem_addStab' hBBne).mp hf hb
      simpa [vadd_eq_add, add_comm] using hfb
    · intro hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzeroF, by simp⟩
  have hKneser := add_kneser_eq_of_card_le hBne hBne (by omega)
  change (B + F).card + (B + F).card = (B + B).card + F.card at hKneser
  have hBBcard : (B + B).card = 3 * F.card := by
    rw [htwo] at hKneser
    omega
  have hBBsat := card_add_subgroup_eq_quotient_image_mul Fsub F hFmem (B + B)
  change ((B + B) + F).card = ((B + B).image r).card * F.card at hBBsat
  have hBBimage : ((B + B).image r).card = 3 := by
    apply Nat.eq_of_mul_eq_mul_right hFpos
    rw [← hBBsat, hBBsatEq, hBBcard]
  have hTimage : (T.image ρ).card = 2 := by
    have heq : T.image ρ = B.image r := by
      change Finset.image (r ∘ q) T = B.image r
      rw [← Finset.image_image]
    rw [heq, hBimage]
  have hTTimage : ((T + T).image ρ).card = 3 := by
    have heq : (T + T).image ρ = (B + B).image r := by
      change Finset.image (r ∘ q) (T + T) = (B + B).image r
      rw [← Finset.image_image]
      change ((T + T).image q).image r = (B + B).image r
      rw [Finset.image_add]
    rw [heq, hBBimage]
  exact not_two_image_three_sum_of_strict_threshold
    (H := ZMod N) (Q := (((ℤ × ZMod N) ⧸ Δ) ⧸ Fsub))
    T ρ hzero hthreshold hTimage hTTimage

end Erdos336
