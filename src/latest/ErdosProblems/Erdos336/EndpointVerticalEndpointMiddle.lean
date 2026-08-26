import ErdosProblems.Erdos336.EndpointVerticalEndpointSums

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1200000

open scoped Pointwise BigOperators

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The elementary arithmetic behind the vertical-full middle/end interaction:
if the aligned endpoint class and an interior class jointly spend at most the
half-fibre deficiency budget, then the larger endpoint fibre and the interior
class have total size greater than one full fibre. -/
theorem larger_endpoint_add_interior_card_gt
    (f a0 al u x d : ℕ)
    (hf2 : 2 ≤ f) (hu : u ≤ a0 + al)
    (hule : u ≤ f) (hxle : x ≤ f)
    (hpair : (f - u) + (f - x) ≤ d)
    (hbudget : 2 * d ≤ f - 2) :
    (a0 ≤ al → f < al + x) ∧ (al ≤ a0 → f < a0 + x) := by
  have hfu := Nat.sub_add_cancel hule
  have hfx := Nat.sub_add_cancel hxle
  constructor <;> intro hord <;> omega

/-- In the vertical-full endpoint branch, the larger endpoint fibre added to
any interior endpoint-quotient class is the complete corresponding vertical
coset.  This is the second assertion of Lev's Claim 2, with all deficiency
bookkeeping explicit. -/
theorem add_larger_endpoint_fiber_class_eq_vertical
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
    ∀ a ∈ T, 0 < a.1 → a.1 < l →
    let K := endpointVerticalPart δ Fsub
    ((integerFiber T 0).card ≤ (integerFiber T l).card →
      integerFiber T l + endpointClassSlice T δ Fsub
          ((QuotientAddGroup.mk' Fsub) (q a)) =
        (δ + a) +ᵥ verticalSubgroupFinset K) ∧
    ((integerFiber T l).card ≤ (integerFiber T 0).card →
      integerFiber T 0 + endpointClassSlice T δ Fsub
          ((QuotientAddGroup.mk' Fsub) (q a)) =
        a +ᵥ verticalSubgroupFinset K) := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Ffin := (B + B).addStab
  let Fsub : AddSubgroup ((ℤ × H) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × H) ⧸ Δ) (B + B : Set ((ℤ × H) ⧸ Δ))
  intro hfull a haT ha0 hal
  let K := endpointVerticalPart δ Fsub
  let V := verticalSubgroupFinset K
  let U := endpointBoundaryUnion T l δ
  let X := endpointClassSlice T δ Fsub
    ((QuotientAddGroup.mk' Fsub) (q a))
  let r : ((ℤ × H) ⧸ Δ) →+ (((ℤ × H) ⧸ Δ) ⧸ Fsub) :=
    QuotientAddGroup.mk' Fsub
  let ca := r (q a)
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
  have hbudget : 2 * ((B + Ffin).card - B.card) ≤ Ffin.card - 2 := by
    simpa [B, Ffin, q, Δ] using hdefRaw.2
  have hUdouble := endpointBoundaryUnion_add_self_eq_vertical
    T l hlpos hzero δ hδ h0 hl hbounds hthreshold hexpand hfull
  change U + U = V at hUdouble
  have hzeroU : ((0 : ℤ), (0 : H)) ∈ U := by
    apply Finset.mem_union_left
    exact mem_integerFiber.mpr ⟨hzero, rfl⟩
  have hUsubV : U ⊆ V := by
    intro u hu
    rw [← hUdouble]
    exact Finset.mem_add.mpr ⟨(0, 0), hzeroU, u, hu, by simp⟩
  have hUle : U.card ≤ V.card := Finset.card_le_card hUsubV
  have hVcard : V.card = Ffin.card := by
    rw [card_verticalSubgroupFinset]
    exact hKcard
  have hUleF : U.card ≤ Ffin.card := by omega
  have hXsub := endpointClassSlice_subset_vertical_of_interior
    T l hlpos δ hδfst hboundsT Fsub Ffin hFmem hfull a haT ha0 hal
  change X ⊆ a +ᵥ V at hXsub
  have hXleV : X.card ≤ V.card := by
    calc
      X.card ≤ (a +ᵥ V).card := Finset.card_le_card hXsub
      _ = V.card := Finset.card_vadd_finset _ _
  have hXleF : X.card ≤ Ffin.card := by omega
  have hcaC : ca ∈ B.image r :=
    Finset.mem_image.mpr ⟨q a, Finset.mem_image.mpr ⟨a, haT, rfl⟩, rfl⟩
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroC : 0 ∈ B.image r :=
    Finset.mem_image.mpr ⟨0, hzeroB, r.map_zero⟩
  have hca0 : ca ≠ 0 := by
    intro hca
    have hqa0 : (QuotientAddGroup.mk' Fsub) (q a) = 0 := by
      simpa [ca, r] using hca
    have hqaF : q a ∈ Fsub :=
      (QuotientAddGroup.eq_zero_iff (q a)).mp hqa0
    obtain ⟨k, hk⟩ := hfull (q a) ((hFmem (q a)).mpr hqaF)
    have hk' : q ((0, k) : ℤ × H) = q a := by
      simpa [q, Δ, verticalEndpointHom] using hk
    have hqeq : q a = q ((0, k) : ℤ × H) := hk'.symm
    have hmem : a - ((0, k) : ℤ × H) ∈ Δ :=
      (QuotientAddGroup.eq_iff_sub_mem).mp hqeq
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hfirst := congrArg Prod.fst hn
    change n * δ.1 = a.1 - 0 at hfirst
    simp only [sub_zero] at hfirst
    rw [hδfst] at hfirst
    rcases lt_trichotomy n 1 with hnlt | hn1 | hngt
    · have hnle : n ≤ 0 := by omega
      have hmul : n * l ≤ 0 * l :=
        (mul_le_mul_iff_of_pos_right hlpos).mpr hnle
      nlinarith
    · nlinarith
    · have hnge : 2 ≤ n := by omega
      have hmul : 2 * l ≤ n * l :=
        (mul_le_mul_iff_of_pos_right hlpos).mpr hnge
      nlinarith
  have hzeroF : 0 ∈ Ffin := (hFmem 0).mpr Fsub.zero_mem
  have hzeroV : (0 : ℤ × H) ∈ V :=
    mem_verticalSubgroupFinset.mpr ⟨rfl, K.zero_mem⟩
  have hUimage : U.image q = B ∩ verticalEndpointFinset δ := by
    simpa [U, B, q, Δ] using
      image_endpointBoundaryUnion_eq_inter_vertical T l hlpos δ hδfst hboundsT
  have hinjU := endpointQuotient_injective_on_boundary T l δ hδpos hδfst
  have hcardUimage : (U.image q).card = U.card :=
    Finset.card_image_iff.mpr (by simpa [U, q, Δ] using hinjU)
  have hQVeq : B ∩ verticalEndpointFinset δ = quotientFiberFinset Fsub B 0 := by
    ext b
    constructor
    · intro hb
      have hbB := (Finset.mem_inter.mp hb).1
      have hbU : b ∈ U.image q := by
        rw [hUimage]
        exact hb
      obtain ⟨u, huU, hub⟩ := Finset.mem_image.mp hbU
      have huV := hUsubV huU
      have hu0 := (mem_verticalSubgroupFinset.mp huV).1
      have huK := (mem_verticalSubgroupFinset.mp huV).2
      have hqu : q u = verticalEndpointHom δ u.2 := by
        apply congrArg q
        exact Prod.ext hu0 rfl
      have hquF : q u ∈ Fsub := by
        rw [hqu]
        exact huK
      have hbF : b ∈ Fsub := by simpa [hub] using hquF
      exact mem_quotientFiberFinset.mpr
        ⟨hbB, (QuotientAddGroup.eq_zero_iff b).mpr hbF⟩
    · intro hb
      have hb' := mem_quotientFiberFinset.mp hb
      have hbF : b ∈ Fsub := (QuotientAddGroup.eq_zero_iff b).mp hb'.2
      obtain ⟨k, hk⟩ := hfull b ((hFmem b).mpr hbF)
      exact Finset.mem_inter.mpr
        ⟨hb'.1, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩⟩
  have hUfiber : U.card = (quotientFiberFinset Fsub B 0).card := by
    rw [← hcardUimage, hUimage, hQVeq]
  have hXfiberLe : (quotientFiberFinset Fsub B ca).card ≤ X.card := by
    have hocc := card_endpointClassInImage_le_slice T δ Fsub ca
    simpa [endpointClassInImage, quotientFiberFinset, B, q, r, ca, X] using hocc
  have hfib0 := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B 0
  have hfiba := card_quotient_fiber_le_subgroup Fsub Ffin hFmem B ca
  have hpairDef : quotientFiberDeficiency Fsub Ffin B 0 +
      quotientFiberDeficiency Fsub Ffin B ca ≤
        quotientDeficiency Fsub Ffin B := by
    let P : Finset (((ℤ × H) ⧸ Δ) ⧸ Fsub) := {0, ca}
    have hPsub : P ⊆ quotientImage Fsub B := by
      intro z hz
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simpa [quotientImage, r] using hzeroC
      · simpa [quotientImage, r] using hcaC
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun z => quotientFiberDeficiency Fsub Ffin B z) hPsub
      (fun _ _ _ => Nat.zero_le _)
    change (∑ z ∈ P, quotientFiberDeficiency Fsub Ffin B z) ≤
      quotientDeficiency Fsub Ffin B at hs
    have hca0' : (0 : (((ℤ × H) ⧸ Δ) ⧸ Fsub)) ≠ ca := Ne.symm hca0
    simpa [P, hca0'] using hs
  have htotal := quotientDeficiency_eq_saturation_sub Fsub Ffin hFmem B
  rw [htotal] at hpairDef
  change (Ffin.card - (quotientFiberFinset Fsub B 0).card) +
      (Ffin.card - (quotientFiberFinset Fsub B ca).card) ≤
        (B + Ffin).card - B.card at hpairDef
  have hpairUX : (Ffin.card - U.card) + (Ffin.card - X.card) ≤
      (B + Ffin).card - B.card := by
    rw [hUfiber]
    exact le_trans (Nat.add_le_add_left
      (Nat.sub_le_sub_left hXfiberLe Ffin.card) _) hpairDef
  have hUcardBound : U.card ≤
      (integerFiber T 0).card + (integerFiber T l).card := by
    dsimp [U, endpointBoundaryUnion]
    exact le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_left (Finset.card_vadd_finset (-δ) (integerFiber T l)).le _)
  have hcards := larger_endpoint_add_interior_card_gt
    Ffin.card (integerFiber T 0).card (integerFiber T l).card
      U.card X.card ((B + Ffin).card - B.card)
      hF2 hUcardBound hUleF hXleF hpairUX hbudget
  have hfibers := endpoint_fibers_single_vertical_cosets T l hlpos hzero δ hδ
    h0 hl hbounds hthreshold hexpand hfull
  change integerFiber T 0 ⊆ V ∧ integerFiber T l ⊆ δ +ᵥ V at hfibers
  constructor
  · intro hord
    have hlargeF : V.card < (integerFiber T l).card + X.card := by
      rw [hVcard]
      exact hcards.1 hord
    change integerFiber T l + X = (δ + a) +ᵥ V
    exact add_eq_vadd_vertical_of_card_lt K (integerFiber T l) X δ a
      hfibers.2 hXsub hlargeF
  · intro hord
    have hlargeF : V.card < (integerFiber T 0).card + X.card := by
      rw [hVcard]
      exact hcards.2 hord
    have hA0sub : integerFiber T 0 ⊆ ((0 : ℤ), (0 : H)) +ᵥ V := by
      intro z hz
      exact Finset.mem_vadd_finset.mpr ⟨z, hfibers.1 hz, by simp⟩
    have hout := add_eq_vadd_vertical_of_card_lt K (integerFiber T 0) X
      ((0 : ℤ), (0 : H)) a hA0sub hXsub hlargeF
    change integerFiber T 0 + X = a +ᵥ V
    have hz : ((0 : ℤ), (0 : H)) + a = a := by simp
    rw [hz] at hout
    exact hout

end Erdos336
