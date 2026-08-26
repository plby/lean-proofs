import ErdosProblems.Erdos336.PrimitiveEndpointQuotientSmall
import ErdosProblems.Erdos336.SubgroupEndpointIndex
import ErdosProblems.Erdos336.LiftedModerateCertificate

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- If the Kneser quotient stabilizer found in F-140 already contains the
whole endpoint quotient set, then the desired progression-plus-vertical-
subgroup certificate follows. -/
theorem liftedModerate_of_endpointQuotient_collapse
    (T : Finset (ℤ × ZMod N)) (l : ℤ) (hlpos : 0 < l)
    (hzero : (0, 0) ∈ T) (δ : ℤ × ZMod N)
    (hδ : δ ∈ integerFiber T l)
    (h0 : 0 ∈ T.image Prod.fst) (hl : l ∈ T.image Prod.fst)
    (hboundsImage : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card)
    (hexpand : HasCoverExpansion T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let F := (B + B).addStab
    B + F = F → LiftedModerateCertificate T := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let F := (B + B).addStab
  intro hBFRaw
  have hBF : B + F = F := by
    simpa [B, F, q, Δ] using hBFRaw
  have hBne : B.Nonempty := Finset.image_nonempty.mpr ⟨(0, 0), hzero⟩
  have hBBne : (B + B).Nonempty := hBne.add hBne
  have hzeroB : 0 ∈ B := Finset.mem_image.mpr
    ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroF : 0 ∈ F := Finset.zero_mem_addStab.mpr hBBne
  have hBsubF : B ⊆ F := by
    intro b hb
    have hbBF : b ∈ B + F :=
      Finset.mem_add.mpr ⟨b, hb, 0, hzeroF, by simp⟩
    rw [hBF] at hbBF
    exact hbBF
  let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ)
      (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
  let J : AddSubgroup (ℤ × ZMod N) := Fsub.comap q
  have hFmem (z : (ℤ × ZMod N) ⧸ Δ) : z ∈ F ↔ z ∈ Fsub := by
    change z ∈ (B + B).addStab ↔ z ∈ Fsub
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simp [Fsub]
  have hδJ : δ ∈ J := by
    change q δ ∈ Fsub
    have hqδ : q δ = 0 := (QuotientAddGroup.eq_zero_iff δ).mpr
      (AddSubgroup.mem_zmultiples δ)
    rw [hqδ]
    exact Fsub.zero_mem
  have hδpos : 0 < δ.1 := by
    rw [(mem_integerFiber.mp hδ).2]
    exact hlpos
  obtain ⟨g, hgJ, hgpos, hdecomp⟩ :=
    exists_positive_generator_add_vertical J δ hδJ hδpos
  let K := verticalPart J
  have hKvert : ∀ k ∈ K, (0, k) ∈ J := by
    intro k hk
    exact hk
  obtain ⟨nδ, kδ, hkδ, hδrepRaw⟩ := hdecomp δ hδJ
  have hnδpos : 0 < nδ := by
    have hfirst := congrArg Prod.fst hδrepRaw
    change δ.1 = nδ * g.1 + 0 at hfirst
    nlinarith
  let L : ℕ := nδ.toNat
  have hL : 0 < L := by
    have hcast : (L : ℤ) = nδ := Int.toNat_of_nonneg hnδpos.le
    have hpos : (0 : ℤ) < (L : ℤ) := by rw [hcast]; exact hnδpos
    exact_mod_cast hpos
  have hLcast : (L : ℤ) = nδ := Int.toNat_of_nonneg hnδpos.le
  have hδrep : δ = (L : ℤ) • g + (0, kδ) := by
    simpa [hLcast] using hδrepRaw
  have hFcharacter : ∀ z, z ∈ F ↔ ∃ x ∈ J, q x = z := by
    intro z
    constructor
    · intro hz
      have hzsub : z ∈ Fsub := (hFmem z).mp hz
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Δ z
      refine ⟨x, ?_, rfl⟩
      exact hzsub
    · rintro ⟨x, hxJ, rfl⟩
      apply (hFmem _).mpr
      exact hxJ
  have hFcard : F.card = L * (addSubgroupFinset K).card := by
    exact card_endpointQuotient_subgroup J K g δ L hL hgJ hgpos
      hKvert hdecomp kδ hkδ hδrep F hFcharacter
  have hTout : ∀ x ∈ T, ∃ i : ℕ, i ≤ L ∧
      ∃ k ∈ K, x = (0, 0) + i • g + (0, k) := by
    intro x hxT
    have hqxB : q x ∈ B := Finset.mem_image.mpr ⟨x, hxT, rfl⟩
    have hqxF : q x ∈ F := hBsubF hqxB
    have hxJ : x ∈ J := by
      change q x ∈ Fsub
      exact (hFmem _).mp hqxF
    obtain ⟨n, k, hk, hxrep⟩ := hdecomp x hxJ
    have hfirst := congrArg Prod.fst hxrep
    change x.1 = n * g.1 + 0 at hfirst
    have hxb := hboundsImage x.1 (Finset.mem_image.mpr ⟨x, hxT, rfl⟩)
    have hδfirst := congrArg Prod.fst hδrep
    change δ.1 = (L : ℤ) * g.1 + 0 at hδfirst
    have hδfst : δ.1 = l := (mem_integerFiber.mp hδ).2
    have hn0 : 0 ≤ n := by nlinarith
    have hnL : n ≤ (L : ℤ) := by nlinarith
    let i := n.toNat
    have hicast : (i : ℤ) = n := Int.toNat_of_nonneg hn0
    have hiL : i ≤ L := by
      have hiLInt : (i : ℤ) ≤ (L : ℤ) := by rw [hicast]; exact hnL
      exact_mod_cast hiLInt
    refine ⟨i, hiL, k, hk, ?_⟩
    calc
      x = n • g + (0, k) := hxrep
      _ = i • g + (0, k) := by rw [← hicast]; simp
      _ = (0, 0) + i • g + (0, k) := by simp
  have hsmall := endpointQuotient_strict_two_minus_one T l hlpos hzero δ hδ
    h0 hl hboundsImage hthreshold hexpand
  change (B + B).card < 2 * B.card - 1 at hsmall
  have hKneser := add_kneser_eq_of_card_le hBne hBne (by omega)
  change (B + F).card + (B + F).card = (B + B).card + F.card at hKneser
  rw [hBF] at hKneser
  have hBBcard : (B + B).card = F.card := by omega
  let E := endpointOverlap T l δ
  have hEsub : E ⊆ T := by
    exact fun _ hx => (mem_integerFiber.mp (Finset.mem_inter.mp hx).1).1
  have hEne : E.Nonempty := by
    refine ⟨((0, 0) : ℤ × ZMod N), ?_⟩
    apply Finset.mem_inter.mpr
    refine ⟨mem_integerFiber.mpr ⟨hzero, rfl⟩, ?_⟩
    apply Finset.mem_vadd_finset.mpr
    refine ⟨δ, hδ, ?_⟩
    change -δ + δ = 0
    simp
  have hTE : T.card + E.card - 1 ≤ (T + E).card := by
    exact hexpand T E (by rfl) hEsub (Finset.union_eq_left.mpr hEsub)
      ⟨(0, 0), hzero⟩ hEne
  have hdoubleBound := card_image_double_add_card_add_endpointOverlap_le
    T l δ hδpos
  change ((T + T).image q).card + (T + E).card ≤ (T + T).card at hdoubleBound
  rw [Finset.image_add] at hdoubleBound
  have himageT : T.image q = B := rfl
  rw [himageT, hBBcard] at hdoubleBound
  have hcost : L * (addSubgroupFinset K).card ≤ (T + T).card - T.card := by
    rw [← hFcard]
    have hEpos := hEne.card_pos
    omega
  refine ⟨(0, 0), g, L, K, hL, hTout, hcost⟩

end Erdos336
