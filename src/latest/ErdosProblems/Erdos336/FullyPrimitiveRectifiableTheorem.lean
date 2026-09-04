import ErdosProblems.Erdos336.EndpointRectifiedKernel
import ErdosProblems.Erdos336.FullyPrimitiveQuotientDescent

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 2500000

open scoped Pointwise

/-- The complete fully primitive rectifiable theorem, obtained by normalizing
the strict-half graph, applying the endpoint assembly, and descending its
lifted certificate. -/
theorem fullyPrimitiveRectifiableThreeMinusThree :
    HasFullyPrimitiveRectifiableThreeMinusThree := by
  intro N hN
  let : NeZero N := ⟨hN.ne'⟩
  dsimp
  intro A hAne hAaff m hm
  let : NeZero m := ⟨hm.ne'⟩
  intro π hπ α houter hthreshold hfull
  have himage2 : 2 ≤ (A.image π).card := by
    by_contra hnot
    have hsmall : (A.image π).card ≤ 1 := by omega
    have hzero : (A.image π).card - 1 = 0 := Nat.sub_eq_zero_of_le hsmall
    rw [hzero] at hthreshold
    simp at hthreshold
  obtain ⟨p, hpA, q, hqA, L, hL, hLshort, hqπ, hnorm⟩ :=
    exists_normalized_strict_half_endpoints A π α houter himage2
  let A₀ : Finset (ZMod N) := -p +ᵥ A
  have houter₀raw : ∀ y ∈ A₀,
      ∃ k : ℕ, k ≤ L ∧ 2 * k < m ∧ π y = (k : ZMod m) := by
    simpa [A₀] using normalized_translate_outer A π p L hnorm
  have houter₀ : ∀ y ∈ A₀,
      ∃ k : ℕ, 2 * k < m ∧ π y = (0 : ZMod m) + (k : ZMod m) := by
    intro y hy
    obtain ⟨k, _hkL, hkshort, hkπ⟩ := houter₀raw y hy
    exact ⟨k, hkshort, by simpa using hkπ⟩
  have hzeroA₀ : (0 : ZMod N) ∈ A₀ := by
    apply Finset.mem_vadd_finset.mpr
    refine ⟨p, hpA, ?_⟩
    simp [vadd_eq_add]
  have hqA₀ : q - p ∈ A₀ := by
    apply Finset.mem_vadd_finset.mpr
    refine ⟨q, hqA, ?_⟩
    simp only [vadd_eq_add]
    abel
  have hlabel0 : halfIntervalLabel π 0 (0 : ZMod N) = 0 := by
    have hs := halfIntervalLabel_spec π 0 (0 : ZMod N)
      (houter₀ 0 hzeroA₀)
    apply short_zmod_cast_injective hs.1 (by simpa using hm)
    simpa using hs.2.symm
  have hlabelq : halfIntervalLabel π 0 (q - p) = L := by
    have hs := halfIntervalLabel_spec π 0 (q - p)
      (houter₀ (q - p) hqA₀)
    apply short_zmod_cast_injective hs.1 hLshort
    calc
      (halfIntervalLabel π 0 (q - p) : ZMod m) = π (q - p) := by
        simpa using hs.2.symm
      _ = (L : ZMod m) := hqπ
  let T := rectifiedLift A₀ π 0
  let l : ℤ := L
  let δ : ℤ × ZMod N := (l, q - p)
  have hzeroT : ((0 : ℤ), 0) ∈ T := by
    apply mem_rectifiedLift.mpr
    refine ⟨0, hzeroA₀, ?_⟩
    simp [hlabel0]
  have hδT : δ ∈ T := by
    apply mem_rectifiedLift.mpr
    refine ⟨q - p, hqA₀, ?_⟩
    simp [δ, l, hlabelq]
  have hlpos : 0 < l := by
    simpa [l] using (show (0 : ℤ) < (L : ℤ) by exact_mod_cast hL)
  have hδ : δ ∈ integerFiber T l :=
    mem_integerFiber.mpr ⟨hδT, rfl⟩
  have h0 : 0 ∈ T.image Prod.fst :=
    Finset.mem_image.mpr ⟨(0, 0), hzeroT, rfl⟩
  have hl : l ∈ T.image Prod.fst :=
    Finset.mem_image.mpr ⟨δ, hδT, rfl⟩
  have hbounds : ∀ z ∈ T.image Prod.fst, 0 ≤ z ∧ z ≤ l := by
    intro z hz
    obtain ⟨x, hxT, hxz⟩ := Finset.mem_image.mp hz
    obtain ⟨a, haA₀, hxa⟩ := mem_rectifiedLift.mp hxT
    obtain ⟨k, hkL, hlabel⟩ :=
      halfIntervalLabel_eq_normalized A₀ π L houter₀raw haA₀
    have hzEq : z = (k : ℤ) := by
      rw [← hxz, hxa, hlabel]
      rfl
    rw [hzEq]
    constructor
    · exact Int.ofNat_zero_le k
    · simpa [l] using (show (k : ℤ) ≤ (L : ℤ) by exact_mod_cast hkL)
  have hA₀card : A₀.card = A.card := by
    dsimp [A₀]
    exact Finset.card_vadd_finset _ _
  have hA₀double : (A₀ + A₀).card = (A + A).card := by
    simpa [A₀] using card_translate_double A p
  have hA₀image : (A₀.image π).card = (A.image π).card := by
    simpa [A₀] using card_image_vadd A p π
  have hTcard : T.card = A₀.card := by
    simpa [T] using card_rectifiedLift A₀ π 0
  have hTdouble : (T + T).card = (A₀ + A₀).card := by
    simpa [T] using card_add_rectifiedLift A₀ π 0 houter₀
  have hTfirst : (T.image Prod.fst).card = (A₀.image π).card := by
    simpa [T] using card_image_fst_rectifiedLift A₀ π 0 houter₀
  have hTthreshold : (T.image Prod.fst).card * (T + T).card <
      3 * ((T.image Prod.fst).card - 1) * T.card := by
    rw [hTfirst, hTdouble, hTcard, hA₀image, hA₀double, hA₀card]
    exact hthreshold
  have hsat₀ : ∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
      (addSubgroupFinset K).card ≤
        (A₀ + addSubgroupFinset K).card - A₀.card := by
    intro K hK hKne
    have hp := (hfull K hK hKne).1
    change (addSubgroupFinset K).card ≤
      ((-p +ᵥ A) + addSubgroupFinset K).card - (-p +ᵥ A).card
    rw [card_translate_add, Finset.card_vadd_finset]
    exact hp
  have hexpand : HasCoverExpansion T := by
    intro X Y hX hY hXY hXne hYne
    apply rectified_subset_expansion_of_kernelPrimitive A₀ π 0 houter₀
      hsat₀ X Y
    · simpa [T] using hX
    · simpa [T] using hY
    · simpa [T] using hXY
    · exact hXne
    · exact hYne
  have hendpoint :
      let Δ := AddSubgroup.zmultiples δ
      let qe : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
      let B := T.image qe
      let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
        AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ) (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
      endpointVerticalPart δ Fsub ≤ π.ker := by
    simpa using endpointVerticalPart_le_rectifyingKernel A₀ π
      (by
        intro x hx
        obtain ⟨k, _hkL, hkshort, hkπ⟩ := houter₀raw x hx
        exact ⟨k, hkshort, hkπ⟩)
      T rfl hzeroT δ hδT
  have hprimitiveT : ∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
      (addSubgroupFinset K).card ≤
        (T + verticalSubgroupFinset K).card - T.card ∧
      (T + verticalSubgroupFinset K).card - T.card <
        ((T + T) + verticalSubgroupFinset K).card - (T + T).card := by
    intro K hK hKne
    have hp := hfull K hK hKne
    have hTV := card_rectifiedLift_add_vertical A₀ π 0 houter₀ K hK
    have hTTV := card_add_rectifiedLift_add_vertical A₀ π 0 houter₀ K hK
    have hA₀K : (A₀ + addSubgroupFinset K).card =
        (A + addSubgroupFinset K).card := by
      simpa [A₀] using card_translate_add A (addSubgroupFinset K) p
    have hA₀AK : ((A₀ + A₀) + addSubgroupFinset K).card =
        ((A + A) + addSubgroupFinset K).card := by
      simpa [A₀] using card_translate_double_add A (addSubgroupFinset K) p
    rw [hTV, hTcard, hTTV, hTdouble, hA₀K, hA₀card, hA₀AK, hA₀double]
    exact hp
  have hTcert : LiftedModerateCertificate T :=
    liftedModerate_of_normalized_relativePrimitive T l hlpos hzeroT δ hδ
      h0 hl hbounds hTthreshold hexpand π.ker hendpoint hprimitiveT
  have hA₀aff : FinsetAffineGenerates A₀ := by
    simpa [A₀] using finsetAffineGenerates_vadd A p hAaff
  have hA₀cert : FinsetRankCertificate A₀ :=
    finsetRankCertificate_of_liftedModerate T A₀
      (by simpa [T] using image_snd_rectifiedLift A₀ π 0)
      hTcard hTdouble hA₀aff hTcert
  exact finsetRankCertificate_of_translate A p (by simpa [A₀] using hA₀cert)

end Erdos336
