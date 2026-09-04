import ErdosProblems.Erdos336.RectifiedLift
import ErdosProblems.Erdos336.RectifiableThreeMinusThreeReduction
import ErdosProblems.Erdos336.CyclicQuotientCardinality

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- The moderate-torsion conclusion in `ℤ × ZMod N`: containment in a
one-dimensional progression plus a vertical subgroup, with sharp defect cost. -/
def LiftedModerateCertificate (T : Finset (ℤ × ZMod N)) : Prop :=
  ∃ (p d : ℤ × ZMod N) (L : ℕ) (K : AddSubgroup (ZMod N)),
    0 < L ∧
    (∀ x ∈ T, ∃ i : ℕ, i ≤ L ∧
      ∃ k ∈ K, x = p + i • d + (0, k)) ∧
    L * (addSubgroupFinset K).card ≤ (T + T).card - T.card

/-- Affine generation forces the direction and vertical subgroup to generate
all of the cyclic coordinate. -/
theorem direction_join_eq_top_of_liftedModerate
    (T : Finset (ℤ × ZMod N)) (A : Finset (ZMod N))
    (himage : T.image Prod.snd = A)
    (hAaff : FinsetAffineGenerates A)
    {p d : ℤ × ZMod N} {L : ℕ} {K : AddSubgroup (ZMod N)}
    (houter : ∀ x ∈ T, ∃ i : ℕ, i ≤ L ∧
      ∃ k ∈ K, x = p + i • d + (0, k)) :
    K ⊔ AddSubgroup.zmultiples d.2 = ⊤ := by
  let H : AddSubgroup (ZMod N) := K ⊔ AddSubgroup.zmultiples d.2
  apply hAaff H p.2
  intro a ha
  have haT : a ∈ T.image Prod.snd := by simpa [himage] using ha
  obtain ⟨x, hxT, hxa⟩ := Finset.mem_image.mp haT
  obtain ⟨i, _hi, k, hk, hx⟩ := houter x hxT
  have hki : k ∈ H := by
    exact AddSubgroup.mem_sup.mpr
      ⟨k, hk, 0, (AddSubgroup.zmultiples d.2).zero_mem, by simp⟩
  have hdi : i • d.2 ∈ H := by
    apply AddSubgroup.mem_sup.mpr
    refine ⟨0, K.zero_mem, i • d.2, ?_, by simp⟩
    exact (AddSubgroup.zmultiples d.2).nsmul_mem
      (AddSubgroup.mem_zmultiples d.2) i
  have hsnd := congrArg Prod.snd hx
  rw [Prod.snd_add, Prod.snd_add] at hsnd
  have hsnd' : a = p.2 + i • d.2 + k := by
    rw [← hxa]
    simpa using hsnd
  rw [hsnd']
  have hadd := H.add_mem hdi hki
  convert hadd using 1 <;> abel

/-- The image of the progression direction generates the quotient by `K`. -/
theorem quotient_zmultiples_direction
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    ∀ y : ZMod N ⧸ K,
      y ∈ AddSubgroup.zmultiples ((QuotientAddGroup.mk' K) d) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective K y
  have hx : x ∈ K ⊔ AddSubgroup.zmultiples d := by rw [hgen]; simp
  obtain ⟨k, hk, z, hz, hkz⟩ := AddSubgroup.mem_sup.mp hx
  obtain ⟨r, hr⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨r, ?_⟩
  rw [← map_zsmul, hr, ← hkz, map_add]
  rw [show (QuotientAddGroup.mk' K) k = 0 from
    (QuotientAddGroup.eq_zero_iff k).mpr hk, zero_add]

/-- Quotient by `K`, normalized so that the direction maps to `1`. -/
noncomputable def directionQuotientEquiv
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    ZMod (Nat.card (ZMod N ⧸ K)) ≃+ (ZMod N ⧸ K) :=
  zmodAddEquivOfGenerator (quotient_zmultiples_direction K d hgen) rfl

noncomputable def directionQuotientHom
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    ZMod N →+ ZMod (Nat.card (ZMod N ⧸ K)) :=
  (directionQuotientEquiv K d hgen).symm.toAddMonoidHom.comp
    (QuotientAddGroup.mk' K)

@[simp] theorem directionQuotientHom_apply_direction
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    directionQuotientHom K d hgen d = 1 := by
  simp [directionQuotientHom, directionQuotientEquiv,
    zmodAddEquivOfGenerator_symm_apply_generator]

@[simp] theorem directionQuotientHom_ker
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    (directionQuotientHom K d hgen).ker = K := by
  ext x
  change directionQuotientHom K d hgen x = 0 ↔ x ∈ K
  constructor
  · intro hx
    have hq : (QuotientAddGroup.mk' K) x = 0 := by
      apply (directionQuotientEquiv K d hgen).symm.injective
      simpa [directionQuotientHom] using hx
    exact (QuotientAddGroup.eq_zero_iff x).mp hq
  · intro hx
    simp [directionQuotientHom, (QuotientAddGroup.eq_zero_iff x).mpr hx]

/-- The normalized direction quotient is surjective. -/
theorem directionQuotientHom_surjective
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤) :
    Function.Surjective (directionQuotientHom K d hgen) := by
  intro z
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective K
    ((directionQuotientEquiv K d hgen) z)
  refine ⟨x, ?_⟩
  simp only [directionQuotientHom, AddMonoidHom.coe_comp,
    AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  rw [hx, AddEquiv.symm_apply_apply]

/-- Every fibre of the direction quotient has cardinality `|K|`. -/
theorem card_directionQuotientHom_fiber
    (K : AddSubgroup (ZMod N)) (d : ZMod N)
    (hgen : K ⊔ AddSubgroup.zmultiples d = ⊤)
    (z : ZMod (Nat.card (ZMod N ⧸ K))) :
    (homFiberFinset (directionQuotientHom K d hgen) z).card =
      (addSubgroupFinset K).card := by
  let : NeZero (Nat.card (ZMod N ⧸ K)) := ⟨Nat.card_pos.ne'⟩
  rw [homFiberFinset,
    card_hom_fiber_finset_eq_card_ker _
      (directionQuotientHom_surjective K d hgen) z,
    directionQuotientHom_ker]

/-- A lifted progression-plus-subgroup certificate descends to the exact
finite rank certificate used by the endgame, provided the lift preserves the
three relevant cardinalities. -/
theorem finsetRankCertificate_of_liftedModerate
    (T : Finset (ℤ × ZMod N)) (A : Finset (ZMod N))
    (himage : T.image Prod.snd = A)
    (hcard : T.card = A.card)
    (hdouble : (T + T).card = (A + A).card)
    (hAaff : FinsetAffineGenerates A)
    (hcert : LiftedModerateCertificate T) :
    FinsetRankCertificate A := by
  obtain ⟨p, d, L, K, hL, houter, hcost⟩ := hcert
  let q := Nat.card (ZMod N ⧸ K)
  have hq : 0 < q := Nat.card_pos
  let _ : NeZero q := ⟨hq.ne'⟩
  have hgen : K ⊔ AddSubgroup.zmultiples d.2 = ⊤ :=
    direction_join_eq_top_of_liftedModerate T A himage hAaff houter
  let ρ : ZMod N →+ ZMod q := directionQuotientHom K d.2 hgen
  refine ⟨q, hq, ρ, directionQuotientHom_surjective K d.2 hgen,
    ρ p.2, L, (addSubgroupFinset K).card, hL, ?_, ?_, ?_⟩
  · intro a ha
    have haT : a ∈ T.image Prod.snd := by simpa [himage] using ha
    obtain ⟨x, hxT, hxa⟩ := Finset.mem_image.mp haT
    obtain ⟨i, hi, k, hk, hx⟩ := houter x hxT
    refine ⟨i, hi, ?_⟩
    have hsnd := congrArg Prod.snd hx
    have hk0 : ρ k = 0 := by
      have : k ∈ ρ.ker := by
        rw [show ρ.ker = K by
          exact directionQuotientHom_ker K d.2 hgen]
        exact hk
      exact this
    rw [← hxa]
    simp only [Prod.snd_add] at hsnd
    rw [hsnd, map_add, map_add]
    change ρ p.2 + ρ (i • d.2) + ρ k = ρ p.2 + (i : ZMod q)
    rw [map_nsmul, hk0, add_zero]
    rw [show ρ d.2 = 1 by
      exact directionQuotientHom_apply_direction K d.2 hgen]
    simp
  · intro z
    exact (card_directionQuotientHom_fiber K d.2 hgen z).le
  · rw [← hcard, ← hdouble]
    have hkpos : 0 < (addSubgroupFinset K).card := by
      rw [Finset.card_pos]
      exact ⟨0, by simpa using K.zero_mem⟩
    have hkprod : 0 < L * (addSubgroupFinset K).card :=
      Nat.mul_pos hL hkpos
    omega

/-- Isolated classical input in genuinely rectified coordinates. -/
def HasLiftedModerateThreeMinusThree : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨hN.ne'⟩
    ∀ (T : Finset (ℤ × ZMod N)), T.Nonempty →
      FinsetAffineGenerates (T.image Prod.snd) →
      (T.image Prod.fst).card * (T + T).card <
        3 * ((T.image Prod.fst).card - 1) * T.card →
      LiftedModerateCertificate T

/-- The genuinely rectified progression-plus-subgroup theorem implies the
cyclic strict-half theorem used in F-128. -/
theorem rectifiableThreeMinusThree_of_liftedModerate
    (hlift : HasLiftedModerateThreeMinusThree) :
    HasRectifiableThreeMinusThree := by
  intro N hN
  let : NeZero N := ⟨hN.ne'⟩
  dsimp
  intro A hAne hAaff m hm
  let : NeZero m := ⟨hm.ne'⟩
  intro π _hπ α houter hthreshold
  let T := rectifiedLift A π α
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, card_rectifiedLift]
    exact hAne.card_pos
  have hTimage : T.image Prod.snd = A :=
    image_snd_rectifiedLift A π α
  have hTaff : FinsetAffineGenerates (T.image Prod.snd) := by
    simpa [hTimage] using hAaff
  have hTthreshold :
      (T.image Prod.fst).card * (T + T).card <
        3 * ((T.image Prod.fst).card - 1) * T.card := by
    rw [card_image_fst_rectifiedLift A π α houter,
      card_add_rectifiedLift A π α houter,
      card_rectifiedLift]
    exact hthreshold
  have hTcert : LiftedModerateCertificate T :=
    hlift N hN T hTne hTaff hTthreshold
  exact finsetRankCertificate_of_liftedModerate T A hTimage
    (card_rectifiedLift A π α)
    (card_add_rectifiedLift A π α houter) hAaff hTcert

end Erdos336
