import ErdosProblems.Erdos336.SmallDefectRankDescent

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- The factor of a homomorphism through the canonical cyclic quotient by a
subgroup contained in its kernel. -/
noncomputable def cyclicQuotientFactor
    {Q : Type*} [AddCommGroup Q]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ Q) (hK : K ≤ π.ker) :
    ZMod (Nat.card (ZMod N ⧸ K)) →+ Q := by
  let hcyc : IsAddCyclic (ZMod N ⧸ K) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' K)
      (QuotientAddGroup.mk'_surjective K)
  let e := zmodAddCyclicAddEquiv hcyc
  exact (QuotientAddGroup.lift K π hK).comp e.toAddMonoidHom

@[simp] theorem cyclicQuotientFactor_apply_cyclicQuotientHom
    {Q : Type*} [AddCommGroup Q]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ Q) (hK : K ≤ π.ker)
    (x : ZMod N) :
    cyclicQuotientFactor K π hK (cyclicQuotientHom K x) = π x := by
  simp [cyclicQuotientFactor, cyclicQuotientHom,
    QuotientAddGroup.lift_mk']

/-- Surjectivity descends to the factor homomorphism. -/
theorem cyclicQuotientFactor_surjective
    {Q : Type*} [AddCommGroup Q]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ Q) (hK : K ≤ π.ker)
    (hπ : Function.Surjective π) :
    Function.Surjective (cyclicQuotientFactor K π hK) := by
  intro y
  obtain ⟨x, hx⟩ := hπ y
  refine ⟨cyclicQuotientHom K x, ?_⟩
  simpa using hx

/-- The image through the original map is exactly the image of the quotient
set through the factor. -/
theorem image_cyclicQuotientFactor
    {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ Q) (hK : K ≤ π.ker)
    (A : Finset (ZMod N)) :
    (A.image (cyclicQuotientHom K)).image (cyclicQuotientFactor K π hK) =
      A.image π := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx,
      (cyclicQuotientFactor_apply_cyclicQuotientHom K π hK x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨cyclicQuotientHom K x, ⟨x, hx, rfl⟩,
      cyclicQuotientFactor_apply_cyclicQuotientHom K π hK x⟩

/-- A strict-half interval certificate descends through every subgroup of the
rectifying kernel. -/
theorem half_interval_descends_cyclicQuotient
    {m : ℕ} [NeZero m]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ ZMod m)
    (hK : K ≤ π.ker) (A : Finset (ZMod N)) (α : ZMod m)
    (houter : ∀ x ∈ A, ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) :
    ∀ y ∈ A.image (cyclicQuotientHom K),
      ∃ q : ℕ, 2 * q < m ∧
        cyclicQuotientFactor K π hK y = α + (q : ZMod m) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨q, hq, hπq⟩ := houter x hx
  exact ⟨q, hq, by simpa using hπq⟩

/-- Affine generation is preserved by a surjective homomorphic image. -/
theorem FinsetAffineGenerates.image
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [DecidableEq G] [DecidableEq Q]
    {A : Finset G} (hA : FinsetAffineGenerates A)
    (f : G →+ Q) (hf : Function.Surjective f) :
    FinsetAffineGenerates (A.image f) := by
  intro H b hcos
  obtain ⟨b0, hb0⟩ := hf b
  let K : AddSubgroup G := H.comap f
  have hpre : ∀ x ∈ A, x - b0 ∈ K := by
    intro x hx
    change f (x - b0) ∈ H
    rw [map_sub, hb0]
    exact hcos (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hKtop : K = ⊤ := hA K b0 hpre
  rw [AddSubgroup.eq_top_iff']
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxK : x ∈ K := by rw [hKtop]; simp
  change f x ∈ H at hxK
  simpa [hx] using hxK

/-- The exact rectifiable threshold descends through a small-defect subgroup
of the rectifying kernel. -/
theorem three_minus_three_descends_cyclicQuotient
    {m : ℕ} [NeZero m]
    (K : AddSubgroup (ZMod N)) (π : ZMod N →+ ZMod m)
    (hK : K ≤ π.ker) (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    (hsmall : (A.image π).card * (A + A).card <
      3 * ((A.image π).card - 1) * A.card) :
    let f := cyclicQuotientHom K
    let πbar := cyclicQuotientFactor K π hK
    ((A.image f).image πbar).card *
        (A.image f + A.image f).card <
      3 * (((A.image f).image πbar).card - 1) * (A.image f).card := by
  let f := cyclicQuotientHom K
  let πbar := cyclicQuotientFactor K π hK
  let s := (A.image π).card
  let X := (A.image f).card
  let Y := (A.image f + A.image f).card
  let k := (addSubgroupFinset K).card
  have hsmallS : s * (A + A).card < 3 * (s - 1) * A.card := by
    simpa [s] using hsmall
  have hs2 : 2 ≤ s := by
    have hs0 : s ≠ 0 := by
      intro hs
      rw [hs] at hsmallS
      simp at hsmallS
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsmallS
      simp at hsmallS
    omega
  have hsat := three_minus_three_survives_small_defect_subgroup_saturation
    s hs2 K A hAne hdefect (by simpa [s] using hsmall)
  have hcardA := card_add_subgroup_eq_cyclicQuotient_image_mul K A
  have himageDouble : (A + A).image f = A.image f + A.image f := by
    simpa [f] using (Finset.image_add f (s := A) (t := A))
  have hcardD := card_add_subgroup_eq_cyclicQuotient_image_mul K (A + A)
  rw [himageDouble] at hcardD
  have hcardA' : (A + addSubgroupFinset K).card = X * k := by
    simpa [X, k, f] using hcardA
  have hcardD' : ((A + A) + addSubgroupFinset K).card = Y * k := by
    simpa [Y, k, f] using hcardD
  have hscaled : s * (Y * k) < 3 * (s - 1) * (X * k) := by
    rw [hcardA', hcardD'] at hsat
    exact hsat.1
  have hkpos : 0 < k := by
    dsimp [k]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  have hcancel : s * Y < 3 * (s - 1) * X := by
    apply (Nat.mul_lt_mul_right hkpos).mp
    simpa [mul_assoc] using hscaled
  have himage := image_cyclicQuotientFactor K π hK A
  change ((A.image f).image πbar).card * Y <
    3 * (((A.image f).image πbar).card - 1) * X
  rw [himage]
  simpa [s] using hcancel

/-- Remaining primitive rectifiable case: every nonzero subgroup of the
rectifying kernel costs at least one full fibre to saturate. -/
def HasKernelPrimitiveRectifiableThreeMinusThree : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨hN.ne'⟩
    ∀ (A : Finset (ZMod N)), A.Nonempty → FinsetAffineGenerates A →
      ∀ (m : ℕ) (hm : 0 < m),
        let _ : NeZero m := ⟨hm.ne'⟩
        ∀ (π : ZMod N →+ ZMod m), Function.Surjective π →
          ∀ α : ZMod m,
            (∀ x ∈ A, ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) →
            (A.image π).card * (A + A).card <
              3 * ((A.image π).card - 1) * A.card →
            (∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
              (A + addSubgroupFinset K).card - A.card ≥
                (addSubgroupFinset K).card) →
            FinsetRankCertificate A

/-- Small-defect quotient descent reduces the full rectifiable theorem to the
kernel-primitive case. -/
theorem rectifiableThreeMinusThree_of_kernelPrimitive
    (hprimitive : HasKernelPrimitiveRectifiableThreeMinusThree) :
    HasRectifiableThreeMinusThree := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      letI : NeZero N := ⟨hN.ne'⟩
      dsimp
      intro A hAne hAaff m hm
      letI : NeZero m := ⟨hm.ne'⟩
      intro π hπ α houter hsmall
      by_cases hsat : ∀ K : AddSubgroup (ZMod N), K ≤ π.ker → K ≠ ⊥ →
          (addSubgroupFinset K).card ≤
            (A + addSubgroupFinset K).card - A.card
      · exact hprimitive N hN A hAne hAaff m hm π hπ α houter hsmall hsat
      · push_neg at hsat
        obtain ⟨K, hKker, hKne, hKsmall⟩ := hsat
        let q := Nat.card (ZMod N ⧸ K)
        have hq : 0 < q := Nat.card_pos
        letI : NeZero q := ⟨hq.ne'⟩
        let f := cyclicQuotientHom K
        let πbar := cyclicQuotientFactor K π hKker
        have hKcard2 : 2 ≤ (addSubgroupFinset K).card := by
          letI : Fintype K := Fintype.ofFinite K
          have hk := (AddSubgroup.one_lt_card_iff_ne_bot K).mpr hKne
          have hk' : 1 < (addSubgroupFinset K).card := by
            simpa [addSubgroupFinset, Nat.card_eq_fintype_card] using hk
          omega
        letI : Fintype K := Fintype.ofFinite K
        have hNcard : N = q * (addSubgroupFinset K).card := by
          have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
          have hkcard : Nat.card K = (addSubgroupFinset K).card := by
            rw [Nat.card_eq_fintype_card]
            simp [addSubgroupFinset]
          calc
            N = Nat.card (ZMod N ⧸ K) * Nat.card K := by simpa using hc
            _ = q * (addSubgroupFinset K).card := by rw [hkcard]
        have hqN : q < N := by rw [hNcard]; nlinarith
        have hImageNe : (A.image f).Nonempty := hAne.image f
        have hImageAff : FinsetAffineGenerates (A.image f) :=
          hAaff.image f (cyclicQuotientHom_surjective K)
        have hπbar : Function.Surjective πbar :=
          cyclicQuotientFactor_surjective K π hKker hπ
        have houterChild : ∀ y ∈ A.image f,
            ∃ r : ℕ, 2 * r < m ∧ πbar y = α + (r : ZMod m) := by
          simpa [f, πbar] using
            half_interval_descends_cyclicQuotient K π hKker A α houter
        have hsmallChild : ((A.image f).image πbar).card *
              (A.image f + A.image f).card <
            3 * (((A.image f).image πbar).card - 1) * (A.image f).card := by
          simpa [f, πbar] using three_minus_three_descends_cyclicQuotient
            K π hKker A hAne hKsmall hsmall
        have hchild : FinsetRankCertificate (A.image f) :=
          ih q hqN hq (A.image f) hImageNe hImageAff m hm πbar hπbar
            α houterChild hsmallChild
        exact finsetRankCertificate_of_small_saturation_quotient
          K A hAne hKsmall (by simpa [f] using hchild)

end Erdos336
