import ErdosProblems.Erdos360.LevIncrementAux

/-!
# Lev's sharp multiple-summand increment

This file proves the normalized natural-number form of Lev's multiple-
summand theorem.  The proof is the modular-fibre argument from Lev's
addendum: Kneser is applied after reduction modulo the diameter of the last
summand, and a missed stabilizer coset is lifted with all its integer fibres.
-/

open scoped BigOperators Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

open Finset

/-! ## A top representative in every occupied residue -/

private def residueFiber (S : Finset ℕ) (v : ℕ) (c : ZMod v) : Finset ℕ :=
  S.filter fun s ↦ (s : ZMod v) = c

private lemma residueFiber_nonempty {S : Finset ℕ} {v : ℕ}
    (c : ↑(Erdos13Additive.modImage S v)) :
    (residueFiber S v c.1).Nonempty := by
  obtain ⟨s, hs, hsc⟩ := Erdos13Additive.mem_modImage.mp c.2
  exact ⟨s, by simp [residueFiber, hs, hsc]⟩

private noncomputable def residueTop (S : Finset ℕ) (v : ℕ)
    (c : ↑(Erdos13Additive.modImage S v)) : ℕ :=
  (residueFiber S v c.1).max' (residueFiber_nonempty c)

private lemma residueTop_mem (S : Finset ℕ) (v : ℕ)
    (c : ↑(Erdos13Additive.modImage S v)) : residueTop S v c ∈ S := by
  exact (mem_filter.mp (max'_mem (residueFiber S v c.1)
    (residueFiber_nonempty c))).1

private lemma residueTop_cast (S : Finset ℕ) (v : ℕ)
    (c : ↑(Erdos13Additive.modImage S v)) :
    (residueTop S v c : ZMod v) = c.1 := by
  exact (mem_filter.mp (max'_mem (residueFiber S v c.1)
    (residueFiber_nonempty c))).2

private lemma le_residueTop {S : Finset ℕ} {v s : ℕ}
    (c : ↑(Erdos13Additive.modImage S v)) (hs : s ∈ S)
    (hsc : (s : ZMod v) = c.1) : s ≤ residueTop S v c := by
  exact le_max' (residueFiber S v c.1) s (by simp [residueFiber, hs, hsc])

private noncomputable def shiftedResidueTops (S : Finset ℕ) (v : ℕ) :
    Finset ℕ :=
  (Erdos13Additive.modImage S v).attach.image
    (fun c ↦ residueTop S v c + v)

private lemma shiftedResidueTops_card (S : Finset ℕ) (v : ℕ) :
    (shiftedResidueTops S v).card =
      (Erdos13Additive.modImage S v).card := by
  rw [shiftedResidueTops, card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    apply Subtype.ext
    rw [← residueTop_cast S v a, ← residueTop_cast S v b]
    have : residueTop S v a = residueTop S v b :=
      Nat.add_right_cancel hab
    rw [this]

private lemma shiftedResidueTops_subset_add {S B : Finset ℕ} {v : ℕ}
    (hvB : v ∈ B) : shiftedResidueTops S v ⊆ S + B := by
  intro z hz
  simp only [shiftedResidueTops, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact add_mem_add (residueTop_mem S v c) hvB

private lemma shiftedResidueTops_disjoint_left {S : Finset ℕ} {v : ℕ}
    (hv : 0 < v) : Disjoint S (shiftedResidueTops S v) := by
  rw [disjoint_left]
  intro s hsS hsT
  simp only [shiftedResidueTops, mem_image] at hsT
  obtain ⟨c, -, rfl⟩ := hsT
  have hcast : ((residueTop S v c + v : ℕ) : ZMod v) = c.1 := by
    simpa using residueTop_cast S v c
  have hle := le_residueTop c hsS hcast
  omega

private lemma modImage_shiftedResidueTops (S : Finset ℕ) (v : ℕ) :
    Erdos13Additive.modImage (shiftedResidueTops S v) v =
      Erdos13Additive.modImage S v := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := Erdos13Additive.mem_modImage.mp hc
    simp only [shiftedResidueTops, mem_image] at hz
    obtain ⟨d, -, rfl⟩ := hz
    have hd := residueTop_cast S v d
    have hcd : c = d.1 := by
      rw [← hzc]
      simpa using hd
    simpa [hcd] using d.2
  · intro hc
    let d : ↑(Erdos13Additive.modImage S v) := ⟨c, hc⟩
    apply Erdos13Additive.mem_modImage.mpr
    refine ⟨residueTop S v d + v, ?_, ?_⟩
    · simp [shiftedResidueTops, d]
    · simpa [d] using residueTop_cast S v d

/-! ## The diameter-free refined lift -/

/-- If `B` contains both `0` and the modulus, one can lift an entire chosen
collection `D` of output residues in addition to the ordinary boundary lift.
No diameter hypothesis is imposed on the already accumulated summand `S`. -/
theorem lev_refined_lift
    {S B : Finset ℕ} {v : ℕ} (D : Finset (ZMod v))
    (hv : 0 < v) (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hD : D ⊆ Erdos13Additive.modImage (S + B) v)
    (hDS : Disjoint D (Erdos13Additive.modImage S v)) :
    (Erdos13Additive.modImage (S + B) v).card + S.card +
        (Erdos13Additive.sumsOverResidues S B v D).card ≤
      (S + B).card + D.card := by
  let T := Erdos13Additive.modImage S v
  let U := Erdos13Additive.modImage (S + B) v
  let Q := T ∪ D
  let R := Erdos13Additive.residueRepsOutside (S + B) v Q
  let E := shiftedResidueTops S v
  let F := Erdos13Additive.sumsOverResidues S B v D
  have hRS : R ⊆ S + B :=
    Erdos13Additive.residueRepsOutside_subset (S + B) v Q
  have hES : E ⊆ S + B := shiftedResidueTops_subset_add hvB
  have hFS : F ⊆ S + B := filter_subset _ _
  have hTU : T ⊆ U := by
    intro c hc
    obtain ⟨s, hs, hsc⟩ := Erdos13Additive.mem_modImage.mp hc
    exact Erdos13Additive.mem_modImage.mpr
      ⟨s, add_mem_add hs hB0, by simpa using hsc⟩
  have hQU : Q ⊆ U := union_subset hTU hD
  have hTD : Disjoint T D := hDS.symm
  have hRE : Disjoint R E := by
    rw [disjoint_left]
    intro z hzR hzE
    have hznot :=
      Erdos13Additive.cast_not_mem_of_mem_residueRepsOutside hzR
    apply hznot
    apply mem_union_left
    change (z : ZMod v) ∈ T
    dsimp only [T]
    rw [← modImage_shiftedResidueTops S v]
    exact Erdos13Additive.mem_modImage.mpr ⟨z, hzE, rfl⟩
  have hRSdisj : Disjoint R S := by
    rw [disjoint_left]
    intro z hzR hzS
    have hznot :=
      Erdos13Additive.cast_not_mem_of_mem_residueRepsOutside hzR
    apply hznot
    apply mem_union_left
    exact Erdos13Additive.mem_modImage.mpr ⟨z, hzS, rfl⟩
  have hSE : Disjoint S E := shiftedResidueTops_disjoint_left hv
  have hRF : Disjoint R F := by
    rw [disjoint_left]
    intro z hzR hzF
    have hznot :=
      Erdos13Additive.cast_not_mem_of_mem_residueRepsOutside hzR
    apply hznot
    apply mem_union_right
    exact (Erdos13Additive.mem_sumsOverResidues.mp hzF).2
  have hSF : Disjoint S F := by
    rw [disjoint_left]
    intro z hzS hzF
    have hzT : (z : ZMod v) ∈ T :=
      Erdos13Additive.mem_modImage.mpr ⟨z, hzS, rfl⟩
    exact (disjoint_left.mp hTD) hzT
      (Erdos13Additive.mem_sumsOverResidues.mp hzF).2
  have hEF : Disjoint E F := by
    rw [disjoint_left]
    intro z hzE hzF
    have hzT : (z : ZMod v) ∈ T := by
      dsimp only [T]
      rw [← modImage_shiftedResidueTops S v]
      exact Erdos13Additive.mem_modImage.mpr ⟨z, hzE, rfl⟩
    exact (disjoint_left.mp hTD) hzT
      (Erdos13Additive.mem_sumsOverResidues.mp hzF).2
  have hSER : Disjoint (S ∪ E) R := by
    rw [disjoint_left]
    intro z hzSE hzR
    rcases mem_union.mp hzSE with hzS | hzE
    · exact (disjoint_left.mp hRSdisj) hzR hzS
    · exact (disjoint_left.mp hRE) hzR hzE
  have hAllF : Disjoint ((S ∪ E) ∪ R) F := by
    rw [disjoint_left]
    intro z hz hzF
    rcases mem_union.mp hz with hzSE | hzR
    · rcases mem_union.mp hzSE with hzS | hzE
      · exact (disjoint_left.mp hSF) hzS hzF
      · exact (disjoint_left.mp hEF) hzE hzF
    · exact (disjoint_left.mp hRF) hzR hzF
  have hSsub : S ⊆ S + B := by
    intro s hs
    exact add_mem_add hs hB0
  have hAll : ((S ∪ E) ∪ R) ∪ F ⊆ S + B :=
    union_subset (union_subset (union_subset hSsub hES) hRS) hFS
  have hcardAll := card_le_card hAll
  rw [card_union_of_disjoint hAllF, card_union_of_disjoint hSER,
    card_union_of_disjoint hSE,
    Erdos13Additive.card_residueRepsOutside, shiftedResidueTops_card] at hcardAll
  change S.card + T.card + (U \ Q).card + F.card ≤ (S + B).card at hcardAll
  have hsplit := card_sdiff_add_card_eq_card hQU
  have hQcard : Q.card = T.card + D.card := card_union_of_disjoint hTD
  change (U \ Q).card + Q.card = U.card at hsplit
  change U.card + S.card + F.card ≤ (S + B).card + D.card
  omega

/-- The boundary-only specialization of `lev_refined_lift`. -/
theorem lev_modular_boundary
    {S B : Finset ℕ} {v : ℕ}
    (hv : 0 < v) (hB0 : 0 ∈ B) (hvB : v ∈ B) :
    (Erdos13Additive.modImage (S + B) v).card + S.card ≤
      (S + B).card := by
  have h := lev_refined_lift (S := S) (B := B) (v := v) ∅
    hv hB0 hvB (by simp) (by simp)
  simpa [Erdos13Additive.sumsOverResidues] using h

/-! ## Modular choices and aperiodicity -/

private lemma exists_levChoices_of_mem
    {v : ℕ} (parts : List (Finset ℕ)) {c : ZMod v}
    (hc : c ∈ levFinsetSum
      (parts.map fun A ↦ Erdos13Additive.modImage A v)) :
    ∃ choices : List (Finset ℕ × ZMod v),
      choices.map Prod.fst = parts ∧
      (∀ choice ∈ choices,
        choice.2 ∈ Erdos13Additive.modImage choice.1 v) ∧
      levChoiceSum choices = c := by
  induction parts generalizing c with
  | nil =>
      have hc0 : c = 0 := by simpa [levFinsetSum] using hc
      refine ⟨[], rfl, by simp, ?_⟩
      simpa [levChoiceSum] using hc0.symm
  | cons A parts ih =>
      simp only [List.map_cons, levFinsetSum_cons] at hc
      obtain ⟨a, ha, s, hs, has⟩ := Finset.mem_add.mp hc
      obtain ⟨choices, hfst, hmem, hsum⟩ := ih hs
      refine ⟨(A, a) :: choices, ?_, ?_, ?_⟩
      · simp [hfst]
      · intro choice hchoice
        simp only [List.mem_cons] at hchoice
        rcases hchoice with rfl | hchoice
        · exact ha
        · exact hmem choice hchoice
      · simp only [levChoiceSum, hsum]
        exact has

private lemma int_gcd_eq_one_of_not_containedInNontrivialAP
    {B : Finset ℕ} (haper : ¬ ContainedInNontrivialAP B) :
    B.gcd (fun n ↦ (n : ℤ)) = 1 := by
  have hnat : B.gcd (fun n : ℕ ↦ n) = 1 := by
    by_contra hne
    let d := B.gcd (fun n : ℕ ↦ n)
    have hd : 2 ≤ d := by
      by_cases hd0 : d = 0
      · exfalso
        apply haper
        refine ⟨2, 0, by omega, ?_⟩
        intro x hx
        have hx0 : x = 0 := by
          apply (Finset.gcd_eq_zero_iff.mp ?_) x hx
          simpa [d] using hd0
        simp [hx0]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hdne1 : d ≠ 1 := by simpa [d] using hne
        omega
    apply haper
    refine ⟨d, 0, hd, ?_⟩
    intro x hx
    have hdx : d ∣ x := Finset.gcd_dvd hx
    simpa [Nat.dvd_iff_mod_eq_zero.mp hdx]
  rw [Erdos13Additive.nat_int_finset_gcd, hnat]
  norm_num

private lemma card_le_modImage_card_add_one_of_subset_Icc
    {A : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (hA : A ⊆ Finset.Icc 0 v) (hA0 : 0 ∈ A) :
    A.card ≤ (Erdos13Additive.modImage A v).card + 1 := by
  by_cases hvA : v ∈ A
  · have h := Erdos13Additive.card_modImage_add_one_eq hv hA hA0 hvA
    omega
  · have hA' : A ⊆ Finset.Icc 0 (v - 1) := by
      intro x hx
      have hxI := Finset.mem_Icc.mp (hA hx)
      apply Finset.mem_Icc.mpr
      constructor
      · exact hxI.1
      · have hxne : x ≠ v := by
          intro hxv
          exact hvA (hxv ▸ hx)
        omega
    have hv' : v - 1 < v := by omega
    have h := Erdos13Additive.card_modImage_eq_card_of_lt hA' hv'
    omega

private lemma mul_le_sum_modImage_card
    {parts : List (Finset ℕ)} {v q : ℕ}
    (hparts : ∀ A ∈ parts,
      q ≤ (Erdos13Additive.modImage A v).card) :
    parts.length * q ≤
      (parts.map fun A ↦ (Erdos13Additive.modImage A v).card).sum := by
  induction parts with
  | nil => simp
  | cons A parts ih =>
      have hA := hparts A (by simp)
      have htail : ∀ B ∈ parts,
          q ≤ (Erdos13Additive.modImage B v).card := by
        intro B hB
        exact hparts B (by simp [hB])
      have hi := ih htail
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul]
      omega

/-! ## The sharp increment -/

/-- Lev's sharp multiple-summand increment, in its intrinsic modular-card
form.  The term subtracted on the right is exactly one for every merge.

This is a normalized natural-number form of Lev's Theorem 5.  The earlier
summands need only be nonempty; all diameter information enters later when
their modular image cardinalities are evaluated. -/
theorem lev_multi_increment_modImage
    {parts : List (Finset ℕ)} {B : Finset ℕ} {v : ℕ}
    (hne : ∀ A ∈ parts, A.Nonempty)
    (hv : 0 < v) (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (haper : ¬ ContainedInNontrivialAP B) :
    (levFinsetSum parts).card +
        min v
          ((parts.map fun A ↦
              (Erdos13Additive.modImage A v).card).sum +
            (Erdos13Additive.modImage B v).card - parts.length) ≤
      (levFinsetSum parts + B).card := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let S := levFinsetSum parts
  let X := Erdos13Additive.modImage S v
  let Y := Erdos13Additive.modImage B v
  let C := Erdos13Additive.modImage (S + B) v
  let H := C.addStab
  let all := parts ++ [B]
  let mods := all.map fun A ↦ Erdos13Additive.modImage A v
  have hBne : B.Nonempty := ⟨0, hB0⟩
  have hSne : S.Nonempty := levFinsetSum_nonempty hne
  have hsumne : (S + B).Nonempty := Finset.add_nonempty.mpr ⟨hSne, hBne⟩
  have hCne : C.Nonempty := Erdos13Additive.modImage_nonempty hsumne
  have hHzero : (0 : ZMod v) ∈ H :=
    Erdos13Additive.zero_mem_addStab hCne
  have hHpos : 0 < H.card := Finset.card_pos.mpr ⟨0, hHzero⟩
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact Erdos13Additive.addStab_add_mem hCne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact Erdos13Additive.addStab_neg_mem hCne hx
  have hCeq : C = X + Y := by
    dsimp only [C, X, Y]
    exact Erdos13Additive.modImage_add S B v
  have hsumall : levFinsetSum all = S + B := by
    dsimp only [all, S]
    rw [levFinsetSum_append, levFinsetSum_singleton]
  have hmodsC : levFinsetSum mods = C := by
    dsimp only [mods]
    rw [← modImage_levFinsetSum, hsumall]
  have hHcard : H.card ≤ v := by
    calc
      H.card ≤ (Finset.univ : Finset (ZMod v)).card :=
        Finset.card_le_card (Finset.subset_univ H)
      _ = v := by simp [ZMod.card]
  have hboundary : C.card + S.card ≤ (S + B).card := by
    dsimp only [C, S]
    exact lev_modular_boundary hv hB0 hvB
  by_cases hwhole : H.card = v
  · have hHC : H.card ≤ C.card := Finset.card_addStab_le_card
    change S.card + min v
        ((parts.map fun A ↦
            (Erdos13Additive.modImage A v).card).sum + Y.card -
          parts.length) ≤ (S + B).card
    omega
  · have hHlt : H.card < v := by omega
    have hYzero : (0 : ZMod v) ∈ Y :=
      Erdos13Additive.zero_mem_modImage hB0
    have hgcd := int_gcd_eq_one_of_not_containedInNontrivialAP haper
    have hYnH : ¬ Y ⊆ H := by
      intro hYH
      let K : AddSubgroup (ZMod v) :=
        AddAction.stabilizer (ZMod v) (C : Set (ZMod v))
      have hHK : (H : Set (ZMod v)) = (K : Set (ZMod v)) := by
        change (↑C.addStab : Set (ZMod v)) = _
        exact Finset.coe_addStab hCne
      have hBK : ∀ n ∈ B, (n : ZMod v) ∈ K := by
        intro n hn
        have hnH : (n : ZMod v) ∈ H :=
          hYH (Erdos13Additive.mem_modImage.mpr ⟨n, hn, rfl⟩)
        have hnHs : (n : ZMod v) ∈ (H : Set (ZMod v)) := hnH
        rw [hHK] at hnHs
        exact hnHs
      have hKtop :=
        Erdos13Additive.stabilizer_eq_top_of_gcd_one hgcd K hBK
      have hHuniv : H = (Finset.univ : Finset (ZMod v)) := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        have hxK : x ∈ K := by rw [hKtop]; trivial
        have hxKs : x ∈ (K : Set (ZMod v)) := hxK
        rw [← hHK] at hxKs
        exact hxKs
      have : H.card = v := by simp [hHuniv, ZMod.card]
      omega
    obtain ⟨b, hbY, hbH⟩ := Finset.not_subset.mp hYnH
    have hdisjBH : Disjoint H (b +ᵥ H) :=
      Erdos13Additive.disjoint_self_vadd_of_not_mem hHadd hHneg hbH
    have hHsubY : H ⊆ Y + H := by
      intro h hh
      exact Finset.mem_add.mpr ⟨0, hYzero, h, hh, by simp⟩
    have hbcoset : b +ᵥ H ⊆ Y + H := Finset.vadd_finset_subset_add hbY
    have hYsat : 2 * H.card ≤ (Y + H).card := by
      have hc := Finset.card_le_card (Finset.union_subset hHsubY hbcoset)
      rw [Finset.card_union_of_disjoint hdisjBH,
        Finset.card_vadd_finset] at hc
      omega
    have hkBinary0 := Finset.add_kneser X Y
    have hkBinary : (X + H).card + (Y + H).card ≤
        C.card + H.card := by
      dsimp only [H]
      rw [hCeq]
      exact hkBinary0
    have hXsubC : X ⊆ C := by
      intro x hx
      rw [hCeq]
      exact Finset.mem_add.mpr ⟨x, hx, 0, hYzero, by simp⟩
    have hXsatSubC : X + H ⊆ C := by
      have hs := Finset.add_subset_add hXsubC (Subset.rfl : H ⊆ H)
      change X + H ⊆ C + H at hs
      simpa only [H, Finset.add_addStab] using hs
    have hXsatCard : (X + H).card + H.card ≤ C.card := by omega
    have hnCX : ¬ C ⊆ X + H := by
      intro hCX
      have hc := Finset.card_le_card hCX
      omega
    obtain ⟨c, hcC, hcX⟩ := Finset.not_subset.mp hnCX
    let D := c +ᵥ H
    have hDsubC : D ⊆ C := by
      have hs : c +ᵥ H ⊆ C + H := Finset.vadd_finset_subset_add hcC
      simpa only [D, H, Finset.add_addStab] using hs
    have hDdisjXsat : Disjoint D (X + H) :=
      Erdos13Additive.disjoint_vadd_add_of_not_mem hHadd hHneg hcX
    have hXsubXsat : X ⊆ X + H := by
      intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hHzero, by simp⟩
    have hDdisjX : Disjoint D X := hDdisjXsat.mono_right hXsubXsat
    let F := Erdos13Additive.sumsOverResidues S B v D
    have hDcard : D.card = H.card := Finset.card_vadd_finset c H
    have hrefined0 := lev_refined_lift D hv hB0 hvB
      (by simpa only [C] using hDsubC)
      (by simpa only [X] using hDdisjX)
    have hrefined : C.card + S.card + F.card ≤
        (S + B).card + H.card := by
      simpa only [C, S, F, hDcard] using hrefined0
    have hcmods : c ∈ levFinsetSum mods := by
      rw [hmodsC]
      exact hcC
    obtain ⟨choices, hfst, hchoice, hchoiceSum⟩ :=
      exists_levChoices_of_mem all hcmods
    have hchosenSlice :=
      levFinsetSum_chosenFibers_subset hHzero hHadd choices
    rw [hchoiceSum, hfst, hsumall] at hchosenSlice
    have hchosenF : levFinsetSum (levChosenFibers H choices) ⊆ F := by
      intro z hz
      have hz' := Erdos13Additive.mem_residueFiberSet.mp (hchosenSlice hz)
      exact Erdos13Additive.mem_sumsOverResidues.mpr ⟨hz'.1, hz'.2⟩
    have hfiber0 :=
      sum_modImage_card_add_mul_card_le_saturation_add_fiber
        hHzero hchoice hchosenF
    have hlenChoices : choices.length = all.length := by
      rw [← hfst]
      simp
    have hmodChoices :
        (choices.map fun choice ↦
          (Erdos13Additive.modImage choice.1 v).card).sum =
        (all.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum := by
      have hs := congrArg
        (fun L : List (Finset ℕ) ↦
          (L.map fun A ↦ (Erdos13Additive.modImage A v).card).sum) hfst
      simpa only [List.map_map, Function.comp_def] using hs
    have hsatChoices :
        (choices.map fun choice ↦
          (Erdos13Additive.modImage choice.1 v + H).card).sum =
        (all.map fun A ↦
          (Erdos13Additive.modImage A v + H).card).sum := by
      have hs := congrArg
        (fun L : List (Finset ℕ) ↦
          (L.map fun A ↦
            (Erdos13Additive.modImage A v + H).card).sum) hfst
      simpa only [List.map_map, Function.comp_def] using hs
    have hfiber :
        (all.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum +
            all.length * H.card ≤
          (all.map fun A ↦
            (Erdos13Additive.modImage A v + H).card).sum +
            F.card + (all.length - 1) := by
      simpa only [hmodChoices, hsatChoices, hlenChoices] using hfiber0
    have hmodsNe : ∀ Q ∈ mods, Q.Nonempty := by
      intro Q hQ
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hQ
      apply Erdos13Additive.modImage_nonempty
      rcases List.mem_append.mp hA with hA | hA
      · exact hne A hA
      · have hAB : A = B := by simpa only [List.mem_singleton] using hA
        simpa only [hAB] using hBne
    have hkAll0 :=
      sum_card_add_addStab_le_card_levFinsetSum_add mods hmodsNe
    have hkAll :
        (all.map fun A ↦
          (Erdos13Additive.modImage A v + H).card).sum ≤
        C.card + (all.length - 1) * H.card := by
      rw [hmodsC] at hkAll0
      simpa only [mods, List.map_map, List.length_map,
        Function.comp_def, H] using hkAll0
    have hcancel :
        (all.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum + H.card ≤
        C.card + F.card + (all.length - 1) := by
      have hallpos : 0 < all.length := by simp [all]
      have hmul : all.length * H.card =
          (all.length - 1) * H.card + H.card := by
        conv_lhs => rw [show all.length = (all.length - 1) + 1 by omega]
        rw [Nat.add_mul, one_mul]
      rw [hmul] at hfiber
      omega
    have hstrong :
        S.card +
          ((all.map fun A ↦
            (Erdos13Additive.modImage A v).card).sum -
              (all.length - 1)) ≤
        (S + B).card := by
      omega
    change S.card + min v
        ((parts.map fun A ↦
            (Erdos13Additive.modImage A v).card).sum + Y.card -
          parts.length) ≤ (S + B).card
    have hallSumCards :
        (all.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum =
        (parts.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum + Y.card := by
      simp [all, Y]
    have hallLength : all.length - 1 = parts.length := by simp [all]
    rw [hallSumCards, hallLength] at hstrong
    omega

/-- Uniform-cardinality specialization used at every prefix in Lev's
Proposition 1.  All summands are normalized into the interval whose right
endpoint is the diameter `v` of the final summand. -/
theorem lev_multi_increment_uniform
    {parts : List (Finset ℕ)} {B : Finset ℕ} {v n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hv : 0 < v)
    (hparts : ∀ A ∈ parts,
      0 ∈ A ∧ A ⊆ Finset.Icc 0 v ∧ n₀ ≤ A.card)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hBbox : B ⊆ Finset.Icc 0 v) (hBcard : n₀ ≤ B.card)
    (haper : ¬ ContainedInNontrivialAP B) :
    (levFinsetSum parts).card +
        min v ((parts.length + 1) * (n₀ - 2) + 1) ≤
      (levFinsetSum parts + B).card := by
  have hne : ∀ A ∈ parts, A.Nonempty := by
    intro A hA
    exact ⟨0, (hparts A hA).1⟩
  have hmodParts : ∀ A ∈ parts,
      n₀ - 1 ≤ (Erdos13Additive.modImage A v).card := by
    intro A hA
    have hcard := card_le_modImage_card_add_one_of_subset_Icc hv
      (hparts A hA).2.1 (hparts A hA).1
    have hAcard := (hparts A hA).2.2
    omega
  have hpartSum := mul_le_sum_modImage_card hmodParts
  have hBmodEq :=
    Erdos13Additive.card_modImage_add_one_eq hv hBbox hB0 hvB
  have hBmodLower :
      n₀ - 1 ≤ (Erdos13Additive.modImage B v).card := by omega
  have hsumLower :
      (parts.length + 1) * (n₀ - 1) ≤
        (parts.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum +
          (Erdos13Additive.modImage B v).card := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_le_add hpartSum hBmodLower
  have hscale :
      (parts.length + 1) * (n₀ - 1) =
        (parts.length + 1) * (n₀ - 2) + (parts.length + 1) := by
    have hn : n₀ - 1 = (n₀ - 2) + 1 := by omega
    rw [hn, Nat.mul_add, mul_one]
  rw [hscale] at hsumLower
  have hraw :
      (parts.length + 1) * (n₀ - 2) + 1 ≤
        (parts.map fun A ↦
          (Erdos13Additive.modImage A v).card).sum +
          (Erdos13Additive.modImage B v).card - parts.length := by
    omega
  have hmain := lev_multi_increment_modImage hne hv hB0 hvB haper
  omega

/-- Endpoint-corrected form of `lev_multi_increment_uniform`.  This is the
exact summand appearing in the prefix sum in Lev's Proposition 1. -/
theorem lev_multi_increment_uniform_sharp
    {parts : List (Finset ℕ)} {B : Finset ℕ} {v n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hv : 0 < v)
    (hparts : ∀ A ∈ parts,
      0 ∈ A ∧ A ⊆ Finset.Icc 0 v ∧ n₀ ≤ A.card)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hBbox : B ⊆ Finset.Icc 0 v) (hBcard : n₀ ≤ B.card)
    (haper : ¬ ContainedInNontrivialAP B) :
    (levFinsetSum parts).card +
        (min (v - 1) ((parts.length + 1) * (n₀ - 2)) + 1) ≤
      (levFinsetSum parts + B).card := by
  have h := lev_multi_increment_uniform hn₀ hv hparts hB0 hvB hBbox
    hBcard haper
  have heq :
      min (v - 1) ((parts.length + 1) * (n₀ - 2)) + 1 =
        min v ((parts.length + 1) * (n₀ - 2) + 1) := by
    omega
  rw [heq]
  exact h

end Erdos360
