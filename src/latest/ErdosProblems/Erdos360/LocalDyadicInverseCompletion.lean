/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ConstantLossInverse
import ErdosProblems.Erdos360.GcdNormalizedCyclicInverse
import ErdosProblems.Erdos360.LowSupportCyclicInverse
import ErdosProblems.Erdos360.FiveLayerGcdNormalizedCyclicInverse

/-!
# Completion of the local dyadic cyclic inverse theorem

This module assembles the Fourier-core extraction with the two completed
support regimes of the cyclic inverse theorem.  The high-support regime is
the gcd-normalized affine-fibre theorem; the at-most-two-layer regime is a
genuine dyadic proper-subgroup argument.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-! ## The two-layer exception

The ordinary `|U-U| \le |U|^2` estimate loses one point when `|U| = 2`.
That point is decisive here: a nonempty two-point set has at most three
differences, not four. -/

lemma card_sub_le_three_of_nonempty_card_le_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {U : Finset G} (hU : U.Nonempty) (hcard : U.card ≤ 2) :
    (U - U).card ≤ 3 := by
  classical
  let u := hU.choose
  have hu : u ∈ U := hU.choose_spec
  let E := U.erase u
  have hEcard : E.card ≤ 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hu]
    omega
  let v := if hE : E.Nonempty then hE.choose else u
  have hUv : U ⊆ {u, v} := by
    intro x hx
    by_cases hxu : x = u
    · simp [hxu]
    · have hxE : x ∈ E := by simpa [E, hxu] using hx
      have hEne : E.Nonempty := ⟨x, hxE⟩
      have hvE : v ∈ E := by simpa [v, hEne] using hEne.choose_spec
      have hxv : x = v := Finset.card_le_one_iff.mp hEcard hxE hvE
      simp [hxv]
  have hdiff : U - U ⊆ {0, u - v, v - u} := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    have hx' := hUv hx
    have hy' := hUv hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy' ⊢
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
      simp [sub_self]
  exact (Finset.card_le_card hdiff).trans Finset.card_le_three

/-- If the `j`th dyadic sumset occupies at most 32 classes in a quotient of
order at least 240, then at level `j ≥ 5` the original set already lies in a
proper subgroup.  The constants are exactly those needed for a four-layer
Fourier core: two Ruzsa-covering translates times at most `4²` differences.
-/
theorem exists_proper_subgroup_of_dyadic_quotient_card_le_32_at_five
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P) {j : ℕ} (hj : 5 ≤ j)
    (H : AddSubgroup G) [DecidableEq (G ⧸ H)]
    (hquot : 240 ≤ Fintype.card (G ⧸ H))
    (hsmall :
      ((dyadicFinsetSum P j).image (QuotientAddGroup.mk' H)).card ≤ 32) :
    ∃ K : AddSubgroup G, K ≠ ⊤ ∧ (P : Set G) ⊆ (K : Set G) := by
  classical
  let q : G →+ G ⧸ H := QuotientAddGroup.mk' H
  let Pbar : Finset (G ⧸ H) := P.image q
  have hqsurj : Function.Surjective q := by
    simpa [q] using QuotientAddGroup.mk'_surjective H
  by_contra hnot
  push Not at hnot
  have hPbarProper : ¬ ∃ L : AddSubgroup (G ⧸ H), L ≠ ⊤ ∧
      ((Pbar : Finset (G ⧸ H)) : Set (G ⧸ H)) ⊆
        (L : Set (G ⧸ H)) := by
    rintro ⟨L, hL, hPL⟩
    have hcomap : L.comap q ≠ ⊤ := by
      intro htop
      apply hL
      apply top_unique
      intro y _hy
      obtain ⟨x, rfl⟩ := hqsurj y
      have hx : x ∈ L.comap q := by rw [htop]; simp
      exact hx
    exact hnot (L.comap q) hcomap (by
      intro x hx
      change q x ∈ L
      apply hPL
      exact Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩)
  have hzeroBar : 0 ∈ Pbar := by
    exact Finset.mem_image.mpr ⟨0, hzero, by simp [q]⟩
  have hPbarCard : 2 ≤ Pbar.card := by
    by_contra hnotCard
    have hcardOne : Pbar.card ≤ 1 := by omega
    have hbotProper : (⊥ : AddSubgroup (G ⧸ H)) ≠ ⊤ := by
      intro hbot
      have hsubsingleton : Subsingleton (G ⧸ H) := by
        constructor
        intro x y
        have hx : x ∈ (⊥ : AddSubgroup (G ⧸ H)) := by rw [hbot]; simp
        have hy : y ∈ (⊥ : AddSubgroup (G ⧸ H)) := by rw [hbot]; simp
        simpa using hx.trans hy.symm
      have hcardSmall : Fintype.card (G ⧸ H) ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsubsingleton
      omega
    apply hPbarProper
    refine ⟨⊥, hbotProper, ?_⟩
    intro x hx
    have hxzero : x = 0 :=
      (Finset.card_le_one_iff.mp hcardOne) hx hzeroBar
    simpa [hxzero]
  have hPbarCoset : NotContainedInProperCoset Pbar :=
    notContainedInProperCoset_of_zero_mem_not_subset_subgroup
      hzeroBar hPbarProper
  have himage :
      (dyadicFinsetSum P j).image q = dyadicFinsetSum Pbar j := by
    simpa [Pbar] using image_dyadicFinsetSum_addMonoidHom q P j
  have hiterCard : (iteratedFinsetSum Pbar (2 ^ j)).card ≤ 32 := by
    rw [← dyadicFinsetSum_eq_iteratedFinsetSum, ← himage]
    simpa [q] using hsmall
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroBar⟩ hPbarCoset (2 ^ j) (by
        have hp : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) j
        omega)
  have hmin : min (2 * Fintype.card (G ⧸ H))
      ((2 ^ j + 1) * Pbar.card) ≤ 64 := by
    exact hlower.trans (Nat.mul_le_mul_left 2 hiterCard)
  have hgroup : 64 < 2 * Fintype.card (G ⧸ H) := by omega
  have hpow : 32 ≤ 2 ^ j := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hj
  have htarget : 64 < (2 ^ j + 1) * Pbar.card := by
    calc
      64 < 33 * 2 := by norm_num
      _ ≤ (2 ^ j + 1) * Pbar.card :=
        Nat.mul_le_mul (by omega) hPbarCard
  omega

/-- A two-layer Fourier core already forces the proper-subgroup branch.

After applying the linear part of the Fourier affine change, Ruzsa covering
puts the dyadic set in two translates of `D-D`.  The image of `D` in the
`m`-element quotient has at most two points, hence `D-D` has at most three
images and the dyadic set at most six.  CFP four-fold growth then makes the
image of the symmetric almost-period set have at most two points.  Such an
image cannot generate a quotient of order at least `240`: symmetry makes its
only possible nonzero element have additive order at most two. -/
theorem proper_subgroup_of_two_layer_affine_core
    {m g j : ℕ} [NeZero g] [NeZero (m * g)]
    {P B C D : Finset (ZMod (m * g))}
    (hzeroP : 0 ∈ P) (hsymmP : ∀ x ∈ P, -x ∈ P) (hj : 2 ≤ j)
    (hBdyadic : B = dyadicFinsetSum P j)
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm240 : 240 ≤ m) (hDzero : 0 ∈ D)
    (htwo :
      (firstCoordinateSet (zmodQuotRemImage m g D)).card ≤ 2) :
    ∃ K : AddSubgroup (ZMod (m * g)), K ≠ ⊤ ∧
      (P : Set (ZMod (m * g))) ⊆ (K : Set (ZMod (m * g))) := by
  classical
  have hm : 0 < m := by omega
  let H₀ : AddSubgroup (ZMod (m * g)) :=
    (⊤ : AddSubgroup (ZMod g)).map (zmodQuotientEmbedding m g)
  let q : ZMod (m * g) →+ (ZMod (m * g) ⧸ H₀) :=
    QuotientAddGroup.mk' H₀
  let e := unitMulAddEquiv w
  let P₀ : Finset (ZMod (m * g)) := P.image e
  let B₀ : Finset (ZMod (m * g)) := B.image e
  let A := firstCoordinateSet (zmodQuotRemImage m g D)
  have hDne : D.Nonempty := ⟨0, hDzero⟩
  have hAne : A.Nonempty := by
    refine ⟨0, ?_⟩
    apply mem_firstCoordinateSet.mpr
    exact ⟨0, Finset.mem_image.mpr
      ⟨0, hDzero, by simp [zmodQuotRemLift]⟩⟩
  have hDquot : D.image q ⊆ A.image (fun a : ℕ => q (a : ZMod (m * g))) := by
    intro y hy
    obtain ⟨z, hzD, rfl⟩ := Finset.mem_image.mp hy
    let a := z.val % m
    have ha : a ∈ A := by
      apply mem_firstCoordinateSet.mpr
      exact ⟨(z.val / m : ZMod g),
        Finset.mem_image.mpr ⟨z, hzD, rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨a, ha, ?_⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    have hrec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := g) z
    have hemb : zmodQuotientEmbedding m g (z.val / m : ZMod g) ∈ H₀ := by
      apply AddSubgroup.mem_map.mpr
      exact ⟨(z.val / m : ZMod g), by simp, rfl⟩
    change (a : ZMod (m * g)) - z ∈ H₀
    rw [← hrec]
    simpa [a] using H₀.neg_mem hemb
  have hDquotCard : (D.image q).card ≤ 2 := by
    calc
      (D.image q).card ≤
          (A.image (fun a : ℕ => q (a : ZMod (m * g)))).card :=
        Finset.card_le_card hDquot
      _ ≤ A.card := Finset.card_image_le
      _ ≤ 2 := by simpa [A] using htwo
  have hDquotNe : (D.image q).Nonempty := hDne.image q
  have hdiffCard : ((D.image q) - (D.image q)).card ≤ 3 :=
    card_sub_le_three_of_nonempty_card_le_two hDquotNe hDquotCard
  have himageDiff : (D - D).image q = D.image q - D.image q := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, z, hz, hxz⟩ := Finset.mem_sub.mp hu
      subst u
      subst y
      exact Finset.mem_sub.mpr
        ⟨q x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
          q z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp⟩
    · intro hy
      obtain ⟨qx, hqx, qz, hqz, hsum⟩ := Finset.mem_sub.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hqx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hqz
      apply Finset.mem_image.mpr
      refine ⟨x - z, Finset.mem_sub.mpr ⟨x, hx, z, hz, rfl⟩, ?_⟩
      simpa using hsum
  obtain ⟨F, hFB, hFcard, hBF⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hBsmall
  let F₀ : Finset (ZMod (m * g)) := F.image e
  have hB₀cover : B₀ ⊆ F₀ + (D - D) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, z, hz, hfb⟩ := Finset.mem_add.mp (hBF hb)
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    apply Finset.mem_add.mpr
    refine ⟨e f, ?_, (c + e x) - (c + e y), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    · apply Finset.mem_sub.mpr
      refine ⟨c + e x, ?_, c + e y, ?_, rfl⟩
      · rw [hDaff]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · rw [hDaff]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · rw [← hfb]
      simp only [map_add, map_sub]
      abel
  have hBquot : B₀.image q ⊆ F₀.image q + (D - D).image q := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, z, hz, rfl⟩ := Finset.mem_add.mp (hB₀cover hb)
    exact Finset.mem_add.mpr
      ⟨q f, Finset.mem_image.mpr ⟨f, hf, rfl⟩,
        q z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp⟩
  have hBquotCard : (B₀.image q).card ≤ 6 := by
    have hF₀card : F₀.card ≤ 2 :=
      Finset.card_image_le.trans hFcard
    calc
      (B₀.image q).card ≤ (F₀.image q + (D - D).image q).card :=
        Finset.card_le_card hBquot
      _ ≤ (F₀.image q).card * ((D - D).image q).card := Finset.card_add_le
      _ ≤ 2 * 3 := Nat.mul_le_mul
        (Finset.card_image_le.trans hF₀card)
        (by simpa [himageDiff] using hdiffCard)
      _ = 6 := by norm_num
  have hB₀dyadic : B₀ = dyadicFinsetSum P₀ j := by
    dsimp only [B₀, P₀]
    rw [hBdyadic]
    simpa using
      (image_dyadicFinsetSum_addMonoidHom e.toAddMonoidHom P j)
  let Pbar : Finset (ZMod (m * g) ⧸ H₀) := P₀.image q
  have hzeroP₀ : 0 ∈ P₀ := Finset.mem_image.mpr ⟨0, hzeroP, by simp [e]⟩
  have hzeroBar : 0 ∈ Pbar :=
    Finset.mem_image.mpr ⟨0, hzeroP₀, by simp [q]⟩
  have hsymmP₀ : ∀ x ∈ P₀, -x ∈ P₀ := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨-z, hsymmP z hz, by simp⟩
  have hsymmBar : ∀ x ∈ Pbar, -x ∈ Pbar := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨-z, hsymmP₀ z hz, by simp⟩
  by_contra hnot
  push Not at hnot
  have hqsurj : Function.Surjective q := by
    simpa [q] using QuotientAddGroup.mk'_surjective H₀
  have heSurj : Function.Surjective e := e.surjective
  have hPbarProper : ¬ ∃ L : AddSubgroup (ZMod (m * g) ⧸ H₀), L ≠ ⊤ ∧
      (Pbar : Set (ZMod (m * g) ⧸ H₀)) ⊆ (L : Set _) := by
    rintro ⟨L, hL, hPL⟩
    let K₀ := L.comap q
    let K := K₀.comap e.toAddMonoidHom
    have hK₀ : K₀ ≠ ⊤ := by
      intro htop
      apply hL
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := hqsurj y
      have hx : x ∈ K₀ := by rw [htop]; simp
      exact hx
    have hK : K ≠ ⊤ := by
      intro htop
      apply hK₀
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := heSurj y
      have hx : x ∈ K := by rw [htop]; simp
      exact hx
    apply hnot K hK
    intro x hx
    change q (e x) ∈ L
    apply hPL
    exact Finset.mem_image.mpr
      ⟨e x, Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩, rfl⟩
  have hPbarCoset : NotContainedInProperCoset Pbar :=
    notContainedInProperCoset_of_zero_mem_not_subset_subgroup
      hzeroBar hPbarProper
  have hfourSubset : iteratedFinsetSum Pbar 4 ⊆ B₀.image q := by
    have hmono : dyadicFinsetSum P₀ 2 ⊆ dyadicFinsetSum P₀ j :=
      dyadicFinsetSum_mono hzeroP₀ hj
    have himage := Finset.image_mono q hmono
    have heq : iteratedFinsetSum Pbar 4 =
        (dyadicFinsetSum P₀ 2).image q := by
      calc
        iteratedFinsetSum Pbar 4 = dyadicFinsetSum Pbar 2 := by
          change (((({0} : Finset (ZMod (m * g) ⧸ H₀)) + Pbar) +
              Pbar) + Pbar) + Pbar = (Pbar + Pbar) + (Pbar + Pbar)
          rw [finset_singleton_zero_add]
          ac_rfl
        _ = (dyadicFinsetSum P₀ 2).image q := by
          simpa [Pbar] using
            (image_dyadicFinsetSum_addMonoidHom q P₀ 2).symm
    rw [heq, hB₀dyadic]
    exact himage
  have hfourCard : (iteratedFinsetSum Pbar 4).card ≤ 6 :=
    (Finset.card_le_card hfourSubset).trans hBquotCard
  have hH₀card : Nat.card H₀ = g := by
    rw [show Nat.card H₀ = Nat.card (⊤ : AddSubgroup (ZMod g)) by
      exact natCard_map_zmodQuotientEmbedding hm ⊤]
    simp
  have hquotCard : Fintype.card (ZMod (m * g) ⧸ H₀) = m := by
    have hcardEq := H₀.card_eq_card_quotient_mul_card_addSubgroup
    rw [hH₀card] at hcardEq
    simp only [ZMod.card, Nat.card_eq_fintype_card] at hcardEq
    exact Nat.mul_right_cancel (NeZero.pos g) hcardEq.symm
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroBar⟩ hPbarCoset 4 (by omega)
  have hPbarCard : Pbar.card ≤ 2 := by
    have hmin : min (2 * Fintype.card (ZMod (m * g) ⧸ H₀))
        (5 * Pbar.card) ≤ 12 := by
      exact hlower.trans (Nat.mul_le_mul_left 2 hfourCard)
    rw [hquotCard] at hmin
    have hmLarge : 12 < 2 * m := by omega
    omega
  by_cases hallzero : ∀ x ∈ Pbar, x = 0
  · apply hPbarProper
    refine ⟨⊥, ?_, ?_⟩
    · intro hbot
      have hcardSmall : Fintype.card (ZMod (m * g) ⧸ H₀) ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr (by
          constructor
          intro x y
          have hx : x ∈ (⊥ : AddSubgroup (ZMod (m * g) ⧸ H₀)) := by
            rw [hbot]; simp
          have hy : y ∈ (⊥ : AddSubgroup (ZMod (m * g) ⧸ H₀)) := by
            rw [hbot]; simp
          simpa using hx.trans hy.symm)
      rw [hquotCard] at hcardSmall
      omega
    · intro x hx
      simpa [hallzero x (by simpa using hx)]
  · push Not at hallzero
    obtain ⟨x, hx, hx0⟩ := hallzero
    have hminus : -x = x := by
      have hmx : -x ∈ Pbar := hsymmBar x hx
      by_contra hne
      have hmxErase : -x ∈ Pbar.erase x := Finset.mem_erase.mpr ⟨hne, hmx⟩
      have hzeroErase : 0 ∈ Pbar.erase x :=
        Finset.mem_erase.mpr ⟨Ne.symm hx0, hzeroBar⟩
      have heraseCard : (Pbar.erase x).card ≤ 1 := by
        rw [Finset.card_erase_of_mem hx]
        omega
      have := Finset.card_le_one_iff.mp heraseCard hmxErase hzeroErase
      exact hx0 (neg_eq_zero.mp this)
    have htwoX : 2 • x = 0 := by
      simpa [two_nsmul] using (congrArg (fun z => z + x) hminus).symm
    have hPbarSub :
        (Pbar : Set (ZMod (m * g) ⧸ H₀)) ⊆
          (AddSubgroup.zmultiples x : Set (ZMod (m * g) ⧸ H₀)) := by
      intro y hy
      by_cases hyx : y = x
      · simpa [hyx] using AddSubgroup.mem_zmultiples x
      · have hyErase : y ∈ Pbar.erase x :=
          Finset.mem_erase.mpr ⟨hyx, by simpa using hy⟩
        have hzeroErase : 0 ∈ Pbar.erase x :=
          Finset.mem_erase.mpr ⟨Ne.symm hx0, hzeroBar⟩
        have heraseCard : (Pbar.erase x).card ≤ 1 := by
          rw [Finset.card_erase_of_mem hx]
          omega
        have hy0 := Finset.card_le_one_iff.mp heraseCard hyErase hzeroErase
        simpa [hy0]
    have hzxTop : AddSubgroup.zmultiples x = ⊤ := by
      by_contra hne
      exact hPbarProper ⟨AddSubgroup.zmultiples x, hne, hPbarSub⟩
    have hgroupCardLe : Fintype.card (ZMod (m * g) ⧸ H₀) ≤ 2 := by
      rw [← Nat.card_eq_fintype_card]
      calc
        Nat.card (ZMod (m * g) ⧸ H₀) =
            Nat.card (⊤ : AddSubgroup (ZMod (m * g) ⧸ H₀)) := by simp
        _ = Nat.card (AddSubgroup.zmultiples x) := by rw [hzxTop]
        _ ≤ 2 := by
          simpa only [Nat.card_eq_fintype_card] using
            card_zmultiples_le x (by norm_num) htwoX
    rw [hquotCard] at hgroupCardLe
    omega

/-- A Fourier core supported on at most four first-coordinate fibres forces
the proper-subgroup branch at every dyadic level `j ≥ 5`.

Ruzsa covering places the affine image of the dyadic set in two translates
of `D-D`.  The quotient image of `D` has at most four points, so the quotient
image of the dyadic set has at most `2 * 4² = 32` points.  The preceding
dyadic quotient lemma then finishes the argument. -/
theorem proper_subgroup_of_four_layer_affine_core_at_five
    {m g j : ℕ} [NeZero g] [NeZero (m * g)]
    {P B C D : Finset (ZMod (m * g))}
    (hzeroP : 0 ∈ P) (hj : 5 ≤ j)
    (hBdyadic : B = dyadicFinsetSum P j)
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm240 : 240 ≤ m) (hDzero : 0 ∈ D)
    (hfour :
      (firstCoordinateSet (zmodQuotRemImage m g D)).card ≤ 4) :
    ∃ K : AddSubgroup (ZMod (m * g)), K ≠ ⊤ ∧
      (P : Set (ZMod (m * g))) ⊆ (K : Set (ZMod (m * g))) := by
  classical
  have hm : 0 < m := by omega
  let H₀ : AddSubgroup (ZMod (m * g)) :=
    (⊤ : AddSubgroup (ZMod g)).map (zmodQuotientEmbedding m g)
  let q : ZMod (m * g) →+ (ZMod (m * g) ⧸ H₀) :=
    QuotientAddGroup.mk' H₀
  let e := unitMulAddEquiv w
  let P₀ : Finset (ZMod (m * g)) := P.image e
  let B₀ : Finset (ZMod (m * g)) := B.image e
  let A := firstCoordinateSet (zmodQuotRemImage m g D)
  have hDquot : D.image q ⊆ A.image (fun a : ℕ => q (a : ZMod (m * g))) := by
    intro y hy
    obtain ⟨z, hzD, rfl⟩ := Finset.mem_image.mp hy
    let a := z.val % m
    have ha : a ∈ A := by
      apply mem_firstCoordinateSet.mpr
      exact ⟨(z.val / m : ZMod g),
        Finset.mem_image.mpr ⟨z, hzD, rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨a, ha, ?_⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    have hrec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := g) z
    have hemb : zmodQuotientEmbedding m g (z.val / m : ZMod g) ∈ H₀ := by
      apply AddSubgroup.mem_map.mpr
      exact ⟨(z.val / m : ZMod g), by simp, rfl⟩
    change (a : ZMod (m * g)) - z ∈ H₀
    rw [← hrec]
    simpa [a] using H₀.neg_mem hemb
  have hDquotCard : (D.image q).card ≤ 4 := by
    calc
      (D.image q).card ≤
          (A.image (fun a : ℕ => q (a : ZMod (m * g)))).card :=
        Finset.card_le_card hDquot
      _ ≤ A.card := Finset.card_image_le
      _ ≤ 4 := by simpa [A] using hfour
  have himageDiff : (D - D).image q = D.image q - D.image q := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, z, hz, hxz⟩ := Finset.mem_sub.mp hu
      subst u
      subst y
      exact Finset.mem_sub.mpr
        ⟨q x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
          q z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp⟩
    · intro hy
      obtain ⟨qx, hqx, qz, hqz, hsum⟩ := Finset.mem_sub.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hqx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hqz
      apply Finset.mem_image.mpr
      refine ⟨x - z, Finset.mem_sub.mpr ⟨x, hx, z, hz, rfl⟩, ?_⟩
      simpa using hsum
  have hdiffCard : ((D.image q) - (D.image q)).card ≤ 16 := by
    exact Finset.card_sub_le.trans (Nat.mul_le_mul hDquotCard hDquotCard)
  obtain ⟨F, hFB, hFcard, hBF⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hBsmall
  let F₀ : Finset (ZMod (m * g)) := F.image e
  have hB₀cover : B₀ ⊆ F₀ + (D - D) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, z, hz, hfb⟩ := Finset.mem_add.mp (hBF hb)
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    apply Finset.mem_add.mpr
    refine ⟨e f, ?_, (c + e x) - (c + e y), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    · apply Finset.mem_sub.mpr
      refine ⟨c + e x, ?_, c + e y, ?_, rfl⟩
      · rw [hDaff]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · rw [hDaff]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · rw [← hfb]
      simp only [map_add, map_sub]
      abel
  have hBquot : B₀.image q ⊆ F₀.image q + (D - D).image q := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, z, hz, rfl⟩ := Finset.mem_add.mp (hB₀cover hb)
    exact Finset.mem_add.mpr
      ⟨q f, Finset.mem_image.mpr ⟨f, hf, rfl⟩,
        q z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, by simp⟩
  have hBquotCard : (B₀.image q).card ≤ 32 := by
    have hF₀card : F₀.card ≤ 2 :=
      Finset.card_image_le.trans hFcard
    calc
      (B₀.image q).card ≤ (F₀.image q + (D - D).image q).card :=
        Finset.card_le_card hBquot
      _ ≤ (F₀.image q).card * ((D - D).image q).card := Finset.card_add_le
      _ ≤ 2 * 16 := Nat.mul_le_mul
        (Finset.card_image_le.trans hF₀card)
        (by simpa [himageDiff] using hdiffCard)
      _ = 32 := by norm_num
  have hB₀dyadic : B₀ = dyadicFinsetSum P₀ j := by
    dsimp only [B₀, P₀]
    rw [hBdyadic]
    simpa using
      (image_dyadicFinsetSum_addMonoidHom e.toAddMonoidHom P j)
  have hzeroP₀ : 0 ∈ P₀ :=
    Finset.mem_image.mpr ⟨0, hzeroP, by simp [e]⟩
  have hH₀card : Nat.card H₀ = g := by
    rw [show Nat.card H₀ = Nat.card (⊤ : AddSubgroup (ZMod g)) by
      exact natCard_map_zmodQuotientEmbedding hm ⊤]
    simp
  have hquotCard : Fintype.card (ZMod (m * g) ⧸ H₀) = m := by
    have hcardEq := H₀.card_eq_card_quotient_mul_card_addSubgroup
    rw [hH₀card] at hcardEq
    simp only [ZMod.card, Nat.card_eq_fintype_card] at hcardEq
    exact Nat.mul_right_cancel (NeZero.pos g) hcardEq.symm
  obtain ⟨K₀, hK₀, hP₀K₀⟩ :=
    exists_proper_subgroup_of_dyadic_quotient_card_le_32_at_five
      hzeroP₀ hj H₀ (by simpa [hquotCard] using hm240) (by
        rw [← hB₀dyadic]
        simpa [q] using hBquotCard)
  let K := K₀.comap e.toAddMonoidHom
  refine ⟨K, ?_, ?_⟩
  · intro htop
    apply hK₀
    apply top_unique
    intro y _hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ K := by rw [htop]; simp
    exact hx
  · intro x hx
    change e x ∈ K₀
    apply hP₀K₀
    exact Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩

/-- The local inverse alternative in the support regimes covered below
by the cyclic fibre theory.  The statement deliberately exposes the support
dichotomy after Fourier extraction, so no low-support case is hidden in a
cardinality shortcut. -/
theorem cfpLocalDyadicInverseAlternativeWithLoss_48_of_support_le_two_or_six
    {t : ℕ} [NeZero t] (S : Finset (ZMod t)) (D j : ℕ)
    (hj : 2 ≤ j)
    (hsparse : 1000000000 *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ t)
    (hsmall : 25 *
      (dyadicFinsetSum (almostPeriods S D) j +
        dyadicFinsetSum (almostPeriods S D) j).card ≤
      51 * (dyadicFinsetSum (almostPeriods S D) j).card)
    (hsupport : ∀ (m g : ℕ) [NeZero g] (htg : t = m * g)
        (w : (ZMod t)ˣ) (c : ZMod t)
        (C E : Finset (ZMod t)) (X : Finset (ℕ × ZMod g)),
        240 ≤ m → C ⊆ dyadicFinsetSum (almostPeriods S D) j →
        33 * (dyadicFinsetSum (almostPeriods S D) j).card ≤ 40 * C.card →
        E = zmodAffineImage c (w : ZMod t) C → 0 ∈ E →
        X = zmodQuotRemImage m g (castZModFinset htg E) →
        (firstCoordinateSet X).card ≤ 2 ∨
          6 ≤ (firstCoordinateSet X).card) :
    CFPLocalDyadicInverseAlternativeWithLoss 48 S D j := by
  classical
  let P := almostPeriods S D
  let B := dyadicFinsetSum P j
  have hB : B.Nonempty := by
    exact ⟨0, zero_mem_dyadicFinsetSum (zero_mem_almostPeriods S D) j⟩
  obtain ⟨m, g, htg, w, c, C, E, X, hm240, hCB, hdense, hEaff,
      hEzero, hEcard, hX, hXcard, hXsum, hXzero, hXrange, hXsmall⟩ :=
    exists_dense_cyclic_smallProductCore_affine B hB
      (by simpa [B, P] using hsmall) (by simpa [B, P] using hsparse)
  letI : NeZero g := ⟨by
    have htpos : 0 < t := NeZero.pos t
    have hmg : 0 < m * g := by simpa [htg] using htpos
    exact (Nat.pos_of_mul_pos_left hmg).ne'⟩
  have hcases : (firstCoordinateSet X).card ≤ 2 ∨
      6 ≤ (firstCoordinateSet X).card :=
    hsupport m g htg w c C E X hm240
      (by simpa [B, P] using hCB)
      (by simpa [B, P] using hdense) hEaff hEzero hX
  subst t
  have hCne : C.Nonempty := by
    apply Finset.card_pos.mp
    have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨0, hEzero⟩
    omega
  change CFPLocalDyadicInverseAlternativeWithLoss 48 S D j
  rcases hcases with htwo | hsix
  · left
    apply proper_subgroup_of_two_layer_affine_core
      (P := almostPeriods S D)
      (B := dyadicFinsetSum (almostPeriods S D) j)
      (C := C) (D := E)
      (hzeroP := zero_mem_almostPeriods S D)
      (hsymmP := by
        intro x hx
        exact neg_mem_almostPeriods_iff.mpr hx)
      (hj := hj)
      (hBdyadic := rfl) w c
      (hC := hCne) (hCB := hCB) (hdense := hdense)
      (hBsmall := by simpa [B, P] using hsmall)
      (hDaff := hEaff) (hm240 := hm240) (hDzero := hEzero)
      (htwo := by simpa only [hX, castZModFinset] using htwo)
  · right
    obtain ⟨H, a, d, L, hprog, hmass⟩ :=
      gcd_normalized_affine_productCore_cyclicProgressionBound
        (B := B) (C := C) (D := E) w c
        (hC := hCne) (hCB := hCB) (hdense := hdense)
        (hBsmall := by simpa [B, P] using hsmall)
        (hDaff := hEaff) (hm := by omega) (hDzero := hEzero)
        (hAcard := by simpa only [hX, castZModFinset] using hsix)
        (hXsumD := by simpa only [hX, castZModFinset] using hXsum)
        (hXsmall := by simpa only [hX, castZModFinset] using hXsmall)
    exact ⟨H, a, d, L, by simpa [B, P] using hprog,
      by simpa [B, P] using hmass⟩

/-- The local inverse theorem after adjoining the sharp five-layer branch.
Only support cardinalities three and four remain outside this assembled
statement. -/
theorem cfpLocalDyadicInverseAlternativeWithLoss_48_of_support_le_two_five_or_six
    {t : ℕ} [NeZero t] (S : Finset (ZMod t)) (D j : ℕ)
    (hj : 2 ≤ j)
    (hsparse : 1000000000 *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ t)
    (hsmall : 25 *
      (dyadicFinsetSum (almostPeriods S D) j +
        dyadicFinsetSum (almostPeriods S D) j).card ≤
      51 * (dyadicFinsetSum (almostPeriods S D) j).card)
    (hsupport : ∀ (m g : ℕ) [NeZero g] (htg : t = m * g)
        (w : (ZMod t)ˣ) (c : ZMod t)
        (C E : Finset (ZMod t)) (X : Finset (ℕ × ZMod g)),
        240 ≤ m → C ⊆ dyadicFinsetSum (almostPeriods S D) j →
        17 * (dyadicFinsetSum (almostPeriods S D) j).card < 20 * C.card →
        E = zmodAffineImage c (w : ZMod t) C → 0 ∈ E →
        X = zmodQuotRemImage m g (castZModFinset htg E) →
        (firstCoordinateSet X).card ≤ 2 ∨
          (firstCoordinateSet X).card = 5 ∨
          6 ≤ (firstCoordinateSet X).card) :
    CFPLocalDyadicInverseAlternativeWithLoss 48 S D j := by
  classical
  let P := almostPeriods S D
  let B := dyadicFinsetSum P j
  have hB : B.Nonempty := by
    exact ⟨0, zero_mem_dyadicFinsetSum (zero_mem_almostPeriods S D) j⟩
  obtain ⟨m, g, htg, w, c, C, E, X, hm240, hCB, hdense17, hEaff,
      hEzero, hEcard, hX, hXcard, hXsum, hXzero, hXrange, hXsmall⟩ :=
    exists_dense_cyclic_smallProductCore_twelve_fifths B hB
      (by simpa [B, P] using hsmall) (by simpa [B, P] using hsparse)
  letI : NeZero g := ⟨by
    have htpos : 0 < t := NeZero.pos t
    have hmg : 0 < m * g := by simpa [htg] using htpos
    exact (Nat.pos_of_mul_pos_left hmg).ne'⟩
  have hcases : (firstCoordinateSet X).card ≤ 2 ∨
      (firstCoordinateSet X).card = 5 ∨
      6 ≤ (firstCoordinateSet X).card :=
    hsupport m g htg w c C E X hm240
      (by simpa [B, P] using hCB)
      (by simpa [B, P] using hdense17) hEaff hEzero hX
  subst t
  have hCne : C.Nonempty := by
    apply Finset.card_pos.mp
    have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨0, hEzero⟩
    omega
  have hdense : 33 * B.card ≤ 40 * C.card := by
    omega
  change CFPLocalDyadicInverseAlternativeWithLoss 48 S D j
  rcases hcases with htwo | hfive | hsix
  · left
    apply proper_subgroup_of_two_layer_affine_core
      (P := almostPeriods S D)
      (B := dyadicFinsetSum (almostPeriods S D) j)
      (C := C) (D := E)
      (hzeroP := zero_mem_almostPeriods S D)
      (hsymmP := by
        intro x hx
        exact neg_mem_almostPeriods_iff.mpr hx)
      (hj := hj) (hBdyadic := rfl) w c
      (hC := hCne) (hCB := hCB) (hdense := hdense)
      (hBsmall := by simpa [B, P] using hsmall)
      (hDaff := hEaff) (hm240 := hm240) (hDzero := hEzero)
      (htwo := by simpa only [hX, castZModFinset] using htwo)
  · right
    obtain ⟨H, a, d, L, hprog, hmass⟩ :=
      gcd_normalized_affine_productCore_cyclicProgressionBound_five
        (B := B) (C := C) (D := E) w c
        (hC := hCne) (hCB := hCB) (hdense := hdense)
        (hBsmall := by simpa [B, P] using hsmall)
        (hDaff := hEaff) (hm := by omega) (hDzero := hEzero)
        (hAcard := by simpa only [hX, castZModFinset] using hfive)
        (hXsumD := by simpa only [hX, castZModFinset] using hXsum)
        (hXsmall := by simpa only [hX, castZModFinset] using hXsmall)
    exact ⟨H, a, d, L, by simpa [B, P] using hprog,
      by simpa [B, P] using hmass⟩
  · right
    obtain ⟨H, a, d, L, hprog, hmass⟩ :=
      gcd_normalized_affine_productCore_cyclicProgressionBound
        (B := B) (C := C) (D := E) w c
        (hC := hCne) (hCB := hCB) (hdense := hdense)
        (hBsmall := by simpa [B, P] using hsmall)
        (hDaff := hEaff) (hm := by omega) (hDzero := hEzero)
        (hAcard := by simpa only [hX, castZModFinset] using hsix)
        (hXsumD := by simpa only [hX, castZModFinset] using hXsum)
        (hXsmall := by
          have : 2 * (X + X).card < 5 * X.card := by omega
          simpa only [hX, castZModFinset] using this)
    exact ⟨H, a, d, L, by simpa [B, P] using hprog,
      by simpa [B, P] using hmass⟩

/-- The complete local dyadic inverse alternative at every scale `j ≥ 5`.
Supports at most four are handled by quotient growth, support five by the
sharp five-layer fibre theorem, and supports at least six by the general
gcd-normalized affine-fibre theorem. -/
theorem cfpLocalDyadicInverseAlternativeWithLoss_48_at_five
    {t : ℕ} [NeZero t] (S : Finset (ZMod t)) (D j : ℕ)
    (hj : 5 ≤ j)
    (hsparse : 1000000000 *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ t)
    (hsmall : 25 *
      (dyadicFinsetSum (almostPeriods S D) j +
        dyadicFinsetSum (almostPeriods S D) j).card ≤
      51 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    CFPLocalDyadicInverseAlternativeWithLoss 48 S D j := by
  classical
  let P := almostPeriods S D
  let B := dyadicFinsetSum P j
  have hB : B.Nonempty := by
    exact ⟨0, zero_mem_dyadicFinsetSum (zero_mem_almostPeriods S D) j⟩
  obtain ⟨m, g, htg, w, c, C, E, X, hm240, hCB, hdense17, hEaff,
      hEzero, hEcard, hX, hXcard, hXsum, hXzero, hXrange, hXsmall⟩ :=
    exists_dense_cyclic_smallProductCore_twelve_fifths B hB
      (by simpa [B, P] using hsmall) (by simpa [B, P] using hsparse)
  letI : NeZero g := ⟨by
    have htpos : 0 < t := NeZero.pos t
    have hmg : 0 < m * g := by simpa [htg] using htpos
    exact (Nat.pos_of_mul_pos_left hmg).ne'⟩
  subst t
  have hCne : C.Nonempty := by
    apply Finset.card_pos.mp
    have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨0, hEzero⟩
    omega
  have hdense : 33 * B.card ≤ 40 * C.card := by
    omega
  have hcases : (firstCoordinateSet X).card ≤ 4 ∨
      (firstCoordinateSet X).card = 5 ∨
      6 ≤ (firstCoordinateSet X).card := by omega
  change CFPLocalDyadicInverseAlternativeWithLoss 48 S D j
  rcases hcases with hfour | hfive | hsix
  · left
    apply proper_subgroup_of_four_layer_affine_core_at_five
      (P := almostPeriods S D)
      (B := dyadicFinsetSum (almostPeriods S D) j)
      (C := C) (D := E)
      (hzeroP := zero_mem_almostPeriods S D)
      (hj := hj) (hBdyadic := rfl) w c
      (hC := hCne) (hCB := hCB) (hdense := hdense)
      (hBsmall := by simpa [B, P] using hsmall)
      (hDaff := hEaff) (hm240 := hm240) (hDzero := hEzero)
      (hfour := by simpa only [hX, castZModFinset] using hfour)
  · right
    obtain ⟨H, a, d, L, hprog, hmass⟩ :=
      gcd_normalized_affine_productCore_cyclicProgressionBound_five
        (B := B) (C := C) (D := E) w c
        (hC := hCne) (hCB := hCB) (hdense := hdense)
        (hBsmall := by simpa [B, P] using hsmall)
        (hDaff := hEaff) (hm := by omega) (hDzero := hEzero)
        (hAcard := by simpa only [hX, castZModFinset] using hfive)
        (hXsumD := by simpa only [hX, castZModFinset] using hXsum)
        (hXsmall := by simpa only [hX, castZModFinset] using hXsmall)
    exact ⟨H, a, d, L, by simpa [B, P] using hprog,
      by simpa [B, P] using hmass⟩
  · right
    obtain ⟨H, a, d, L, hprog, hmass⟩ :=
      gcd_normalized_affine_productCore_cyclicProgressionBound
        (B := B) (C := C) (D := E) w c
        (hC := hCne) (hCB := hCB) (hdense := hdense)
        (hBsmall := by simpa [B, P] using hsmall)
        (hDaff := hEaff) (hm := by omega) (hDzero := hEzero)
        (hAcard := by simpa only [hX, castZModFinset] using hsix)
        (hXsumD := by simpa only [hX, castZModFinset] using hXsum)
        (hXsmall := by
          have : 2 * (X + X).card < 5 * X.card := by omega
          simpa only [hX, castZModFinset] using this)
    exact ⟨H, a, d, L, by simpa [B, P] using hprog,
      by simpa [B, P] using hmass⟩

end Erdos360

#print axioms Erdos360.cfpLocalDyadicInverseAlternativeWithLoss_48_of_support_le_two_or_six
#print axioms Erdos360.cfpLocalDyadicInverseAlternativeWithLoss_48_of_support_le_two_five_or_six
#print axioms Erdos360.cfpLocalDyadicInverseAlternativeWithLoss_48_at_five
