import ErdosProblems.Erdos360.FiberCoherence
import ErdosProblems.Erdos360.AlmostPeriod
import ErdosProblems.Erdos360.CosetContraction

open scoped Pointwise

namespace Erdos360

/-- A scaled form of `subgroup_translates_shifted_longProgressionCover`.
The displayed subgroup translates are lifted to ordinary progressions and
then every progression is lengthened by the same factor `k`. -/
lemma subgroup_translates_shifted_longProgressionCover_scaled
    {b k : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (B F : Finset (ZMod b))
    (hk : 1 ≤ k)
    (hBF : B ⊆ F + subgroupFinset H)
    (hlong : B.card ≤ (k * Nat.card H) ^ 3) :
    HasLongProgressionCover (shiftedZmodValues B)
      (k * (F.card * Nat.card H)) := by
  classical
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  obtain ⟨q, hq, hqb, hHdiv, hmult⟩ := exists_generator_modulus hb H
  let P : Fin F.card → NatProgressionSpec := fun i ↦
    { start := ((F.equivFin).symm i).1.val % q
      step := q
      length := b / q
      step_pos := hq }
  let Q : Fin F.card → NatProgressionSpec := fun i ↦
    ((P i).extendLength k).translate b
  refine ⟨F.card, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxB, hxy⟩ := mem_shiftedZmodValues_iff.mp hy
    obtain ⟨f, hfF, h, hhH, hfh⟩ := Finset.mem_add.mp (hBF hxB)
    let i : Fin F.card := F.equivFin ⟨f, hfF⟩
    have hxcos : x ∈ (subgroupFinset H).image (fun z ↦ f + z) := by
      exact Finset.mem_image.mpr ⟨h, hhH, hfh⟩
    have hxval : x.val ∈ zmodValues
        ((subgroupFinset H).image (fun z ↦ f + z)) :=
      mem_zmodValues_iff.mpr ⟨x, hxcos, rfl⟩
    have hxP := coset_values_subset_natProgression
      hq hqb H hHdiv hmult f hxval
    have hPi : (P i).carrier =
        natProgression (f.val % q) q (b / q) := by
      simp [P, i, NatProgressionSpec.carrier]
    have hxi : x.val ∈ (P i).carrier := by rwa [hPi]
    have hxi' := (P i).carrier_subset_extendLength hk hxi
    refine ⟨i, ?_⟩
    have htrans := NatProgressionSpec.add_mem_translate (c := b) hxi'
    rwa [hxy] at htrans
  · change (∑ _i : Fin F.card, k * (b / q)) ≤
      k * (F.card * Nat.card H)
    rw [show (∑ _i : Fin F.card, k * (b / q)) =
        F.card * (k * (b / q)) by simp]
    rw [natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
    rw [show F.card * (k * (b / q)) =
      k * (F.card * (b / q)) by ring]
  · intro i
    rw [card_shiftedZmodValues]
    change B.card ≤ (k * (b / q)) ^ 3
    rw [← natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
    exact hlong

/-- The residue support indexes a cover by translates of the embedded full
remainder subgroup. -/
lemma zmodQuotRem_support_translates
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) :
    let A := firstCoordinateSet (zmodQuotRemImage m d D)
    let F := A.image (fun a : ℕ ↦ (a : ZMod (m * d)))
    let K := (⊤ : AddSubgroup (ZMod d)).map (zmodQuotientEmbedding m d)
    D ⊆ F + subgroupFinset K := by
  classical
  dsimp only
  intro z hz
  let a := z.val % m
  let q : ZMod d := (z.val / m : ℕ)
  have ha : a ∈ firstCoordinateSet (zmodQuotRemImage m d D) := by
    rw [firstCoordinateSet_zmodQuotRemImage]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have haf : (a : ZMod (m * d)) ∈
      (firstCoordinateSet (zmodQuotRemImage m d D)).image
        (fun r : ℕ ↦ (r : ZMod (m * d))) :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hqK : zmodQuotientEmbedding m d q ∈
      (⊤ : AddSubgroup (ZMod d)).map (zmodQuotientEmbedding m d) := by
    apply AddSubgroup.mem_map.mpr
    exact ⟨q, by simp, rfl⟩
  apply Finset.mem_add.mpr
  refine ⟨(a : ZMod (m * d)), haf, zmodQuotientEmbedding m d q, ?_, ?_⟩
  · exact mem_subgroupFinset.mpr hqK
  · dsimp [a, q]
    rw [add_comm]
    exact zmodQuotientEmbedding_quotient_add_remainder z

/-- At most five quotient--remainder layers always have a long ordinary
progression cover of mass at most fifteen times the larger of the remainder
modulus and the original set size.

No small-doubling hypothesis is required: the five occupied residues index
five cosets of the embedded remainder group, and tripling the lengths of
their ordinary lifts makes each piece long enough. -/
theorem low_support_zmodQuotRem_longProgressionCover
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hsupport :
      (firstCoordinateSet (zmodQuotRemImage m d D)).card ≤ 5) :
    HasLongProgressionCover (shiftedZmodValues D) (15 * max d D.card) := by
  classical
  let A := firstCoordinateSet (zmodQuotRemImage m d D)
  let F : Finset (ZMod (m * d)) :=
    A.image (fun a : ℕ ↦ (a : ZMod (m * d)))
  let K := (⊤ : AddSubgroup (ZMod d)).map (zmodQuotientEmbedding m d)
  have hDK : D ⊆ F + subgroupFinset K := by
    simpa [A, F, K] using zmodQuotRem_support_translates D
  have hFcard : F.card ≤ 5 := by
    calc
      F.card ≤ A.card := Finset.card_image_le
      _ ≤ 5 := by simpa [A] using hsupport
  have hKcard : Nat.card K = d := by
    rw [show Nat.card K = Nat.card (⊤ : AddSubgroup (ZMod d)) by
      exact natCard_map_zmodQuotientEmbedding hm ⊤]
    simp
  have hDcard : D.card ≤ F.card * Nat.card K := by
    calc
      D.card ≤ (F + subgroupFinset K).card := Finset.card_le_card hDK
      _ ≤ F.card * (subgroupFinset K).card := Finset.card_add_le
      _ = F.card * Nat.card K := by rw [card_subgroupFinset]
  have hdpos : 0 < d := NeZero.pos d
  have hlong : D.card ≤ (3 * Nat.card K) ^ 3 := by
    rw [hKcard]
    rw [hKcard] at hDcard
    have hDfive : D.card ≤ 5 * d :=
      hDcard.trans (Nat.mul_le_mul_right d hFcard)
    have hdCube : d ≤ d ^ 3 := le_self_pow (by omega) (by omega)
    calc
      D.card ≤ 5 * d := hDfive
      _ ≤ 27 * d := Nat.mul_le_mul_right d (by omega)
      _ ≤ 27 * d ^ 3 := Nat.mul_le_mul_left 27 hdCube
      _ = (3 * d) ^ 3 := by ring
  have hcover := subgroup_translates_shifted_longProgressionCover_scaled
    K D F (by omega : 1 ≤ 3) hDK hlong
  apply hcover.mono_mass
  rw [hKcard]
  have hdmax : d ≤ max d D.card := le_max_left _ _
  nlinarith only [hFcard, hdmax]

/-- In the range where the remainder modulus is no larger than the set, the
low-support cover has genuinely linear mass. -/
theorem low_support_zmodQuotRem_longProgressionCover_linear
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hsupport :
      (firstCoordinateSet (zmodQuotRemImage m d D)).card ≤ 5)
    (hdD : d ≤ D.card) :
    HasLongProgressionCover (shiftedZmodValues D) (15 * D.card) := by
  simpa [max_eq_right hdD] using
    low_support_zmodQuotRem_longProgressionCover D hm hsupport

/-! ### The three-coset exception in the CFP dyadic argument

The next lemmas isolate the source-faithful reason why the exceptional
three-coset conclusion of the Deshouillers--Freiman theorem does not cost a
factor equal to the dyadic sumset size.  At a dyadic level at least two, the
image in the quotient contains a four-fold sumset.  If that image has at
most three elements, CFP Lemma 2.3 forces the quotient to have at most three
elements unless the original almost-period set lies in a proper subgroup.
Under the sparsity inequality `3 * |H| < |G|`, the latter is the only
possibility. -/

lemma image_finset_add_addMonoidHom
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [DecidableEq G] [DecidableEq Q]
    (f : G →+ Q) (A B : Finset G) :
    (A + B).image f = A.image f + B.image f := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    exact Finset.mem_add.mpr
      ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, by simp⟩
  · intro hz
    obtain ⟨fa, hfa, fb, hfb, hsum⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hfa
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hfb
    refine Finset.mem_image.mpr ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
    simpa using hsum

lemma image_dyadicFinsetSum_addMonoidHom
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [DecidableEq G] [DecidableEq Q]
    (f : G →+ Q) (A : Finset G) (j : ℕ) :
    (dyadicFinsetSum A j).image f =
      dyadicFinsetSum (A.image f) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [dyadicFinsetSum_succ, image_finset_add_addMonoidHom,
        ih, dyadicFinsetSum_succ]

/-- CFP's three-coset exception collapses to the proper-subgroup branch.

Here `H` is the subgroup whose quotient contains at most three occupied
cosets at a dyadic level.  The strict index inequality says that `H` has
index at least four.  Thus four-fold growth in the quotient contradicts the
three-coset bound unless `P` was already contained in a proper subgroup of
the ambient group. -/
theorem exists_proper_subgroup_of_dyadic_quotient_card_le_three
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P) {j : ℕ} (hj : 2 ≤ j)
    (H : AddSubgroup G)
    [DecidableEq (G ⧸ H)]
    (hindex : 3 * Nat.card H < Nat.card G)
    (hthree :
      ((dyadicFinsetSum P j).image (QuotientAddGroup.mk' H)).card ≤ 3) :
    ∃ K : AddSubgroup G, K ≠ ⊤ ∧ (P : Set G) ⊆ (K : Set G) := by
  classical
  let q : G →+ G ⧸ H := QuotientAddGroup.mk' H
  let Pbar : Finset (G ⧸ H) := P.image q
  have hqsurj : Function.Surjective q := by
    simpa [q] using QuotientAddGroup.mk'_surjective H
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hcardEq := H.card_eq_card_quotient_mul_card_addSubgroup
  have hqgt : 3 < Nat.card (G ⧸ H) := by
    apply (Nat.mul_lt_mul_right hHpos).mp
    calc
      3 * Nat.card H < Nat.card G := hindex
      _ = Nat.card (G ⧸ H) * Nat.card H := hcardEq
  have hqfour : 4 ≤ Fintype.card (G ⧸ H) := by
    simpa only [Nat.card_eq_fintype_card] using Nat.add_one_le_iff.mpr hqgt
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
  have hzeroAdd : ({0} : Finset (G ⧸ H)) + Pbar = Pbar := by
    ext x
    simp [Finset.mem_add]
  have hfourSubset :
      iteratedFinsetSum Pbar 4 ⊆
        (dyadicFinsetSum P j).image q := by
    have hmono : dyadicFinsetSum P 2 ⊆ dyadicFinsetSum P j :=
      dyadicFinsetSum_mono hzero hj
    have himage : (dyadicFinsetSum P 2).image q ⊆
        (dyadicFinsetSum P j).image q := Finset.image_mono q hmono
    have heq : iteratedFinsetSum Pbar 4 =
        (dyadicFinsetSum P 2).image q := by
      calc
        iteratedFinsetSum Pbar 4 = dyadicFinsetSum Pbar 2 := by
          change (((({0} : Finset (G ⧸ H)) + Pbar) + Pbar) + Pbar) + Pbar =
            (Pbar + Pbar) + (Pbar + Pbar)
          rw [hzeroAdd]
          ac_rfl
        _ = (dyadicFinsetSum P 2).image q := by
          simpa [Pbar] using
            (image_dyadicFinsetSum_addMonoidHom q P 2).symm
    rw [heq]
    exact himage
  have hfourCard : (iteratedFinsetSum Pbar 4).card ≤ 3 := by
    exact (Finset.card_le_card hfourSubset).trans (by simpa [q] using hthree)
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroBar⟩ hPbarCoset 4 (by omega)
  have hminUpper :
      min (2 * Fintype.card (G ⧸ H)) (5 * Pbar.card) ≤ 6 := by
    exact hlower.trans (Nat.mul_le_mul_left 2 hfourCard)
  have hminLower :
      7 ≤ min (2 * Fintype.card (G ⧸ H)) (5 * Pbar.card) := by
    apply le_min
    · omega
    · omega
  omega

/-- A cyclic progression of `L` subgroup cosets has at most `L` distinct
images in the quotient, even when the displayed progression wraps. -/
lemma card_quotient_image_le_length_of_subset_cyclicCosetProgression
    {t : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    [DecidableEq (ZMod t ⧸ H)]
    {B : Finset (ZMod t)} {a d : ZMod t} {L : ℕ}
    (hB : B ⊆ cyclicCosetProgression H a d L) :
    (B.image (QuotientAddGroup.mk' H)).card ≤ L := by
  classical
  let q : ZMod t →+ ZMod t ⧸ H := QuotientAddGroup.mk' H
  let R : Finset (ZMod t ⧸ H) :=
    (Finset.range L).image (fun i ↦ q (a + i • d))
  have himage : B.image q ⊆ R := by
    intro x hx
    obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hi, hyi⟩ :=
      mem_cyclicCosetProgression_iff.mp (hB hyB)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    simpa only [neg_sub] using H.neg_mem hyi
  calc
    (B.image (QuotientAddGroup.mk' H)).card = (B.image q).card := by rfl
    _ ≤ R.card := Finset.card_le_card himage
    _ ≤ (Finset.range L).card := Finset.card_image_le
    _ = L := Finset.card_range L

/-- The literal three-coset-progression interface supplied by the
Deshouillers--Freiman alternative.  Under index at least four it is already
the proper-subgroup branch of CFP Lemma 5.7. -/
theorem exists_proper_subgroup_of_dyadic_subset_three_cosetProgression
    {t : ℕ} [NeZero t] {P : Finset (ZMod t)}
    (hzero : 0 ∈ P) {j : ℕ} (hj : 2 ≤ j)
    (H : AddSubgroup (ZMod t)) [DecidableEq (ZMod t ⧸ H)]
    (hindex : 3 * Nat.card H < t) (a d : ZMod t)
    (hprog : dyadicFinsetSum P j ⊆
      cyclicCosetProgression H a d 3) :
    ∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      (P : Set (ZMod t)) ⊆ (K : Set (ZMod t)) := by
  apply exists_proper_subgroup_of_dyadic_quotient_card_le_three
    hzero hj H
  · simpa using hindex
  · exact card_quotient_image_le_length_of_subset_cyclicCosetProgression
      H hprog

/-- If a dyadic sumset containing zero occupies one coset of a proper
subgroup, then the original set lies in that subgroup.  This is CFP's
one-coset exclusion, phrased so it can also be used constructively as the
proper-subgroup alternative. -/
theorem exists_proper_subgroup_of_dyadic_containedInAddCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P) (j : ℕ)
    (H : AddSubgroup G) (hHcard : Nat.card H < Nat.card G)
    (hcos : ContainedInAddCoset H (dyadicFinsetSum P j)) :
    ∃ K : AddSubgroup G, K ≠ ⊤ ∧ (P : Set G) ⊆ (K : Set G) := by
  classical
  have hHproper : H ≠ ⊤ := by
    intro htop
    subst H
    simpa using hHcard
  refine ⟨H, hHproper, ?_⟩
  obtain ⟨a, ha⟩ := hcos
  have hzeroDy : 0 ∈ dyadicFinsetSum P j :=
    zero_mem_dyadicFinsetSum hzero j
  have hzeroCos := ha (by simpa using hzeroDy)
  rw [Set.mem_vadd_set] at hzeroCos
  obtain ⟨h₀, hh₀, ha0⟩ := hzeroCos
  have haH : a ∈ H := by
    have haeq : a = -h₀ := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [vadd_eq_add, add_comm] using ha0
    simpa [haeq] using H.neg_mem hh₀
  have hPdy : P ⊆ dyadicFinsetSum P j :=
    dyadicFinsetSum_mono hzero (Nat.zero_le j)
  intro x hx
  have hxCos := ha (by simpa using hPdy (by simpa using hx))
  rw [Set.mem_vadd_set] at hxCos
  obtain ⟨h, hh, hax⟩ := hxCos
  have : a + h ∈ H := H.add_mem haH hh
  simpa [vadd_eq_add] using hax ▸ this

/-- The long-progression alternative of the corrected
Deshouillers--Freiman theorem, connected all the way to the exact structural
output consumed by `almostPeriod_cyclicCoset_trichotomy_from_two`.

The inverse theorem is used only through `hDFmass`: its progression of
`H`-cosets has displayed mass at most `52/25` times the dyadic set.  The
quotient interval contraction removes the factor `2^j`; CFP equation (16)
and the canonical choice of the terminal scale then give the absolute
bound `128D`. -/
theorem almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression
    {t N : ℕ} [NeZero t] [NeZero N]
    {S : Finset (ZMod t)} {D i j L : ℕ}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (e : ZMod N ≃+ (ZMod t ⧸ H))
    (hgen : e 1 = QuotientAddGroup.mk' H d)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card)
    (hkL : 2 ^ j ≤ L) (hhalf : 2 * L ≤ N)
    (hsum : dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L)
    (hDFmass : 25 * (L * Nat.card H) ≤
      52 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  classical
  let P := almostPeriods S D
  let k := 2 ^ j
  have hzero : 0 ∈ P := by simp [P]
  have hk : 0 < k := by simp [k]
  have hsum' : iteratedFinsetSum P k ⊆
      cyclicCosetProgression H a d L := by
    rw [show iteratedFinsetSum P k = dyadicFinsetSum P j by
      simpa [k] using (dyadicFinsetSum_eq_iteratedFinsetSum P j).symm]
    simpa [P] using hsum
  obtain ⟨a', ell, hPprog, hcontract⟩ :=
    cyclic_coset_progression_contraction H a d e hgen hzero hk
      (by simpa [k] using hkL) hhalf hsum'
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  have hcontract' : 2 ^ (j - 1) * (ell * Nat.card H) ≤
      L * Nat.card H := by
    have htwo : 2 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        2 * (L * Nat.card H) := by
      calc
        2 * (2 ^ (j - 1) * (ell * Nat.card H)) =
            k * (ell * Nat.card H) := by rw [show k = 2 ^ j by rfl, hpow]; ring
        _ ≤ 2 * (L * Nat.card H) := hcontract
    omega
  have hCFPcontract :
      25 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        52 * (dyadicFinsetSum (almostPeriods S D) j).card := by
    exact (Nat.mul_le_mul_left 25 hcontract').trans hDFmass
  have hmass : ell * Nat.card H ≤ 128 * D :=
    cfp_contracted_progression_mass_le hj hji hscale hlevel hCFPcontract
  exact ⟨H, a', d, ell, by simpa [P] using hPprog, hmass⟩

/-- Closure-based form of the long-progression connector.  This removes
all quotient-coordinate choices from the local inverse interface: since the
almost-period set generates the ambient cyclic group, the displayed step is
automatically a generator of the quotient. -/
theorem almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_closure
    {t : ℕ} [NeZero t]
    {S : Finset (ZMod t)} {D i j L : ℕ}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (hclosure : AddSubgroup.closure
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) = ⊤)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card)
    (hkL : 2 ^ j ≤ L)
    (hhalf : 2 * L ≤ Nat.card (ZMod t ⧸ H))
    (hsum : dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L)
    (hDFmass : 25 * (L * Nat.card H) ≤
      52 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  classical
  let P := almostPeriods S D
  let k := 2 ^ j
  have hzero : 0 ∈ P := by simp [P]
  have hk : 0 < k := by simp [k]
  have hsum' : iteratedFinsetSum P k ⊆
      cyclicCosetProgression H a d L := by
    rw [show iteratedFinsetSum P k = dyadicFinsetSum P j by
      simpa [k] using (dyadicFinsetSum_eq_iteratedFinsetSum P j).symm]
    simpa [P] using hsum
  obtain ⟨a', ell, hPprog, hcontract⟩ :=
    cyclic_coset_progression_contraction_of_closure_eq_top
      H a d hzero hk (by simpa [k] using hkL)
      (by simpa [P] using hclosure) hhalf hsum'
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  have hcontract' : 2 ^ (j - 1) * (ell * Nat.card H) ≤
      L * Nat.card H := by
    have htwo : 2 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        2 * (L * Nat.card H) := by
      calc
        2 * (2 ^ (j - 1) * (ell * Nat.card H)) =
            k * (ell * Nat.card H) := by rw [show k = 2 ^ j by rfl, hpow]; ring
        _ ≤ 2 * (L * Nat.card H) := hcontract
    omega
  have hCFPcontract :
      25 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        52 * (dyadicFinsetSum (almostPeriods S D) j).card := by
    exact (Nat.mul_le_mul_left 25 hcontract').trans hDFmass
  have hmass : ell * Nat.card H ≤ 128 * D :=
    cfp_contracted_progression_mass_le hj hji hscale hlevel hCFPcontract
  exact ⟨H, a', d, ell, by simpa [P] using hPprog, hmass⟩

/-- Conditional but source-complete packaging of CFP Lemma 5.7.  The sole
remaining local inverse input is the corrected Deshouillers--Freiman
alternative at a slow dyadic doubling step.  Its one- and three-coset
exceptions should be returned through the first branch (the lemmas above do
exactly that); its long-progression alternative supplies the second branch.

All iteration, exclusion of proper subgroups, equation (16), quotient
contraction, and the final `128D` calculation are discharged here. -/
theorem almostPeriod_cyclicCoset_trichotomy_from_two_of_localDF
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i : ℕ}
    (hS : S.Nonempty) (hi : 2 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hsparse : 2 * S.card < Fintype.card (ZMod t))
    (hlocalDF : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
        ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
          (K : Set (ZMod t))) ∨
      ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
        2 ^ j ≤ L ∧
        2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
        dyadicFinsetSum (almostPeriods S D) j ⊆
          cyclicCosetProgression H a d L ∧
        25 * (L * Nat.card H) ≤
          52 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    51 ^ (i - 2) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 2) * S.card) ∨
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  classical
  let P := almostPeriods S D
  by_cases hproper : ∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((P : Finset (ZMod t)) : Set (ZMod t)) ⊆ (K : Set (ZMod t))
  · exact Or.inl (by simpa [P] using hproper)
  have hclosure : AddSubgroup.closure
      ((P : Finset (ZMod t)) : Set (ZMod t)) = ⊤ := by
    by_contra hne
    apply hproper
    exact ⟨AddSubgroup.closure ((P : Finset (ZMod t)) : Set (ZMod t)),
      hne, AddSubgroup.subset_closure⟩
  rcases almostPeriod_dyadic_trichotomy_from_two hS hi hbudget with
      hproper' | hsmall | hnumeric
  · exact Or.inl hproper'
  · obtain ⟨j, hj, hji, hslow⟩ := hsmall
    rcases hlocalDF j hj hji hslow with hlocalProper |
      ⟨H, a, d, L, hkL, hhalf, hprog, hDFmass⟩
    · exact Or.inl hlocalProper
    · right; right
      have hlevel0 := pow_two_mul_card_dyadic_le_two_mul_final
        hS (Nat.le_of_lt hji) hbudget hsparse (by simpa [P] using hproper)
      have hfinal := card_dyadicFinsetSum_almostPeriods_le_two_mul
        hS hbudget
      have hlevel : 2 ^ (i - j) *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card :=
        hlevel0.trans (by omega)
      exact
        almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_closure
          H a d (by omega) (Nat.le_of_lt hji)
          (by simpa [P] using hclosure) hscale hlevel hkL hhalf hprog hDFmass
  · exact Or.inr (Or.inl hnumeric)

/-- Progression-cover form of the packaged conditional Lemma 5.7. -/
theorem almostPeriod_longProgressionCover_trichotomy_from_two_of_localDF
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i : ℕ}
    (hS : S.Nonempty) (hi : 2 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hsparse : 2 * S.card < Fintype.card (ZMod t))
    (hlocalDF : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
        ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
          (K : Set (ZMod t))) ∨
      ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
        2 ^ j ≤ L ∧
        2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
        dyadicFinsetSum (almostPeriods S D) j ⊆
          cyclicCosetProgression H a d L ∧
        25 * (L * Nat.card H) ≤
          52 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    51 ^ (i - 2) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 2) * S.card) ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (768 * D) := by
  rcases almostPeriod_cyclicCoset_trichotomy_from_two_of_localDF
      hS hi hbudget hscale hsparse hlocalDF with
      hproper | hnumeric | hstruct
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hnumeric)
  · right; right
    have hP : (almostPeriods S D).Nonempty :=
      ⟨0, zero_mem_almostPeriods S D⟩
    have hcover := hstruct.longProgressionCover hP
    convert hcover using 1 <;> ring

/-- Canonical-scale, integer-power form of CFP Lemma 5.7 reduced only to
the corrected local Deshouillers--Freiman alternative.  This is the final
interface needed by the modular-growth argument: its structural conclusion
is already the `768D` long integer-progression cover. -/
theorem almostPeriod_longProgressionCover_polynomial_trichotomy_of_localDF
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hsparse : 2 * S.card < Fintype.card (ZMod t))
    (hlocalDF : ∀ j, 2 ≤ j →
      j < Nat.log 2 (S.card / (2 * D)) →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
        ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
          (K : Set (ZMod t))) ∨
      ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
        2 ^ j ≤ L ∧
        2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
        dyadicFinsetSum (almostPeriods S D) j ⊆
          cyclicCosetProgression H a d L ∧
        25 * (L * Nat.card H) ≤
          52 * (dyadicFinsetSum (almostPeriods S D) j).card) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 *
        (almostPeriods S D).card ^ 100 ≤
      2 ^ 406 * S.card ^ 100 ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (768 * D) := by
  let q := S.card / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨hi, hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change 2 ≤ i at hi
  change 2 * ((2 ^ i) * D) ≤ S.card at hbudget
  change q < 2 ^ (i + 1) at hqpow
  have hscale : S.card < 4 * D * 2 ^ i := by
    simpa [i, q] using
      (almostPeriod_chosenIndex_card_lt_four_mul hD hlarge)
  have hlocalDF' : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
        ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
          (K : Set (ZMod t))) ∨
      ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
        2 ^ j ≤ L ∧
        2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
        dyadicFinsetSum (almostPeriods S D) j ⊆
          cyclicCosetProgression H a d L ∧
        25 * (L * Nat.card H) ≤
          52 * (dyadicFinsetSum (almostPeriods S D) j).card := by
    simpa [i, q] using hlocalDF
  rcases almostPeriod_longProgressionCover_trichotomy_from_two_of_localDF
      hS hi hbudget hscale hsparse hlocalDF' with
      hproper | hnumeric | hcover
  · exact Or.inl hproper
  · right; left
    have hshift : i - 2 + 3 = i + 1 := by omega
    have hpoly := dyadic_numeric_bound_one_point_zero_two
      (n := i - 2) (q := q) (P := (almostPeriods S D).card)
      (S := S.card) (by simpa [hshift] using hqpow) hnumeric
    simpa [q] using hpoly
  · exact Or.inr (Or.inr hcover)

/-! ### Final sparse corrected-DF interface -/

/-- The exact output needed from the corrected local
Deshouillers--Freiman theorem at one dyadic scale.  All quotient-generator,
half-circle, and contraction facts have deliberately been removed from this
interface. -/
def CFPLocalDyadicInverseAlternative
    {t : ℕ} [NeZero t] (S : Finset (ZMod t)) (D j : ℕ) : Prop :=
  (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
    ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
      (K : Set (ZMod t))) ∨
  ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
    dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L ∧
    25 * (L * Nat.card H) ≤
      52 * (dyadicFinsetSum (almostPeriods S D) j).card

/-- Long-progression contraction with every formerly auxiliary hypothesis
derived internally.  The inverse theorem supplies only its progression,
its `52/25` mass bound, and ambient sparsity. -/
theorem almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_sparse
    {t : ℕ} [NeZero t]
    {S : Finset (ZMod t)} {D i j L : ℕ}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (hclosure : AddSubgroup.closure
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) = ⊤)
    (hscale : S.card < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) *
      (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card)
    (hsum : dyadicFinsetSum (almostPeriods S D) j ⊆
      cyclicCosetProgression H a d L)
    (hDFmass : 25 * (L * Nat.card H) ≤
      52 * (dyadicFinsetSum (almostPeriods S D) j).card)
    (hsparse : 104 * (dyadicFinsetSum (almostPeriods S D) j).card <
      25 * t) :
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  classical
  let P := almostPeriods S D
  let k := 2 ^ j
  have hzero : 0 ∈ P := by simp [P]
  have hk : 0 < k := by simp [k]
  have hsum' : iteratedFinsetSum P k ⊆
      cyclicCosetProgression H a d L := by
    rw [show iteratedFinsetSum P k = dyadicFinsetSum P j by
      simpa [k] using (dyadicFinsetSum_eq_iteratedFinsetSum P j).symm]
    simpa [P] using hsum
  obtain ⟨a', ell, hPprog, hcontract⟩ :=
    cyclic_coset_progression_contraction_of_mass_and_sparse
      H a d hzero hk (by simpa [P] using hclosure) hsum'
      hDFmass hsparse
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  have hcontract' : 2 ^ (j - 1) * (ell * Nat.card H) ≤
      L * Nat.card H := by
    have htwo : 2 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        2 * (L * Nat.card H) := by
      calc
        2 * (2 ^ (j - 1) * (ell * Nat.card H)) =
            k * (ell * Nat.card H) := by rw [show k = 2 ^ j by rfl, hpow]; ring
        _ ≤ 2 * (L * Nat.card H) := hcontract
    omega
  have hCFPcontract :
      25 * (2 ^ (j - 1) * (ell * Nat.card H)) ≤
        52 * (dyadicFinsetSum (almostPeriods S D) j).card := by
    exact (Nat.mul_le_mul_left 25 hcontract').trans hDFmass
  have hmass : ell * Nat.card H ≤ 128 * D :=
    cfp_contracted_progression_mass_le hj hji hscale hlevel hCFPcontract
  exact ⟨H, a', d, ell, by simpa [P] using hPprog, hmass⟩

/-- Final canonical CFP Lemma 5.7 connector.  The constant
`2,000,000,000` is a harmless explicit choice of the paper's sufficiently
small absolute density `ξ`.  It supplies both equation (16)'s unsaturated
range and the corrected inverse theorem's `10⁹`-sparsity hypothesis at
every relevant dyadic scale.

No quotient coordinate, lower bound on the inverse progression length, or
half-circle assumption remains in `hlocalDF`. -/
theorem almostPeriod_longProgressionCover_polynomial_trichotomy_of_sparse_localDF
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hambient : 2000000000 * S.card ≤ t)
    (hlocalDF : ∀ j, 2 ≤ j →
      j < Nat.log 2 (S.card / (2 * D)) →
      1000000000 *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ t →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      CFPLocalDyadicInverseAlternative S D j) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (K : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 *
        (almostPeriods S D).card ^ 100 ≤
      2 ^ 406 * S.card ^ 100 ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (768 * D) := by
  classical
  let P := almostPeriods S D
  let q := S.card / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨hi, hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change 2 ≤ i at hi
  change 2 * ((2 ^ i) * D) ≤ S.card at hbudget
  change q < 2 ^ (i + 1) at hqpow
  have hscale : S.card < 4 * D * 2 ^ i := by
    simpa [i, q] using
      (almostPeriod_chosenIndex_card_lt_four_mul hD hlarge)
  have hScardPos : 0 < S.card := Finset.card_pos.mpr hS
  have hsparseEq : 2 * S.card < Fintype.card (ZMod t) := by
    rw [ZMod.card]
    nlinarith only [hambient, hScardPos]
  by_cases hproper : ∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      ((P : Finset (ZMod t)) : Set (ZMod t)) ⊆ (K : Set (ZMod t))
  · exact Or.inl (by simpa [P] using hproper)
  have hclosure : AddSubgroup.closure
      ((P : Finset (ZMod t)) : Set (ZMod t)) = ⊤ := by
    by_contra hne
    apply hproper
    exact ⟨AddSubgroup.closure ((P : Finset (ZMod t)) : Set (ZMod t)),
      hne, AddSubgroup.subset_closure⟩
  rcases almostPeriod_dyadic_trichotomy_from_two hS hi hbudget with
      hproper' | hsmall | hnumeric
  · exact Or.inl hproper'
  · obtain ⟨j, hj, hji, hslow⟩ := hsmall
    have hBcard := card_dyadicFinsetSum_almostPeriods_le_two_mul_of_le
      hS (Nat.le_of_lt hji) hbudget
    have hDFsparse : 1000000000 *
        (dyadicFinsetSum (almostPeriods S D) j).card ≤ t := by
      calc
        1000000000 *
            (dyadicFinsetSum (almostPeriods S D) j).card ≤
            1000000000 * (2 * S.card) :=
          Nat.mul_le_mul_left 1000000000 hBcard
        _ = 2000000000 * S.card := by ring
        _ ≤ t := hambient
    rcases hlocalDF j hj (by simpa [i, q] using hji) hDFsparse hslow with
      hlocalProper | ⟨H, a, d, L, hprog, hDFmass⟩
    · exact Or.inl hlocalProper
    · right; right
      have hlevel0 := pow_two_mul_card_dyadic_le_two_mul_final
        hS (Nat.le_of_lt hji) hbudget hsparseEq (by simpa [P] using hproper)
      have hfinal := card_dyadicFinsetSum_almostPeriods_le_two_mul
        hS hbudget
      have hlevel : 2 ^ (i - j) *
          (dyadicFinsetSum (almostPeriods S D) j).card ≤ 4 * S.card :=
        hlevel0.trans (by omega)
      have hcontractSparse : 104 *
          (dyadicFinsetSum (almostPeriods S D) j).card < 25 * t := by
        nlinarith only [hBcard, hambient, hScardPos]
      have hstruct :=
        almostPeriods_hasCyclicCosetProgressionBound_of_dyadic_longProgression_sparse
          H a d (by omega) (Nat.le_of_lt hji)
          (by simpa [P] using hclosure) hscale hlevel hprog hDFmass
          hcontractSparse
      have hPnonempty : (almostPeriods S D).Nonempty :=
        ⟨0, zero_mem_almostPeriods S D⟩
      have hcover := hstruct.longProgressionCover hPnonempty
      convert hcover using 1 <;> ring
  · right; left
    have hshift : i - 2 + 3 = i + 1 := by omega
    have hpoly := dyadic_numeric_bound_one_point_zero_two
      (n := i - 2) (q := q) (P := (almostPeriods S D).card)
      (S := S.card) (by simpa [hshift] using hqpow) hnumeric
    simpa [q] using hpoly

end Erdos360
