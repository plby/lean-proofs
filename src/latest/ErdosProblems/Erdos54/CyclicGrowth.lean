import ErdosProblems.Erdos54.AlmostPeriods
import ErdosProblems.Erdos54.CyclicGrowthArithmetic
import ErdosProblems.Erdos54.CyclicGrowthParameters
import ErdosProblems.Erdos54.CyclicGrowthTail
import ErdosProblems.Erdos54.FiniteSums
import ErdosProblems.Erdos54.IteratedSumset
import ErdosProblems.Erdos54.Probability
import ErdosProblems.Erdos54.RoughNumbers

/-!
# Cyclic subset-sum growth for Erdős Problem 54

This file formalizes the finite cyclic process in Conlon--Fox--Pham,
Lemma 3.1.  A sample is kept as an ordered list (and, at the public
interface, as a tuple), because the proof exposes one independent sample at
a time.  The state after a prefix is the set of all distinct-index subset
sums modulo `m`.

The definitions and elementary state identities below deliberately do not
use probability measures.  The final estimate is a division-free counting
inequality on the finite type of tuples.
-/

open scoped BigOperators Pointwise

namespace Erdos54

noncomputable section

/-! ## The cyclic subset-sum process -/

/-- Add one sampled residue to a cyclic subset-sum state. -/
def cyclicResidueStep (m : ℕ) (D : Finset (ZMod m)) (a : ℕ) :
    Finset (ZMod m) :=
  D ∪ translate D (a : ZMod m)

/-- Residues of all distinct-position subset sums of an ordered sample. -/
def cyclicSubsetSumResiduesList (m : ℕ) (s : List ℕ) : Finset (ZMod m) :=
  s.foldl (cyclicResidueStep m) {0}

/-- Tuple form of `cyclicSubsetSumResiduesList`. -/
def cyclicSubsetSumResidues {q : ℕ} (m : ℕ) (s : Fin q → ℕ) :
    Finset (ZMod m) :=
  cyclicSubsetSumResiduesList m (List.ofFn s)

@[simp] theorem cyclicSubsetSumResiduesList_nil (m : ℕ) :
    cyclicSubsetSumResiduesList m [] = {0} := by
  rfl

theorem cyclicSubsetSumResiduesList_append (m : ℕ) (s t : List ℕ) :
    cyclicSubsetSumResiduesList m (s ++ t) =
      t.foldl (cyclicResidueStep m) (cyclicSubsetSumResiduesList m s) := by
  simp [cyclicSubsetSumResiduesList, List.foldl_append]

@[simp] theorem cyclicSubsetSumResiduesList_append_singleton
    (m : ℕ) (s : List ℕ) (a : ℕ) :
    cyclicSubsetSumResiduesList m (s ++ [a]) =
      cyclicResidueStep m (cyclicSubsetSumResiduesList m s) a := by
  simp [cyclicSubsetSumResiduesList, List.foldl_append]

@[simp] theorem zero_mem_cyclicSubsetSumResiduesList (m : ℕ) (s : List ℕ) :
    0 ∈ cyclicSubsetSumResiduesList m s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s a ih =>
      rw [cyclicSubsetSumResiduesList_append_singleton]
      exact Finset.mem_union_left _ ih

theorem cyclicSubsetSumResiduesList_nonempty (m : ℕ) (s : List ℕ) :
    (cyclicSubsetSumResiduesList m s).Nonempty :=
  ⟨0, zero_mem_cyclicSubsetSumResiduesList m s⟩

theorem cyclicSubsetSumResiduesList_mono_append (m : ℕ) (s t : List ℕ) :
    cyclicSubsetSumResiduesList m s ⊆ cyclicSubsetSumResiduesList m (s ++ t) := by
  induction t generalizing s with
  | nil => simp
  | cons a t ih =>
      rw [List.append_cons]
      have hstep : cyclicSubsetSumResiduesList m s ⊆
          cyclicSubsetSumResiduesList m (s ++ [a]) := by
        rw [cyclicSubsetSumResiduesList_append_singleton]
        exact Finset.subset_union_left
      exact hstep.trans (ih (s ++ [a]))

private theorem union_translate_card (m : ℕ) (D : Finset (ZMod m)) (a : ZMod m) :
    (D ∪ translate D a).card = D.card + expansion D a := by
  let E := translate D a \ D
  have hdecomp : D ∪ translate D a = D ∪ E := by
    ext z
    by_cases hz : z ∈ D <;> simp [E, hz]
  have hdisj : Disjoint D E := by
    exact Finset.sdiff_disjoint.symm
  rw [hdecomp, Finset.card_union_of_disjoint hdisj]
  rfl

/-- Exposing one more sample grows the state by exactly its translation
expansion. -/
theorem card_cyclicResidueStep (m : ℕ) (D : Finset (ZMod m)) (a : ℕ) :
    (cyclicResidueStep m D a).card = D.card + expansion D (a : ZMod m) := by
  exact union_translate_card m D (a : ZMod m)

theorem card_cyclicSubsetSumResiduesList_append_singleton
    (m : ℕ) (s : List ℕ) (a : ℕ) :
    (cyclicSubsetSumResiduesList m (s ++ [a])).card =
      (cyclicSubsetSumResiduesList m s).card +
        expansion (cyclicSubsetSumResiduesList m s) (a : ZMod m) := by
  rw [cyclicSubsetSumResiduesList_append_singleton, card_cyclicResidueStep]

/-! ## Comparison with value-indexed subset sums -/

/-- Adjoining a fresh natural number updates represented residues by union
with its translate. -/
theorem subsetSumResidues_insert_step {m a : ℕ} {B : Finset ℕ} (ha : a ∉ B) :
    subsetSumResidues m (insert a B) =
      cyclicResidueStep m (subsetSumResidues m B) a := by
  unfold cyclicResidueStep
  simp only [subsetSumResidues]
  rw [subsetSumValues_insert ha, Finset.image_union]
  unfold translate
  ext z
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · rcases hz with ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      exact Or.inr ⟨(n : ZMod m), ⟨n, hn, rfl⟩, by simp⟩
  · rintro (hz | hz)
    · exact Or.inl hz
    · rcases hz with ⟨r, ⟨n, hn, rfl⟩, rfl⟩
      exact Or.inr ⟨n + a, ⟨n, hn, rfl⟩, by simp⟩

/-- For a duplicate-free ordered sample, the fold state is exactly the
residue set of the ordinary finset of sample values. -/
theorem cyclicSubsetSumResiduesList_eq_subsetSumResidues (m : ℕ)
    (s : List ℕ) (hs : s.Nodup) :
    cyclicSubsetSumResiduesList m s = subsetSumResidues m s.toFinset := by
  induction s using List.reverseRecOn with
  | nil =>
      ext z
      simp [cyclicSubsetSumResiduesList, subsetSumResidues,
        subsetSumValues_empty]
  | append_singleton s a ih =>
      have hs' : s.Nodup := hs.of_append_left
      have ha : a ∉ s.toFinset := by
        have hdisj := (List.nodup_append.mp hs).2.2
        intro ha
        exact hdisj a (by simpa using ha) a (by simp) rfl
      rw [cyclicSubsetSumResiduesList_append_singleton, ih hs']
      have htf : (s ++ [a]).toFinset = insert a s.toFinset := by simp
      rw [htf]
      exact (subsetSumResidues_insert_step ha).symm

/-- Downstream bridge used by the robust block: an injective tuple has the
same cyclic fold state as the finite set of its values. -/
theorem cyclicSubsetSumResidues_eq_subsetSumResidues_image {m q : ℕ}
    (s : Fin q → ℕ) (hs : Function.Injective s) :
    cyclicSubsetSumResidues m s =
      subsetSumResidues m (Finset.univ.image s) := by
  rw [cyclicSubsetSumResidues, Fin.univ_image_def]
  exact cyclicSubsetSumResiduesList_eq_subsetSumResidues m (List.ofFn s)
    (List.nodup_ofFn.mpr hs)

/-! ## Bad tuples -/

/-- The integral sample length used in the two-colour specialization. -/
noncomputable def cyclicSampleLength (x : ℕ) : ℕ :=
  Nat.ceil (6 * Real.log (x : ℝ))

/-- Ordered samples from the rough set at scale `x`. -/
abbrev CyclicSample (x q : ℕ) := Fin q → ↑(roughNumbers x)

/-- Samples whose cyclic subset sums occupy fewer than `x / 4` residues.

The comparison is written as `4 * card < x`, avoiding any convention about
rounding `x / 4`.
-/
def badCyclicTuples (x m q : ℕ) : Finset (CyclicSample x q) :=
  Finset.univ.filter fun s ↦
    4 * (cyclicSubsetSumResidues m (fun i ↦ (s i : ℕ))).card < x

@[simp] theorem mem_badCyclicTuples {x m q : ℕ} {s : CyclicSample x q} :
    s ∈ badCyclicTuples x m q ↔
      4 * (cyclicSubsetSumResidues m (fun i ↦ (s i : ℕ))).card < x := by
  simp [badCyclicTuples]

theorem card_all_cyclicSamples (x q : ℕ) :
    Fintype.card (CyclicSample x q) = (roughNumbers x).card ^ q := by
  simp [CyclicSample]

theorem badCyclicTuples_card_le_all (x m q : ℕ) :
    (badCyclicTuples x m q).card ≤ (roughNumbers x).card ^ q := by
  rw [← card_all_cyclicSamples x q]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-! ## Uniform bounds for one bad extension -/

/-- If an almost-period threshold is at most half the set, the elementary
double-counting lemma bounds the number of almost periods by twice the size
of the set. -/
theorem card_almostPeriods_le_two_mul_card {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (D : Finset G) {d : ℕ}
    (hD : D.Nonempty) (hd : 2 * d ≤ D.card) :
    (almostPeriods D d).card ≤ 2 * D.card := by
  have hhalf : D.card ≤ 2 * (D.card - d) := by omega
  have hmul : (almostPeriods D d).card * D.card ≤
      (2 * D.card) * D.card := by
    calc
      (almostPeriods D d).card * D.card ≤
          (almostPeriods D d).card * (2 * (D.card - d)) :=
        Nat.mul_le_mul_left _ hhalf
      _ = 2 * ((almostPeriods D d).card * (D.card - d)) := by ring
      _ ≤ 2 * (D.card * D.card) :=
        Nat.mul_le_mul_left 2 (card_almostPeriods_mul_sub_le_square D d)
      _ = (2 * D.card) * D.card := by ring
  exact le_of_mul_le_mul_right hmul hD.card_pos

/-- Sums of `k` `d`-almost periods are `k*d`-almost periods.  This is the
pointwise-finset form of CFP Lemma 2.7. -/
theorem nsmul_almostPeriods_subset (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (D : Finset G) (d : ℕ) :
    ∀ k : ℕ, k • almostPeriods D d ⊆ almostPeriods D (k * d) := by
  intro k
  induction k with
  | zero =>
      intro z hz
      change z ∈ ({0} : Finset G) at hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      simp [expansion]
  | succ k ih =>
      rw [succ_nsmul]
      intro z hz
      rcases Finset.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
      apply mem_almostPeriods.mpr
      calc
        expansion D (x + y) ≤ expansion D x + expansion D y :=
          expansion_add_le D x y
        _ ≤ k * d + d := by
          gcongr
          · exact mem_almostPeriods.mp (ih hx)
          · exact mem_almostPeriods.mp hy
        _ = (k + 1) * d := by simp [Nat.add_mul]

/-- A cardinal upper bound for `k`-fold sums of almost periods, as long as
the accumulated expansion is at most half of `D`. -/
theorem card_nsmul_almostPeriods_le_two_mul_card {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (D : Finset G) (hD : D.Nonempty) (d k : ℕ)
    (hkd : 2 * (k * d) ≤ D.card) :
    (k • almostPeriods D d).card ≤ 2 * D.card := by
  exact (Finset.card_le_card (nsmul_almostPeriods_subset G D d k)).trans
    (card_almostPeriods_le_two_mul_card D hD hkd)

/-- A finset formulation of the fact that every proper subgroup coset has
at most `B` elements.  It matches the subgroup representation used by the
proved COS module. -/
def ProperCosetCardBound (m B : ℕ) : Prop :=
  ∀ (H : Finset (ZMod m)), H.Nonempty →
    (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) →
    (∀ x ∈ H, -x ∈ H) →
    H.card < m → H.card ≤ B

/-- The subgroup-order bound for `ZMod m` implies the custom finset form
used by `NotContainedInProperCoset`. -/
theorem properCosetCardBound_zmod_div {x m R : ℕ}
    (hm : 1 < m) (hmx : m < 2 * x) (hR : R ≤ m.minFac) (hR0 : 0 < R) :
    ProperCosetCardBound m (2 * x / R) := by
  let _ : NeZero m := ⟨by omega⟩
  intro H hH hHadd hHneg hHlt
  let K : AddSubgroup (ZMod m) :=
    { carrier := (H : Set (ZMod m))
      zero_mem' := by
        obtain ⟨a, ha⟩ := hH
        simpa using hHadd a ha (-a) (hHneg a ha)
      add_mem' := by
        intro a b ha hb
        exact hHadd a ha b hb
      neg_mem' := by
        intro a ha
        exact hHneg a ha }
  have hKcard : Nat.card K = H.card := by
    change Nat.card ↑(H : Set (ZMod m)) = H.card
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hKne : K ≠ ⊤ := by
    intro htop
    have hHuniv : H = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro a
      have haK : a ∈ K := by rw [htop]; simp
      exact haK
    subst H
    simpa using hHlt
  apply (Nat.le_div_iff_mul_le hR0).mpr
  rw [← hKcard]
  simpa [mul_comm] using
    (zmod_proper_addSubgroup_scale_card_le m R hm hR K hKne).trans
      (Nat.le_of_lt hmx)

theorem notContainedInProperCoset_of_card_gt
    {m B : ℕ} [NeZero m] {S : Finset (ZMod m)}
    (hproper : ProperCosetCardBound m B) (hS : B < S.card) :
    NotContainedInProperCoset S := by
  intro H hH hHadd hHneg hHuniv a hsub
  have hHlt : H.card < m := by
    have hss : H ⊂ (Finset.univ : Finset (ZMod m)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ H, hHuniv⟩
    have hlt : H.card < (Finset.univ : Finset (ZMod m)).card :=
      Finset.card_lt_card hss
    simpa using hlt
  have hcard : S.card ≤ H.card := by
    calc
      S.card ≤ (a +ᵥ H).card := Finset.card_le_card hsub
      _ = H.card := by simpa only using Finset.card_vadd_finset a H
  exact (not_le_of_gt hS) (hcard.trans (hproper H hH hHadd hHneg hHlt))

/-- Reduction modulo `m` maps at most `|H|` members of a subset of
`[x,2x)` into `H`. -/
theorem card_subtype_filter_natCast_mem_le {x m : ℕ} (X : Finset ℕ)
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (H : Finset (ZMod m)) :
    ((Finset.univ : Finset ↑X).filter
      (fun a : ↑X ↦ ((a : ℕ) : ZMod m) ∈ H)).card ≤ H.card := by
  let f : ↑X → ZMod m := fun a ↦ ((a : ℕ) : ZMod m)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact natCast_zmod_injOn_Ico (hx.trans_le hxm) hxm
      (hXIco a.property) (hXIco b.property) hab
  let T : Finset ↑X := (Finset.univ : Finset ↑X).filter
    (fun a : ↑X ↦ ((a : ℕ) : ZMod m) ∈ H)
  have himage : T.image f ⊆ H := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  change T.card ≤ H.card
  calc
    T.card = (T.image f).card := (Finset.card_image_of_injective T hf).symm
    _ ≤ H.card := Finset.card_le_card himage

/-- In the small range of CFP's growth argument, at most `2*x/R`
extensions have expansion at most half of the current state. -/
theorem small_bad_extension_card_le {x m u R : ℕ} (X : Finset ℕ)
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (hR : 0 < R) (hRu : R ≤ u) (D : Finset (ZMod m)) (hD : D.Nonempty)
    (hsmall : u * D.card ≤ x) :
    ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
      2 * expansion D ((a : ℕ) : ZMod m) ≤ D.card).card ≤
      2 * x / R := by
  let _ : NeZero m := ⟨(hx.trans_le hxm).ne'⟩
  have hfilter :
      ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
        2 * expansion D ((a : ℕ) : ZMod m) ≤ D.card) ⊆
      (Finset.univ : Finset ↑X).filter fun a : ↑X ↦
        ((a : ℕ) : ZMod m) ∈ almostPeriods D (D.card / 2) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨by simp, mem_almostPeriods.mpr ?_⟩
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [mul_comm] using ha.2)
  have hhalf : 2 * (D.card / 2) ≤ D.card := by omega
  have hraw := (Finset.card_le_card hfilter).trans
    (card_subtype_filter_natCast_mem_le X hx hxm hXIco
      (almostPeriods D (D.card / 2)))
  have hG := hraw.trans (card_almostPeriods_le_two_mul_card D hD hhalf)
  apply (Nat.le_div_iff_mul_le hR).mpr
  have hmul : R * ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
      2 * expansion D ((a : ℕ) : ZMod m) ≤ D.card).card
      ≤ 2 * x := by
    calc
      R * ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
        2 * expansion D ((a : ℕ) : ZMod m) ≤ D.card).card
          ≤ R * (2 * D.card) := Nat.mul_le_mul_left R hG
      _ ≤ 2 * (u * D.card) := by
        calc
          R * (2 * D.card) = (2 * R) * D.card := by ring
          _ ≤ (2 * u) * D.card :=
            Nat.mul_le_mul_right D.card (Nat.mul_le_mul_left 2 hRu)
          _ = 2 * (u * D.card) := by ring
      _ ≤ 2 * x := Nat.mul_le_mul_left 2 hsmall
  simpa [mul_comm] using hmul

/-- In the medium range, the almost-period/COS argument gives the same
uniform bad-extension bound. -/
theorem medium_bad_extension_card_le {x m R : ℕ} (X : Finset ℕ)
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (hR : 2 ≤ R) (hproper : ProperCosetCardBound m (2 * x / R))
    (D : Finset (ZMod m)) (hD : D.Nonempty) (hmedium : 4 * D.card < x) :
    ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
      R * expansion D ((a : ℕ) : ZMod m) ≤ D.card).card ≤
      2 * x / R := by
  let _ : NeZero m := ⟨(hx.trans_le hxm).ne'⟩
  let d := D.card / R
  let k := R / 2
  let H := almostPeriods D d
  have hfilter :
      ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
        R * expansion D ((a : ℕ) : ZMod m) ≤ D.card) ⊆
      (Finset.univ : Finset ↑X).filter fun a : ↑X ↦
      ((a : ℕ) : ZMod m) ∈ H := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨by simp, mem_almostPeriods.mpr ?_⟩
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [mul_comm] using ha.2)
  have hraw := (Finset.card_le_card hfilter).trans
    (card_subtype_filter_natCast_mem_le X hx hxm hXIco H)
  suffices hHcard : H.card ≤ 2 * x / R by exact hraw.trans hHcard
  by_contra hnot
  have hHgt : 2 * x / R < H.card := Nat.lt_of_not_ge hnot
  have haper : NotContainedInProperCoset H :=
    notContainedInProperCoset_of_card_gt hproper hHgt
  have hk : 1 ≤ k := by simp only [k]; omega
  have htwok : 2 * k ≤ R := by
    simp only [k]
    exact Nat.mul_div_le R 2
  have hRd : R * d ≤ D.card := by
    simp only [d]
    exact Nat.mul_div_le D.card R
  have hkd : 2 * (k * d) ≤ D.card := by
    calc
      2 * (k * d) = (2 * k) * d := by ring
      _ ≤ R * d := Nat.mul_le_mul_right d htwok
      _ ≤ D.card := hRd
  have hsumcard : (k • H).card ≤ 2 * D.card :=
    card_nsmul_almostPeriods_le_two_mul_card D hD d k hkd
  have hcos := min_two_card_le_two_card_nsmul H
    ⟨0, zero_mem_almostPeriods D d⟩ haper k hk
  have hsecond : (k + 1) * H.card ≤ 2 * (k • H).card := by
    by_cases hle : 2 * Fintype.card (ZMod m) ≤ (k + 1) * H.card
    · rw [min_eq_left hle] at hcos
      have hmcard : Fintype.card (ZMod m) = m := ZMod.card m
      rw [hmcard] at hcos
      have htwosum : 2 * (k • H).card ≤ 4 * D.card := by
        have htwosum' := Nat.mul_le_mul_left 2 hsumcard
        omega
      have : 2 * m ≤ 4 * D.card := hcos.trans htwosum
      omega
    · rw [min_eq_right (Nat.le_of_not_ge hle)] at hcos
      exact hcos
  have hkg_lt_x : (k + 1) * H.card < x := by
    have htwo : 2 * (k • H).card < x := by
      exact (Nat.mul_le_mul_left 2 hsumcard).trans_lt (by omega)
    exact hsecond.trans_lt htwo
  have hRle : R ≤ 2 * (k + 1) := by
    have hmod : R % 2 < 2 := Nat.mod_lt R (by omega)
    have heq := (Nat.mod_add_div R 2).symm
    simp only [k]
    omega
  have hRH : R * H.card ≤ 2 * x := by
    calc
      R * H.card ≤ (2 * (k + 1)) * H.card := Nat.mul_le_mul_right H.card hRle
      _ = 2 * ((k + 1) * H.card) := by ring
      _ ≤ 2 * x := Nat.mul_le_mul_left 2 (Nat.le_of_lt hkg_lt_x)
  exact hnot ((Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [mul_comm] using hRH))

/-! ## Bad stages -/

/-- CFP's two bad-growth alternatives, stated through the exact expansion
of the prefix state.  The small alternative allows growth by at most `3/2`;
the medium alternative allows growth by at most `1 + 1/R`. -/
def cyclicStepBad (x u R m : ℕ) (hist : List ℕ) (a : ℕ) : Prop :=
  let D := cyclicSubsetSumResiduesList m hist
  (u * D.card ≤ x ∧ 2 * expansion D (a : ZMod m) ≤ D.card) ∨
    (x < u * D.card ∧ 4 * D.card < x ∧
      R * expansion D (a : ZMod m) ≤ D.card)

instance cyclicStepBad_decidable (x u R m : ℕ) (hist : List ℕ) (a : ℕ) :
    Decidable (cyclicStepBad x u R m hist a) := by
  unfold cyclicStepBad
  infer_instance

/-- The bad-stage predicate lifted to the subtype sampling alphabet. -/
def cyclicSubtypeStepBad (X : Finset ℕ) (x u R m : ℕ)
    (hist : List ↑X) (a : ↑X) : Prop :=
  cyclicStepBad x u R m (hist.map ((↑) : ↑X → ℕ)) (a : ℕ)

instance cyclicSubtypeStepBad_decidable (X : Finset ℕ) (x u R m : ℕ)
    (hist : List ↑X) : DecidablePred (cyclicSubtypeStepBad X x u R m hist) :=
  fun _ ↦ cyclicStepBad_decidable _ _ _ _ _ _

/-- Uniform conditional count: whatever the exposed prefix is, at most
`2*x/R` members of the sampling alphabet make the next stage bad.  This is
Claim 1 in CFP Lemma 3.1, with the source's real parameter `δ` replaced by
the exact reciprocal integer parameter `R`. -/
theorem cyclicStepBad_card_le {x m u R : ℕ} (X : Finset ℕ)
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (hR : 2 ≤ R) (hRu : R ≤ u)
    (hproper : ProperCosetCardBound m (2 * x / R)) (hist : List ↑X) :
    ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
      cyclicStepBad x u R m (hist.map ((↑) : ↑X → ℕ)) (a : ℕ)).card ≤
      2 * x / R := by
  let _ : NeZero m := ⟨(hx.trans_le hxm).ne'⟩
  let D := cyclicSubsetSumResiduesList m (hist.map ((↑) : ↑X → ℕ))
  have hD : D.Nonempty := cyclicSubsetSumResiduesList_nonempty _ _
  by_cases hsmall : u * D.card ≤ x
  · have hnotmedium : ¬x < u * D.card := not_lt_of_ge hsmall
    simpa only [cyclicStepBad, D, hsmall, true_and, hnotmedium, false_and,
      or_false] using
      small_bad_extension_card_le X hx hxm hXIco (by omega) hRu D hD hsmall
  · have hlarge : x < u * D.card := Nat.lt_of_not_ge hsmall
    by_cases hmedium : 4 * D.card < x
    · simpa only [cyclicStepBad, D, hsmall, false_and, hlarge, true_and,
        hmedium, false_or] using
        medium_bad_extension_card_le X hx hxm hXIco hR hproper D hD hmedium
    · have hnotmedium : ¬4 * D.card < x := hmedium
      simp only [cyclicStepBad, D, hsmall, false_and, hlarge, true_and,
        hnotmedium, false_or]
      simp

/-- Finite chain rule for any prescribed lower bound `b` on the number of
bad cyclic stages.  The event at stage `i` may depend on the entire exposed
prefix; `Probability.all_prefixStageEvents_card_le` is precisely the
adaptive counting lemma needed here. -/
theorem cyclic_many_bad_stages_card_le {x m u R q b : ℕ} (X : Finset ℕ)
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (hR : 2 ≤ R) (hRu : R ≤ u)
    (hproper : ProperCosetCardBound m (2 * x / R)) :
    ((Finset.univ : Finset (Fin q → ↑X)).filter fun s ↦
      b ≤ ((Finset.univ : Finset (Fin q)).filter fun i ↦
        FiniteProbability.prefixStageEvent
          (cyclicSubtypeStepBad X x u R m) i s).card).card ≤
      Nat.choose q b * ((2 * x / R) ^ b * X.card ^ (q - b)) := by
  have hstep : ∀ hist : List ↑X,
      ((Finset.univ : Finset ↑X).filter fun a : ↑X ↦
        cyclicSubtypeStepBad X x u R m hist a).card ≤ 2 * x / R := by
    intro hist
    exact cyclicStepBad_card_le X hx hxm hXIco hR hRu hproper hist
  simpa using
    (FiniteProbability.card_atLeast_prefixStageBad_le
      (X := ↑X) (cyclicSubtypeStepBad X x u R m) q b (2 * x / R) hstep)

/-! ## From failed growth to many bad stages -/

/-- Cardinality of the cyclic state after the first `i` coordinates of a
tuple.  For `i ≥ q` the `take` operation makes the sequence constant. -/
def cyclicPrefixCard {q : ℕ} (m : ℕ) (s : Fin q → ℕ) (i : ℕ) : ℕ :=
  (cyclicSubsetSumResiduesList m (List.ofFn s |>.take i)).card

@[simp] theorem cyclicPrefixCard_zero {q m : ℕ} (s : Fin q → ℕ) :
    cyclicPrefixCard m s 0 = 1 := by
  simp [cyclicPrefixCard]

theorem cyclicPrefixCard_monotone {q m : ℕ} (s : Fin q → ℕ) :
    Monotone (cyclicPrefixCard m s) := by
  intro i j hij
  let l := List.ofFn s
  have htake : l.take i = (l.take j).take i := by
    rw [List.take_take]
    simp [Nat.min_eq_left hij]
  rw [cyclicPrefixCard, cyclicPrefixCard, htake]
  apply Finset.card_le_card
  have happ := cyclicSubsetSumResiduesList_mono_append m
    ((l.take j).take i) ((l.take j).drop i)
  simpa using happ

theorem cyclicPrefixCard_succ {q m : ℕ} (s : Fin q → ℕ)
    (i : ℕ) (hi : i < q) :
    cyclicPrefixCard m s (i + 1) = cyclicPrefixCard m s i +
      expansion (cyclicSubsetSumResiduesList m ((List.ofFn s).take i))
        (s ⟨i, hi⟩ : ZMod m) := by
  have hlen : i < (List.ofFn s).length := by simpa using hi
  rw [cyclicPrefixCard, cyclicPrefixCard,
    List.take_succ_eq_append_getElem hlen,
    card_cyclicSubsetSumResiduesList_append_singleton]
  simp

theorem cyclic_step_bad_iff_arithmetic {X : Finset ℕ} {q x u R m : ℕ}
    (s : Fin q → ↑X) (i : Fin q) :
    FiniteProbability.prefixStageEvent
        (cyclicSubtypeStepBad X x u R m) i s ↔
      ((u * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) i.val ≤ x ∧
          2 * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) (i.val + 1) ≤
            3 * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) i.val) ∨
        (x < u * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) i.val ∧
          4 * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) i.val < x ∧
          R * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) (i.val + 1) ≤
            (R + 1) * cyclicPrefixCard m (fun j ↦ (s j : ℕ)) i.val)) := by
  let natSample : Fin q → ℕ := fun j ↦ (s j : ℕ)
  let D := cyclicSubsetSumResiduesList m ((List.ofFn natSample).take i.val)
  let e := expansion D (natSample i : ZMod m)
  have hmap : ((List.ofFn s).take i.val).map ((↑) : ↑X → ℕ) =
      (List.ofFn natSample).take i.val := by
    simp [natSample, List.map_take, Function.comp_def]
  have hstate : cyclicPrefixCard m natSample i.val = D.card := by
    rfl
  have hnext : cyclicPrefixCard m natSample (i.val + 1) = D.card + e := by
    rw [cyclicPrefixCard_succ natSample i.val i.isLt, hstate]
  have hsmallSlow :
      2 * e ≤ D.card ↔ 2 * cyclicPrefixCard m natSample (i.val + 1) ≤
        3 * cyclicPrefixCard m natSample i.val := by
    rw [hstate, hnext]
    omega
  have hlargeSlow :
      R * e ≤ D.card ↔ R * cyclicPrefixCard m natSample (i.val + 1) ≤
        (R + 1) * cyclicPrefixCard m natSample i.val := by
    rw [hstate, hnext, Nat.mul_add, Nat.add_mul, one_mul]
    constructor
    · exact fun h ↦ Nat.add_le_add_left h _
    · exact Nat.le_of_add_le_add_left
  simp only [FiniteProbability.prefixStageEvent, cyclicSubtypeStepBad,
    cyclicStepBad, hmap]
  change
    ((u * D.card ≤ x ∧ 2 * e ≤ D.card) ∨
      (x < u * D.card ∧ 4 * D.card < x ∧ R * e ≤ D.card)) ↔
    ((u * cyclicPrefixCard m natSample i.val ≤ x ∧
        2 * cyclicPrefixCard m natSample (i.val + 1) ≤
          3 * cyclicPrefixCard m natSample i.val) ∨
      (x < u * cyclicPrefixCard m natSample i.val ∧
        4 * cyclicPrefixCard m natSample i.val < x ∧
        R * cyclicPrefixCard m natSample (i.val + 1) ≤
          (R + 1) * cyclicPrefixCard m natSample i.val))
  rw [hstate, hsmallSlow, hlargeSlow, hstate]

theorem cyclic_bad_stage_card_eq {X : Finset ℕ} {q x u R m : ℕ}
    (s : Fin q → ↑X) :
    ((Finset.univ : Finset (Fin q)).filter fun i ↦
      FiniteProbability.prefixStageEvent
        (cyclicSubtypeStepBad X x u R m) i s).card =
      (cyclicBadStages (cyclicPrefixCard m (fun j ↦ (s j : ℕ)))
        x u R q).card := by
  apply Finset.card_bij (fun i _ ↦ i.val)
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [cyclicBadStages, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    exact (cyclic_step_bad_iff_arithmetic s i).mp hi.2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    let i : Fin q := ⟨n, Finset.mem_range.mp hn'.1⟩
    refine ⟨i, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    exact (cyclic_step_bad_iff_arithmetic s i).mpr hn'.2

/-- A failed final cyclic state forces at least `u` adaptive bad stages. -/
theorem cyclic_failure_has_many_bad_stages {X : Finset ℕ}
    {q x u R v m : ℕ} (s : Fin q → ↑X)
    (hu : 0 < u) (hR : 2 ≤ R) (hRu : R ≤ u)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hq : 5 * u ≤ q)
    (hfail : 4 * (cyclicSubsetSumResidues m (fun j ↦ (s j : ℕ))).card < x) :
    u ≤ ((Finset.univ : Finset (Fin q)).filter fun i ↦
      FiniteProbability.prefixStageEvent
        (cyclicSubtypeStepBad X x u R m) i s).card := by
  let a := cyclicPrefixCard m (fun j ↦ (s j : ℕ))
  have ha0 : 0 < a 0 := by simp [a]
  have ha : Monotone a := cyclicPrefixCard_monotone _
  have hfinal : 4 * a q < x := by
    change 4 * (cyclicSubsetSumResiduesList m
      ((List.ofFn fun j ↦ (s j : ℕ)).take q)).card < x
    rw [List.take_of_length_le (by simp)]
    exact hfail
  rw [cyclic_bad_stage_card_eq]
  exact cyclicBadStages_card_ge hu hR hRu ha0 ha hxpow huPow hRv hfinal hq

/-- CFP Lemma 3.1 in a completely finite, division-free parameter form.
The following numeric/asymptotic specialization chooses `u = ceil(log x)`,
`q = ceil(6 log x)`, `v = log₂ u + 1`, and `R = u/(8v)`. -/
theorem cyclic_failure_card_le {X : Finset ℕ} {q x u R v m : ℕ}
    (hx : 0 < x) (hxm : x ≤ m) (hXIco : X ⊆ Finset.Ico x (2 * x))
    (hu : 0 < u) (hR : 2 ≤ R) (hRu : R ≤ u)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hq : 5 * u ≤ q) (hproper : ProperCosetCardBound m (2 * x / R)) :
    ((Finset.univ : Finset (Fin q → ↑X)).filter fun s ↦
      4 * (cyclicSubsetSumResidues m (fun j ↦ (s j : ℕ))).card < x).card ≤
      Nat.choose q u * ((2 * x / R) ^ u * X.card ^ (q - u)) := by
  have hsubset :
      ((Finset.univ : Finset (Fin q → ↑X)).filter fun s ↦
        4 * (cyclicSubsetSumResidues m (fun j ↦ (s j : ℕ))).card < x) ⊆
      (Finset.univ : Finset (Fin q → ↑X)).filter fun s ↦
        u ≤ ((Finset.univ : Finset (Fin q)).filter fun i ↦
          FiniteProbability.prefixStageEvent
            (cyclicSubtypeStepBad X x u R m) i s).card := by
    intro s hs
    rw [Finset.mem_filter] at hs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ s,
      cyclic_failure_has_many_bad_stages s hu hR hRu hxpow huPow hRv hq hs.2⟩
  exact (Finset.card_le_card hsubset).trans
    (cyclic_many_bad_stages_card_le X hx hxm hXIco hR hRu hproper)

/-- The finite cyclic estimate specialized to the rough sampling set.  All
remaining assumptions are explicit inequalities on the rounded analytic
parameters. -/
theorem rough_cyclic_failure_card_le {q x u R v m : ℕ}
    (hx : 2 ≤ x) (hm : m ∈ roughNumbers x)
    (hu : 0 < u) (hR : 2 ≤ R) (hRu : R ≤ u)
    (hRcut : R ≤ roughCutoff x)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hq : 5 * u ≤ q) :
    (badCyclicTuples x m q).card ≤
      Nat.choose q u *
        ((2 * x / R) ^ u * (roughNumbers x).card ^ (q - u)) := by
  have hmAt : m ∈ roughNumbersAt x (roughCutoff x) := by
    simpa [roughNumbers] using hm
  have hmData := mem_roughNumbersAt.mp hmAt
  have hm1 : 1 < m := by omega
  have hRmin : R ≤ m.minFac :=
    hRcut.trans (Nat.le_of_lt (cutoff_lt_minFac_of_mem_roughNumbersAt hmAt hm1))
  have hproper : ProperCosetCardBound m (2 * x / R) :=
    properCosetCardBound_zmod_div hm1 hmData.2.1 hRmin (by omega)
  have hXIco : roughNumbers x ⊆ Finset.Ico x (2 * x) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨(mem_roughNumbers.mp hn).1,
      (mem_roughNumbers.mp hn).2.1⟩
  simpa [badCyclicTuples] using
    (cyclic_failure_card_le (X := roughNumbers x)
      (x := x) (m := m) (q := q) (u := u) (R := R) (v := v)
      (by omega) hmData.1 hXIco hu hR hRu hxpow huPow hRv hq hproper)

/-- The rough cyclic estimate in the superpolynomially small form used by
the robust-block union bound.  The explicit hypotheses are precisely the
integer inequalities satisfied by the rounded choices in CFP Lemma 3.1. -/
theorem rough_cyclic_failure_scaled_card_le {q x u R v m : ℕ}
    (hx : 2 ≤ x) (hm : m ∈ roughNumbers x)
    (hu : 0 < u) (hv : 0 < v) (hR : 2 ≤ R) (hRu : R ≤ u)
    (hRcut : R ≤ roughCutoff x)
    (hxpow : x ≤ 3 ^ u) (huPow : u ≤ 2 ^ v) (hRv : R * v ≤ u)
    (hqLower : 5 * u ≤ q) (hqUpper : q ≤ 6 * u)
    (huR : u ≤ 16 * v * R)
    (hxM : x ≤ 16 * v * (roughNumbers x).card)
    (hpow : 2 ^ 30 * v ^ 4 ≤ u) :
    u ^ (u / 2) * (badCyclicTuples x m q).card ≤
      (roughNumbers x).card ^ q := by
  apply cyclicGrowth_raw_count_scale
      ((badCyclicTuples x m q).card) ((roughNumbers x).card)
      (2 * x / R) q u v R x hu hv (by omega)
  · omega
  · exact hqUpper
  · exact rough_cyclic_failure_card_le hx hm hu hR hRu hRcut hxpow huPow hRv
      hqLower
  · exact Nat.div_mul_le_self (2 * x) R
  · exact huR
  · exact hxM
  · exact hpow

/-- CFP Lemma 3.1 at its rounded parameters.  Uniformly for every rough
modulus `m`, the proportion of samples whose modular subset-sum set has size
less than `x/4` is at most
`cyclicLogScale x ^ (-(cyclicLogScale x / 2))` in division-free form. -/
theorem eventually_rough_cyclic_failure_scaled_card_le :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ m ∈ roughNumbers x,
      cyclicLogScale x ^ (cyclicLogScale x / 2) *
          (badCyclicTuples x m (cyclicSampleLength x)).card ≤
        (roughNumbers x).card ^ cyclicSampleLength x := by
  filter_upwards [eventually_cyclicGrowthParameterBounds] with x h
  intro m hm
  simpa only [cyclicSampleLength, cyclicTupleLength] using
    (rough_cyclic_failure_scaled_card_le
      (q := cyclicTupleLength x) (x := x)
      (u := cyclicLogScale x) (R := cyclicReciprocalScale x)
      (v := cyclicSecondaryScale x) (m := m)
      h.two_le_x hm h.logScale_pos h.secondaryScale_pos
      h.reciprocalScale_two_le h.reciprocalScale_le_logScale
      h.reciprocalScale_le_cutoff h.scale_le_three_pow
      h.scale_le_two_pow_secondary h.reciprocal_mul_secondary_le
      h.five_scale_le_tupleLength h.tupleLength_le_six_scale
      h.scale_le_sixteen_mul h.rough_card_lower h.secondary_fourth_le)

end

end Erdos54
