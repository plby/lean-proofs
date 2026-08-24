import ErdosProblems.Erdos360.OrdinaryGrowth

/-!
# The Lev interval and final completion step for Erdős 360

This file isolates the part of the Conlon--Fox--Pham lower-bound argument
after their Lemma 2.2 (Lev) has produced an ordinary interval of subset
sums.  The endpoint hypotheses below are deliberately division-free and
match the two estimates called (R8) and (R9) in the accompanying writeup.
-/

open scoped BigOperators Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-! ## A finite-list interface for the missing many-summand Lev theorem -/

/-- The union of a finite list of disjoint pools. -/
def levFamilyUnion : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | A :: parts => A ∪ levFamilyUnion parts

/-- The Minkowski sum of the subset-sum sets of a finite list of pools.
The empty list contributes the neutral singleton `{0}`. -/
def levIteratedSubsetSum : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | A :: parts => A.subsetSum + levIteratedSubsetSum parts

/-- Subset sums selected from two disjoint pools may be combined without
losing distinctness. -/
lemma add_subsetSum_subset_subsetSum_union
    {A B : Finset ℕ} (hAB : Disjoint A B) :
    A.subsetSum + B.subsetSum ⊆ (A ∪ B).subsetSum := by
  intro x hx
  rw [Finset.mem_add] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  obtain ⟨U, hUA, hUsum⟩ := Finset.mem_subsetSum_iff.mp hu
  obtain ⟨V, hVB, hVsum⟩ := Finset.mem_subsetSum_iff.mp hv
  rw [Finset.mem_subsetSum_iff]
  refine ⟨U ∪ V, Finset.union_subset_union hUA hVB, ?_⟩
  have hUV : Disjoint U V := hAB.mono hUA hVB
  rw [Finset.sum_union hUV, hUsum, hVsum]

lemma disjoint_levFamilyUnion_of_pairwise
    {A : Finset ℕ} {parts : List (Finset ℕ)}
    (hpair : (A :: parts).Pairwise (fun P Q ↦ Disjoint P Q)) :
    Disjoint A (levFamilyUnion parts) := by
  induction parts with
  | nil => simp [levFamilyUnion]
  | cons P parts ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hAP : Disjoint A P := hcons.1 P (by simp)
      have hApart : ∀ Q ∈ parts, Disjoint A Q := by
        intro Q hQ
        exact hcons.1 Q (by simp [hQ])
      have hpartsPair : parts.Pairwise (fun Q R ↦ Disjoint Q R) :=
        (List.pairwise_cons.mp hcons.2).2
      have hpair' : (A :: parts).Pairwise (fun Q R ↦ Disjoint Q R) :=
        List.pairwise_cons.mpr ⟨hApart, hpartsPair⟩
      rw [Finset.disjoint_left] at hAP ih ⊢
      intro x hxA hxunion
      simp only [levFamilyUnion, Finset.mem_union] at hxunion
      rcases hxunion with hxP | hxtail
      · exact hAP hxA hxP
      · exact ih hpair' hxA hxtail

/-- The iterated sumset of subset-sum sets embeds into the subset sums of
the disjoint union.  This is the exact bridge from Lev's conclusion to the
single pool used by the coloring argument. -/
lemma levIteratedSubsetSum_subset_union_subsetSum
    {parts : List (Finset ℕ)}
    (hpair : parts.Pairwise (fun P Q ↦ Disjoint P Q)) :
    levIteratedSubsetSum parts ⊆ (levFamilyUnion parts).subsetSum := by
  induction parts with
  | nil => simp [levIteratedSubsetSum, levFamilyUnion]
  | cons A parts ih =>
      have hcons := List.pairwise_cons.mp hpair
      have htail := hcons.2
      have hdisj := disjoint_levFamilyUnion_of_pairwise hpair
      intro x hx
      simp only [levIteratedSubsetSum] at hx
      rw [Finset.mem_add] at hx
      obtain ⟨u, hu, v, hv, rfl⟩ := hx
      have hv' : v ∈ (levFamilyUnion parts).subsetSum := ih htail hv
      exact add_subsetSum_subset_subsetSum_union hdisj
        (Finset.mem_add.mpr ⟨u, hu, v, hv', rfl⟩)

lemma levFamilyUnion_subset
    {parts : List (Finset ℕ)} {Z : Finset ℕ}
    (hparts : ∀ P ∈ parts, P ⊆ Z) : levFamilyUnion parts ⊆ Z := by
  intro z hz
  induction parts with
  | nil => simp [levFamilyUnion] at hz
  | cons A parts ih =>
      simp only [levFamilyUnion, Finset.mem_union] at hz
      rcases hz with hzA | hztail
      · exact hparts A (by simp) hzA
      · apply ih
        · intro P hP
          exact hparts P (by simp [hP])
        · exact hztail

/-- The hypotheses on the summands in the specialization of Lev's theorem
used by CFP: the pools are disjoint, and each ordinary subset-sum set has
the required size, diameter, and aperiodicity. -/
def IsCFPLevFamily (parts : List (Finset ℕ))
    (ℓ n₀ q : ℕ) : Prop :=
  parts.length = ℓ ∧
    parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
    ∀ P ∈ parts,
      n₀ ≤ P.subsetSum.card ∧
      P.subsetSum ⊆ Finset.Icc 0 q ∧
      ¬ ContainedInNontrivialAP P.subsetSum

/-- The conclusion of CFP Lemma 2.2 (Lev), specialized to subset-sum sets.
The rightmost inequality counts integer points, so it includes the essential
`+1` endpoint correction. -/
def HasCFPLevInterval (parts : List (Finset ℕ))
    (ℓ n₀ : ℕ) : Prop :=
  ∃ a b : ℕ,
    a ≤ b ∧
    Finset.Icc a b ⊆ levIteratedSubsetSum parts ∧
    ℓ * (n₀ - 1) + 1 ≤ b + 1 - a

/-- A uniform lower bound for the elements of a finite set gives the
corresponding lower bound for its sum. -/
lemma card_mul_le_sum_of_forall_le
    {A : Finset ℕ} {lo : ℕ} (hlo : ∀ a ∈ A, lo ≤ a) :
    A.card * lo ≤ ∑ a ∈ A, a := by
  calc
    A.card * lo = ∑ _a ∈ A, lo := by simp
    _ ≤ ∑ a ∈ A, a := by
      apply Finset.sum_le_sum
      intro a ha
      exact hlo a ha

/-- Every subset sum is at most the sum of the whole ambient finset. -/
lemma mem_subsetSum_le_sum {A : Finset ℕ} {s : ℕ}
    (hs : s ∈ A.subsetSum) : s ≤ ∑ a ∈ A, a := by
  obtain ⟨S, hSA, hsum⟩ := Finset.mem_subsetSum_iff.mp hs
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hSA (by simp)

/-- Pure post-Lev completion.  An interval already present among the
subset sums of `V` can be extended through every unused element of `Z`.
The two endpoint inequalities say precisely that the target lies in the
resulting interval. -/
theorem mem_subsetSum_of_lev_interval_and_unused
    {V Z : Finset ℕ} {a b target : ℕ}
    (hVZ : V ⊆ Z) (hab : a ≤ b)
    (hinterval : Finset.Icc a b ⊆ V.subsetSum)
    (hunused : ∀ t ∈ Z \ V, t ≤ b + 1 - a)
    (hleft : a ≤ target)
    (hright : target ≤ b + ∑ t ∈ Z \ V, t) :
    target ∈ Z.subsetSum := by
  have hdisj : Disjoint V (Z \ V) := Finset.disjoint_sdiff
  have hext := Icc_subset_subsetSum_union_of_le_length
    hab hdisj hinterval hunused
  have htarget : target ∈
      Finset.Icc a (b + ∑ t ∈ Z \ V, t) :=
    Finset.mem_Icc.mpr ⟨hleft, hright⟩
  have hunion : V ∪ (Z \ V) = Z := by
    exact Finset.union_sdiff_of_subset hVZ
  rw [hunion] at hext
  exact hext htarget

/-- Source-faithful numerical form of the final CFP completion.

`width ≤ b+1-a` is the conclusion that Lev's interval has more than
`width` integer points.  Every unused same-color term is at most `width`,
so CFP Lemma 2.1 extends the interval through all of them.  The upper
endpoint bound `b < target` is (R8), while
`target ≤ lo * (|Z|-|V|)` is the rounded form of (R9). -/
theorem mem_subsetSum_of_lev_interval_card_estimates
    {V Z : Finset ℕ} {a b target lo width : ℕ}
    (hVZ : V ⊆ Z) (hab : a ≤ b)
    (hinterval : Finset.Icc a b ⊆ V.subsetSum)
    (hlength : width ≤ b + 1 - a)
    (hupper : ∀ z ∈ Z, z ≤ width)
    (hlower : ∀ z ∈ Z, lo ≤ z)
    (hbtarget : b < target)
    (hmass : target ≤ lo * (Z.card - V.card)) :
    target ∈ Z.subsetSum := by
  apply mem_subsetSum_of_lev_interval_and_unused hVZ hab hinterval
  · intro t ht
    exact (hupper t (Finset.mem_sdiff.mp ht).1).trans hlength
  · exact (hab.trans hbtarget.le)
  · have hcard : (Z \ V).card = Z.card - V.card :=
      Finset.card_sdiff_of_subset hVZ
    have hsum : (Z \ V).card * lo ≤ ∑ t ∈ Z \ V, t := by
      apply card_mul_le_sum_of_forall_le
      intro t ht
      exact hlower t (Finset.mem_sdiff.mp ht).1
    calc
      target ≤ lo * (Z.card - V.card) := hmass
      _ = (Z \ V).card * lo := by rw [hcard, Nat.mul_comm]
      _ ≤ ∑ t ∈ Z \ V, t := hsum
      _ ≤ b + ∑ t ∈ Z \ V, t := Nat.le_add_left _ _

/-- Exact quotient-target interface consumed by
`forcesTarget_of_extracted_colorClass_completion`.  This theorem is the
last finite step after a common divisor `d` has been extracted. -/
theorem quotient_mem_subsetSum_of_lev_completion
    {n d : ℕ} {V Z : Finset ℕ} {a b lo width : ℕ}
    (hVZ : V ⊆ Z) (hab : a ≤ b)
    (hinterval : Finset.Icc a b ⊆ V.subsetSum)
    (hlength : width ≤ b + 1 - a)
    (hupper : ∀ z ∈ Z, z ≤ width)
    (hlower : ∀ z ∈ Z, lo ≤ z)
    (hbtarget : b < n / d)
    (hmass : n / d ≤ lo * (Z.card - V.card)) :
    n / d ∈ Z.subsetSum := by
  exact mem_subsetSum_of_lev_interval_card_estimates hVZ hab hinterval
    hlength hupper hlower hbtarget hmass

/-- Full finite assembly around the many-summand Lev input.  The hypotheses
`hfamily` are exactly the ordinary-growth outputs of the modular phase
argument.  Once `hlev` supplies CFP Lemma 2.2, the remaining hypotheses are
the rounded R8/R9 estimates and this theorem produces precisely the quotient
subset sum required by `forcesTarget_of_extracted_colorClass_completion`. -/
theorem quotient_mem_subsetSum_of_cfp_lev_family
    {n d ℓ n₀ q lo width : ℕ} {parts : List (Finset ℕ)}
    {Z : Finset ℕ}
    (hfamily : IsCFPLevFamily parts ℓ n₀ q)
    (hlev : HasCFPLevInterval parts ℓ n₀)
    (hpartsZ : ∀ P ∈ parts, P ⊆ Z)
    (hwidth : width ≤ ℓ * (n₀ - 1) + 1)
    (hupper : ∀ z ∈ Z, z ≤ width)
    (hlower : ∀ z ∈ Z, lo ≤ z)
    (hsumUpper : ∀ s ∈ (levFamilyUnion parts).subsetSum, s < n / d)
    (hmass : n / d ≤ lo *
      (Z.card - (levFamilyUnion parts).card)) :
    n / d ∈ Z.subsetSum := by
  obtain ⟨_hlen, hpair, _hordinary⟩ := hfamily
  obtain ⟨a, b, hab, hIiter, hIlength⟩ := hlev
  have hI : Finset.Icc a b ⊆ (levFamilyUnion parts).subsetSum :=
    hIiter.trans (levIteratedSubsetSum_subset_union_subsetSum hpair)
  have hVZ : levFamilyUnion parts ⊆ Z :=
    levFamilyUnion_subset hpartsZ
  have hbmem : b ∈ (levFamilyUnion parts).subsetSum :=
    hI (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
  exact quotient_mem_subsetSum_of_lev_completion hVZ hab hI
    (hwidth.trans hIlength) hupper hlower (hsumUpper b hbmem) hmass

/-- Same finite assembly with CFP's actual R8 input: the sum of every term
reserved for the Lev stage is already below the quotient target. -/
theorem quotient_mem_subsetSum_of_cfp_lev_family_sum_bound
    {n d ℓ n₀ q lo width : ℕ} {parts : List (Finset ℕ)}
    {Z : Finset ℕ}
    (hfamily : IsCFPLevFamily parts ℓ n₀ q)
    (hlev : HasCFPLevInterval parts ℓ n₀)
    (hpartsZ : ∀ P ∈ parts, P ⊆ Z)
    (hwidth : width ≤ ℓ * (n₀ - 1) + 1)
    (hupper : ∀ z ∈ Z, z ≤ width)
    (hlower : ∀ z ∈ Z, lo ≤ z)
    (hR8 : (∑ z ∈ levFamilyUnion parts, z) < n / d)
    (hR9 : n / d ≤ lo *
      (Z.card - (levFamilyUnion parts).card)) :
    n / d ∈ Z.subsetSum := by
  apply quotient_mem_subsetSum_of_cfp_lev_family hfamily hlev hpartsZ
    hwidth hupper hlower
  · intro s hs
    exact (mem_subsetSum_le_sum hs).trans_lt hR8
  · exact hR9

end Erdos360
