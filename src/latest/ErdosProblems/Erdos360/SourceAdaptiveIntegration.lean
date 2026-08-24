/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.SourceAdaptiveRecursion
import ErdosProblems.Erdos360.AdaptiveOrdinaryCertificate

/-!
# Counting and integration for the source-adaptive recursion

`SourceAdaptiveRecursion` supplies the selector used in the CFP proof: a
growth phase uses the internal `3/2` witness, while a nongrowth phase uses a
maximum translation of the minimum occupied normalized fibre.  This file
does the bookkeeping which is independent of the local inverse theorem.

The only substantive phase-local hypothesis retained by the main machine is
the exact increment in an unsaturated phase.  A separate connector below
derives that increment from `NormalizedFiberLossPhaseConditions`.  Thus the
local Deshouillers--Freiman alternative, the progression sieve, and the
structured coprimality assertion remain visible and are not replaced by a
cardinality oracle.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

section GrowthCounting

variable {b : ℕ} [NeZero b]

noncomputable def IsSourceAdaptiveSmallGrowthStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i ∧
    2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i <
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card

noncomputable def IsSourceAdaptiveLargeGrowthStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i ∧
    (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card ≤
      2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i

noncomputable def sourceAdaptiveGrowthIndices
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q)

noncomputable def sourceAdaptiveSmallGrowthIndices
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q)

noncomputable def sourceAdaptiveLargeGrowthIndices
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsSourceAdaptiveLargeGrowthStep hb R₀ E hE hdiverse Q)

lemma sourceAdaptiveModulus_eq_between
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i j r : ℕ} (hij : i ≤ j) (hjr : j ≤ r)
    (hir : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q r) :
    sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q j := by
  apply Nat.dvd_antisymm
  · exact sourceAdaptiveModulus_dvd_of_le
      hb R₀ E hE hdiverse Q hij
  · rw [hir]
    exact sourceAdaptiveModulus_dvd_of_le
      hb R₀ E hE hdiverse Q hjr

lemma sourceAdaptiveModulus_eq_of_log_eq
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ)
    {i j : ℕ} (hij : i ≤ j)
    (hlog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) =
      Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q j)) :
    sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q j := by
  exact eq_of_dvd_of_log_two_eq
    (closureModulus_pos hb _) (closureModulus_pos hb _)
    (sourceAdaptiveModulus_dvd_of_le hb R₀ E hE hdiverse Q hij) hlog

lemma sourceAdaptiveInternalCard_le_threshold_of_growth
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) {i : ℕ}
    (hi : 2 * i ≤ R₀.card)
    (hg : IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i) :
    sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤ Q := by
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i
  obtain ⟨u, huNe, huQ⟩ := hg
  have hwide : R₀.card ≤ 2 * R.card :=
    sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q hi
  have hle := seededSubsetSum_fiber_lower
    (AddSubgroup.closure (R : Set (ZMod b))) E (R₀ \ R) u huNe
  exact hle.trans huQ

lemma sourceAdaptive_smallStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ)
    (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k, 4 * Q ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card) :
    ∀ i < k,
      IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
  intro i hi hg hmod
  exact sourceAdaptiveInternalCard_growth_step
    hb R₀ E hE hdiverse Q (by omega)
    (sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q (by omega))
    (hQ i hi) hg.1 hmod

lemma sourceAdaptive_largeStep
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q L k : ℕ)
    (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k, 4 * Q ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hL : ∀ i < k, 4 * L ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card) :
    ∀ i < k,
      IsSourceAdaptiveLargeGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
  intro i hi hg hmod
  have hgrowth := sourceAdaptiveInternalCard_growth_step
    hb R₀ E hE hdiverse Q (by omega)
    (sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q (by omega))
    (hQ i hi) hg.1 hmod
  have htwoL : 2 * L ≤
      sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i := by
    have hroom := hL i hi
    have hlarge := hg.2
    omega
  omega

lemma sourceAdaptive_small_growth_code_not_three
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ)
    (hsmallStep : ∀ i < k,
      IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1))
    {i j r : ℕ} (hij : i < j) (hjr : j < r) (hrk : r < k)
    (hgi : IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i)
    (hgj : IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q j)
    (hqIJ : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) =
      Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q j))
    (hqJR : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q j) =
      Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q r))
    (hcIJ : Nat.log 2 (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i) =
      Nat.log 2 (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j))
    (hcJR : Nat.log 2 (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j) =
      Nat.log 2 (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q r)) : False := by
  let qi := sourceAdaptiveModulus hb R₀ E hE hdiverse Q i
  let qj := sourceAdaptiveModulus hb R₀ E hE hdiverse Q j
  let qr := sourceAdaptiveModulus hb R₀ E hE hdiverse Q r
  let ci := sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i
  let cj := sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j
  let cr := sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q r
  have hqEqIJ : qi = qj :=
    sourceAdaptiveModulus_eq_of_log_eq hb R₀ E hE hdiverse Q hij.le hqIJ
  have hqEqJR : qj = qr :=
    sourceAdaptiveModulus_eq_of_log_eq hb R₀ E hE hdiverse Q hjr.le hqJR
  have hqiSucc : qi =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) :=
    sourceAdaptiveModulus_eq_between hb R₀ E hE hdiverse Q
      (by omega) (by omega) (hqEqIJ.trans hqEqJR)
  have hqjSucc : qj =
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q (j + 1) :=
    sourceAdaptiveModulus_eq_between hb R₀ E hE hdiverse Q
      (by omega) (by omega) hqEqJR
  have hgrowI := hsmallStep i (by omega) hgi hqiSucc
  have hmonoIJ : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) ≤
      cj := sourceAdaptiveInternalCard_mono_of_modulus_eq
        hb R₀ E hE hdiverse Q (by omega) (hqiSucc.symm.trans hqEqIJ)
  have hgrowJ := hsmallStep j (by omega) hgj hqjSucc
  have hmonoJR : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (j + 1) ≤
      cr := sourceAdaptiveInternalCard_mono_of_modulus_eq
        hb R₀ E hE hdiverse Q (by omega) (hqjSucc.symm.trans hqEqJR)
  have hthreeI : 3 * ci ≤ 2 * cj :=
    hgrowI.trans (Nat.mul_le_mul_left 2 hmonoIJ)
  have hthreeJ : 3 * cj ≤ 2 * cr :=
    hgrowJ.trans (Nat.mul_le_mul_left 2 hmonoJR)
  have hciPos : 0 < ci := modularInternalCard_pos R₀ _
  have hdouble : 2 * ci ≤ cr := by omega
  have hloglt : Nat.log 2 ci < Nat.log 2 cr :=
    log_two_lt_of_double_le hciPos hdouble
  exact (Nat.ne_of_lt hloglt) (hcIJ.trans hcJR)

/-- Small source-growth steps are counted by their modulus and internal-cardinality
binary buckets, with multiplicity at most two per pair of buckets. -/
theorem card_sourceAdaptiveSmallGrowthIndices_le
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax k : ℕ)
    (hmodMax : ∀ i < k,
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ dMax)
    (hsmallStep : ∀ i < k,
      IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1)) :
    (sourceAdaptiveSmallGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) := by
  classical
  let G := sourceAdaptiveSmallGrowthIndices hb R₀ E hE hdiverse Q k
  let C := Fin (Nat.log 2 dMax + 1) × Fin (Nat.log 2 b + 1)
  let f : ℕ → C := fun i ↦
    (⟨min (Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i))
        (Nat.log 2 dMax),
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
     ⟨Nat.log 2 (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i),
      Nat.lt_succ_of_le (Nat.log_mono_right
        (modularInternalCard_le R₀ _))⟩)
  by_contra hnot
  have hlarge : (Finset.univ : Finset C).card * 2 < G.card := by
    simp only [Finset.card_univ, C, Fintype.card_prod, Fintype.card_fin]
    dsimp only [G] at hnot ⊢
    have hgt : 2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) <
        (sourceAdaptiveSmallGrowthIndices hb R₀ E hE hdiverse Q k).card :=
      Nat.lt_of_not_ge hnot
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgt
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := Finset.univ) (f := f)
      (n := 2) (fun _ _ ↦ Finset.mem_univ _) hlarge
  let S := G.filter fun i ↦ f i = y
  have hScard : 2 < S.card := by simpa only [S] using hy
  obtain ⟨i, hiS, j, hjS, r, hrS, hij, hjr⟩ :=
    exists_three_ordered_of_two_lt_card hScard
  have hiG : i ∈ G := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ G := (Finset.mem_filter.mp hjS).1
  have hrG : r ∈ G := (Finset.mem_filter.mp hrS).1
  have hfi : f i = y := (Finset.mem_filter.mp hiS).2
  have hfj : f j = y := (Finset.mem_filter.mp hjS).2
  have hfr : f r = y := (Finset.mem_filter.mp hrS).2
  have hiData := Finset.mem_filter.mp hiG
  have hjData := Finset.mem_filter.mp hjG
  have hrData := Finset.mem_filter.mp hrG
  have hiMod := hmodMax i (Finset.mem_range.mp hiData.1)
  have hjMod := hmodMax j (Finset.mem_range.mp hjData.1)
  have hrMod := hmodMax r (Finset.mem_range.mp hrData.1)
  have hiLog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) ≤
      Nat.log 2 dMax := Nat.log_mono_right hiMod
  have hjLog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q j) ≤
      Nat.log 2 dMax := Nat.log_mono_right hjMod
  have hrLog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q r) ≤
      Nat.log 2 dMax := Nat.log_mono_right hrMod
  have hcodeIJ := congrArg (fun z : C ↦ z.1.val) (hfi.trans hfj.symm)
  have hcodeJR := congrArg (fun z : C ↦ z.1.val) (hfj.trans hfr.symm)
  have hcIJ := congrArg (fun z : C ↦ z.2.val) (hfi.trans hfj.symm)
  have hcJR := congrArg (fun z : C ↦ z.2.val) (hfj.trans hfr.symm)
  dsimp only [f] at hcodeIJ hcodeJR hcIJ hcJR
  rw [min_eq_left hiLog, min_eq_left hjLog] at hcodeIJ
  rw [min_eq_left hjLog, min_eq_left hrLog] at hcodeJR
  exact sourceAdaptive_small_growth_code_not_three hb R₀ E hE hdiverse Q k
    hsmallStep hij hjr (Finset.mem_range.mp hrData.1)
    hiData.2 hjData.2 hcodeIJ hcodeJR hcIJ hcJR

/-- Large source-growth steps gain at least `L` in the internal set for each
fixed modulus bucket. -/
theorem card_sourceAdaptiveLargeGrowthIndices_le
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax L k : ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hmodMax : ∀ i < k,
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ dMax)
    (hlargeStep : ∀ i < k,
      IsSourceAdaptiveLargeGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1)) :
    (sourceAdaptiveLargeGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (Nat.log 2 dMax + 1) * (Q / L + 1) := by
  classical
  let G := sourceAdaptiveLargeGrowthIndices hb R₀ E hE hdiverse Q k
  let C := Fin (Nat.log 2 dMax + 1) × Fin (Q / L + 1)
  let f : ℕ → C := fun i ↦
    (⟨min (Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i))
        (Nat.log 2 dMax),
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
     ⟨min (sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i / L) (Q / L),
      Nat.lt_succ_of_le (min_le_right _ _)⟩)
  have hordered : ∀ {i j : ℕ}, i ∈ G → j ∈ G → i < j → f i ≠ f j := by
    intro i j hiG hjG hij hf
    have hiData := Finset.mem_filter.mp hiG
    have hjData := Finset.mem_filter.mp hjG
    have hiRange : i < k := Finset.mem_range.mp hiData.1
    have hjRange : j < k := Finset.mem_range.mp hjData.1
    have hiMod := hmodMax i hiRange
    have hjMod := hmodMax j hjRange
    have hiLog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i) ≤
        Nat.log 2 dMax := Nat.log_mono_right hiMod
    have hjLog : Nat.log 2 (sourceAdaptiveModulus hb R₀ E hE hdiverse Q j) ≤
        Nat.log 2 dMax := Nat.log_mono_right hjMod
    have hciQ : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤ Q :=
      sourceAdaptiveInternalCard_le_threshold_of_growth hb R₀ E hE hdiverse Q
        (by omega) hiData.2.1
    have hcjQ : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j ≤ Q :=
      sourceAdaptiveInternalCard_le_threshold_of_growth hb R₀ E hE hdiverse Q
        (by omega) hjData.2.1
    have hiQuot : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i / L ≤
        Q / L := Nat.div_le_div_right hciQ
    have hjQuot : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j / L ≤
        Q / L := Nat.div_le_div_right hcjQ
    have hqLog := congrArg (fun z : C ↦ z.1.val) hf
    have hcQuot := congrArg (fun z : C ↦ z.2.val) hf
    dsimp only [f] at hqLog hcQuot
    rw [min_eq_left hiLog, min_eq_left hjLog] at hqLog
    rw [min_eq_left hiQuot, min_eq_left hjQuot] at hcQuot
    have hqEq := sourceAdaptiveModulus_eq_of_log_eq hb R₀ E hE hdiverse Q
      hij.le hqLog
    have hqiSucc : sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) :=
      sourceAdaptiveModulus_eq_between hb R₀ E hE hdiverse Q
        (by omega) (by omega) hqEq
    have hadd := hlargeStep i hiRange hiData.2 hqiSucc
    have hmono : sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j :=
      sourceAdaptiveInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse Q
        (by omega) (hqiSucc.symm.trans hqEq)
    have hinc : L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q j := hadd.trans hmono
    have hdiv := Nat.div_le_div_right hinc (c := L)
    rw [show L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i =
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i + L by omega,
      Nat.add_div_right _ hL] at hdiv
    omega
  have hcard : G.card ≤ (Finset.univ : Finset C).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hf
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact (hordered hi hj hij) hf
      · exact (hordered hj hi hji) hf.symm
  simpa only [G, Finset.card_univ, C, Fintype.card_prod,
    Fintype.card_fin] using hcard

/-- The complete source-growth count, obtained by partitioning at half the
current remainder. -/
theorem card_sourceAdaptiveGrowthIndices_le
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax L k : ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hmodMax : ∀ i < k,
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ dMax)
    (hsmallStep : ∀ i < k,
      IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1))
    (hlargeStep : ∀ i < k,
      IsSourceAdaptiveLargeGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1)) :
    (sourceAdaptiveGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)) := by
  let G := sourceAdaptiveGrowthIndices hb R₀ E hE hdiverse Q k
  let Gsmall := sourceAdaptiveSmallGrowthIndices hb R₀ E hE hdiverse Q k
  let Glarge := sourceAdaptiveLargeGrowthIndices hb R₀ E hE hdiverse Q k
  have hpart : G ⊆ Gsmall ∪ Glarge := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    rw [Finset.mem_union]
    by_cases hs : 2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i <
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card
    · left
      change i ∈ sourceAdaptiveSmallGrowthIndices hb R₀ E hE hdiverse Q k
      rw [sourceAdaptiveSmallGrowthIndices, Finset.mem_filter]
      exact ⟨hiData.1, hiData.2, hs⟩
    · right
      change i ∈ sourceAdaptiveLargeGrowthIndices hb R₀ E hE hdiverse Q k
      rw [sourceAdaptiveLargeGrowthIndices, Finset.mem_filter]
      exact ⟨hiData.1, hiData.2, by omega⟩
  have hGS := card_sourceAdaptiveSmallGrowthIndices_le hb R₀ E hE hdiverse
    Q dMax k hmodMax hsmallStep
  have hGL := card_sourceAdaptiveLargeGrowthIndices_le hb R₀ E hE hdiverse
    Q dMax L k hL hhalf hmodMax hlargeStep
  calc
    G.card ≤ (Gsmall ∪ Glarge).card := Finset.card_le_card hpart
    _ ≤ Gsmall.card + Glarge.card := Finset.card_union_le _ _
    _ ≤ 2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) +
        (Nat.log 2 dMax + 1) * (Q / L + 1) := Nat.add_le_add hGS hGL
    _ = (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)) := by ring

/-! ## Accumulating nongrowth steps -/

noncomputable def sourceAdaptiveNonGrowthIndices
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i ↦
    ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i

lemma card_sourceAdaptiveNonGrowthIndices
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) :
    (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card =
      k - (sourceAdaptiveGrowthIndices hb R₀ E hE hdiverse Q k).card := by
  classical
  have heq : sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k =
      Finset.range k \
        sourceAdaptiveGrowthIndices hb R₀ E hE hdiverse Q k := by
    ext i
    simp only [sourceAdaptiveNonGrowthIndices, sourceAdaptiveGrowthIndices,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
    tauto
  rw [heq, Finset.card_sdiff_of_subset]
  · simp
  · exact Finset.filter_subset _ _

/-- A uniform increment on every source nongrowth step accumulates.  The
bound `k ≤ |R₀|` is the exact range needed for phase monotonicity. -/
theorem sourceAdaptive_nongrowth_increment_lower
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q D k : ℕ)
    (hk : k ≤ R₀.card)
    (hstep : ∀ i < k,
      ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i →
      D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i).card ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1)).card) :
    D * (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := by
  induction k with
  | zero => simp [sourceAdaptiveNonGrowthIndices]
  | succ k ih =>
      have hk' : k ≤ R₀.card := by omega
      have hIH := ih hk' (fun i hi ↦ hstep i (by omega))
      by_cases hg : IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q k
      · have hcard :
            (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q (k + 1)).card =
              (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card := by
          rw [sourceAdaptiveNonGrowthIndices, sourceAdaptiveNonGrowthIndices,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hcard]
        exact hIH.trans (Finset.card_le_card
          (sourceAdaptivePhaseSums_mono hb R₀ E hE hdiverse Q (by omega)))
      · have hcard :
            (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q (k + 1)).card =
              (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card + 1 := by
          rw [sourceAdaptiveNonGrowthIndices, sourceAdaptiveNonGrowthIndices,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hcard]
        have hinc := hstep k (by omega) hg
        calc
          D * ((sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card + 1) =
              D * (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card + D := by
            ring
          _ ≤ (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card + D :=
            Nat.add_le_add_right hIH D
          _ = D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := by
            omega
          _ ≤ (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (k + 1)).card := hinc

lemma sourceAdaptivePhaseSums_subset_full
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) :
    sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i ⊆
      E + R₀.subsetSum := by
  rw [sourceAdaptivePhaseSums, sourceAdaptivePhaseSet]
  apply Finset.add_subset_add_left
  exact Finset.subsetSum_mono (Finset.sdiff_subset.trans (by rfl))

/-- Complete phase-counting machine for the source-adaptive recursion.  Its
only phase-local analytic input is the stated increment for an unsaturated
step; the connector below proves that input from the normalized local
inverse and structured coprimality conditions. -/
theorem sourceAdaptive_modular_phase_machine
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (Q dMax L D k satTarget unsatTarget : ℕ) (sat : ℕ → ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hQ : ∀ i < k, 4 * Q ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hLroom : ∀ i < k, 4 * L ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hmodMax : ∀ i < k,
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ dMax)
    (hunsaturatedStep : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse Q sat i →
      D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i).card ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1)).card)
    (hsatTarget : ∀ i < k,
      satTarget ≤ sourceAdaptiveModulus hb R₀ E hE hdiverse Q i *
        sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i))
    (hgrowthBudget :
      (Nat.log 2 dMax + 1) *
          (2 * (Nat.log 2 b + 1) + (Q / L + 1)) ≤ k)
    (hunsatTarget : unsatTarget ≤ D *
      (k - (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)))) :
    min satTarget unsatTarget ≤ (E + R₀.subsetSum).card := by
  classical
  let B := (Nat.log 2 dMax + 1) *
    (2 * (Nat.log 2 b + 1) + (Q / L + 1))
  have hk : k ≤ R₀.card := by omega
  have hsmall := sourceAdaptive_smallStep hb R₀ E hE hdiverse Q k hhalf hQ
  have hlarge := sourceAdaptive_largeStep hb R₀ E hE hdiverse Q L k
    hhalf hQ hLroom
  by_cases hex : ∃ i < k,
      IsSourceAdaptiveSaturatedStep hb R₀ E hE hdiverse Q sat i
  · obtain ⟨i, hi, hsat⟩ := hex
    have hphase := sourceAdaptive_saturated_phase_card hb R₀ E hE hdiverse
      Q sat (by omega) hsat
    have hfull := Finset.card_le_card
      (sourceAdaptivePhaseSums_subset_full hb R₀ E hE hdiverse Q i)
    exact (min_le_left _ _).trans
      ((hsatTarget i hi).trans (hphase.trans hfull))
  · have hnonGrowthUnsat : ∀ i < k,
        ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i →
        IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse Q sat i := by
      intro i hi hng
      by_contra hnu
      apply hex
      exact ⟨i, hi, hng, hnu⟩
    have hinc := sourceAdaptive_nongrowth_increment_lower
      hb R₀ E hE hdiverse Q D k hk
      (fun i hi hng ↦ hunsaturatedStep i hi (hnonGrowthUnsat i hi hng))
    have hgrowth := card_sourceAdaptiveGrowthIndices_le
      hb R₀ E hE hdiverse Q dMax L k hL hhalf hmodMax hsmall hlarge
    have hnonCard := card_sourceAdaptiveNonGrowthIndices
      hb R₀ E hE hdiverse Q k
    have hfull := Finset.card_le_card
      (sourceAdaptivePhaseSums_subset_full hb R₀ E hE hdiverse Q k)
    have hremain : k - B ≤
        (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card := by
      rw [hnonCard]
      exact Nat.sub_le_sub_left hgrowth k
    have htarget : unsatTarget ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := by
      calc
        unsatTarget ≤ D * (k - B) := by simpa [B] using hunsatTarget
        _ ≤ D * (sourceAdaptiveNonGrowthIndices
              hb R₀ E hE hdiverse Q k).card :=
          Nat.mul_le_mul_left D hremain
        _ ≤ (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := hinc
    exact (min_le_right _ _).trans (htarget.trans hfull)

/-- CFP-exact phase machine.  Unlike the coarse wrapper above, the external
growth threshold need not fit inside the remainder.  Small internal sets
grow by `3/2`; large internal sets gain `L` from generation and the ambient
quarter-density condition, exactly as in Claim 1 of CFP Lemma 5.6. -/
theorem sourceAdaptive_modular_phase_machine_cfp
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (Q dMax L D k satTarget unsatTarget : ℕ) (sat : ℕ → ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hambient : ∀ i < k,
      4 * Q < Nat.card (AddSubgroup.closure
        ((sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i :
          Finset (ZMod b)) : Set (ZMod b))))
    (hLroom : ∀ i < k, 16 * L ≤
      (sourceAdaptiveRemainder hb R₀ E hE hdiverse Q i).card)
    (hmodMax : ∀ i < k,
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i ≤ dMax)
    (hunsaturatedStep : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse Q sat i →
      D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q i).card ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q (i + 1)).card)
    (hsatTarget : ∀ i < k,
      satTarget ≤ sourceAdaptiveModulus hb R₀ E hE hdiverse Q i *
        sat (sourceAdaptiveModulus hb R₀ E hE hdiverse Q i))
    (hgrowthBudget :
      (Nat.log 2 dMax + 1) *
          (2 * (Nat.log 2 b + 1) + (Q / L + 1)) ≤ k)
    (hunsatTarget : unsatTarget ≤ D *
      (k - (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)))) :
    min satTarget unsatTarget ≤ (E + R₀.subsetSum).card := by
  classical
  let B := (Nat.log 2 dMax + 1) *
    (2 * (Nat.log 2 b + 1) + (Q / L + 1))
  have hk : k ≤ R₀.card := by omega
  have hsmall : ∀ i < k,
      IsSourceAdaptiveSmallGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      3 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        2 * sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
    intro i hi hg hmod
    exact sourceAdaptiveInternalCard_small_growth_step
      hb R₀ E hE hdiverse Q (by omega) hg.1 hg.2 hmod
  have hlarge : ∀ i < k,
      IsSourceAdaptiveLargeGrowthStep hb R₀ E hE hdiverse Q i →
      sourceAdaptiveModulus hb R₀ E hE hdiverse Q i =
        sourceAdaptiveModulus hb R₀ E hE hdiverse Q (i + 1) →
      L + sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q i ≤
        sourceAdaptiveInternalCard hb R₀ E hE hdiverse Q (i + 1) := by
    intro i hi hg hmod
    exact sourceAdaptiveInternalCard_large_growth_step
      hb R₀ E hE hdiverse Q L (by omega)
      (sourceAdaptive_wide_of_half hb R₀ E hE hdiverse Q (by omega))
      hg.1 hg.2 (hambient i hi) (hLroom i hi) hmod
  by_cases hex : ∃ i < k,
      IsSourceAdaptiveSaturatedStep hb R₀ E hE hdiverse Q sat i
  · obtain ⟨i, hi, hsat⟩ := hex
    have hphase := sourceAdaptive_saturated_phase_card hb R₀ E hE hdiverse
      Q sat (by omega) hsat
    have hfull := Finset.card_le_card
      (sourceAdaptivePhaseSums_subset_full hb R₀ E hE hdiverse Q i)
    exact (min_le_left _ _).trans
      ((hsatTarget i hi).trans (hphase.trans hfull))
  · have hnonGrowthUnsat : ∀ i < k,
        ¬ IsSourceAdaptiveGrowthStep hb R₀ E hE hdiverse Q i →
        IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse Q sat i := by
      intro i hi hng
      by_contra hnu
      apply hex
      exact ⟨i, hi, hng, hnu⟩
    have hinc := sourceAdaptive_nongrowth_increment_lower
      hb R₀ E hE hdiverse Q D k hk
      (fun i hi hng ↦ hunsaturatedStep i hi (hnonGrowthUnsat i hi hng))
    have hgrowth := card_sourceAdaptiveGrowthIndices_le
      hb R₀ E hE hdiverse Q dMax L k hL hhalf hmodMax hsmall hlarge
    have hnonCard := card_sourceAdaptiveNonGrowthIndices
      hb R₀ E hE hdiverse Q k
    have hfull := Finset.card_le_card
      (sourceAdaptivePhaseSums_subset_full hb R₀ E hE hdiverse Q k)
    have hremain : k - B ≤
        (sourceAdaptiveNonGrowthIndices hb R₀ E hE hdiverse Q k).card := by
      rw [hnonCard]
      exact Nat.sub_le_sub_left hgrowth k
    have htarget : unsatTarget ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := by
      calc
        unsatTarget ≤ D * (k - B) := by simpa [B] using hunsatTarget
        _ ≤ D * (sourceAdaptiveNonGrowthIndices
              hb R₀ E hE hdiverse Q k).card :=
          Nat.mul_le_mul_left D hremain
        _ ≤ (sourceAdaptivePhaseSums hb R₀ E hE hdiverse Q k).card := hinc
    exact (min_le_right _ _).trans (htarget.trans hfull)

end GrowthCounting

/-! ## The explicit normalized-fibre connector -/

section FiberLossConnector

variable {b : ℕ} [NeZero b]

/-- The source recursion's unsaturated increment follows from the exact
normalized-fibre inverse/sieve hypotheses at that step.  In particular,
`NormalizedFiberLossPhaseConditions.localDF` and `.coprime` remain explicit
fields of `hconditions`; no replacement cardinality assumption is used. -/
theorem sourceAdaptive_unsaturated_increment_of_normalizedFiberLossConditions
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (phaseQ D : ℕ) (sat : ℕ → ℕ)
    (k n y sieveLevel sieveQ κ : ℕ) (ratio : ℝ)
    (hD : 0 < D) (hhalf : 2 * k ≤ R₀.card)
    (coordinateEquiv : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse phaseQ sat i →
      let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod b))
      ZMod (Nat.card H) ≃+ H)
    (coordinateBase : ∀ i (hi : i < k),
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse phaseQ sat i → ℕ)
    (hconditions : ∀ i (hi : i < k)
      (hu : IsSourceAdaptiveUnsaturatedStep
        hb R₀ E hE hdiverse phaseQ sat i),
      let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod b))
      let U := sourceAdaptiveFiber R₀ E R
        (sourceAdaptiveMinFiberCenter R₀ E R)
      let X := liftFinsetToClosure R
      @NormalizedFiberLossPhaseConditions A C n y sieveLevel sieveQ κ (D - 1)
        ratio b inferInstance H
        (by exact ⟨Nat.ne_of_gt Nat.card_pos⟩) (coordinateEquiv i hi hu)
        (coordinateBase i hi hu) U X) :
    ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse phaseQ sat i →
      D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse phaseQ i).card ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse phaseQ (i + 1)).card := by
  intro i hi hu
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i
  let S := sourceAdaptivePhaseSums hb R₀ E hE hdiverse phaseQ i
  let u := sourceAdaptiveMinFiberCenter R₀ E R
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    rw [card_sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ (by omega)]
    omega
  have hglobal := normalizedFiberMaxPick_global_increment A C hsieve
    R S u hR hD (coordinateEquiv i hi hu) (coordinateBase i hi hu)
      (hconditions i hi hu)
  have hpick := sourceAdaptivePhasePick_eq_normalized_of_unsaturated
    hb R₀ E hE hdiverse phaseQ sat hu
  have hsucc := sourceAdaptivePhaseSums_succ
    hb R₀ E hE hdiverse phaseQ (show i < R₀.card by omega)
  rw [hsucc, hpick]
  simpa [R, S, u, sourceAdaptiveFiber, sourceAdaptivePhaseSums,
    normalizedFiberMaxPick, hR] using hglobal

end FiberLossConnector

/-! ## Packaged source-adaptive certificate and ordinary bridge -/

section SourceCertificate

variable {t : ℕ} [NeZero t]

/-- Parameters of the source-faithful recursion at one pivot.  Unlike the
legacy `CFPAdaptiveSelectorData`, its increment is stated for the actual
Q-dependent source recursion. -/
structure CFPSourceAdaptiveSelectorData
    (ht : 0 < t) (R₀ : Finset (ZMod t))
    (hdiverse : PhaseDiverse ht R₀) (residueTarget : ℕ) where
  phaseQ : ℕ
  largeGain : ℕ
  unsaturatedGain : ℕ
  phaseCount : ℕ
  saturatedTarget : ℕ
  unsaturatedTarget : ℕ
  saturation : ℕ → ℕ
  largeGain_pos : 0 < largeGain
  half : 2 * phaseCount ≤ R₀.card
  phaseQ_room : ∀ i < phaseCount,
    4 * phaseQ ≤
      (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card
  largeGain_room : ∀ i < phaseCount,
    4 * largeGain ≤
      (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card
  unsaturatedIncrement : ∀ i < phaseCount,
    IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ saturation i →
      unsaturatedGain +
          (sourceAdaptivePhaseSums ht R₀ {0} (by simp) hdiverse phaseQ i).card ≤
        (sourceAdaptivePhaseSums ht R₀ {0} (by simp) hdiverse
          phaseQ (i + 1)).card
  saturated_bound : ∀ i < phaseCount,
    saturatedTarget ≤
      sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i *
        saturation
          (sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i)
  growth_budget :
    (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)) ≤ phaseCount
  unsaturated_bound : unsaturatedTarget ≤ unsaturatedGain *
    (phaseCount - (Nat.log 2 t + 1) *
      (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)))
  target_bound : residueTarget ≤ min saturatedTarget unsaturatedTarget

theorem CFPSourceAdaptiveSelectorData.card_le_full_modular_subsetSum
    {ht : 0 < t} {R₀ : Finset (ZMod t)}
    {hdiverse : PhaseDiverse ht R₀} {residueTarget : ℕ}
    (h : CFPSourceAdaptiveSelectorData ht R₀ hdiverse residueTarget) :
    residueTarget ≤ ({0} + R₀.subsetSum).card := by
  apply h.target_bound.trans
  exact sourceAdaptive_modular_phase_machine
    ht R₀ {0} (by simp) hdiverse
    h.phaseQ t h.largeGain h.unsaturatedGain h.phaseCount
    h.saturatedTarget h.unsaturatedTarget h.saturation
    h.largeGain_pos h.half h.phaseQ_room h.largeGain_room
    (fun i _ ↦ sourceAdaptiveModulus_le_ambient
      ht R₀ {0} (by simp) hdiverse h.phaseQ i)
    h.unsaturatedIncrement h.saturated_bound h.growth_budget
    h.unsaturated_bound

/-- A source-adaptive modular certificate gives occupied residues of genuine
integer subset sums. -/
theorem occupiedResidues_lower_of_source_adaptive_selector
    (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)))
    {residueTarget : ℕ}
    (h : CFPSourceAdaptiveSelectorData ht
      (A.image fun a : ℕ ↦ (a : ZMod t)) hdiverse residueTarget) :
    residueTarget ≤ (occupiedResidues A.subsetSum t).card := by
  have hgrowth := h.card_le_full_modular_subsetSum
  have hsub :
      ({0} + (A.image fun a : ℕ ↦ (a : ZMod t)).subsetSum) ⊆
        occupiedResidues A.subsetSum t := by
    rw [finset_singleton_zero_add]
    simpa [occupiedResidues] using
      (subsetSum_image_subset_image_subsetSum
        (Nat.castAddMonoidHom (ZMod t)) A)
  exact hgrowth.trans (Finset.card_le_card hsub)

/-- Compatibility with the semantic ordinary-growth interface. -/
theorem hasCFPAdaptivePivotGrowth_of_source_adaptive_selector
    (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)))
    {residueTarget : ℕ}
    (h : CFPSourceAdaptiveSelectorData ht
      (A.image fun a : ℕ ↦ (a : ZMod t)) hdiverse residueTarget) :
    HasCFPAdaptivePivotGrowth A t residueTarget := by
  exact ⟨ht, occupiedResidues_lower_of_source_adaptive_selector ht A hdiverse h⟩

end SourceCertificate

end Erdos360

#print axioms Erdos360.sourceAdaptive_modular_phase_machine
#print axioms Erdos360.sourceAdaptive_unsaturated_increment_of_normalizedFiberLossConditions
#print axioms Erdos360.CFPSourceAdaptiveSelectorData.card_le_full_modular_subsetSum
#print axioms Erdos360.hasCFPAdaptivePivotGrowth_of_source_adaptive_selector
