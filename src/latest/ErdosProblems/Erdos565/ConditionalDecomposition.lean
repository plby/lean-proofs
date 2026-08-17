import ErdosProblems.Erdos565.Hypergraph
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum

/-!
# A finite conditional-probability fingerprint decomposition

This file contains the finite probability calculation used in Section 4 of the proof of
Erdős Problem 565.  A hypergraph is represented by a finite family of finite sets.  The
probability space is the binomial random subset of a fixed finite ground set `U`.

The cover below deliberately contains only **nonempty** sets.  This is the correction needed
in the strict conditional-probability conclusion: the empty set always has conditional
probability one.
-/

namespace Erdos565
namespace ConditionalDecomposition

open scoped BigOperators

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- `I` contains no edge of `G`. -/
abbrev Independent (G : Hypergraph V) (I : Finset V) : Prop :=
  G.IsIndependent I

@[simp] theorem independent_iff_isIndependent {G : Hypergraph V} {I : Finset V} :
    Independent G I ↔ G.IsIndependent I := Iff.rfl

noncomputable instance independentDecidable (G : Hypergraph V) (I : Finset V) :
    Decidable (Independent G I) := Classical.propDecidable _

/-- All edges of `G` lie in the declared ground set `U`. -/
def SupportedOn (G : Hypergraph V) (U : Finset V) : Prop :=
  ∀ E ∈ G, E ⊆ U

/-- The mass of `X` in the binomial `q`-random-subset model on `U`. -/
def subsetWeight (q : ℝ) (U X : Finset V) : ℝ :=
  q ^ X.card * (1 - q) ^ (U.card - X.card)

/-- The mass of a finite event in the binomial random-subset model. -/
def qMass (q : ℝ) (U : Finset V) (A : Finset (Finset V)) : ℝ :=
  ∑ X ∈ A, subsetWeight q U X

/-- The finite event consisting of the `G`-independent subsets of `U` containing `T`. -/
noncomputable def independentContainingEvent (U : Finset V) (G : Hypergraph V)
    (T : Finset V) : Finset (Finset V) := by
  classical
  exact U.powerset.filter fun X ↦ Independent G X ∧ T ⊆ X

/-- Mass of the `G`-independent random subsets which contain `T`. -/
def independentContainingMass (q : ℝ) (U : Finset V) (G : Hypergraph V)
    (T : Finset V) : ℝ :=
  qMass q U (independentContainingEvent U G T)

/-- Conditional probability that the random subset contains `T`, given `G`-independence. -/
def conditionalContainment (q : ℝ) (U : Finset V) (G : Hypergraph V)
    (T : Finset V) : ℝ :=
  independentContainingMass q U G T / independentContainingMass q U G ∅

/--
Conditional probability of adjoining `L`, after `T` is already present and after conditioning
on `G`-independence.  This is also the containment probability in the usual residual-link
model on `U \ T`.
-/
def extensionProbability (q : ℝ) (U : Finset V) (G : Hypergraph V)
    (T L : Finset V) : ℝ :=
  independentContainingMass q U G (T ∪ L) / independentContainingMass q U G T

/-- The multiplicative threshold in the decomposition. -/
def threshold (q α : ℝ) (T : Finset V) : ℝ :=
  ((1 - α) * q) ^ T.card

@[simp] theorem independent_empty_containing_mass (q : ℝ) (U : Finset V)
    (G : Hypergraph V) :
    independentContainingMass q U G ∅ =
      qMass q U (independentContainingEvent U G ∅) := rfl

@[simp] theorem threshold_empty (q α : ℝ) : threshold q α (∅ : Finset V) = 1 := by
  simp [threshold]

theorem independent_mono {G : Hypergraph V} {I J : Finset V}
    (hI : Independent G I) (hJI : J ⊆ I) : Independent G J := by
  intro E hE hsub
  exact hI E hE (hsub.trans hJI)

theorem independent_empty (G : Hypergraph V) (hG : ∅ ∉ G) : Independent G ∅ := by
  intro E hE hsub
  have : E = ∅ := Finset.subset_empty.mp hsub
  exact hG (this ▸ hE)

theorem subsetWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U X : Finset V) : 0 ≤ subsetWeight q U X := by
  exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)

theorem subsetWeight_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (U X : Finset V) : 0 < subsetWeight q U X := by
  exact mul_pos (pow_pos hq0 _) (pow_pos (sub_pos.mpr hq1) _)

theorem qMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset V) (A : Finset (Finset V)) : 0 ≤ qMass q U A := by
  unfold qMass
  exact Finset.sum_nonneg fun X _ ↦ subsetWeight_nonneg hq0 hq1 U X

/-- The mass of the whole powerset is one. -/
theorem qMass_true (q : ℝ) (U : Finset V) : qMass q U U.powerset = 1 := by
  rw [qMass]
  simp only [subsetWeight]
  rw [Finset.sum_powerset_apply_card (fun k ↦ q ^ k * (1 - q) ^ (U.card - k))]
  simp only [nsmul_eq_mul]
  calc
    (∑ x ∈ Finset.range (U.card + 1),
        (U.card.choose x : ℝ) * (q ^ x * (1 - q) ^ (U.card - x))) =
        ∑ x ∈ Finset.range (U.card + 1),
          q ^ x * (1 - q) ^ (U.card - x) * (U.card.choose x : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (q + (1 - q)) ^ U.card := (add_pow q (1 - q) U.card).symm
    _ = 1 := by ring

theorem qMass_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset V) (A : Finset (Finset V)) (hA : A ⊆ U.powerset) : qMass q U A ≤ 1 := by
  rw [← qMass_true q U]
  unfold qMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hA fun X _ _ ↦ subsetWeight_nonneg hq0 hq1 U X

@[simp] theorem mem_independentContainingEvent {U T X : Finset V} {G : Hypergraph V} :
    X ∈ independentContainingEvent U G T ↔ X ⊆ U ∧ Independent G X ∧ T ⊆ X := by
  classical
  simp [independentContainingEvent, and_assoc]

/-- The singleton sample `T` contributes its full binomial weight. -/
theorem subsetWeight_le_independentContainingMass {q : ℝ} {U T : Finset V}
    {G : Hypergraph V} (hTU : T ⊆ U) (hTI : Independent G T)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    subsetWeight q U T ≤ independentContainingMass q U G T := by
  rw [independentContainingMass, qMass]
  have hTmem : T ∈ independentContainingEvent U G T := by
    exact mem_independentContainingEvent.mpr ⟨hTU, hTI, Finset.Subset.rfl⟩
  apply Finset.single_le_sum
  · intro X hX
    exact subsetWeight_nonneg hq0 hq1 U X
  · exact hTmem

/-- Positivity of the conditioning mass, witnessed by the sample `T` itself. -/
theorem independentContainingMass_pos {q : ℝ} {U T : Finset V}
    {G : Hypergraph V} (hTU : T ⊆ U) (hTI : Independent G T)
    (hq0 : 0 < q) (hq1 : q < 1) :
    0 < independentContainingMass q U G T := by
  exact lt_of_lt_of_le (subsetWeight_pos hq0 hq1 U T)
    (subsetWeight_le_independentContainingMass hTU hTI hq0.le hq1.le)

theorem independentContainingMass_mono {q : ℝ} {U A B : Finset V}
    {G : Hypergraph V} (hAB : A ⊆ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    independentContainingMass q U G B ≤ independentContainingMass q U G A := by
  unfold independentContainingMass qMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro X hX
    rw [mem_independentContainingEvent] at hX ⊢
    exact ⟨hX.1, hX.2.1, hAB.trans hX.2.2⟩
  · intro X hXA hXB
    exact subsetWeight_nonneg hq0 hq1 U X

/-- Exact chain rule for conditional containment. -/
theorem conditional_chain_rule {q : ℝ} {U T L : Finset V} {G : Hypergraph V}
    (hTU : T ⊆ U) (hTI : Independent G T) (hq0 : 0 < q) (hq1 : q < 1) :
    conditionalContainment q U G (T ∪ L) =
      conditionalContainment q U G T * extensionProbability q U G T L := by
  unfold conditionalContainment extensionProbability
  have hTpos := independentContainingMass_pos hTU hTI hq0 hq1
  have hEpos := independentContainingMass_pos (T := ∅) (G := G)
    (Finset.empty_subset U) (independent_mono hTI (Finset.empty_subset T)) hq0 hq1
  field_simp

theorem conditionalContainment_nonneg {q : ℝ} {U T : Finset V} {G : Hypergraph V}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ conditionalContainment q U G T := by
  unfold conditionalContainment
  exact div_nonneg (qMass_nonneg hq0 hq1 _ _) (qMass_nonneg hq0 hq1 _ _)

theorem extensionProbability_nonneg {q : ℝ} {U T L : Finset V} {G : Hypergraph V}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ extensionProbability q U G T L := by
  unfold extensionProbability
  exact div_nonneg (qMass_nonneg hq0 hq1 _ _) (qMass_nonneg hq0 hq1 _ _)

theorem threshold_nonneg {q α : ℝ} (hq : 0 ≤ q) (hα : α ≤ 1) (T : Finset V) :
    0 ≤ threshold q α T := by
  exact pow_nonneg (mul_nonneg (sub_nonneg.mpr hα) hq) _

/-- The elementary real inequality which supplies the `qn / α` fingerprint bound. -/
theorem card_bound_of_pow_le {q α : ℝ} {n t : ℕ}
    (hq : 0 < q) (hqα : q ≤ α) (hα : α < 1)
    (hpow : (1 - q) ^ n ≤ (1 - α) ^ t) :
    α * t ≤ q * n := by
  by_contra hcard
  have hcard' : q * (n : ℝ) < α * (t : ℝ) := lt_of_not_ge hcard
  have hq1 : q < 1 := lt_of_le_of_lt hqα hα
  have hratio : 1 ≤ α / q := by
    exact (le_div_iff₀ hq).2 (by simpa using hqα)
  have hbern0 := one_add_mul_self_le_rpow_one_add (s := -q)
    (p := α / q) (by linarith) hratio
  have hbern : 1 - α ≤ (1 - q) ^ (α / q) := by
    convert hbern0 using 1 <;> field_simp <;> ring
  have hpowbern : (1 - α) ^ t ≤ ((1 - q) ^ (α / q)) ^ t := by
    exact pow_le_pow_left₀ (sub_nonneg.mpr hα.le) hbern t
  have hexp : (n : ℝ) < (α / q) * (t : ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hq).2 (by nlinarith)
  have hrpow : (1 - q) ^ ((α / q) * (t : ℝ)) < (1 - q) ^ (n : ℝ) :=
    Real.strictAnti_rpow_of_base_lt_one (sub_pos.mpr hq1) (by linarith [hq]) hexp
  have hcontra : (1 - α) ^ t < (1 - q) ^ n := by
    calc
      (1 - α) ^ t ≤ ((1 - q) ^ (α / q)) ^ t := hpowbern
      _ = (1 - q) ^ ((α / q) * (t : ℝ)) :=
        (Real.rpow_mul_natCast (sub_nonneg.mpr hq1.le) (α / q) t).symm
      _ < (1 - q) ^ (n : ℝ) := hrpow
      _ = (1 - q) ^ n := Real.rpow_natCast _ _
  exact (not_lt_of_ge hpow) hcontra

/-- The size estimate for any fingerprint satisfying the defining probability inequality. -/
theorem fingerprint_card_bound {q α : ℝ} {U T : Finset V} {G : Hypergraph V}
    (hq : 0 < q) (hqα : q ≤ α) (hα : α < 1)
    (hTU : T ⊆ U) (hTI : Independent G T)
    (hgood : conditionalContainment q U G T ≤ threshold q α T) :
    α * T.card ≤ q * U.card := by
  have hq1 : q < 1 := lt_of_le_of_lt hqα hα
  have hdenpos : 0 < independentContainingMass q U G ∅ :=
    independentContainingMass_pos (Finset.empty_subset U)
      (independent_mono hTI (Finset.empty_subset T)) hq hq1
  have hevent : independentContainingEvent U G ∅ ⊆ U.powerset := by
    intro X hX
    exact Finset.mem_powerset.mpr (mem_independentContainingEvent.mp hX).1
  have hdenle : independentContainingMass q U G ∅ ≤ 1 := by
    exact qMass_le_one hq.le hq1.le U _ hevent
  have hw0 : 0 ≤ subsetWeight q U T := subsetWeight_nonneg hq.le hq1.le U T
  have hw_le_cond : subsetWeight q U T ≤ conditionalContainment q U G T := by
    unfold conditionalContainment
    apply (le_div_iff₀ hdenpos).2
    calc
      subsetWeight q U T * independentContainingMass q U G ∅ ≤
          subsetWeight q U T := mul_le_of_le_one_right hw0 hdenle
      _ ≤ independentContainingMass q U G T :=
        subsetWeight_le_independentContainingMass hTU hTI hq.le hq1.le
  have hw_le : subsetWeight q U T ≤ threshold q α T := hw_le_cond.trans hgood
  have hcancel : (1 - q) ^ (U.card - T.card) ≤ (1 - α) ^ T.card := by
    have hqpow : 0 < q ^ T.card := pow_pos hq _
    apply le_of_mul_le_mul_left _ hqpow
    simpa [subsetWeight, threshold, mul_pow, mul_comm, mul_left_comm, mul_assoc] using hw_le
  have hpow : (1 - q) ^ U.card ≤ (1 - α) ^ T.card := by
    refine (pow_le_pow_of_le_one (by linarith [hq]) (by linarith [hq])
      (Nat.sub_le U.card T.card)).trans hcancel
  exact card_bound_of_pow_le hq hqα hα hpow

/-- The nonempty low-conditional-probability extensions of a fingerprint. -/
noncomputable def badExtensions (q α : ℝ) (U : Finset V) (G : Hypergraph V)
    (T : Finset V) : Hypergraph V := by
  classical
  exact (U \ T).powerset.filter fun L ↦
    L.Nonempty ∧ extensionProbability q U G T L ≤ threshold q α L

@[simp] theorem mem_badExtensions {q α : ℝ} {U T L : Finset V} {G : Hypergraph V} :
    L ∈ badExtensions q α U G T ↔
      L ⊆ U \ T ∧ L.Nonempty ∧
        extensionProbability q U G T L ≤ threshold q α L := by
  classical
  simp [badExtensions, and_assoc]

/-- A finite output package for the conditional-probability decomposition. -/
structure Decomposition (q α : ℝ) (U : Finset V) (G : Hypergraph V)
    (I : Finset V) where
  fingerprint : Finset V
  fingerprint_subset : fingerprint ⊆ I
  fingerprint_supported : fingerprint ⊆ U
  fingerprint_card : α * fingerprint.card ≤ q * U.card
  cover : Hypergraph V
  cover_eq : cover = badExtensions q α U G fingerprint
  cover_supported : ∀ L ∈ cover, L ⊆ U \ fingerprint
  cover_nonempty : ∀ L ∈ cover, L.Nonempty
  independent_cover : Independent cover I
  covers : ∀ E ∈ G, ∃ L ∈ cover, L ⊆ E
  conditional_large : ∀ L, L ⊆ U \ fingerprint → L.Nonempty → L ∉ cover →
    threshold q α L < extensionProbability q U G fingerprint L

/-- The probability inequality used to select a fingerprint. -/
def IsFingerprintCandidate (q α : ℝ) (U : Finset V) (G : Hypergraph V)
    (T : Finset V) : Prop :=
  conditionalContainment q U G T ≤ threshold q α T

/-- All candidate fingerprints contained in `I`. -/
noncomputable def fingerprintCandidates (q α : ℝ) (U : Finset V)
    (G : Hypergraph V) (I : Finset V) : Finset (Finset V) := by
  classical
  exact I.powerset.filter (IsFingerprintCandidate q α U G)

@[simp] theorem mem_fingerprintCandidates {q α : ℝ} {U I T : Finset V}
    {G : Hypergraph V} :
    T ∈ fingerprintCandidates q α U G I ↔
      T ⊆ I ∧ IsFingerprintCandidate q α U G T := by
  classical
  simp [fingerprintCandidates]

theorem threshold_union_of_disjoint {q α : ℝ} {T L : Finset V}
    (hdisj : Disjoint T L) :
    threshold q α (T ∪ L) = threshold q α T * threshold q α L := by
  rw [threshold, threshold, threshold, Finset.card_union_of_disjoint hdisj, pow_add]

/--
Conditional-probability fingerprint decomposition (the corrected form of Theorem 4.3).

The assumption `∅ ∉ G` is forced by the existence of the independent input `I`, but is
listed explicitly so the positivity witness for the conditioning event is transparent.  The
strict conclusion is restricted to nonempty `L`.
-/
theorem decompose_nonempty (q α : ℝ) (U : Finset V) (G : Hypergraph V)
    (I : Finset V) (hq : 0 < q) (hqα : q ≤ α) (hα : α < 1)
    (hGU : SupportedOn G U) (hIU : I ⊆ U) (hII : Independent G I) :
    Nonempty (Decomposition q α U G I) := by
  classical
  have hq1 : q < 1 := lt_of_le_of_lt hqα hα
  have hEmptyIndependent : Independent G ∅ :=
    independent_mono hII (Finset.empty_subset I)
  have hdenpos : 0 < independentContainingMass q U G ∅ :=
    independentContainingMass_pos (Finset.empty_subset U) hEmptyIndependent hq hq1
  have hEmptyCandidate :
      ∅ ∈ fingerprintCandidates q α U G I := by
    rw [mem_fingerprintCandidates]
    refine ⟨Finset.empty_subset I, ?_⟩
    unfold IsFingerprintCandidate conditionalContainment
    rw [div_self hdenpos.ne', threshold_empty]
  obtain ⟨T, hTC, hmax⟩ :=
    (fingerprintCandidates q α U G I).exists_max_image Finset.card
      ⟨∅, hEmptyCandidate⟩
  have hTI : T ⊆ I := (mem_fingerprintCandidates.mp hTC).1
  have hTU : T ⊆ U := hTI.trans hIU
  have hTIndependent : Independent G T := independent_mono hII hTI
  have hTgood : conditionalContainment q U G T ≤ threshold q α T :=
    (mem_fingerprintCandidates.mp hTC).2
  let C : Hypergraph V := badExtensions q α U G T
  have hmaximal : ∀ L, L ∈ C → L ⊆ I → False := by
    intro L hLC hLI
    have hLdata := mem_badExtensions.mp hLC
    have hLUdiff : L ⊆ U \ T := hLdata.1
    have hLne : L.Nonempty := hLdata.2.1
    have hLbad : extensionProbability q U G T L ≤ threshold q α L := hLdata.2.2
    have hdisj : Disjoint T L := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxT hxL
      exact (Finset.mem_sdiff.mp (hLUdiff hxL)).2 hxT
    have hUnionSubset : T ∪ L ⊆ I := Finset.union_subset hTI hLI
    have hUnionIndependent : Independent G (T ∪ L) := independent_mono hII hUnionSubset
    have hUnionGood : IsFingerprintCandidate q α U G (T ∪ L) := by
      unfold IsFingerprintCandidate
      calc
        conditionalContainment q U G (T ∪ L) =
            conditionalContainment q U G T * extensionProbability q U G T L :=
          conditional_chain_rule hTU hTIndependent hq hq1
        _ ≤ threshold q α T * threshold q α L := by
          exact mul_le_mul hTgood hLbad
            (extensionProbability_nonneg hq.le hq1.le)
            (threshold_nonneg hq.le hα.le T)
        _ = threshold q α (T ∪ L) := (threshold_union_of_disjoint hdisj).symm
    have hUnionCandidate : T ∪ L ∈ fingerprintCandidates q α U G I :=
      mem_fingerprintCandidates.mpr ⟨hUnionSubset, hUnionGood⟩
    have hcardle : (T ∪ L).card ≤ T.card := hmax _ hUnionCandidate
    have hcardlt : T.card < (T ∪ L).card := by
      rw [Finset.card_union_of_disjoint hdisj]
      exact Nat.lt_add_of_pos_right hLne.card_pos
    exact (not_lt_of_ge hcardle) hcardlt
  have hCoverIndependent : Independent C I := by
    intro L hLC hLI
    exact hmaximal L hLC hLI
  have hCovers : ∀ E ∈ G, ∃ L ∈ C, L ⊆ E := by
    intro E hEG
    let L := E \ T
    have hEU : E ⊆ U := hGU E hEG
    have hLsubset : L ⊆ E := Finset.sdiff_subset
    have hLdiff : L ⊆ U \ T := Finset.sdiff_subset_sdiff hEU Finset.Subset.rfl
    have hLne : L.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
      intro hET
      exact hTIndependent E hEG hET
    have hmass0 : independentContainingMass q U G (T ∪ L) = 0 := by
      unfold independentContainingMass qMass
      have hevent : independentContainingEvent U G (T ∪ L) = ∅ := by
        ext X
        constructor
        · intro hX
          have hXdata := mem_independentContainingEvent.mp hX
          have hEUnion : E ⊆ T ∪ L := by
            intro x hxE
            by_cases hxT : x ∈ T
            · exact Finset.mem_union_left L hxT
            · exact Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨hxE, hxT⟩)
          exact (hXdata.2.1 E hEG (hEUnion.trans hXdata.2.2)).elim
        · intro hX
          simpa using hX
      rw [hevent]
      simp
    have hExt0 : extensionProbability q U G T L = 0 := by
      simp [extensionProbability, hmass0]
    have hLmem : L ∈ C := by
      rw [show C = badExtensions q α U G T by rfl, mem_badExtensions]
      refine ⟨hLdiff, hLne, ?_⟩
      rw [hExt0]
      exact threshold_nonneg hq.le hα.le L
    exact ⟨L, hLmem, hLsubset⟩
  refine
    ⟨{ fingerprint := T
       fingerprint_subset := hTI
       fingerprint_supported := hTU
       fingerprint_card := fingerprint_card_bound hq hqα hα hTU hTIndependent hTgood
       cover := C
       cover_eq := rfl
       cover_supported := ?_
       cover_nonempty := ?_
       independent_cover := hCoverIndependent
       covers := hCovers
       conditional_large := ?_ }⟩
  · intro L hLC
    exact (mem_badExtensions.mp hLC).1
  · intro L hLC
    exact (mem_badExtensions.mp hLC).2.1
  · intro L hLsub hLne hLnot
    have hnle : ¬ extensionProbability q U G T L ≤ threshold q α L := by
      intro hle
      apply hLnot
      exact mem_badExtensions.mpr ⟨hLsub, hLne, hle⟩
    exact lt_of_not_ge hnle

/-- A chosen decomposition; all its specification fields are proof-relevant projections. -/
noncomputable def decompose (q α : ℝ) (U : Finset V) (G : Hypergraph V)
    (I : Finset V) (hq : 0 < q) (hqα : q ≤ α) (hα : α < 1)
    (hGU : SupportedOn G U) (hIU : I ⊆ U) (hII : Independent G I) :
    Decomposition q α U G I :=
  Classical.choice (decompose_nonempty q α U G I hq hqα hα hGU hIU hII)

/-- The `α = 1/2` form used in the specialised container theorem. -/
theorem exists_half_fingerprint (q : ℝ) (U : Finset V) (G : Hypergraph V)
    (I : Finset V) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hGU : SupportedOn G U) (hIU : I ⊆ U) (hII : G.IsIndependent I) :
    ∃ T : Finset V,
      (T.card : ℝ) ≤ 2 * q * U.card ∧ T ⊆ I ∧
        (badExtensions q (1 / 2) U G T).IsIndependent I := by
  let d := decompose q (1 / 2) U G I hq hqhalf (by norm_num) hGU hIU hII
  refine ⟨d.fingerprint, ?_, d.fingerprint_subset, ?_⟩
  · have hcard := d.fingerprint_card
    norm_num at hcard ⊢
    nlinarith
  · rw [← d.cover_eq]
    exact d.independent_cover

/-- A natural-number cutoff wrapper for `exists_half_fingerprint`. -/
theorem exists_half_fingerprint_nat (q : ℝ) (U : Finset V) (G : Hypergraph V)
    (I : Finset V) (b : ℕ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hGU : SupportedOn G U) (hIU : I ⊆ U) (hII : G.IsIndependent I)
    (hcut : 2 * q * U.card ≤ b) :
    ∃ T : Finset V, T.card ≤ b ∧ T ⊆ I ∧
      (badExtensions q (1 / 2) U G T).IsIndependent I := by
  obtain ⟨T, hTcard, hTI, hInd⟩ :=
    exists_half_fingerprint q U G I hq hqhalf hGU hIU hII
  refine ⟨T, ?_, hTI, hInd⟩
  exact_mod_cast hTcard.trans hcut

end

end ConditionalDecomposition
end Erdos565
