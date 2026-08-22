/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ExternalCountTransport
import ErdosProblems.Erdos1165.ExternalHLOZOnePoint

/-!
# Weighted one-site transport for the deleted external walk

This file supplies the conditional one-site estimate used as the first-shell
input in HLOZ Proposition 4.8.  The argument first proves the usual first-hit
factorization for the IID retained-block walk.  It then passes the inequality
through the exact finite thinning of `ExternalCountTransport`, including the
random number of retained pairs and the shifted orientation.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalWeightedOnePoint

open LazyDecomposition ExternalWalk ExternalOnePoint ExternalRenewal
open ExternalProposition44 ExternalThickCount ExternalCountTransport
open ExternalHLOZOnePoint
open ExternalGreenRenewal

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## First occurrence in a finite list -/

/-- `x` occurs for the first time at list index `t`. -/
def firstValueAt {α : Type*} [BEq α] (p : List α) (x : α) (t : ℕ) : Prop :=
  p.idxOf x = t ∧ x ∈ p

lemma firstValueAt_unique {α : Type*} [BEq α] {p : List α} {x : α}
    {s t : ℕ} (hs : firstValueAt p x s) (ht : firstValueAt p x t) : s = t := by
  exact hs.1.symm.trans ht.1

lemma exists_firstValueAt_iff_mem {α : Type*} [BEq α] [LawfulBEq α]
    (p : List α) (x : α) :
    (∃ t ∈ Finset.range p.length, firstValueAt p x t) ↔ x ∈ p := by
  constructor
  · rintro ⟨t, ht, hfirst⟩
    exact hfirst.2
  · intro hx
    exact ⟨p.idxOf x, Finset.mem_range.mpr (List.idxOf_lt_length_iff.mpr hx), rfl, hx⟩

/-- Once the first occurrence is fixed, a global multiplicity lower bound is
already a lower bound in the suffix beginning at that occurrence. -/
lemma suffixGoodAt_of_firstValueAt {α : Type*} [BEq α] [LawfulBEq α]
    (p : List α) (x : α) (k t : ℕ)
    (hfirst : firstValueAt p x t) (hk : k ≤ p.count x) :
    suffixGoodAt p k t := by
  have ht : t < p.length := by
    rw [← hfirst.1]
    exact List.idxOf_lt_length_iff.mpr hfirst.2
  have hget : p[t] = x := by
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hfirst.2
    have hval : p[p.idxOf x] = x := List.getElem_idxOf hidx
    simpa only [hfirst.1] using hval
  have hnot : x ∉ p.take t := by
    intro hx
    have hlt := (List.mem_take_iff_idxOf_lt hfirst.2).mp hx
    rw [hfirst.1] at hlt
    exact (Nat.lt_irrefl t hlt)
  have hcount : p.count x = (p.drop t).count x := by
    nth_rw 1 [← List.take_append_drop t p]
    rw [List.count_append, List.count_eq_zero.mpr hnot, zero_add]
  unfold suffixGoodAt
  rw [List.drop_eq_getElem_cons ht, hget]
  have hdrop : p.drop t = x :: p.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons ht, hget]
  rw [hcount, hdrop] at hk
  exact hk

lemma firstValueAt_prefix_iff {α : Type*} [BEq α] [LawfulBEq α]
    {p q : List α} (hpq : p <+: q) {x : α} {t : ℕ}
    (hlen : p.length = t + 1) :
    firstValueAt p x t ↔ firstValueAt q x t := by
  constructor
  · intro hp
    refine ⟨?_, hpq.mem hp.2⟩
    exact (hpq.idxOf_eq_of_mem hp.2).symm.trans hp.1
  · intro hq
    have htq : t < q.length := by
      rw [← hq.1]
      exact List.idxOf_lt_length_iff.mpr hq.2
    have htp : t < p.length := by omega
    have hgetq : q[t] = x := by
      have hidx : q.idxOf x < q.length := List.idxOf_lt_length_iff.mpr hq.2
      have hval : q[q.idxOf x] = x := List.getElem_idxOf hidx
      simpa only [hq.1] using hval
    have hgetp : p[t] = x := by
      exact (hpq.getElem htp).trans hgetq
    have hxp : x ∈ p := by
      have hmem := List.getElem_mem (l := p) (n := t) htp
      simpa only [hgetp] using hmem
    exact ⟨(hpq.idxOf_eq_of_mem hxp).trans hq.1, hxp⟩

/-! ## Weighted first-hit bound for the IID retained-block chain -/

def externalFirstValueAt (o : Orientation) (x : Point) (n t : ℕ) :
    Set (ℕ → RetainedBlock o) :=
  {η | firstValueAt (externalPositionList o η n) x t}

def finiteExternalFirstValueAt (o : Orientation) (x : Point) (t : ℕ) :
    Set (Fin t → RetainedBlock o) :=
  {u | firstValueAt (finiteExternalPositionList o u) x t}

def finiteExternalOriginLarge (o : Orientation) (r k : ℕ) :
    Set (Fin r → RetainedBlock o) :=
  {u | k ≤ listLocalTime (finiteExternalPositionList o u) 0}

lemma listLocalTime_externalPositionList_zero (o : Orientation)
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    listLocalTime (externalPositionList o η n) 0 =
      externalOriginLocalTime o η n := by
  unfold externalPositionList
  rw [← finiteLocalTime_eq_listLocalTime]
  unfold externalOriginLocalTime
  rw [Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if externalPosition o η j = 0 then 1 else 0)]

lemma externalFirstValueAt_eq_prefix_preimage (o : Orientation)
    (x : Point) (n t : ℕ) (ht : t < n + 1) :
    externalFirstValueAt o x n t =
      externalPrefix o t ⁻¹' finiteExternalFirstValueAt o x t := by
  ext η
  change firstValueAt (externalPositionList o η n) x t ↔
    firstValueAt (finiteExternalPositionList o (externalPrefix o t η)) x t
  rw [finiteExternalPositionList_externalPrefix]
  symm
  apply firstValueAt_prefix_iff
  · exact externalPositionList_prefix o η (Nat.le_of_lt_succ ht)
  · simp

lemma suffixGoodAt_eq_block_preimage (o : Orientation) (n k t : ℕ)
    (ht : t < n + 1) :
    {η : ℕ → RetainedBlock o |
        suffixGoodAt (externalPositionList o η n) k t} =
      externalBlock o t (n - t) ⁻¹' finiteExternalOriginLarge o (n - t) k := by
  ext η
  change suffixGoodAt (externalPositionList o η n) k t ↔ _
  rw [suffixGoodAt_externalPositionList_iff o η n k t ht]
  change k ≤ externalOriginLocalTime o
      (ExternalProposition44.externalShift (o := o) t η) (n - t) ↔
    k ≤ listLocalTime
      (finiteExternalPositionList o (externalBlock o t (n - t) η)) 0
  have hprefix : externalBlock o t (n - t) η =
      externalPrefix o (n - t)
        (ExternalProposition44.externalShift (o := o) t η) := rfl
  rw [hprefix, finiteExternalPositionList_externalPrefix]
  rw [listLocalTime_externalPositionList_zero]

lemma externalBlocks_firstValueAt_inter_suffixGoodAt_le
    (o : Orientation) (x : Point) (n k t : ℕ) (q : ℝ≥0∞)
    (ht : t < n + 1)
    (hone : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η n} ≤ q) :
    externalBlocks o
        (externalFirstValueAt o x n t ∩
          {η | suffixGoodAt (externalPositionList o η n) k t}) ≤
      q * externalBlocks o (externalFirstValueAt o x n t) := by
  have htn : t ≤ n := Nat.le_of_lt_succ ht
  rw [externalFirstValueAt_eq_prefix_preimage o x n t ht,
    suffixGoodAt_eq_block_preimage o n k t ht]
  rw [measure_externalPrefix_inter_externalBlock]
  have htail : externalBlockLaw o (n - t)
      (finiteExternalOriginLarge o (n - t) k) ≤ q := by
    have hmass : externalBlockLaw o (n - t)
        (finiteExternalOriginLarge o (n - t) k) =
        externalBlocks o {η |
          k ≤ externalOriginLocalTime o η (n - t)} := by
      rw [← externalBlocks_map_externalPrefix]
      rw [Measure.map_apply (measurable_externalPrefix o (n - t))
        (Set.to_countable (finiteExternalOriginLarge o (n - t) k)).measurableSet]
      congr 1
      ext η
      simp only [Set.mem_ofPred_eq]
      change k ≤ listLocalTime
          (finiteExternalPositionList o (externalPrefix o (n - t) η)) 0 ↔ _
      rw [finiteExternalPositionList_externalPrefix]
      rw [listLocalTime_externalPositionList_zero]
    rw [hmass]
    exact (measure_mono fun η hη ↦
      hη.trans (externalOriginLocalTime_mono o η (Nat.sub_le n t))).trans hone
  calc
    externalBlockLaw o t (finiteExternalFirstValueAt o x t) *
        externalBlockLaw o (n - t) (finiteExternalOriginLarge o (n - t) k) ≤
      externalBlockLaw o t (finiteExternalFirstValueAt o x t) * q := by
        gcongr
    _ = q * externalBlocks o
        (externalPrefix o t ⁻¹' finiteExternalFirstValueAt o x t) := by
      rw [mul_comm]
      congr 1
      rw [← externalBlocks_map_externalPrefix]
      rw [Measure.map_apply (measurable_externalPrefix o t)
        (Set.to_countable (finiteExternalFirstValueAt o x t)).measurableSet]

theorem externalBlocks_weighted_oneSite (o : Orientation)
    (n k : ℕ) (q : ℝ≥0∞)
    (hone : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η n} ≤ q) (x : Point) :
    externalBlocks o {η |
        x ∈ (externalPositionList o η n).toFinset ∧
          k ≤ listLocalTime (externalPositionList o η n) x} ≤
      q * externalBlocks o {η |
        x ∈ (externalPositionList o η n).toFinset} := by
  let H : ℕ → Set (ℕ → RetainedBlock o) :=
    fun t ↦ externalFirstValueAt o x n t
  let S : ℕ → Set (ℕ → RetainedBlock o) :=
    fun t ↦ {η | suffixGoodAt (externalPositionList o η n) k t}
  have hcand : {η : ℕ → RetainedBlock o |
        x ∈ (externalPositionList o η n).toFinset ∧
          k ≤ listLocalTime (externalPositionList o η n) x} ⊆
      ⋃ t ∈ Finset.range (n + 1), H t ∩ S t := by
    intro η hη
    have hx : x ∈ externalPositionList o η n := by simpa using hη.1
    obtain ⟨t, ht, hfirst⟩ :=
      (exists_firstValueAt_iff_mem (externalPositionList o η n) x).2 hx
    rw [Set.mem_iUnion₂]
    refine ⟨t, ?_, hfirst, ?_⟩
    · simpa using ht
    · exact suffixGoodAt_of_firstValueAt _ x k t hfirst hη.2
  have hdis : Set.PairwiseDisjoint (Finset.range (n + 1)) H := by
    intro a ha b hb hab
    change Disjoint (H a) (H b)
    rw [Set.disjoint_left]
    intro η hηa hηb
    exact hab (firstValueAt_unique hηa hηb)
  have hmeas : ∀ t ∈ Finset.range (n + 1), MeasurableSet (H t) := by
    intro t ht
    rw [show H t = externalPrefix o t ⁻¹'
        finiteExternalFirstValueAt o x t by
      exact externalFirstValueAt_eq_prefix_preimage o x n t
        (by simpa using Finset.mem_range.mp ht)]
    exact (Set.to_countable _).measurableSet.preimage (measurable_externalPrefix o t)
  have hmember : {η : ℕ → RetainedBlock o |
        x ∈ (externalPositionList o η n).toFinset} =
      ⋃ t ∈ Finset.range (n + 1), H t := by
    ext η
    simp only [List.mem_toFinset, Set.mem_ofPred_eq, Set.mem_iUnion, H,
      externalFirstValueAt]
    constructor
    · intro hx
      obtain ⟨t, ht, hfirst⟩ :=
        (exists_firstValueAt_iff_mem (externalPositionList o η n) x).2 hx
      rw [externalPositionList_length] at ht
      exact ⟨t, ht, hfirst⟩
    · rintro ⟨t, ht, hfirst⟩
      apply (exists_firstValueAt_iff_mem (externalPositionList o η n) x).1
      rw [externalPositionList_length]
      exact ⟨t, ht, hfirst⟩
  calc
    externalBlocks o {η |
        x ∈ (externalPositionList o η n).toFinset ∧
          k ≤ listLocalTime (externalPositionList o η n) x} ≤
        externalBlocks o (⋃ t ∈ Finset.range (n + 1), H t ∩ S t) :=
      measure_mono hcand
    _ ≤ ∑ t ∈ Finset.range (n + 1), externalBlocks o (H t ∩ S t) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.range (n + 1),
        q * externalBlocks o (H t) := by
      exact Finset.sum_le_sum fun t ht ↦
        externalBlocks_firstValueAt_inter_suffixGoodAt_le o x n k t q
          (by simpa using Finset.mem_range.mp ht) hone
    _ = q * externalBlocks o (⋃ t ∈ Finset.range (n + 1), H t) := by
      rw [measure_biUnion_finset hdis hmeas, Finset.mul_sum]
    _ = q * externalBlocks o {η |
        x ∈ (externalPositionList o η n).toFinset} := by rw [hmember]

/-! ## Passing the weighted inequality through finite thinning -/

def retainedMemberProperty (o : Orientation) (x : Point) (j : ℕ)
    (v : Fin j → RetainedBlock o) : Prop :=
  x ∈ (finiteExternalPositionList o v).toFinset

def retainedCandidateProperty (o : Orientation) (x : Point) (k j : ℕ)
    (v : Fin j → RetainedBlock o) : Prop :=
  retainedMemberProperty o x j v ∧
    k ≤ listLocalTime (finiteExternalPositionList o v) x

def retainedPropertyFinset (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (j : ℕ) :
    Finset (Fin j → RetainedBlock o) :=
  Finset.univ.filter (B j)

lemma card_retainedPropertyFinset (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (j : ℕ) :
    (retainedPropertyFinset o B j).card =
      Fintype.card (GoodRetainedWords o B j) := by
  calc
    (retainedPropertyFinset o B j).card =
        Nat.card ↥(retainedPropertyFinset o B j) :=
      (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (GoodRetainedWords o B j) :=
      Nat.card_congr (filterUnivSubtypeEquiv (B j))
    _ = _ := Nat.card_eq_fintype_card

theorem externalBlocks_retainedProperty_mass (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (j : ℕ) :
    externalBlocks o {η | B j (externalPrefix o j η)} =
      (Fintype.card (GoodRetainedWords o B j) : ℝ≥0∞) / 15 ^ j := by
  let G := retainedPropertyFinset o B j
  have hG : MeasurableSet (G : Set (Fin j → RetainedBlock o)) := by
    measurability
  calc
    externalBlocks o {η | B j (externalPrefix o j η)} =
        (externalBlocks o).map (externalPrefix o j) G := by
      rw [Measure.map_apply (measurable_externalPrefix o j) hG]
      congr 1
      ext η
      simp [G, retainedPropertyFinset]
    _ = externalBlockLaw o j G := by rw [externalBlocks_map_externalPrefix]
    _ = ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin j → RetainedBlock o)) G := by
      rw [externalBlockLaw_eq_uniform]
    _ = (G.card : ℝ≥0∞) / 15 ^ j := by
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
      congr 2
      simp
    _ = _ := by rw [card_retainedPropertyFinset]

theorem card_retainedCandidate_le (o : Orientation) (x : Point)
    (j N k : ℕ) (q : ℝ≥0∞) (hjN : j ≤ N)
    (hone : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η N} ≤ q) :
    (Fintype.card
        (GoodRetainedWords o (retainedCandidateProperty o x k) j) : ℝ≥0∞) ≤
      q * Fintype.card
        (GoodRetainedWords o (retainedMemberProperty o x) j) := by
  have honej : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η j} ≤ q :=
    (measure_mono fun η hη ↦
      hη.trans (externalOriginLocalTime_mono o η hjN)).trans hone
  have hweighted := externalBlocks_weighted_oneSite o j k q honej x
  have hcandEvent : {η : ℕ → RetainedBlock o |
      x ∈ (externalPositionList o η j).toFinset ∧
        k ≤ listLocalTime (externalPositionList o η j) x} =
      {η | retainedCandidateProperty o x k j (externalPrefix o j η)} := by
    ext η
    simp only [Set.mem_ofPred_eq, retainedCandidateProperty,
      retainedMemberProperty, finiteExternalPositionList_externalPrefix]
  have hmemEvent : {η : ℕ → RetainedBlock o |
      x ∈ (externalPositionList o η j).toFinset} =
      {η | retainedMemberProperty o x j (externalPrefix o j η)} := by
    ext η
    simp only [Set.mem_ofPred_eq, retainedMemberProperty,
      finiteExternalPositionList_externalPrefix]
  rw [hcandEvent, hmemEvent,
    externalBlocks_retainedProperty_mass,
    externalBlocks_retainedProperty_mass] at hweighted
  let A : ℝ≥0∞ := Fintype.card
    (GoodRetainedWords o (retainedCandidateProperty o x k) j)
  let C : ℝ≥0∞ := Fintype.card
    (GoodRetainedWords o (retainedMemberProperty o x) j)
  let d : ℝ≥0∞ := 15 ^ j
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdtop : d ≠ ∞ := by simp [d]
  have hrearrange : q * (C / d) = (q * C) / d := by
    simp only [ENNReal.div_eq_inv_mul]
    ac_rfl
  change A / d ≤ q * (C / d) at hweighted
  rw [hrearrange, ENNReal.div_le_iff hd0 hdtop] at hweighted
  rw [ENNReal.div_mul_cancel hd0 hdtop] at hweighted
  exact hweighted

theorem card_goodBlock_candidate_le (o : Orientation) (x : Point)
    (a N k : ℕ) (q : ℝ≥0∞) (haN : a ≤ N)
    (hone : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η N} ≤ q) :
    (Fintype.card
        (GoodBlockWords o (retainedCandidateProperty o x k) a) : ℝ≥0∞) ≤
      q * Fintype.card
        (GoodBlockWords o (retainedMemberProperty o x) a) := by
  rw [card_goodBlockWords, card_goodBlockWords]
  push_cast
  calc
    ∑ j ∈ Finset.range (a + 1),
        (a.choose j : ℝ≥0∞) *
          Fintype.card (GoodRetainedWords o
            (retainedCandidateProperty o x k) j) ≤
      ∑ j ∈ Finset.range (a + 1),
        (a.choose j : ℝ≥0∞) *
          (q * Fintype.card (GoodRetainedWords o
            (retainedMemberProperty o x) j)) := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      apply card_retainedCandidate_le o x j N k q
      · exact (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans haN
      · exact hone
    _ = q * ∑ j ∈ Finset.range (a + 1),
        (a.choose j : ℝ≥0∞) *
          Fintype.card (GoodRetainedWords o
            (retainedMemberProperty o x) j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ac_rfl

def goodBlockPropertyFinset (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (a : ℕ) :
    Finset (Fin a → ExternalWalk.Block) :=
  Finset.univ.filter (HasGoodExtracted o B)

lemma card_goodBlockPropertyFinset (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (a : ℕ) :
    (goodBlockPropertyFinset o B a).card =
      Fintype.card (GoodBlockWords o B a) := by
  calc
    (goodBlockPropertyFinset o B a).card =
        Nat.card ↥(goodBlockPropertyFinset o B a) :=
      (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (GoodBlockWords o B a) :=
      Nat.card_congr (filterUnivSubtypeEquiv (HasGoodExtracted o B))
    _ = _ := Nat.card_eq_fintype_card

theorem fairSteps_hasGood_pairedSegment_mass (o : Orientation)
    (B : ∀ j, (Fin j → RetainedBlock o) → Prop) (start a : ℕ) :
    fairSteps {ω | HasGoodExtracted o B (pairedSegment start a ω)} =
      (Fintype.card (GoodBlockWords o B a) : ℝ≥0∞) / 16 ^ a := by
  let G := goodBlockPropertyFinset o B a
  have hG : MeasurableSet (G : Set (Fin a → ExternalWalk.Block)) := by
    measurability
  calc
    fairSteps {ω | HasGoodExtracted o B (pairedSegment start a ω)} =
        (fairSteps.map (pairedSegment start a)) G := by
      rw [Measure.map_apply (measurable_pairedSegment start a) hG]
      congr 1
      ext ω
      simp [G, goodBlockPropertyFinset]
    _ = ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin a → ExternalWalk.Block)) G := by
      rw [fairSteps_map_pairedSegment]
    _ = (G.card : ℝ≥0∞) / 16 ^ a := by
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
      congr 2
      simp
    _ = _ := by rw [card_goodBlockPropertyFinset]

theorem fairSteps_pairedSegment_weighted (o : Orientation) (x : Point)
    (start a N k : ℕ) (q : ℝ≥0∞) (haN : a ≤ N)
    (hone : externalBlocks o {η |
      k ≤ externalOriginLocalTime o η N} ≤ q) :
    fairSteps {ω | HasGoodExtracted o (retainedCandidateProperty o x k)
        (pairedSegment start a ω)} ≤
      q * fairSteps {ω | HasGoodExtracted o (retainedMemberProperty o x)
        (pairedSegment start a ω)} := by
  rw [fairSteps_hasGood_pairedSegment_mass,
    fairSteps_hasGood_pairedSegment_mass]
  have hcard := card_goodBlock_candidate_le o x a N k q haN hone
  have hrearrange : q *
      ((Fintype.card (GoodBlockWords o (retainedMemberProperty o x) a) : ℝ≥0∞) /
        16 ^ a) =
      (q * Fintype.card
        (GoodBlockWords o (retainedMemberProperty o x) a)) / 16 ^ a := by
    simp only [ENNReal.div_eq_inv_mul]
    ac_rfl
  rw [hrearrange]
  exact ENNReal.div_le_div_right hcard _

/-! ## Pathwise identification of one-site events -/

lemma hasGoodExtracted_retainedMember_iff (o : Orientation) (x : Point)
    {a : ℕ} (u : Fin a → ExternalWalk.Block) :
    HasGoodExtracted o (retainedMemberProperty o x) u ↔
      x ∈ (blockEndpointPath 0
        (PathInsertion.deleteRemovableBlocks o (List.ofFn u))).toFinset := by
  constructor
  · rintro ⟨j, hu, h⟩
    unfold retainedMemberProperty finiteExternalPositionList at h
    rwa [← deleteRemovableBlocks_eq_extractedWord o u hu] at h
  · intro h
    let j := (retainedIndices o u).card
    let hu : (retainedIndices o u).card = j := rfl
    refine ⟨j, hu, ?_⟩
    unfold retainedMemberProperty finiteExternalPositionList
    rwa [← deleteRemovableBlocks_eq_extractedWord o u hu]

lemma hasGoodExtracted_retainedCandidate_iff (o : Orientation)
    (x : Point) (k : ℕ) {a : ℕ} (u : Fin a → ExternalWalk.Block) :
    HasGoodExtracted o (retainedCandidateProperty o x k) u ↔
      x ∈ (blockEndpointPath 0
          (PathInsertion.deleteRemovableBlocks o (List.ofFn u))).toFinset ∧
        k ≤ listLocalTime
          (blockEndpointPath 0
            (PathInsertion.deleteRemovableBlocks o (List.ofFn u))) x := by
  constructor
  · rintro ⟨j, hu, h⟩
    unfold retainedCandidateProperty retainedMemberProperty
      finiteExternalPositionList at h
    rwa [← deleteRemovableBlocks_eq_extractedWord o u hu] at h
  · intro h
    let j := (retainedIndices o u).card
    let hu : (retainedIndices o u).card = j := rfl
    refine ⟨j, hu, ?_⟩
    unfold retainedCandidateProperty retainedMemberProperty
      finiteExternalPositionList
    rwa [← deleteRemovableBlocks_eq_extractedWord o u hu]

lemma filtered_orientedExternalPath_even_blocks (omega : StepPath) (n : ℕ) :
    (orientedExternalPath .even (pathPrefix (trajectory omega) n)).filter
        (orientationClass .even) =
      blockEndpointPath 0
        (PathInsertion.deleteRemovableBlocks .even
          (List.ofFn (pairedSegment 0 (n / 2) omega))) := by
  rw [orientedExternalPath_even_blocks, List.filter_append,
    filter_prefixRemainder_even, List.append_nil]
  apply blockPath_filter_orientationClass
  rfl

lemma filtered_orientedExternalPath_shifted_blocks (omega : StepPath)
    (n : ℕ) (hn : 0 < n) :
    (orientedExternalPath .shifted (pathPrefix (trajectory omega) n)).filter
        (orientationClass .shifted) =
      blockEndpointPath (trajectory omega 1)
        (PathInsertion.deleteRemovableBlocks .shifted
          (List.ofFn (pairedSegment 1 ((n - 1) / 2) omega))) := by
  rw [orientedExternalPath_shifted_blocks omega n hn, List.filter_append,
    filter_shiftedPrefixRemainder, List.append_nil]
  rw [blockPath_filter_orientationClass]
  exact trajectory_odd_time omega 0

lemma listLocalTime_filter_orientationClass (o : Orientation)
    (p : List Point) {x : Point} (hx : orientationClass o x) :
    listLocalTime (p.filter (orientationClass o)) x = listLocalTime p x := by
  unfold listLocalTime
  exact List.count_filter (p := fun y ↦ decide (orientationClass o y))
    (decide_eq_true hx)

lemma even_memberEvent_iff_hasGoodExtracted (omega : StepPath)
    (n : ℕ) (x : Point) :
    trajectory omega ∈ memberEvent
        (fun s ↦ orientedExternalVisitedSites .even s n) x ↔
      HasGoodExtracted .even (retainedMemberProperty .even x)
        (pairedSegment 0 (n / 2) omega) := by
  rw [hasGoodExtracted_retainedMember_iff .even x,
    ← filtered_orientedExternalPath_even_blocks]
  unfold memberEvent orientedExternalVisitedSites
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq]

lemma even_candidateEvent_iff_hasGoodExtracted (omega : StepPath)
    (n k : ℕ) (x : Point) :
    trajectory omega ∈ candidateEvent
        (fun s ↦ orientedExternalVisitedSites .even s n)
        (orientedLargeEvent .even n k) x ↔
      HasGoodExtracted .even (retainedCandidateProperty .even x k)
        (pairedSegment 0 (n / 2) omega) := by
  rw [hasGoodExtracted_retainedCandidate_iff .even x k,
    ← filtered_orientedExternalPath_even_blocks]
  unfold candidateEvent memberEvent orientedExternalVisitedSites
    orientedLargeEvent orientedExternalLocalTime
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_filter,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hxmem, hxclass⟩, hxlarge⟩
    refine ⟨⟨hxmem, hxclass⟩, ?_⟩
    simpa only [listLocalTime_filter_orientationClass .even _ hxclass] using hxlarge
  · rintro ⟨⟨hxmem, hxclass⟩, hxlarge⟩
    refine ⟨⟨hxmem, hxclass⟩, ?_⟩
    simpa only [listLocalTime_filter_orientationClass .even _ hxclass] using hxlarge

lemma blockEndpointPath_translate (start : Point)
    (bs : List PathInsertion.Block) :
    blockEndpointPath start bs =
      (blockEndpointPath 0 bs).map fun z ↦ start + z := by
  simpa only [add_zero] using blockEndpointPath_add start 0 bs

lemma mem_blockEndpointPath_translate_iff (start x : Point)
    (bs : List PathInsertion.Block) :
    x ∈ blockEndpointPath start bs ↔
      x - start ∈ blockEndpointPath 0 bs := by
  rw [blockEndpointPath_translate]
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
    have heq : z = x - start := by
      rw [← hzx]
      abel
    simpa only [heq] using hz
  · intro hx
    apply List.mem_map.mpr
    refine ⟨x - start, hx, ?_⟩
    abel

lemma listLocalTime_blockEndpointPath_translate (start x : Point)
    (bs : List PathInsertion.Block) :
    listLocalTime (blockEndpointPath start bs) x =
      listLocalTime (blockEndpointPath 0 bs) (x - start) := by
  rw [blockEndpointPath_translate]
  unfold listLocalTime
  have hcount := List.count_map_of_injective (blockEndpointPath 0 bs)
    (fun z : Point ↦ start + z) (addPoint_injective start) (x - start)
  have heq : start + (x - start) = x := by abel
  simpa only [heq] using hcount

lemma shifted_memberEvent_iff_hasGoodExtracted (omega : StepPath)
    (n : ℕ) (hn : 0 < n) (x : Point) :
    trajectory omega ∈ memberEvent
        (fun s ↦ orientedExternalVisitedSites .shifted s n) x ↔
      HasGoodExtracted .shifted
        (retainedMemberProperty .shifted (x - trajectory omega 1))
        (pairedSegment 1 ((n - 1) / 2) omega) := by
  rw [hasGoodExtracted_retainedMember_iff .shifted
    (x - trajectory omega 1)]
  simp only [List.mem_toFinset]
  rw [← mem_blockEndpointPath_translate_iff (trajectory omega 1) x]
  rw [← filtered_orientedExternalPath_shifted_blocks omega n hn]
  unfold memberEvent orientedExternalVisitedSites
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq]

lemma shifted_candidateEvent_iff_hasGoodExtracted (omega : StepPath)
    (n k : ℕ) (hn : 0 < n) (x : Point) :
    trajectory omega ∈ candidateEvent
        (fun s ↦ orientedExternalVisitedSites .shifted s n)
        (orientedLargeEvent .shifted n k) x ↔
      HasGoodExtracted .shifted
        (retainedCandidateProperty .shifted (x - trajectory omega 1) k)
        (pairedSegment 1 ((n - 1) / 2) omega) := by
  rw [hasGoodExtracted_retainedCandidate_iff .shifted
    (x - trajectory omega 1) k]
  simp only [List.mem_toFinset]
  rw [← mem_blockEndpointPath_translate_iff (trajectory omega 1) x,
    ← listLocalTime_blockEndpointPath_translate (trajectory omega 1) x]
  rw [← filtered_orientedExternalPath_shifted_blocks omega n hn]
  unfold candidateEvent memberEvent orientedExternalVisitedSites
    orientedLargeEvent orientedExternalLocalTime
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_filter,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hxmem, hxclass⟩, hxlarge⟩
    refine ⟨⟨hxmem, hxclass⟩, ?_⟩
    simpa only [listLocalTime_filter_orientationClass .shifted _ hxclass]
      using hxlarge
  · rintro ⟨⟨hxmem, hxclass⟩, hxlarge⟩
    refine ⟨⟨hxmem, hxclass⟩, ?_⟩
    simpa only [listLocalTime_filter_orientationClass .shifted _ hxclass]
      using hxlarge

end

end Erdos1165.ExternalWeightedOnePoint
