import Mathlib

/-!
# Dyadic blocks for Erdős Problem 814

This file isolates the numerical part of the dyadic decomposition in
Sauermann's proof.  A family is represented by a list of finite sets, ordered
by nonincreasing cardinality.  Level `j` consists of the positions

`2 ^ j - 1, ..., 2 ^ (j + 1) - 2`.

Thus level `j` has `2 ^ j` members, and the first `J` complete levels occupy
exactly the first `2 ^ J - 1` positions.  The results below only use the
cardinalities of the sets; no graph-theoretic hypotheses occur here.
-/

namespace Erdos814
namespace Dyadic

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The first position of zero-based dyadic level `j`. -/
def levelStart (j : ℕ) : ℕ := 2 ^ j - 1

/-- The positions belonging to zero-based dyadic level `j`. -/
def levelIndices (j : ℕ) : Finset ℕ :=
  Finset.Ico (levelStart j) (levelStart (j + 1))

/-- The actual list members in zero-based dyadic level `j`. -/
def levelMembers (C : List (Finset V)) (j : ℕ) : List (Finset V) :=
  (C.drop (levelStart j)).take (2 ^ j)

/-- The actual members in the first `J` complete levels. -/
def retainedMembers (C : List (Finset V)) (J : ℕ) : List (Finset V) :=
  C.take (levelStart J)

/-- Cardinality of the member at position `i`, and zero beyond the list. -/
def cardAt (C : List (Finset V)) (i : ℕ) : ℕ :=
  (C.getD i ∅).card

/-- The list is sorted in nonincreasing order of cardinality. -/
def Nonincreasing (C : List (Finset V)) : Prop :=
  ∀ {i j : ℕ}, i ≤ j → j < C.length → cardAt C j ≤ cardAt C i

/-- Total cardinality (with multiplicity) of the members in level `j`. -/
def levelMass (C : List (Finset V)) (j : ℕ) : ℕ :=
  ∑ i ∈ levelIndices j, cardAt C i

/-- Total cardinality of the first `J` complete levels. -/
def retainedMass (C : List (Finset V)) (J : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (levelStart J), cardAt C i

/-- Total cardinality of all list members, expressed as an indexed sum. -/
def totalMass (C : List (Finset V)) : ℕ :=
  ∑ i ∈ Finset.range C.length, cardAt C i

/-- The mass after the first `J` levels. -/
def tailMass (C : List (Finset V)) (J : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (levelStart J) C.length, cardAt C i

/-- The mass of levels `J₀, ..., J₁ - 1`. -/
def betweenMass (C : List (Finset V)) (J₀ J₁ : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (levelStart J₀) (levelStart J₁), cardAt C i

/-- The first `J` levels are present in the list. -/
def CompleteThrough (C : List (Finset V)) (J : ℕ) : Prop :=
  levelStart J ≤ C.length

/-- `J` is a maximal number of complete levels. -/
def MaximalComplete (C : List (Finset V)) (J : ℕ) : Prop :=
  CompleteThrough C J ∧ C.length < levelStart (J + 1)

lemma levelStart_zero : levelStart 0 = 0 := by
  simp [levelStart]

lemma levelStart_succ (j : ℕ) : levelStart (j + 1) = levelStart j + 2 ^ j := by
  simp only [levelStart, pow_succ]
  omega

lemma levelStart_mono : Monotone levelStart := by
  intro i j hij
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) hij) 1

lemma levelStart_le_succ (j : ℕ) : levelStart j ≤ levelStart (j + 1) :=
  levelStart_mono (Nat.le_succ j)

@[simp] lemma card_levelIndices (j : ℕ) : (levelIndices j).card = 2 ^ j := by
  simp [levelIndices, Nat.card_Ico, levelStart_succ]

lemma mem_levelIndices {i j : ℕ} :
    i ∈ levelIndices j ↔ levelStart j ≤ i ∧ i < levelStart (j + 1) := by
  simp [levelIndices]

lemma levelIndices_subset_range {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    levelIndices j ⊆ Finset.range C.length := by
  intro i hi
  rw [mem_levelIndices] at hi
  exact Finset.mem_range.2 (hi.2.trans_le hC)

@[simp] lemma length_retainedMembers {C : List (Finset V)} {J : ℕ}
    (hC : CompleteThrough C J) :
    (retainedMembers C J).length = levelStart J := by
  rw [retainedMembers, List.length_take, min_eq_left]
  exact hC

@[simp] lemma length_levelMembers {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    (levelMembers C j).length = 2 ^ j := by
  rw [levelMembers, List.length_take, List.length_drop]
  have : 2 ^ j ≤ C.length - levelStart j := by
    unfold CompleteThrough at hC
    rw [levelStart_succ] at hC
    omega
  simp [this]

lemma levelMembers_nonempty {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    levelMembers C j ≠ [] := by
  intro hnil
  have hlen := length_levelMembers hC
  rw [hnil] at hlen
  have hpow : 0 < 2 ^ j := pow_pos (by omega) _
  simp only [List.length_nil] at hlen
  omega

lemma cardAt_eq_card_getElem (C : List (Finset V)) (i : ℕ) (hi : i < C.length) :
    cardAt C i = C[i].card := by
  simp [cardAt, List.getD, hi]

lemma totalMass_eq_sum_card (C : List (Finset V)) :
    totalMass C = (C.map Finset.card).sum := by
  rw [totalMass, Finset.sum_range, ← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro i _
  simp [cardAt, List.getD_eq_getElem]

lemma retainedMass_succ (C : List (Finset V)) (j : ℕ) :
    retainedMass C (j + 1) = retainedMass C j + levelMass C j := by
  rw [retainedMass, retainedMass, levelMass, levelIndices]
  exact (Finset.sum_range_add_sum_Ico (cardAt C) (levelStart_le_succ j)).symm

lemma totalMass_eq_retained_add_tail {C : List (Finset V)} {J : ℕ}
    (hJ : CompleteThrough C J) :
    totalMass C = retainedMass C J + tailMass C J := by
  rw [totalMass, retainedMass, tailMass]
  exact (Finset.sum_range_add_sum_Ico (cardAt C) hJ).symm

lemma betweenMass_eq_retained_sub {C : List (Finset V)} {J₀ J₁ : ℕ}
    (hJJ : J₀ ≤ J₁) :
    betweenMass C J₀ J₁ = retainedMass C J₁ - retainedMass C J₀ := by
  have hadd := Finset.sum_range_add_sum_Ico (cardAt C) (levelStart_mono hJJ)
  unfold betweenMass retainedMass
  omega

lemma retained_add_between {C : List (Finset V)} {J₀ J₁ : ℕ}
    (hJJ : J₀ ≤ J₁) :
    retainedMass C J₀ + betweenMass C J₀ J₁ = retainedMass C J₁ := by
  rw [betweenMass_eq_retained_sub hJJ, Nat.add_sub_of_le]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (levelStart_mono hJJ))

private lemma sum_le_card_mul {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, f i ≤ b) :
    s.sum f ≤ s.card * b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_le : f a ≤ b := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, f i ≤ b := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      calc
        f a + s.sum f ≤ b + s.card * b := Nat.add_le_add ha_le hsum
        _ = (s.card + 1) * b := by ring

private lemma card_mul_le_sum {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, b ≤ f i) :
    s.card * b ≤ s.sum f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_ge : b ≤ f a := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, b ≤ f i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      calc
        (s.card + 1) * b = b + s.card * b := by ring
        _ ≤ f a + s.sum f := Nat.add_le_add ha_ge hsum

lemma levelMass_succ_le_two_mul (C : List (Finset V)) (j : ℕ)
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C (j + 2)) :
    levelMass C (j + 1) ≤ 2 * levelMass C j := by
  let b := levelStart (j + 1)
  let x := cardAt C b
  have hb_lt : b < C.length := by
    have hb_step : b < levelStart (j + 2) := by
      rw [show j + 2 = (j + 1) + 1 by omega, levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hb_step.trans_le hcomplete
  have hnext : levelMass C (j + 1) ≤ (levelIndices (j + 1)).card * x := by
    apply sum_le_card_mul
    intro i hi
    rw [mem_levelIndices] at hi
    exact hord hi.1 (hi.2.trans_le hcomplete)
  have hcurrent : (levelIndices j).card * x ≤ levelMass C j := by
    apply card_mul_le_sum
    intro i hi
    rw [mem_levelIndices] at hi
    exact hord (Nat.le_of_lt hi.2) hb_lt
  simp only [card_levelIndices] at hnext hcurrent
  calc
    levelMass C (j + 1) ≤ 2 ^ (j + 1) * x := hnext
    _ = 2 * (2 ^ j * x) := by rw [pow_succ]; ring
    _ ≤ 2 * levelMass C j := Nat.mul_le_mul_left 2 hcurrent

lemma tailMass_le_retainedMass (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    tailMass C J ≤ retainedMass C J := by
  by_cases hempty : C.length = levelStart J
  · simp [tailMass, hempty]
  · have hb_lt : levelStart J < C.length := lt_of_le_of_ne hmax.1 (Ne.symm hempty)
    let x := cardAt C (levelStart J)
    have htail : tailMass C J ≤ (Finset.Ico (levelStart J) C.length).card * x := by
      apply sum_le_card_mul
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hord hi.1 hi.2
    have hretained : (Finset.range (levelStart J)).card * x ≤ retainedMass C J := by
      apply card_mul_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact hord (Nat.le_of_lt hi) hb_lt
    have hcards : (Finset.Ico (levelStart J) C.length).card ≤
        (Finset.range (levelStart J)).card := by
      simp only [Nat.card_Ico, Finset.card_range]
      have hmaxUpper := hmax.2
      rw [show levelStart (J + 1) = 2 * levelStart J + 1 by
        have hp : 0 < 2 ^ J := pow_pos (by omega) _
        simp only [levelStart, pow_succ]
        omega] at hmaxUpper
      omega
    exact htail.trans <| (Nat.mul_le_mul_right x hcards).trans hretained

lemma two_mul_retainedMass_ge_totalMass (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    totalMass C ≤ 2 * retainedMass C J := by
  rw [totalMass_eq_retained_add_tail hmax.1, two_mul]
  exact Nat.add_le_add_left (tailMass_le_retainedMass C J hord hmax) _

lemma retainedMass_ge_half_total (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    totalMass C / 2 ≤ retainedMass C J := by
  exact Nat.div_le_of_le_mul (two_mul_retainedMass_ge_totalMass C J hord hmax)

/-! ## Minimal cutoffs -/

/-- A cutoff is the least positive number of levels whose retained mass reaches `q`. -/
structure IsMinimalCutoff (C : List (Finset V)) (q J : ℕ) : Prop where
  pos : 0 < J
  reaches : q ≤ retainedMass C J
  previous_lt : retainedMass C (J - 1) < q

lemma exists_minimalCutoff (C : List (Finset V)) {q Jmax : ℕ}
    (hq : 0 < q) (hr : q ≤ retainedMass C Jmax) :
    ∃ J ≤ Jmax, IsMinimalCutoff C q J := by
  let P : ℕ → Prop := fun J ↦ q ≤ retainedMass C J
  have hex : ∃ J, P J := ⟨Jmax, hr⟩
  let J := Nat.find hex
  have hJP : P J := Nat.find_spec hex
  change q ≤ retainedMass C J at hJP
  have hJpos : 0 < J := by
    by_contra h
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos h
    have hzero : retainedMass C J = 0 := by
      simp [retainedMass, hJ0, levelStart]
    have hqzero : q ≤ 0 := hJP.trans_eq hzero
    omega
  have hJle : J ≤ Jmax := Nat.find_min' hex hr
  refine ⟨J, hJle, hJpos, hJP, ?_⟩
  by_contra hnot
  have hpred : P (J - 1) := Nat.le_of_not_gt hnot
  have := Nat.find_min' hex hpred
  omega

lemma cutoff_level_lt_two_mul (C : List (Finset V)) {q J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hcut : IsMinimalCutoff C q J) (hJ : 1 < J) :
    levelMass C (J - 1) < 2 * q := by
  have hidx : J - 2 + 1 = J - 1 := by omega
  have hcompleteIdx : J - 2 + 2 = J := by omega
  have hsucc : levelMass C (J - 1) ≤ 2 * levelMass C (J - 2) := by
    have hc : CompleteThrough C (J - 2 + 2) := by
      simpa [hcompleteIdx] using hcomplete
    have hs := levelMass_succ_le_two_mul C (J - 2) hord hc
    simpa [hidx] using hs
  have hlevel_prev : levelMass C (J - 2) ≤ retainedMass C (J - 1) := by
    have hs := retainedMass_succ C (J - 2)
    rw [hidx] at hs
    omega
  have hprev := hcut.previous_lt
  omega

lemma cutoff_retained_lt_three_mul (C : List (Finset V)) {q J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hcut : IsMinimalCutoff C q J) (hJ : 1 < J) :
    retainedMass C J < 3 * q := by
  rw [show J = (J - 1) + 1 by omega, retainedMass_succ]
  have hlevel := cutoff_level_lt_two_mul C hord hcomplete hcut hJ
  have hprev := hcut.previous_lt
  omega

lemma cutoff_tail_gt (C : List (Finset V)) {q J Jmax lower : ℕ}
    (hJJ : J ≤ Jmax)
    (hlower : lower + 3 * q ≤ retainedMass C Jmax)
    (hprefix : retainedMass C J < 3 * q) :
    lower < betweenMass C J Jmax := by
  have hadd := retained_add_between (C := C) hJJ
  omega

/-! ## A quarter of every late level -/

private lemma levelIndices_disjoint_of_lt {j l : ℕ} (hjl : j < l) :
    Disjoint (levelIndices j) (levelIndices l) := by
  rw [Finset.disjoint_left]
  intro i hij hil
  rw [mem_levelIndices] at hij hil
  have hboundary : levelStart (j + 1) ≤ levelStart l :=
    levelStart_mono (Nat.succ_le_of_lt hjl)
  omega

lemma levelIndices_disjoint {j l : ℕ} (hjl : j ≠ l) :
    Disjoint (levelIndices j) (levelIndices l) := by
  rcases lt_or_gt_of_ne hjl with hlt | hgt
  · exact levelIndices_disjoint_of_lt hlt
  · exact (levelIndices_disjoint_of_lt hgt).symm

/-- The dyadic levels from `J₀` through `J - 1` partition the corresponding
interval of list positions. -/
lemma biUnion_levelIndices_Ico {J₀ J : ℕ} (hJJ : J₀ ≤ J) :
    (Finset.Ico J₀ J).biUnion levelIndices =
      Finset.Ico (levelStart J₀) (levelStart J) := by
  induction J, hJJ using Nat.le_induction with
  | base => simp
  | @succ J hJJ ih =>
      rw [Nat.Ico_succ_right_eq_insert_Ico hJJ, Finset.biUnion_insert, ih,
        levelIndices, Finset.union_comm]
      exact Finset.Ico_union_Ico_eq_Ico (levelStart_mono hJJ) (levelStart_le_succ J)

lemma betweenMass_succ (C : List (Finset V)) {J₀ J : ℕ} (hJJ : J₀ ≤ J) :
    betweenMass C J₀ (J + 1) = betweenMass C J₀ J + levelMass C J := by
  unfold betweenMass levelMass levelIndices
  exact (Finset.sum_Ico_consecutive (cardAt C) (levelStart_mono hJJ)
    (levelStart_le_succ J)).symm

/-- A cardinality-quarter of one dyadic level has at most half the mass of
the preceding level. -/
lemma twice_selected_level_le_previous
    (C : List (Finset V)) (S : Finset ℕ) {j : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C (j + 1))
    (hj : 0 < j) (hS : S ⊆ levelIndices j)
    (hquarter : 4 * S.card ≤ 2 ^ j) :
    2 * S.sum (cardAt C) ≤ levelMass C (j - 1) := by
  let b := levelStart j
  let x := cardAt C b
  have hb_lt : b < C.length := by
    have hb_step : b < levelStart (j + 1) := by
      rw [levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hb_step.trans_le hcomplete
  have hselected : S.sum (cardAt C) ≤ S.card * x := by
    apply sum_le_card_mul
    intro i hi
    have hiLevel := hS hi
    rw [mem_levelIndices] at hiLevel
    exact hord hiLevel.1 (hiLevel.2.trans_le hcomplete)
  have hprev : (levelIndices (j - 1)).card * x ≤ levelMass C (j - 1) := by
    apply card_mul_le_sum
    intro i hi
    rw [mem_levelIndices] at hi
    have hidx : j - 1 + 1 = j := by omega
    have hib : i < b := by simpa [b, hidx] using hi.2
    exact hord hib.le hb_lt
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    calc
      2 ^ j = 2 ^ ((j - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := by ring
  have hcard : 2 * S.card ≤ 2 ^ (j - 1) := by
    rw [hpow] at hquarter
    omega
  calc
    2 * S.sum (cardAt C) ≤ 2 * (S.card * x) := Nat.mul_le_mul_left 2 hselected
    _ = (2 * S.card) * x := by ring
    _ ≤ 2 ^ (j - 1) * x := Nat.mul_le_mul_right x hcard
    _ = (levelIndices (j - 1)).card * x := by simp
    _ ≤ levelMass C (j - 1) := hprev

private lemma sum_previous_levels_add_last
    (C : List (Finset V)) {J₀ J : ℕ} (hJ₀ : 0 < J₀) (hJJ : J₀ ≤ J) :
    (Finset.Ico J₀ J).sum (fun j ↦ levelMass C (j - 1)) + levelMass C (J - 1) =
      levelMass C (J₀ - 1) + betweenMass C J₀ J := by
  induction J, hJJ using Nat.le_induction with
  | base => simp [betweenMass]
  | @succ J hJJ ih =>
      rw [Finset.sum_Ico_succ_top hJJ, betweenMass_succ C hJJ]
      have hsub : J + 1 - 1 = J := by omega
      rw [hsub]
      omega

/-- Global dyadic quarter estimate used by the coloring step: if selected
positions occupy at most one quarter of every level, twice their total mass
is absorbed by the preceding level and the full late-level mass. -/
lemma twice_selected_mass_le
    (C : List (Finset V)) (S : Finset ℕ) {J₀ J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hJ₀ : 0 < J₀) (hJJ : J₀ ≤ J)
    (hsel : S ⊆ Finset.Ico (levelStart J₀) (levelStart J))
    (hquarter : ∀ j, J₀ ≤ j → j < J →
      4 * (S ∩ levelIndices j).card ≤ 2 ^ j) :
    2 * S.sum (cardAt C) ≤ levelMass C (J₀ - 1) + betweenMass C J₀ J := by
  let levels := Finset.Ico J₀ J
  let selectedAt : ℕ → Finset ℕ := fun j ↦ S ∩ levelIndices j
  have hpair : (↑levels : Set ℕ).PairwiseDisjoint selectedAt := by
    intro j hj l hl hjl
    exact (levelIndices_disjoint hjl).mono Finset.inter_subset_right Finset.inter_subset_right
  have hunion : levels.biUnion selectedAt = S := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hij⟩
      exact (Finset.mem_inter.mp hij).1
    · intro hi
      have hiRange := hsel hi
      rw [← biUnion_levelIndices_Ico hJJ] at hiRange
      rcases Finset.mem_biUnion.mp hiRange with ⟨j, hj, hij⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hi, hij⟩⟩
  have hmassDecompose :
      S.sum (cardAt C) = levels.sum (fun j ↦ (selectedAt j).sum (cardAt C)) := by
    have hsum := Finset.sum_biUnion (f := cardAt C) hpair
    simpa [hunion] using hsum
  have hperLevel : ∀ j ∈ levels,
      2 * (selectedAt j).sum (cardAt C) ≤ levelMass C (j - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hc : CompleteThrough C (j + 1) :=
      hcomplete.trans' (levelStart_mono (by omega))
    exact twice_selected_level_le_previous C (selectedAt j) hord hc (by omega)
      Finset.inter_subset_right (hquarter j hj.1 hj.2)
  have hsumLevels :
      levels.sum (fun j ↦ 2 * (selectedAt j).sum (cardAt C)) ≤
        levels.sum (fun j ↦ levelMass C (j - 1)) := by
    exact Finset.sum_le_sum hperLevel
  have hprevious := sum_previous_levels_add_last C hJ₀ hJJ
  have hpreviousLe :
      levels.sum (fun j ↦ levelMass C (j - 1)) ≤
        levelMass C (J₀ - 1) + betweenMass C J₀ J := by
    calc
      levels.sum (fun j ↦ levelMass C (j - 1)) ≤
          levels.sum (fun j ↦ levelMass C (j - 1)) + levelMass C (J - 1) := by
            omega
      _ = levelMass C (J₀ - 1) + betweenMass C J₀ J := by
        simpa [levels] using hprevious
  rw [hmassDecompose, Finset.mul_sum]
  exact hsumLevels.trans hpreviousLe

/-! ## Averaging and the signed-shortage power estimate -/

lemma retainedMass_le_first (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J) :
    retainedMass C J ≤ levelStart J * cardAt C 0 := by
  by_cases hJ : levelStart J = 0
  · simp [retainedMass, hJ]
  · have hs : (Finset.range (levelStart J)).sum (cardAt C) ≤
        (Finset.range (levelStart J)).card * cardAt C 0 := by
      apply sum_le_card_mul
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_len : i < C.length := hi.trans_le hcomplete
      exact hord (Nat.zero_le i) hi_len
    simpa [retainedMass] using hs

lemma exists_large_member_of_retained_mass (C : List (Finset V)) {q J : ℕ}
    (hq : 0 < q) (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hmass : q ≤ retainedMass C J) :
    ∃ i < levelStart J, q ≤ levelStart J * cardAt C i := by
  have hstart : 0 < levelStart J := by
    by_contra h
    have : levelStart J = 0 := Nat.eq_zero_of_not_pos h
    have hzero : retainedMass C J = 0 := by simp [retainedMass, this]
    have hqzero : q ≤ 0 := by simpa [hzero] using hmass
    omega
  refine ⟨0, hstart, ?_⟩
  exact hmass.trans (retainedMass_le_first C J hord hcomplete)

/--
Signed form of the power estimate used in Claim 2.9.

If the mass in the first `J` levels is at least `q`, while deleting the
largest member is known to be too small in the precise sense
`t * |C[0]| < q`, then `t < 2 ^ J`.  This statement also handles `t ≤ 0`
without a separate natural-number subtraction convention.
-/
lemma signed_shortage_lt_two_pow (C : List (Finset V)) {q J : ℕ} {t : ℤ}
    (hJ : 0 < J) (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hmass : q ≤ retainedMass C J)
    (hforbidden : t * (cardAt C 0 : ℤ) < q) :
    t < (2 ^ J : ℕ) := by
  by_contra hnot
  have hpow : ((2 ^ J : ℕ) : ℤ) ≤ t := by omega
  have hret := retainedMass_le_first C J hord hcomplete
  have hstart : levelStart J < 2 ^ J := by
    simp [levelStart, pow_pos (by omega : 0 < (2 : ℕ))]
  have hq : (q : ℤ) ≤ (levelStart J : ℤ) * (cardAt C 0 : ℤ) := by
    exact_mod_cast hmass.trans hret
  have hnonneg : (0 : ℤ) ≤ cardAt C 0 := by positivity
  have hmul : (levelStart J : ℤ) * (cardAt C 0 : ℤ) ≤
      t * (cardAt C 0 : ℤ) := by
    apply mul_le_mul_of_nonneg_right _ hnonneg
    exact (Int.ofNat_lt.2 hstart).le.trans hpow
  omega

end Dyadic
end Erdos814
