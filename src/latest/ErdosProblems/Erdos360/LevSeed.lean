import ErdosProblems.Erdos360.LevHighMultiplicity
import ErdosProblems.Erdos360.LevNumericPairing

/-!
# Lev's odd-family seed theorem

This file contains the finite reordering and numerical part of Lev's
high-multiplicity argument.  The genuinely additive input is isolated as
`HasLevSharpPrefixTheorem`: it is the sharp prefix-cardinality consequence of
Lev's multi-summand increment theorem.  Everything after that input -- sorting,
alternating the summands, balancing their diameters, applying the dense
two-summand lemma, and checking the endpoint arithmetic -- is proved here.
-/

open scoped BigOperators Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- For a CFP pool `P`, the diameter of `P.subsetSum` is the sum of all
members of `P`. -/
def levPoolMass (P : Finset ℕ) : ℕ := ∑ x ∈ P, x

/-- Sum of the pool masses in a finite list. -/
def levFamilyMass (parts : List (Finset ℕ)) : ℕ :=
  (parts.map levPoolMass).sum

@[simp] lemma levFamilyMass_nil : levFamilyMass [] = 0 := rfl

@[simp] lemma levFamilyMass_cons (P : Finset ℕ) (parts : List (Finset ℕ)) :
    levFamilyMass (P :: parts) = levPoolMass P + levFamilyMass parts := by
  simp [levFamilyMass]

lemma levPoolMass_mem_subsetSum (P : Finset ℕ) :
    levPoolMass P ∈ P.subsetSum := by
  rw [Finset.mem_subsetSum_iff]
  exact ⟨P, fun _ hx ↦ hx, rfl⟩

lemma subsetSum_subset_Icc_levPoolMass (P : Finset ℕ) :
    P.subsetSum ⊆ Finset.Icc 0 (levPoolMass P) := by
  intro s hs
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, mem_subsetSum_le_sum hs⟩

lemma card_subsetSum_le_levPoolMass_add_one (P : Finset ℕ) :
    P.subsetSum.card ≤ levPoolMass P + 1 := by
  calc
    P.subsetSum.card ≤ (Finset.Icc 0 (levPoolMass P)).card :=
      Finset.card_le_card (subsetSum_subset_Icc_levPoolMass P)
    _ = levPoolMass P + 1 := by simp

lemma length_mul_le_levFamilyMass_of_card
    {parts : List (Finset ℕ)} {n0 : ℕ}
    (hparts : ∀ P ∈ parts, n0 ≤ P.subsetSum.card) :
    parts.length * (n0 - 1) ≤ levFamilyMass parts := by
  induction parts with
  | nil => simp [levFamilyMass]
  | cons P parts ih =>
      have hP : n0 - 1 ≤ levPoolMass P := by
        have hc := hparts P (by simp)
        have hu := card_subsetSum_le_levPoolMass_add_one P
        omega
      have htail : ∀ Q ∈ parts, n0 ≤ Q.subsetSum.card := by
        intro Q hQ
        exact hparts Q (by simp [hQ])
      have hi := ih htail
      simp only [List.length_cons, Nat.succ_mul, levFamilyMass_cons]
      omega

lemma levFamilyMass_mem_levIteratedSubsetSum (parts : List (Finset ℕ)) :
    levFamilyMass parts ∈ levIteratedSubsetSum parts := by
  induction parts with
  | nil => simp [levFamilyMass, levIteratedSubsetSum]
  | cons P parts ih =>
      simp only [levFamilyMass_cons, levIteratedSubsetSum]
      exact Finset.mem_add.mpr
        ⟨levPoolMass P, levPoolMass_mem_subsetSum P,
          levFamilyMass parts, ih, rfl⟩

lemma levIteratedSubsetSum_subset_Icc_familyMass
    (parts : List (Finset ℕ)) :
    levIteratedSubsetSum parts ⊆ Finset.Icc 0 (levFamilyMass parts) := by
  induction parts with
  | nil => simp [levFamilyMass, levIteratedSubsetSum]
  | cons P parts ih =>
      intro s hs
      simp only [levIteratedSubsetSum] at hs
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hs
      have hu' := Finset.mem_Icc.mp (subsetSum_subset_Icc_levPoolMass P hu)
      have hv' := Finset.mem_Icc.mp (ih hv)
      simp only [levFamilyMass_cons]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

lemma levFamilyMass_eq_of_perm {left right : List (Finset ℕ)}
    (h : left.Perm right) : levFamilyMass left = levFamilyMass right := by
  exact (h.map levPoolMass).sum_eq

/-! ## The alternating partition -/

/-- Put positions `1,3,5,...` in the first list, positions `2,4,6,...` in
the second list, except that a final unpaired entry also goes in the second
list.  Thus an input of length `2h-1` is split into lengths `h-1` and `h`. -/
def levAlternateSplit : List α → List α × List α
  | [] => ([], [])
  | [x] => ([], [x])
  | x :: y :: rest =>
      let p := levAlternateSplit rest
      (x :: p.1, y :: p.2)

lemma levAlternateSplit_perm : ∀ xs : List α,
    xs.Perm ((levAlternateSplit xs).1 ++ (levAlternateSplit xs).2)
  | [] => by simp [levAlternateSplit]
  | [x] => by simp [levAlternateSplit]
  | x :: y :: rest => by
      simp only [levAlternateSplit]
      let p := levAlternateSplit rest
      have ih : rest.Perm (p.1 ++ p.2) := by
        simpa [p] using levAlternateSplit_perm rest
      exact ((ih.cons y).cons x).trans (by
        simpa only [List.cons_append] using (List.perm_middle.cons x).symm)

lemma levAlternateSplit_left_sublist : ∀ xs : List α,
    List.Sublist (levAlternateSplit xs).1 xs
  | [] => by simp [levAlternateSplit]
  | [x] => by simp [levAlternateSplit]
  | x :: y :: rest => by
      simp only [levAlternateSplit]
      exact ((levAlternateSplit_left_sublist rest).cons y).cons_cons x

lemma levAlternateSplit_right_sublist : ∀ xs : List α,
    List.Sublist (levAlternateSplit xs).2 xs
  | [] => by simp [levAlternateSplit]
  | [x] => by simp [levAlternateSplit]
  | x :: y :: rest => by
      simp only [levAlternateSplit]
      exact ((levAlternateSplit_right_sublist rest).cons_cons y).cons x

lemma levAlternateSplit_lengths_of_odd
    {xs : List α} {h : ℕ} (hh : 1 ≤ h)
    (hlen : xs.length = 2 * h - 1) :
    (levAlternateSplit xs).1.length = h - 1 ∧
      (levAlternateSplit xs).2.length = h := by
  induction h generalizing xs with
  | zero => omega
  | succ h ih =>
      by_cases h0 : h = 0
      · subst h
        have hxlen : xs.length = 1 := by omega
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hxlen
        simp [levAlternateSplit]
      · have hh' : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
        have hx2 : 2 ≤ xs.length := by omega
        cases xs with
        | nil => simp at hx2
        | cons x tail =>
          cases tail with
          | nil => simp at hx2
          | cons y rest =>
            have hrest : rest.length = 2 * h - 1 := by
              simp [Nat.mul_succ] at hlen
              omega
            have hi := ih hh' hrest
            simp only [levAlternateSplit, List.length_cons]
            omega

lemma levAlternateSplit_mass_bounds_of_odd
    {xs : List α} {h m : ℕ} {weight : α → ℕ}
    (hh : 1 ≤ h) (hlen : xs.length = 2 * h - 1)
    (hbound : ∀ x ∈ xs, weight x ≤ m)
    (hdesc : xs.Pairwise fun x y ↦ weight y ≤ weight x) :
    ((levAlternateSplit xs).1.map weight).sum ≤
        ((levAlternateSplit xs).2.map weight).sum + m ∧
      ((levAlternateSplit xs).2.map weight).sum ≤
        ((levAlternateSplit xs).1.map weight).sum + m := by
  induction h generalizing xs m with
  | zero => omega
  | succ h ih =>
      by_cases h0 : h = 0
      · subst h
        have hxlen : xs.length = 1 := by omega
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hxlen
        have hx := hbound x (by simp)
        simp [levAlternateSplit, hx]
      · have hh' : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
        have hx2 : 2 ≤ xs.length := by omega
        cases xs with
        | nil => simp at hx2
        | cons x tail =>
          cases tail with
          | nil => simp at hx2
          | cons y rest =>
            have hrest : rest.length = 2 * h - 1 := by
              simp [Nat.mul_succ] at hlen
              omega
            have hxy : weight y ≤ weight x := by
              exact (List.pairwise_cons.mp hdesc).1 y (by simp)
            have hrestDesc : rest.Pairwise fun u v ↦ weight v ≤ weight u :=
              (List.pairwise_cons.mp (List.pairwise_cons.mp hdesc).2).2
            have hrestBound : ∀ z ∈ rest, weight z ≤ weight y := by
              intro z hz
              exact (List.pairwise_cons.mp (List.pairwise_cons.mp hdesc).2).1 z hz
            have hi' := ih hh' hrest hrestBound hrestDesc
            have hxm : weight x ≤ m := hbound x (by simp)
            have hym : weight y ≤ m := hbound y (by simp)
            simp only [levAlternateSplit, List.map_cons, List.sum_cons] at hi' ⊢
            omega

lemma levAlternateSplit_reverse_pairwise
    {xs : List α} {r : α → α → Prop}
    (h : xs.Pairwise r) :
    ((levAlternateSplit xs).1.reverse).Pairwise (fun x y ↦ r y x) ∧
      ((levAlternateSplit xs).2.reverse).Pairwise (fun x y ↦ r y x) := by
  constructor
  · exact (h.sublist (levAlternateSplit_left_sublist xs)).reverse
  · exact (h.sublist (levAlternateSplit_right_sublist xs)).reverse

/-! ## Indexed prefix bookkeeping -/

lemma getD_mem_of_lt (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_get (l := l) (d := d) ⟨i, hi⟩]
  exact l.get_mem _

lemma sum_Icc_getD_eq_map_sum
    [AddCommMonoid β] (f : α → β) (d : α) (l : List α) :
    (∑ i ∈ Finset.Icc 1 l.length, f (l.getD (i - 1) d)) =
      (l.map f).sum := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
      simp only [List.length_append, List.length_singleton]
      rw [show l.length + 1 = l.length + 1 by rfl,
        Finset.sum_Icc_succ_top (by omega)]
      have hfront :
          (∑ i ∈ Finset.Icc 1 l.length,
              f ((l ++ [x]).getD (i - 1) d)) =
            ∑ i ∈ Finset.Icc 1 l.length, f (l.getD (i - 1) d) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiI := Finset.mem_Icc.mp hi
        rw [List.getD_append l [x] d (i - 1) (by omega)]
      rw [hfront, ih]
      have hlast : (l ++ [x]).getD l.length d = x := by
        rw [List.getD_append_right l [x] d l.length le_rfl]
        simp
      simp

/-- The exact sharp prefix-cardinality statement extracted from Lev's
multi-summand increment theorem.  Lists are ordered by nondecreasing
diameter because the theorem is applied one summand at a time. -/
def HasLevSharpPrefixTheorem (n0 : ℕ) : Prop :=
  ∀ parts : List (Finset ℕ),
    parts.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q) →
    (∀ P ∈ parts,
      n0 ≤ P.subsetSum.card ∧
      ¬ ContainedInNontrivialAP P.subsetSum) →
    1 + ∑ i ∈ Finset.Icc 1 parts.length,
        (min (levPoolMass (parts.getD (i - 1) ∅) - 1)
          (i * (n0 - 2)) + 1) ≤
      (levIteratedSubsetSum parts).card

lemma getD_levPoolMass_mono
    {parts : List (Finset ℕ)}
    (hsorted : parts.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ parts.length) :
    levPoolMass (parts.getD (i - 1) ∅) ≤
      levPoolMass (parts.getD (j - 1) ∅) := by
  have hii : i - 1 < parts.length := by omega
  have hjj : j - 1 < parts.length := by omega
  rw [List.getD_eq_get (l := parts) (d := ∅) ⟨i - 1, hii⟩,
    List.getD_eq_get (l := parts) (d := ∅) ⟨j - 1, hjj⟩]
  exact hsorted.rel_get_of_le (Fin.mk_le_mk.mpr (by omega))

lemma levPoolMass_lower_of_card
    {P : Finset ℕ} {n0 : ℕ} (hcard : n0 ≤ P.subsetSum.card) :
    n0 - 1 ≤ levPoolMass P := by
  have hu := card_subsetSum_le_levPoolMass_add_one P
  omega

lemma lev_prop_one_ii_of_sharpPrefix
    {parts : List (Finset ℕ)} {n0 L : ℕ}
    (hn0 : 3 ≤ n0)
    (hsorted : parts.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q))
    (hparts : ∀ P ∈ parts,
      n0 ≤ P.subsetSum.card ∧
      ¬ ContainedInNontrivialAP P.subsetSum)
    (hmass : ∀ P ∈ parts, levPoolMass P ≤ L)
    (hL : L ≤ parts.length * (n0 - 2) + 1)
    (hsharp : HasLevSharpPrefixTheorem n0) :
    levFamilyMass parts + parts.length * (n0 - 1) + 2 ≤
      2 * (levIteratedSubsetSum parts).card := by
  let a : ℕ → ℕ := fun i ↦ levPoolMass (parts.getD (i - 1) ∅)
  have haLo : ∀ i, 1 ≤ i → i ≤ parts.length → n0 - 1 ≤ a i := by
    intro i hi hil
    have himem : parts.getD (i - 1) ∅ ∈ parts :=
      getD_mem_of_lt parts ∅ (by omega)
    exact levPoolMass_lower_of_card (hparts _ himem).1
  have haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ parts.length → a i ≤ a j := by
    intro i j hi hij hj
    exact getD_levPoolMass_mono hsorted hi hij hj
  have haHi : ∀ i, 1 ≤ i → i ≤ parts.length → a i ≤ L := by
    intro i hi hil
    exact hmass _ (getD_mem_of_lt parts ∅ (by omega))
  have hp := lev_prop_one_ii_of_prefix_bound
    (r := n0 - 2) (k := parts.length) (L := L)
    (cardS := (levIteratedSubsetSum parts).card) (a := a)
    (by omega) (by
      intro i hi hil
      have hlo : n0 - 1 ≤ levPoolMass (parts.getD (i - 1) ∅) := by
        simpa only [a] using haLo i hi hil
      change n0 - 2 + 1 ≤ levPoolMass (parts.getD (i - 1) ∅)
      omega) haMono haHi hL
    (hsharp parts hsorted hparts)
  rw [sum_Icc_getD_eq_map_sum levPoolMass ∅ parts] at hp
  have hrEq : n0 - 2 + 1 = n0 - 1 := by omega
  rw [hrEq] at hp
  simpa [levFamilyMass] using hp

lemma lev_prop_one_i_of_sharpPrefix
    {parts : List (Finset ℕ)} {n0 L : ℕ}
    (hn0 : 3 ≤ n0) (hnL : n0 - 1 ≤ L)
    (hsorted : parts.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q))
    (hparts : ∀ P ∈ parts,
      n0 ≤ P.subsetSum.card ∧
      ¬ ContainedInNontrivialAP P.subsetSum)
    (hmass : ∀ P ∈ parts, levPoolMass P ≤ L)
    (hL : L ≤ (parts.length + 1) * (n0 - 2) + 1)
    (hsharp : HasLevSharpPrefixTheorem n0) :
    levFamilyMass parts + (parts.length + 1) * (n0 - 1) + 2 ≤
      2 * (levIteratedSubsetSum parts).card + L := by
  let a : ℕ → ℕ := fun i ↦ levPoolMass (parts.getD (i - 1) ∅)
  have haLo : ∀ i, 1 ≤ i → i ≤ parts.length → n0 - 1 ≤ a i := by
    intro i hi hil
    exact levPoolMass_lower_of_card
      (hparts _ (getD_mem_of_lt parts ∅ (by omega))).1
  have haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ parts.length → a i ≤ a j := by
    intro i j hi hij hj
    exact getD_levPoolMass_mono hsorted hi hij hj
  have haHi : ∀ i, 1 ≤ i → i ≤ parts.length → a i ≤ L := by
    intro i hi hil
    exact hmass _ (getD_mem_of_lt parts ∅ (by omega))
  have hp := lev_prop_one_i_of_prefix_bound
    (r := n0 - 2) (k := parts.length) (L := L)
    (cardS := (levIteratedSubsetSum parts).card) (a := a)
    (by omega) (by omega) (by
      intro i hi hil
      have hlo : n0 - 1 ≤ levPoolMass (parts.getD (i - 1) ∅) := by
        simpa only [a] using haLo i hi hil
      change n0 - 2 + 1 ≤ levPoolMass (parts.getD (i - 1) ∅)
      omega) haMono haHi hL
    (hsharp parts hsorted hparts)
  rw [sum_Icc_getD_eq_map_sum levPoolMass ∅ parts] at hp
  have hrEq : n0 - 2 + 1 = n0 - 1 := by omega
  rw [hrEq] at hp
  simpa [levFamilyMass] using hp

/-! ## The exact odd-family seed -/

/-- Lev's Theorem 4 in the precise seed interface used by the CFP
high-multiplicity corollary.  The only additive input is the sharp prefix
theorem; all other steps are internal to this file. -/
theorem hasCFPLevSeedTheorem_of_sharpPrefix
    {n0 : ℕ} (hsharp : HasLevSharpPrefixTheorem n0) :
    HasCFPLevSeedTheorem n0 := by
  intro seed m hseedLen hn0 hnm hseed
  let h := (m - 1) ⌈/⌉ (n0 - 2)
  have hden : 0 < n0 - 2 := by omega
  have hmul : m - 1 ≤ (n0 - 2) * h := by
    exact (ceilDiv_le_iff_le_mul hden).mp (le_rfl : h ≤ h)
  have hh : 1 ≤ h := by
    by_contra hh0
    have : h = 0 := Nat.eq_zero_of_not_pos hh0
    rw [this, Nat.mul_zero] at hmul
    omega
  have hmhr : m ≤ h * (n0 - 2) + 1 := by
    rw [Nat.mul_comm]
    omega
  have hhmass : m ≤ h * (n0 - 1) := by
    calc
      m ≤ h * (n0 - 2) + 1 := hmhr
      _ ≤ h * (n0 - 2) + h := Nat.add_le_add_left hh _
      _ = h * (n0 - 1) := by
        rw [show n0 - 1 = (n0 - 2) + 1 by omega,
          Nat.mul_add, Nat.mul_one]
  let ordered := seed.mergeSort
    (fun P Q ↦ decide (levPoolMass P ≥ levPoolMass Q))
  have hsortPerm : ordered.Perm seed := by
    dsimp [ordered]
    exact List.mergeSort_perm _ _
  have hordered :
      ordered.Pairwise (fun P Q ↦ levPoolMass Q ≤ levPoolMass P) := by
    dsimp [ordered]
    have hs := List.pairwise_mergeSort
      (le := fun P Q : Finset ℕ ↦ decide (levPoolMass P ≥ levPoolMass Q))
      (fun A B C hAB hBC => by
        simp only [decide_eq_true_eq] at hAB hBC ⊢
        exact hBC.trans hAB)
      (fun A B => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (levPoolMass B) (levPoolMass A)) seed
    simpa only [decide_eq_true_eq] using hs
  have horderedLen : ordered.length = 2 * h - 1 := by
    rw [hsortPerm.length_eq]
    simpa [h] using hseedLen
  let left := (levAlternateSplit ordered).1
  let right := (levAlternateSplit ordered).2
  let leftAsc := left.reverse
  let rightAsc := right.reverse
  have hlrLen := levAlternateSplit_lengths_of_odd hh horderedLen
  have hleftLen : leftAsc.length = h - 1 := by
    simpa [leftAsc, left] using hlrLen.1
  have hrightLen : rightAsc.length = h := by
    simpa [rightAsc, right] using hlrLen.2
  have hlrSorted := levAlternateSplit_reverse_pairwise hordered
  have hleftSorted :
      leftAsc.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q) := by
    simpa [leftAsc, left] using hlrSorted.1
  have hrightSorted :
      rightAsc.Pairwise (fun P Q ↦ levPoolMass P ≤ levPoolMass Q) := by
    simpa [rightAsc, right] using hlrSorted.2
  have hsplitPerm : ordered.Perm (left ++ right) := by
    simpa [left, right] using levAlternateSplit_perm ordered
  have hreversePerm : (left ++ right).Perm (leftAsc ++ rightAsc) := by
    exact left.reverse_perm.symm.append right.reverse_perm.symm
  have hfinalPerm : seed.Perm (leftAsc ++ rightAsc) :=
    hsortPerm.symm.trans (hsplitPerm.trans hreversePerm)
  have hcombined : ∀ P ∈ leftAsc ++ rightAsc,
      n0 ≤ P.subsetSum.card ∧
      P.subsetSum ⊆ Finset.Icc 0 m ∧
      ¬ ContainedInNontrivialAP P.subsetSum := by
    intro P hP
    exact hseed P (hfinalPerm.mem_iff.mpr hP)
  have hleftParts : ∀ P ∈ leftAsc,
      n0 ≤ P.subsetSum.card ∧
      ¬ ContainedInNontrivialAP P.subsetSum := by
    intro P hP
    have hp := hcombined P (by simp [hP])
    exact ⟨hp.1, hp.2.2⟩
  have hrightParts : ∀ P ∈ rightAsc,
      n0 ≤ P.subsetSum.card ∧
      ¬ ContainedInNontrivialAP P.subsetSum := by
    intro P hP
    have hp := hcombined P (by simp [hP])
    exact ⟨hp.1, hp.2.2⟩
  have hmassCombined : ∀ P ∈ leftAsc ++ rightAsc, levPoolMass P ≤ m := by
    intro P hP
    have hp := hcombined P hP
    exact (Finset.mem_Icc.mp (hp.2.1 (levPoolMass_mem_subsetSum P))).2
  have hleftMass : ∀ P ∈ leftAsc, levPoolMass P ≤ m := by
    intro P hP
    exact hmassCombined P (by simp [hP])
  have hrightMass : ∀ P ∈ rightAsc, levPoolMass P ≤ m := by
    intro P hP
    exact hmassCombined P (by simp [hP])
  have hleftMassLower :
      leftAsc.length * (n0 - 1) ≤ levFamilyMass leftAsc :=
    length_mul_le_levFamilyMass_of_card fun P hP ↦ (hleftParts P hP).1
  have hrightMassLower :
      rightAsc.length * (n0 - 1) ≤ levFamilyMass rightAsc :=
    length_mul_le_levFamilyMass_of_card fun P hP ↦ (hrightParts P hP).1
  have horderedMass : ∀ P ∈ ordered, levPoolMass P ≤ m := by
    intro P hP
    exact (Finset.mem_Icc.mp
      ((hseed P (hsortPerm.mem_iff.mp hP)).2.1
        (levPoolMass_mem_subsetSum P))).2
  have hlrMass := levAlternateSplit_mass_bounds_of_odd
    hh horderedLen horderedMass hordered
  have hmassBalance :
      levFamilyMass leftAsc ≤ levFamilyMass rightAsc + m ∧
      levFamilyMass rightAsc ≤ levFamilyMass leftAsc + m := by
    simpa [levFamilyMass, leftAsc, rightAsc, left, right] using hlrMass
  have hleftL : m ≤ (leftAsc.length + 1) * (n0 - 2) + 1 := by
    rw [hleftLen]
    rw [Nat.sub_add_cancel hh]
    exact hmhr
  have hrightL : m ≤ rightAsc.length * (n0 - 2) + 1 := by
    rw [hrightLen]
    exact hmhr
  have hleftCard := lev_prop_one_i_of_sharpPrefix hn0 hnm hleftSorted
    hleftParts hleftMass hleftL hsharp
  have hrightCard := lev_prop_one_ii_of_sharpPrefix hn0 hrightSorted
    hrightParts hrightMass hrightL hsharp
  let S₁ := levIteratedSubsetSum leftAsc
  let S₂ := levIteratedSubsetSum rightAsc
  let L₁ := levFamilyMass leftAsc
  let L₂ := levFamilyMass rightAsc
  let K := S₁.card + S₂.card - 2
  have hleftCard' : L₁ + h * (n0 - 1) + 2 ≤ 2 * S₁.card + m := by
    dsimp [L₁, S₁]
    rw [hleftLen] at hleftCard
    simpa only [Nat.sub_add_cancel hh] using hleftCard
  have hrightCard' : L₂ + h * (n0 - 1) + 2 ≤ 2 * S₂.card := by
    dsimp [L₂, S₂]
    rw [hrightLen] at hrightCard
    exact hrightCard
  have hS₁ne : S₁.Nonempty := levIteratedSubsetSum_nonempty leftAsc
  have hS₂ne : S₂.Nonempty := levIteratedSubsetSum_nonempty rightAsc
  have hS₁box : S₁ ⊆ Finset.Icc 0 L₁ :=
    levIteratedSubsetSum_subset_Icc_familyMass leftAsc
  have hS₂box : S₂ ⊆ Finset.Icc 0 L₂ :=
    levIteratedSubsetSum_subset_Icc_familyMass rightAsc
  have hKexact : K + 2 = S₁.card + S₂.card := by
    dsimp [K]
    have hc1 : 0 < S₁.card := Finset.card_pos.mpr hS₁ne
    have hc2 : 0 < S₂.card := Finset.card_pos.mpr hS₂ne
    omega
  have htwohm : 2 * m ≤ 2 * (h * (n0 - 1)) :=
    Nat.mul_le_mul_left 2 hhmass
  have hsumLower :
      L₁ + L₂ + m + 4 ≤ 2 * (S₁.card + S₂.card) := by
    omega
  have hL₁sum : L₁ + 2 ≤ S₁.card + S₂.card := by
    have hb := hmassBalance.1
    omega
  have hL₂sum : L₂ + 2 ≤ S₁.card + S₂.card := by
    have hb := hmassBalance.2
    omega
  have hL₁K : L₁ ≤ K := by
    rw [← hKexact] at hL₁sum
    omega
  have hL₂K : L₂ ≤ K := by
    rw [← hKexact] at hL₂sum
    omega
  have hHL₂ : h * (n0 - 1) ≤ L₂ := by
    dsimp [L₂]
    rw [hrightLen] at hrightMassLower
    exact hrightMassLower
  have hmK : m ≤ K := hhmass.trans (hHL₂.trans hL₂K)
  have hdense : max L₁ L₂ ≤ S₁.card + S₂.card - 2 := by
    rw [max_le_iff]
    exact ⟨by simpa [K] using hL₁K, by simpa [K] using hL₂K⟩
  have hinterval := lev_dense_two_sum_interval
    (S₁ := S₁) (S₂ := S₂) (L₁ := L₁) (L₂ := L₂)
    hS₁ne hS₂ne hS₁box hS₂box hdense
  have hsumCard :
      L₁ + L₂ + 2 * (h * (n0 - 1)) ≤ 2 * K + m := by
    omega
  have ha : L₁ + L₂ - K ≤ K := by
    omega
  have hLsum : L₁ + L₂ ≤ 2 * K := by omega
  have hdoubleHLower :
      2 * (h * (n0 - 1)) ≤ L₁ + L₂ + (n0 - 1) := by
    have hleft' : (h - 1) * (n0 - 1) ≤ L₁ := by
      dsimp [L₁]
      rw [hleftLen] at hleftMassLower
      exact hleftMassLower
    have hdecomp :
        2 * (h * (n0 - 1)) =
          (h - 1) * (n0 - 1) + h * (n0 - 1) + (n0 - 1) := by
      calc
        2 * (h * (n0 - 1)) = h * (n0 - 1) + h * (n0 - 1) := by ring
        _ = ((h - 1) + 1) * (n0 - 1) + h * (n0 - 1) := by
          rw [Nat.sub_add_cancel hh]
        _ = (h - 1) * (n0 - 1) + h * (n0 - 1) + (n0 - 1) := by ring
    rw [hdecomp]
    omega
  have htargetBase : 2 * (h * (n0 - 1)) ≤ K + m := by
    omega
  have hwidth : m ≤ K + 1 - (L₁ + L₂ - K) := by
    by_cases hsumK : L₁ + L₂ ≤ K
    · rw [Nat.sub_eq_zero_of_le hsumK]
      omega
    · have hKsum : K ≤ L₁ + L₂ := le_of_not_ge hsumK
      have heq : K + 1 - (L₁ + L₂ - K) =
          2 * K - (L₁ + L₂) + 1 := by omega
      rw [heq]
      omega
  have htargetWidth :
      2 * (h * (n0 - 1)) + 1 ≤
        K + m + 1 - (L₁ + L₂ - K) := by
    by_cases hsumK : L₁ + L₂ ≤ K
    · rw [Nat.sub_eq_zero_of_le hsumK]
      omega
    · have hKsum : K ≤ L₁ + L₂ := le_of_not_ge hsumK
      have heq : K + m + 1 - (L₁ + L₂ - K) =
          2 * K + m + 1 - (L₁ + L₂) := by omega
      rw [heq]
      omega
  refine ⟨L₁ + L₂ - K, K, ha, ?_, ?_, ?_⟩
  · rw [levIteratedSubsetSum_eq_of_perm hfinalPerm,
      levIteratedSubsetSum_append]
    exact hinterval
  · exact hwidth
  · have hpartsLen : seed.length + 1 = 2 * h := by
      rw [hseedLen]
      omega
    rw [hpartsLen]
    rw [Nat.mul_assoc]
    exact htargetWidth

end Erdos360
