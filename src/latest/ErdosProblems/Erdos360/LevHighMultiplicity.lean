import ErdosProblems.Erdos360.LevDenseInterval

open scoped BigOperators Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

lemma zero_mem_levIteratedSubsetSum (parts : List (Finset ℕ)) :
    0 ∈ levIteratedSubsetSum parts := by
  induction parts with
  | nil => simp [levIteratedSubsetSum]
  | cons P parts ih =>
      simp only [levIteratedSubsetSum]
      exact Finset.mem_add.mpr ⟨0, by simp, 0, ih, by simp⟩

lemma levIteratedSubsetSum_nonempty (parts : List (Finset ℕ)) :
    (levIteratedSubsetSum parts).Nonempty :=
  ⟨0, zero_mem_levIteratedSubsetSum parts⟩

lemma levIteratedSubsetSum_subset_Icc_mul
    {parts : List (Finset ℕ)} {q : ℕ}
    (hparts : ∀ P ∈ parts, P.subsetSum ⊆ Finset.Icc 0 q) :
    levIteratedSubsetSum parts ⊆ Finset.Icc 0 (parts.length * q) := by
  induction parts with
  | nil => simp [levIteratedSubsetSum]
  | cons P parts ih =>
      have hP : P.subsetSum ⊆ Finset.Icc 0 q := hparts P (by simp)
      have htail : ∀ Q ∈ parts, Q.subsetSum ⊆ Finset.Icc 0 q := by
        intro Q hQ
        exact hparts Q (by simp [hQ])
      intro x hx
      simp only [levIteratedSubsetSum] at hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      have huI := Finset.mem_Icc.mp (hP hu)
      have hvI := Finset.mem_Icc.mp (ih htail hv)
      rw [List.length_cons, Nat.succ_mul]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

lemma levIteratedSubsetSum_card_lower
    {parts : List (Finset ℕ)} {n0 : ℕ}
    (hn0 : 1 ≤ n0)
    (hparts : ∀ P ∈ parts, n0 ≤ P.subsetSum.card) :
    parts.length * (n0 - 1) + 1 ≤
      (levIteratedSubsetSum parts).card := by
  induction parts with
  | nil => simp [levIteratedSubsetSum]
  | cons P parts ih =>
      have hPcard : n0 ≤ P.subsetSum.card := hparts P (by simp)
      have htail : ∀ Q ∈ parts, n0 ≤ Q.subsetSum.card := by
        intro Q hQ
        exact hparts Q (by simp [hQ])
      have hPne : P.subsetSum.Nonempty := ⟨0, by simp⟩
      have htailne := levIteratedSubsetSum_nonempty parts
      have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hPne htailne
      have hi := ih htail
      simp only [levIteratedSubsetSum, List.length_cons, Nat.succ_mul]
      omega

/-- An interval of at least `m` integer spacings is extended by `m` when
the next summand contains both endpoints `0` and `m`. -/
lemma Icc_subset_add_of_zero_top_mem
    {S T : Finset ℕ} {a b m : ℕ}
    (hab : a ≤ b) (hI : Finset.Icc a b ⊆ S)
    (h0 : 0 ∈ T) (hm : m ∈ T)
    (hwidth : m ≤ b + 1 - a) :
    Finset.Icc a (b + m) ⊆ S + T := by
  intro x hx
  have hxI := Finset.mem_Icc.mp hx
  by_cases hxb : x ≤ b
  · exact Finset.mem_add.mpr
      ⟨x, hI (Finset.mem_Icc.mpr ⟨hxI.1, hxb⟩), 0, h0, by omega⟩
  · have hxm : m ≤ x := by omega
    have hsub : x - m ∈ Finset.Icc a b := by
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    exact Finset.mem_add.mpr
      ⟨x - m, hI hsub, m, hm, by omega⟩

/-- Adding a subset-sum set extends a sufficiently wide interval by the
largest element of its underlying pool. -/
lemma Icc_subset_add_subsetSum_of_wide
    {S P : Finset ℕ} {a b : ℕ}
    (hab : a ≤ b) (hI : Finset.Icc a b ⊆ S)
    (hwidth : (∑ x ∈ P, x) ≤ b + 1 - a) :
    Finset.Icc a (b + ∑ x ∈ P, x) ⊆ S + P.subsetSum := by
  apply Icc_subset_add_of_zero_top_mem hab hI (by simp) ?_ hwidth
  rw [Finset.mem_subsetSum_iff]
  exact ⟨P, fun _ hx ↦ hx, rfl⟩

private lemma singleton_zero_add (S : Finset ℕ) : {0} + S = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, s, hs, hzs⟩ := Finset.mem_add.mp hx
    simp only [Finset.mem_singleton] at hz
    subst z
    rw [← hzs]
    simpa using hs
  · intro hx
    exact Finset.mem_add.mpr ⟨0, by simp, x, hx, by simp⟩

private lemma add_singleton_zero (S : Finset ℕ) : S + {0} = S := by
  rw [add_comm]
  exact singleton_zero_add S

lemma levIteratedSubsetSum_append
    (left right : List (Finset ℕ)) :
    levIteratedSubsetSum (left ++ right) =
      levIteratedSubsetSum left + levIteratedSubsetSum right := by
  induction left with
  | nil =>
      simp only [List.nil_append, levIteratedSubsetSum]
      exact (singleton_zero_add _).symm
  | cons P left ih =>
      simp only [List.cons_append, levIteratedSubsetSum, ih]
      rw [add_assoc]

lemma levIteratedSubsetSum_singleton (P : Finset ℕ) :
    levIteratedSubsetSum [P] = P.subsetSum := by
  simp only [levIteratedSubsetSum]
  exact add_singleton_zero _

/-- The iterated sumset depends only on the multiset of summands. -/
lemma levIteratedSubsetSum_eq_of_perm
    {left right : List (Finset ℕ)} (hperm : left.Perm right) :
    levIteratedSubsetSum left = levIteratedSubsetSum right := by
  induction hperm with
  | nil => rfl
  | cons P _ ih => simp only [levIteratedSubsetSum, ih]
  | swap P Q parts =>
      simp only [levIteratedSubsetSum]
      rw [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A nonempty list of finite pools can be reordered so that a pool of
maximal total sum occurs last.  For ordinary subset-sum sets this total sum
is exactly their diameter, since both zero and the full sum occur. -/
lemma exists_perm_append_max_poolSum
    {parts : List (Finset ℕ)} (hne : parts ≠ []) :
    ∃ middle last,
      parts.Perm (middle ++ [last]) ∧
      ∀ P ∈ middle, (∑ x ∈ P, x) ≤ ∑ x ∈ last, x := by
  induction parts with
  | nil => exact False.elim (hne rfl)
  | cons P tail ih =>
      by_cases htail : tail = []
      · subst tail
        refine ⟨[], P, by simp, ?_⟩
        simp
      · obtain ⟨middle, last, hperm, hmax⟩ := ih htail
        by_cases hPle : (∑ x ∈ P, x) ≤ ∑ x ∈ last, x
        · refine ⟨P :: middle, last, ?_, ?_⟩
          · simpa only [List.cons_append] using hperm.cons P
          · intro Q hQ
            simp only [List.mem_cons] at hQ
            rcases hQ with rfl | hQ
            · exact hPle
            · exact hmax Q hQ
        · refine ⟨middle ++ [last], P, ?_, ?_⟩
          · exact (hperm.cons P).trans
              (List.perm_append_singleton P (middle ++ [last])).symm
          · intro Q hQ
            simp only [List.mem_append, List.mem_singleton] at hQ
            rcases hQ with hQ | rfl
            · exact (hmax Q hQ).trans (Nat.le_of_not_ge hPle)
            · exact Nat.le_of_not_ge hPle

/-- Once the seed interval is at least as wide as every remaining summand,
each remaining CFP pool extends it by at least `n0 - 1`. -/
lemma exists_levInterval_through_suffix
    {pre suffix : List (Finset ℕ)} {a b q n0 : ℕ}
    (hab : a ≤ b)
    (hseed : Finset.Icc a b ⊆ levIteratedSubsetSum pre)
    (hwide : q ≤ b + 1 - a)
    (hcard : ∀ P ∈ suffix, n0 ≤ P.subsetSum.card)
    (hbox : ∀ P ∈ suffix, P.subsetSum ⊆ Finset.Icc 0 q) :
    ∃ c : ℕ,
      b + suffix.length * (n0 - 1) ≤ c ∧
      Finset.Icc a c ⊆ levIteratedSubsetSum (pre ++ suffix) := by
  induction suffix generalizing pre b with
  | nil =>
      refine ⟨b, by simp, ?_⟩
      simpa using hseed
  | cons P suffix ih =>
      let m := ∑ x ∈ P, x
      have hPcard : n0 ≤ P.subsetSum.card := hcard P (by simp)
      have hPbox : P.subsetSum ⊆ Finset.Icc 0 q := hbox P (by simp)
      have hmMem : m ∈ P.subsetSum := by
        rw [Finset.mem_subsetSum_iff]
        exact ⟨P, fun _ hx ↦ hx, rfl⟩
      have hmq : m ≤ q := (Finset.mem_Icc.mp (hPbox hmMem)).2
      have hsubsetM : P.subsetSum ⊆ Finset.Icc 0 m := by
        intro s hs
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, mem_subsetSum_le_sum hs⟩
      have hcardM : P.subsetSum.card ≤ m + 1 := by
        calc
          P.subsetSum.card ≤ (Finset.Icc 0 m).card :=
            Finset.card_le_card hsubsetM
          _ = m + 1 := by simp
      have hgain : n0 - 1 ≤ m := by omega
      have hnext : Finset.Icc a (b + m) ⊆
          levIteratedSubsetSum (pre ++ [P]) := by
        rw [levIteratedSubsetSum_append, levIteratedSubsetSum_singleton]
        exact Icc_subset_add_subsetSum_of_wide hab hseed
          (hmq.trans hwide)
      have habm : a ≤ b + m := hab.trans (Nat.le_add_right b m)
      have hwideNext : q ≤ b + m + 1 - a := by omega
      have hcardTail : ∀ Q ∈ suffix, n0 ≤ Q.subsetSum.card := by
        intro Q hQ
        exact hcard Q (by simp [hQ])
      have hboxTail : ∀ Q ∈ suffix, Q.subsetSum ⊆ Finset.Icc 0 q := by
        intro Q hQ
        exact hbox Q (by simp [hQ])
      obtain ⟨c, hbc, hIc⟩ := ih habm hnext hwideNext hcardTail hboxTail
      refine ⟨c, ?_, ?_⟩
      · simp only [List.length_cons, Nat.succ_mul] at hbc ⊢
        omega
      · simpa only [List.append_assoc, List.singleton_append] using hIc

/-- Source-faithful completion of Lev's seed construction.  A seed interval
whose width already exceeds the largest remaining diameter is extended first
through the intermediate summands, and then by the two endpoints of a final
summand of maximal diameter.  The permutation hypothesis lets the seed be
chosen after reordering the original family. -/
lemma hasCFPLevInterval_of_permuted_seed
    {parts seed middle : List (Finset ℕ)} {last : Finset ℕ}
    {n0 m a b : ℕ}
    (hperm : parts.Perm (seed ++ middle ++ [last]))
    (hab : a ≤ b)
    (hseed : Finset.Icc a b ⊆ levIteratedSubsetSum seed)
    (hseedWide : m ≤ b + 1 - a)
    (hseedTarget : (seed.length + 1) * (n0 - 1) + 1 ≤ b + m + 1 - a)
    (hcardMiddle : ∀ P ∈ middle, n0 ≤ P.subsetSum.card)
    (hsumMiddle : ∀ P ∈ middle, (∑ x ∈ P, x) ≤ m)
    (hlastSum : (∑ x ∈ last, x) = m) :
    HasCFPLevInterval parts parts.length n0 := by
  have hboxMiddle : ∀ P ∈ middle, P.subsetSum ⊆ Finset.Icc 0 m := by
    intro P hP s hs
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le s, (mem_subsetSum_le_sum hs).trans (hsumMiddle P hP)⟩
  obtain ⟨c, hbc, hIc⟩ := exists_levInterval_through_suffix
    hab hseed hseedWide hcardMiddle hboxMiddle
  have hac : a ≤ c := hab.trans (le_trans (Nat.le_add_right b _) hbc)
  have hwideLast : m ≤ c + 1 - a := by omega
  have hfinal : Finset.Icc a (c + m) ⊆
      levIteratedSubsetSum ((seed ++ middle) ++ [last]) := by
    rw [levIteratedSubsetSum_append, levIteratedSubsetSum_singleton]
    have hext := Icc_subset_add_subsetSum_of_wide hac (by
      simpa only [List.append_assoc] using hIc) (by
        rw [hlastSum]
        exact hwideLast)
    simpa only [hlastSum] using hext
  have hlen : parts.length = seed.length + middle.length + 1 := by
    rw [hperm.length_eq]
    simp only [List.length_append, List.length_singleton]
  refine ⟨a, c + m, hac.trans (Nat.le_add_right c m), ?_, ?_⟩
  · rw [levIteratedSubsetSum_eq_of_perm hperm]
    simpa only [List.append_assoc] using hfinal
  · rw [hlen]
    rw [Nat.add_mul, Nat.add_mul]
    rw [Nat.add_mul] at hseedTarget
    omega

/-- The precise seed statement furnished by Lev's Theorem 4.  Isolating it
from the elementary maximal-diameter and interval-extension argument makes
the quantitative role of the difficult additive theorem explicit. -/
def HasCFPLevSeedTheorem (n0 : ℕ) : Prop :=
  ∀ {seed : List (Finset ℕ)} {m : ℕ},
    seed.length = 2 * ((m - 1) ⌈/⌉ (n0 - 2)) - 1 →
    3 ≤ n0 →
    n0 - 1 ≤ m →
    (∀ P ∈ seed,
      n0 ≤ P.subsetSum.card ∧
      P.subsetSum ⊆ Finset.Icc 0 m ∧
      ¬ ContainedInNontrivialAP P.subsetSum) →
    ∃ a b : ℕ,
      a ≤ b ∧
      Finset.Icc a b ⊆ levIteratedSubsetSum seed ∧
      m ≤ b + 1 - a ∧
      (seed.length + 1) * (n0 - 1) + 1 ≤ b + m + 1 - a

/-- Lev's Corollary 1 follows formally from its sharp odd-family seed
theorem.  This lemma performs all reordering, ceiling-division, truncation,
and endpoint-extension bookkeeping. -/
theorem hasCFPLevInterval_of_high_multiplicity_of_seedTheorem
    {parts : List (Finset ℕ)} {n0 q : ℕ}
    (hfamily : IsCFPLevFamily parts parts.length n0 q)
    (hn0 : 3 ≤ n0)
    (hmult : 2 * ((q - 1) ⌈/⌉ (n0 - 2)) ≤ parts.length)
    (hseedTheorem : HasCFPLevSeedTheorem n0) :
    HasCFPLevInterval parts parts.length n0 := by
  by_cases hpartsNil : parts = []
  · subst parts
    refine ⟨0, 0, le_rfl, ?_, by simp⟩
    simp [levIteratedSubsetSum]
  obtain ⟨front, last, hperm, hmax⟩ :=
    exists_perm_append_max_poolSum hpartsNil
  obtain ⟨_hlen, _hpair, hord⟩ := hfamily
  have hlastMem : last ∈ parts := hperm.mem_iff.mpr (by simp)
  have hlastOrd := hord last hlastMem
  let m := ∑ x ∈ last, x
  have hmMem : m ∈ last.subsetSum := by
    dsimp [m]
    rw [Finset.mem_subsetSum_iff]
    exact ⟨last, fun _ hx ↦ hx, rfl⟩
  have hmq : m ≤ q :=
    (Finset.mem_Icc.mp (hlastOrd.2.1 hmMem)).2
  have hlastBoxM : last.subsetSum ⊆ Finset.Icc 0 m := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le s, mem_subsetSum_le_sum hs⟩
  have hcardUpper : last.subsetSum.card ≤ m + 1 := by
    calc
      last.subsetSum.card ≤ (Finset.Icc 0 m).card :=
        Finset.card_le_card hlastBoxM
      _ = m + 1 := by simp
  have hmLower : n0 - 1 ≤ m := by omega
  have hden : 0 < n0 - 2 := by omega
  let h := (m - 1) ⌈/⌉ (n0 - 2)
  let hq := (q - 1) ⌈/⌉ (n0 - 2)
  have hhqBound : q - 1 ≤ (n0 - 2) * hq := by
    exact (ceilDiv_le_iff_le_mul hden).mp (le_rfl : hq ≤ hq)
  have hhq : h ≤ hq := by
    apply (ceilDiv_le_iff_le_mul hden).mpr
    have hmSub : m - 1 ≤ q - 1 := by omega
    exact hmSub.trans hhqBound
  have htwice : 2 * h ≤ parts.length := by
    dsimp [hq] at hmult hhq
    omega
  have hfrontLen : parts.length = front.length + 1 := by
    rw [hperm.length_eq]
    simp
  let r := 2 * h - 1
  have hrle : r ≤ front.length := by
    dsimp [r]
    omega
  let seed := front.take r
  let middle := front.drop r
  have hseedLen : seed.length = r := by
    dsimp [seed]
    rw [List.length_take, min_eq_left hrle]
  have hsplit : seed ++ middle = front := by
    exact List.take_append_drop r front
  have hperm' : parts.Perm (seed ++ middle ++ [last]) := by
    rw [hsplit]
    exact hperm
  have hfrontMem : ∀ P ∈ front, P ∈ parts := by
    intro P hP
    exact hperm.mem_iff.mpr (by simp [hP])
  have hseedOrd : ∀ P ∈ seed,
      n0 ≤ P.subsetSum.card ∧
      P.subsetSum ⊆ Finset.Icc 0 m ∧
      ¬ ContainedInNontrivialAP P.subsetSum := by
    intro P hP
    have hPf : P ∈ front := List.mem_of_mem_take hP
    have hPo := hord P (hfrontMem P hPf)
    refine ⟨hPo.1, ?_, hPo.2.2⟩
    intro s hs
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le s, (mem_subsetSum_le_sum hs).trans (hmax P hPf)⟩
  obtain ⟨a, b, hab, hI, hwide, htarget⟩ := hseedTheorem
    (by simpa [r, h] using hseedLen) hn0 hmLower hseedOrd
  have hcardMiddle : ∀ P ∈ middle, n0 ≤ P.subsetSum.card := by
    intro P hP
    exact (hord P (hfrontMem P (List.mem_of_mem_drop hP))).1
  have hsumMiddle : ∀ P ∈ middle, (∑ x ∈ P, x) ≤ m := by
    intro P hP
    exact hmax P (List.mem_of_mem_drop hP)
  exact hasCFPLevInterval_of_permuted_seed hperm' hab hI hwide htarget
    hcardMiddle hsumMiddle rfl

end Erdos360
