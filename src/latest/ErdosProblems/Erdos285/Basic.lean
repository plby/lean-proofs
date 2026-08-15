/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 285: elementary representation infrastructure

This file contains the definitions occurring literally in the formal-conjectures
statement, their equivalent finite-set formulation, and the elementary splitting
operation for Egyptian fractions.  The analytic and number-theoretic estimates in
Martin's theorem are intentionally kept out of this file.
-/

open Filter
open scoped BigOperators Topology Real

namespace Erdos285

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A strictly increasing representation of one by exactly `k + 1` positive,
distinct unit fractions.  This is the predicate used in the upstream statement. -/
def Representation (k : ℕ) (n : Fin k.succ → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The set of indices `k` for which a representation with `k + 1` terms exists. -/
def ValidIndices : Set ℕ :=
  {k | ∃ n : Fin k.succ → ℕ, Representation k n}

/-- The possible final (and therefore largest) denominators of `k + 1`-term
representations.  Its syntax matches the set minimized in the upstream theorem. -/
def LastDenominators (k : ℕ) : Set ℕ :=
  {n (Fin.last k) |
    (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
      (_ : 1 = ∑ i, (1 : ℝ) / n i)}

/-- `m` is the least possible final denominator among `k + 1`-term
representations. -/
def IsMinimalLastDenominator (k m : ℕ) : Prop :=
  IsLeast (LastDenominators k) m

@[simp] theorem mem_validIndices {k : ℕ} :
    k ∈ ValidIndices ↔ ∃ n : Fin k.succ → ℕ, Representation k n :=
  Iff.rfl

theorem validIndices_eq_upstream :
    ValidIndices =
      {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
        1 = ∑ i, (1 : ℝ) / n i} := by
  rfl

@[simp] theorem mem_lastDenominators {k m : ℕ} :
    m ∈ LastDenominators k ↔
      ∃ n : Fin k.succ → ℕ, Representation k n ∧ n (Fin.last k) = m := by
  simp only [LastDenominators, Representation, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hnmono, hnzero, hnsum, rfl⟩
    exact ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
  · rintro ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
    exact ⟨n, hnmono, hnzero, hnsum, rfl⟩

theorem lastDenominators_nonempty_iff {k : ℕ} :
    (LastDenominators k).Nonempty ↔ k ∈ ValidIndices := by
  simp only [Set.Nonempty, mem_lastDenominators, mem_validIndices]
  constructor
  · rintro ⟨m, n, hn, -⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n (Fin.last k), n, hn, rfl⟩

/-- Every nonempty set of possible last denominators has a least element. -/
theorem exists_minimalLastDenominator {k : ℕ} (hk : k ∈ ValidIndices) :
    ∃ m : ℕ, IsMinimalLastDenominator k m := by
  have hne : (LastDenominators k).Nonempty := lastDenominators_nonempty_iff.2 hk
  refine ⟨sInf (LastDenominators k), ?_, ?_⟩
  · exact Nat.sInf_mem hne
  · intro m hm
    exact Nat.sInf_le hm

/-! ## Conversion to finite sets -/

/-- The finite set of denominators occurring in an indexed family. -/
def denominatorFinset {k : ℕ} (n : Fin k.succ → ℕ) : Finset ℕ :=
  Finset.image n Finset.univ

@[simp] theorem mem_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ} {m : ℕ} :
    m ∈ denominatorFinset n ↔ m ∈ Set.range n := by
  simp [denominatorFinset]

theorem card_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : StrictMono n) :
    (denominatorFinset n).card = k.succ := by
  simp [denominatorFinset, Finset.card_image_of_injective _ hn.injective]

theorem zero_not_mem_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : 0 ∉ Set.range n) :
    0 ∉ denominatorFinset n := by
  simpa using hn

theorem sum_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : StrictMono n) :
    ∑ m ∈ denominatorFinset n, (1 : ℝ) / m = ∑ i, (1 : ℝ) / n i := by
  classical
  rw [denominatorFinset, Finset.sum_image]
  exact fun i _ j _ hij ↦ hn.injective hij

theorem representation_to_finset {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : Representation k n) :
    (denominatorFinset n).card = k.succ ∧
      0 ∉ denominatorFinset n ∧
      ∑ m ∈ denominatorFinset n, (1 : ℝ) / m = 1 := by
  refine ⟨card_denominatorFinset hn.1, zero_not_mem_denominatorFinset hn.2.1, ?_⟩
  rw [sum_denominatorFinset hn.1, ← hn.2.2]

/-- Enumerate a finite set increasingly when its cardinality is `k + 1`. -/
def enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) : Fin k.succ → ℕ :=
  A.orderEmbOfFin hA

theorem enumerate_strictMono {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    StrictMono (enumerate A hA) :=
  (A.orderEmbOfFin hA).strictMono

theorem range_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    Set.range (enumerate A hA) = A := by
  exact A.range_orderEmbOfFin hA

@[simp] theorem denominatorFinset_enumerate {k : ℕ} (A : Finset ℕ)
    (hA : A.card = k.succ) :
    denominatorFinset (enumerate A hA) = A := by
  exact A.image_orderEmbOfFin_univ hA

theorem sum_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    ∑ i, (1 : ℝ) / enumerate A hA i = ∑ m ∈ A, (1 : ℝ) / m := by
  calc
    ∑ i, (1 : ℝ) / enumerate A hA i =
        ∑ m ∈ denominatorFinset (enumerate A hA), (1 : ℝ) / m :=
      (sum_denominatorFinset (enumerate_strictMono A hA)).symm
    _ = ∑ m ∈ A, (1 : ℝ) / m := by
      rw [denominatorFinset_enumerate A hA]

theorem representation_enumerate {k : ℕ} {A : Finset ℕ}
    (hcard : A.card = k.succ) (hzero : 0 ∉ A)
    (hsum : ∑ m ∈ A, (1 : ℝ) / m = 1) :
    Representation k (enumerate A hcard) := by
  refine ⟨enumerate_strictMono A hcard, ?_, ?_⟩
  · rwa [range_enumerate A hcard]
  · rw [sum_enumerate A hcard, hsum]

theorem validIndices_iff_finset {k : ℕ} :
    k ∈ ValidIndices ↔
      ∃ A : Finset ℕ, A.card = k.succ ∧ 0 ∉ A ∧
        ∑ m ∈ A, (1 : ℝ) / m = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨denominatorFinset n, representation_to_finset hn⟩
  · rintro ⟨A, hcard, hzero, hsum⟩
    exact ⟨enumerate A hcard, representation_enumerate hcard hzero hsum⟩

theorem enumerate_last_eq_max' {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    enumerate A hA (Fin.last k) = A.max' (Finset.card_pos.mp (by omega)) := by
  unfold enumerate
  have hlast : Fin.last k =
      (⟨k.succ - 1, Nat.sub_lt (Nat.succ_pos k) (Nat.succ_pos 0)⟩ : Fin k.succ) := by
    apply Fin.ext
    simp
  rw [hlast]
  exact Finset.orderEmbOfFin_last (s := A) hA (Nat.succ_pos k)

theorem lastDenominators_iff_finset {k m : ℕ} :
    m ∈ LastDenominators k ↔
      ∃ (A : Finset ℕ) (hA : A.Nonempty),
        A.card = k.succ ∧ 0 ∉ A ∧
          ∑ a ∈ A, (1 : ℝ) / a = 1 ∧ m = A.max' hA := by
  rw [mem_lastDenominators]
  constructor
  · rintro ⟨n, hn, rfl⟩
    let A := denominatorFinset n
    have hfin := representation_to_finset hn
    have hAne : A.Nonempty := by
      apply Finset.card_pos.mp
      rw [hfin.1]
      exact Nat.succ_pos k
    refine ⟨A, hAne, hfin.1, hfin.2.1, hfin.2.2, ?_⟩
    have henum : n = enumerate A hfin.1 := by
      apply Finset.orderEmbOfFin_unique hfin.1
      · intro i
        exact mem_denominatorFinset.2 ⟨i, rfl⟩
      · exact hn.1
    rw [henum, enumerate_last_eq_max']
  · rintro ⟨A, hAne, hcard, hzero, hsum, rfl⟩
    refine ⟨enumerate A hcard, representation_enumerate hcard hzero hsum, ?_⟩
    exact enumerate_last_eq_max' A hcard

/-! ## Splitting the largest denominator -/

/-- The elementary splitting identity
`1/n = 1/(n+1) + 1/(n(n+1))`. -/
theorem one_div_eq_split (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / n = 1 / (n + 1) + 1 / (n * (n + 1)) := by
  field_simp

/-- Replace the final denominator `m` by `m+1` and `m(m+1)`, retaining all
earlier denominators. -/
def splitLast {k : ℕ} (n : Fin k.succ → ℕ) : Fin k.succ.succ → ℕ :=
  let m := n (Fin.last k)
  Fin.snoc (Fin.snoc (Fin.init n) (m + 1)) (m * (m + 1))

@[simp] theorem splitLast_last {k : ℕ} (n : Fin k.succ → ℕ) :
    splitLast n (Fin.last k.succ) =
      n (Fin.last k) * (n (Fin.last k) + 1) := by
  simp [splitLast]

@[simp] theorem splitLast_penultimate {k : ℕ} (n : Fin k.succ → ℕ) :
    splitLast n (Fin.castSucc (Fin.last k)) = n (Fin.last k) + 1 := by
  simp [splitLast]

@[simp] theorem splitLast_castSucc_castSucc {k : ℕ} (n : Fin k.succ → ℕ)
    (i : Fin k) :
    splitLast n (Fin.castSucc (Fin.castSucc i)) = n (Fin.castSucc i) := by
  simp [splitLast]
  rfl

private theorem strictMono_snoc {r : ℕ} {f : Fin r.succ → ℕ} (hf : StrictMono f)
    {x : ℕ} (hx : f (Fin.last r) < x) :
    StrictMono (Fin.snoc f x) := by
  simpa only [Fin.insertNth_last'] using Fin.strictMono_insertNth_last hf x hx

theorem representation_last_pos {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : Representation k n) :
    0 < n (Fin.last k) := by
  have hne : n (Fin.last k) ≠ 0 := by
    intro hzero
    exact hn.2.1 ⟨Fin.last k, hzero⟩
  omega

theorem representation_last_gt_one {k : ℕ} {n : Fin k.succ → ℕ}
    (hk : 1 ≤ k) (hn : Representation k n) :
    1 < n (Fin.last k) := by
  have hnzero : n 0 ≠ 0 := by
    intro hzero
    exact hn.2.1 ⟨0, hzero⟩
  have hidx : (0 : Fin k.succ) < Fin.last k := by
    change 0 < k
    omega
  have hlt := hn.1 hidx
  omega

theorem splitLast_strictMono {k : ℕ} {n : Fin k.succ → ℕ}
    (hk : 1 ≤ k) (hn : Representation k n) :
    StrictMono (splitLast n) := by
  let m := n (Fin.last k)
  have hm : 1 < m := representation_last_gt_one hk hn
  have hinit : StrictMono (Fin.init n) := hn.1.comp Fin.strictMono_castSucc
  have hinner : StrictMono (Fin.snoc (Fin.init n) (m + 1)) := by
    cases k with
    | zero => omega
    | succ r =>
        apply strictMono_snoc hinit
        dsimp [m]
        have hlt := hn.1 (Fin.castSucc_lt_last (Fin.last r))
        change n (Fin.castSucc (Fin.last r)) < n (Fin.last (r + 1)) + 1
        exact hlt.trans (Nat.lt_succ_self _)
  apply strictMono_snoc hinner
  simp only [Fin.snoc_last]
  nlinarith [Nat.mul_pos (by omega : 0 < m) (Nat.succ_pos m)]

theorem splitLast_zero_not_mem {k : ℕ} {n : Fin k.succ → ℕ}
    (hk : 1 ≤ k) (hn : Representation k n) :
    0 ∉ Set.range (splitLast n) := by
  have hfirst : splitLast n 0 = n 0 := by
    let i0 : Fin k := ⟨0, by omega⟩
    calc
      splitLast n 0 = splitLast n (Fin.castSucc (Fin.castSucc i0)) := by
        congr 1
      _ = n (Fin.castSucc i0) := splitLast_castSucc_castSucc n i0
      _ = n 0 := by congr 1
  have hnzero : 0 < n 0 := by
    have : n 0 ≠ 0 := by
      intro hzero
      exact hn.2.1 ⟨0, hzero⟩
    omega
  intro hzero
  obtain ⟨i, hi⟩ := hzero
  have hle := (splitLast_strictMono hk hn).monotone (Fin.zero_le i)
  rw [hfirst, hi] at hle
  omega

theorem splitLast_sum {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : Representation k n) :
    1 = ∑ i, (1 : ℝ) / splitLast n i := by
  let m := n (Fin.last k)
  have hmpos : 0 < m := representation_last_pos hn
  have hsplit := one_div_eq_split m hmpos
  have horig := hn.2.2
  rw [Fin.sum_univ_castSucc] at horig
  rw [Fin.sum_univ_castSucc]
  simp only [splitLast, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init]
  dsimp [m] at hsplit ⊢
  push_cast at hsplit ⊢
  rw [add_assoc, ← hsplit]
  exact horig

theorem representation_splitLast {k : ℕ} {n : Fin k.succ → ℕ}
    (hk : 1 ≤ k) (hn : Representation k n) :
    Representation k.succ (splitLast n) :=
  ⟨splitLast_strictMono hk hn, splitLast_zero_not_mem hk hn, splitLast_sum hn⟩

theorem validIndices_succ {k : ℕ} (hk : 1 ≤ k) (hvalid : k ∈ ValidIndices) :
    k.succ ∈ ValidIndices := by
  obtain ⟨n, hn⟩ := hvalid
  exact ⟨splitLast n, representation_splitLast hk hn⟩

/-- Iterating the last-denominator split pads any representation at an index
at least one by an arbitrary finite number of additional terms. -/
theorem add_mem_validIndices {k : ℕ} (hk : 1 ≤ k) (hvalid : k ∈ ValidIndices) :
    ∀ d : ℕ, k + d ∈ ValidIndices
  | 0 => by simpa using hvalid
  | d + 1 => by
      have ih := add_mem_validIndices hk hvalid d
      have hs := validIndices_succ (k := k + d) (by omega) ih
      simpa [Nat.add_assoc] using hs

/-- The classical seed `1/2 + 1/3 + 1/6 = 1`. -/
theorem two_mem_validIndices : 2 ∈ ValidIndices := by
  let n : Fin 3 → ℕ := ![2, 3, 6]
  refine ⟨n, ?_, ?_, ?_⟩
  · decide
  · decide
  · norm_num [n, Fin.sum_univ_succ]

theorem add_two_mem_validIndices : ∀ d : ℕ, 2 + d ∈ ValidIndices
  := add_mem_validIndices (k := 2) (by omega) two_mem_validIndices

/-- There are representations with every number of terms at least three. -/
theorem mem_validIndices_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    k ∈ ValidIndices := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact add_two_mem_validIndices d

theorem eventually_mem_validIndices : ∀ᶠ k in atTop, k ∈ ValidIndices := by
  rw [eventually_atTop]
  exact ⟨2, fun k hk ↦ mem_validIndices_of_two_le hk⟩

end

end Erdos285

#print axioms Erdos285.exists_minimalLastDenominator
#print axioms Erdos285.eventually_mem_validIndices
