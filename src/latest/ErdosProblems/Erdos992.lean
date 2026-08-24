/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 992.
https://www.erdosproblems.com/forum/thread/992

Informal authors:
- István Berkes
- Walter Philipp

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos992.md
-/
/-
This file formalizes the negative resolution of Erdős Problem 992.

The construction is a self-contained resonant-block version of the mechanism
behind Berkes--Philipp, "The size of trigonometric and Walsh series and
uniform distribution mod 1", J. London Math. Soc. (2) 50 (1994), 454--464.
The detailed mathematical proof is in `tex/992.tex`.
-/

import Mathlib

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace Erdos992

/-! ## The discrepancy in the problem -/

/-- The number of the first `N` fractional parts lying in `[a,b)`. -/
noncomputable def intervalCount (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ Ico a b).card

/-- The type of half-open subintervals of `[0,1]`, represented by endpoints. -/
def UnitSubinterval := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- The signed error associated with one interval. -/
noncomputable def intervalError (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : UnitSubinterval) : ℝ :=
  intervalCount x α N I.1.1 I.1.2 - (I.1.2 - I.1.1) * N

/-- The unnormalised interval discrepancy from Erdős Problem 992. -/
noncomputable def intervalDiscrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : UnitSubinterval ↦ |intervalError x α N I|)

private lemma intervalCount_le (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (a b : ℝ) :
    intervalCount x α N a b ≤ N := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range N)

private lemma intervalError_abs_le (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    (I : UnitSubinterval) : |intervalError x α N I| ≤ N := by
  rcases I.2 with ⟨ha0, hab, hb1⟩
  have hc : (intervalCount x α N I.1.1 I.1.2 : ℝ) ≤ N := by
    exact_mod_cast intervalCount_le x α N I.1.1 I.1.2
  have hlen0 : 0 ≤ I.1.2 - I.1.1 := sub_nonneg.2 hab
  have hlen1 : I.1.2 - I.1.1 ≤ 1 := by linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hexp0 : 0 ≤ (I.1.2 - I.1.1) * (N : ℝ) := mul_nonneg hlen0 hN0
  have hexpN : (I.1.2 - I.1.1) * (N : ℝ) ≤ N := by
    nlinarith
  have hcount0 : (0 : ℝ) ≤ intervalCount x α N I.1.1 I.1.2 := by positivity
  rw [intervalError]
  rw [abs_le]
  constructor <;> linarith

lemma intervalError_le_discrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    (I : UnitSubinterval) :
    |intervalError x α N I| ≤ intervalDiscrepancy x α N := by
  apply le_csSup
  · refine ⟨(N : ℝ), ?_⟩
    rintro y ⟨J, rfl⟩
    exact intervalError_abs_le x α N J
  · exact ⟨I, rfl⟩

/-- A concrete interval can be used as a lower bound for discrepancy. -/
lemma concrete_interval_le_discrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(intervalCount x α N a b : ℝ) - (b - a) * N| ≤
      intervalDiscrepancy x α N := by
  let I : UnitSubinterval := ⟨(a, b), ha, hab, hb⟩
  simpa [I, intervalError] using intervalError_le_discrepancy x α N I

/-- A precise, loophole-free form of `limsup d(N)/sqrt(N log N) > 0`. -/
def HasPositiveSqrtNLogNLimsup (d : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
    c * Real.sqrt ((N : ℝ) * Real.log N) ≤ d N

/-! ## Elementary endpoint lemmas -/

lemma max_abs_ge_half_sub (u v t : ℝ) (h : t ≤ v - u) :
    t / 2 ≤ max |u| |v| := by
  have huv : v - u ≤ |v| + |u| := by
    calc
      v - u ≤ |v - u| := le_abs_self _
      _ ≤ |v| + |u| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le v (-u)
  have hsum : t ≤ |v| + |u| := h.trans huv
  have hu : |u| ≤ max |u| |v| := le_max_left _ _
  have hv : |v| ≤ max |u| |v| := le_max_right _ _
  linarith

lemma one_endpoint_large {A : ℕ → ℝ} {s L : ℕ} {t : ℝ}
    (hinc : t ≤ A (s + L) - A s) :
    t / 2 ≤ max |A s| |A (s + L)| := by
  exact max_abs_ge_half_sub _ _ _ hinc

/-! ## The resonant block sequence -/

/-- The dyadic phase containing block `j`. -/
def phase (j : ℕ) : ℕ := Nat.log2 (j + 1)

/-- All `2^h` blocks in phase `h` have length `2^h (h+1)`. -/
def blockLength (j : ℕ) : ℕ := 2 ^ phase j * (phase j + 1)

lemma blockLength_pos (j : ℕ) : 0 < blockLength j := by
  simp [blockLength]

/-- Prefix endpoint of the first `j` blocks. -/
def endpoint : ℕ → ℕ
  | 0 => 0
  | j + 1 => endpoint j + blockLength j

@[simp] lemma endpoint_zero : endpoint 0 = 0 := rfl

@[simp] lemma endpoint_succ (j : ℕ) :
    endpoint (j + 1) = endpoint j + blockLength j := rfl

lemma endpoint_strictMono : StrictMono endpoint := by
  exact strictMono_nat_of_lt_succ fun j ↦ by
    rw [endpoint_succ]
    have := blockLength_pos j
    omega

lemma self_le_endpoint (j : ℕ) : j ≤ endpoint j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [endpoint_succ]
      have := blockLength_pos j
      omega

/-- The mixed-radix base used by the `j`th resonance event. -/
def radix (j : ℕ) : ℕ := 12 * blockLength j

lemma radix_pos (j : ℕ) : 0 < radix j := by
  simp [radix, blockLength_pos]

/-- The common difference of the `j`th arithmetic block. -/
def frequency : ℕ → ℕ
  | 0 => 1
  | j + 1 => radix j * frequency j

@[simp] lemma frequency_zero : frequency 0 = 1 := rfl

@[simp] lemma frequency_succ (j : ℕ) :
    frequency (j + 1) = radix j * frequency j := rfl

lemma frequency_pos (j : ℕ) : 0 < frequency j := by
  induction j with
  | zero => simp
  | succ j ih => simp [frequency_succ, radix_pos j, ih]

private lemma exists_lt_endpoint_succ (n : ℕ) : ∃ j, n < endpoint (j + 1) := by
  refine ⟨n + 1, ?_⟩
  have h := self_le_endpoint (n + 2)
  have h' : n < endpoint (n + 2) := Nat.lt_of_lt_of_le (by omega) h
  simpa only [Nat.add_assoc] using h'

/-- The unique block containing the sequence index `n`. -/
noncomputable def blockIndex (n : ℕ) : ℕ :=
  Nat.find (exists_lt_endpoint_succ n)

lemma blockIndex_spec (n : ℕ) :
    endpoint (blockIndex n) ≤ n ∧ n < endpoint (blockIndex n + 1) := by
  constructor
  · by_contra h
    have hn : n < endpoint (blockIndex n) := by omega
    rcases Nat.eq_zero_or_pos (blockIndex n) with hzero | hpos
    · simp [hzero] at hn
    · have hpred : blockIndex n - 1 < blockIndex n := by omega
      have hbad := Nat.find_min (exists_lt_endpoint_succ n) hpred
      have heq : blockIndex n - 1 + 1 = blockIndex n := by omega
      exact hbad (by simpa [heq] using hn)
  · exact Nat.find_spec (exists_lt_endpoint_succ n)

lemma blockIndex_eq_of_mem {n j : ℕ} (hlo : endpoint j ≤ n)
    (hhi : n < endpoint (j + 1)) : blockIndex n = j := by
  apply le_antisymm
  · exact Nat.find_min' (exists_lt_endpoint_succ n) hhi
  · by_contra h
    have hj : blockIndex n < j := by omega
    have hmono : endpoint (blockIndex n + 1) ≤ endpoint j := by
      exact (endpoint_strictMono.monotone (Nat.succ_le_iff.2 hj))
    exact (not_lt_of_ge (hmono.trans hlo)) (blockIndex_spec n).2

/-- Position in the containing block, numbered from `1`. -/
noncomputable def blockPosition (n : ℕ) : ℕ :=
  n - endpoint (blockIndex n) + 1

lemma blockPosition_pos (n : ℕ) : 0 < blockPosition n := by
  simp [blockPosition]

lemma blockPosition_le (n : ℕ) :
    blockPosition n ≤ blockLength (blockIndex n) := by
  have hs := blockIndex_spec n
  rw [endpoint_succ] at hs
  simp only [blockPosition]
  omega

/-- The natural-number sequence obtained by concatenating the arithmetic blocks. -/
noncomputable def naturalSequence (n : ℕ) : ℕ :=
  blockPosition n * frequency (blockIndex n)

/-- The integer-valued sequence occurring in the final theorem. -/
noncomputable def integerSequence (n : ℕ) : ℤ := naturalSequence n

private lemma naturalSequence_strictMono : StrictMono naturalSequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  let j := blockIndex n
  have hn := blockIndex_spec n
  change endpoint j ≤ n ∧ n < endpoint (j + 1) at hn
  by_cases hinside : n + 1 < endpoint (j + 1)
  · have hjnext : blockIndex (n + 1) = j :=
      blockIndex_eq_of_mem (hn.1.trans (Nat.le_succ n)) hinside
    have hj : blockIndex n = j := rfl
    simp only [naturalSequence, blockPosition, hj, hjnext]
    have hq := frequency_pos j
    have hsub : n - endpoint j + 1 < (n + 1) - endpoint j + 1 := by omega
    exact Nat.mul_lt_mul_of_pos_right hsub hq
  · have hboundary : n + 1 = endpoint (j + 1) := by omega
    have hnextUpper : n + 1 < endpoint (j + 1 + 1) := by
      rw [hboundary]
      exact endpoint_strictMono (by omega)
    have hjnext : blockIndex (n + 1) = j + 1 := by
      apply blockIndex_eq_of_mem
      · omega
      · exact hnextUpper
    have hj : blockIndex n = j := rfl
    have hposEq : blockPosition n = blockLength j := by
      simp only [blockPosition, hj]
      rw [endpoint_succ] at hboundary
      omega
    have hnextPos : blockPosition (n + 1) = 1 := by
      simp only [blockPosition, hjnext]
      omega
    simp only [naturalSequence, hj, hjnext, hposEq, hnextPos, one_mul, frequency_succ]
    have hq := frequency_pos j
    have hL := blockLength_pos j
    simp only [radix]
    nlinarith

lemma integerSequence_strictMono : StrictMono integerSequence := by
  intro a b hab
  change (naturalSequence a : ℤ) < naturalSequence b
  exact_mod_cast naturalSequence_strictMono hab

/-! ## Finite mixed-radix cylinders -/

/-- The `a`th half-open cell of the grid with denominator `q`. -/
def gridCell (q a : ℕ) : Set ℝ :=
  Ico ((a : ℝ) / q) (((a + 1 : ℕ) : ℝ) / q)

/-- A finite union of cells in one grid. -/
def gridSet (q : ℕ) (A : Finset ℕ) : Set ℝ :=
  ⋃ a ∈ A, gridCell q a

lemma gridCell_measurable (q a : ℕ) : MeasurableSet (gridCell q a) :=
  measurableSet_Ico

lemma gridSet_measurable (q : ℕ) (A : Finset ℕ) : MeasurableSet (gridSet q A) := by
  exact A.measurableSet_biUnion fun a _ ↦ gridCell_measurable q a

private lemma gridCell_pairwiseDisjoint {q : ℕ} (hq : 0 < q) :
    (Set.univ : Set ℕ).PairwiseDisjoint (gridCell q) := by
  intro a _ b _ hab
  change Disjoint (gridCell q a) (gridCell q b)
  rw [Set.disjoint_left]
  intro x hxa hxb
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · have hsucc : a + 1 ≤ b := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hend : (((a + 1 : ℕ) : ℝ) / q) ≤ (b : ℝ) / q := by
      gcongr
    exact (not_lt_of_ge (hend.trans hxb.1)) hxa.2
  · have hsucc : b + 1 ≤ a := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hend : (((b + 1 : ℕ) : ℝ) / q) ≤ (a : ℝ) / q := by
      gcongr
    exact (not_lt_of_ge (hend.trans hxa.1)) hxb.2

lemma volume_gridCell {q : ℕ} (hq : 0 < q) (a : ℕ) :
    volume (gridCell q a) = ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [gridCell, Real.volume_Ico]
  congr 1
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp
  ring

lemma volume_gridSet {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    volume (gridSet q A) = A.card * ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [gridSet, measure_biUnion_finset]
  · simp_rw [volume_gridCell hq]
    simp
  · intro a ha b hb hab
    exact gridCell_pairwiseDisjoint hq (Set.mem_univ a) (Set.mem_univ b) hab
  · intro a _
    exact gridCell_measurable q a

/-- The children of cell `a` after refining by a factor `m`. -/
def allChildren (m a : ℕ) : Finset ℕ :=
  (Finset.range m).image fun d ↦ a * m + d

/-- Only the digit-zero child of cell `a`. -/
def zeroChild (m a : ℕ) : Finset ℕ := {a * m}

private lemma union_initial_children {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (a k : ℕ) (hk : k ≤ m) :
    (⋃ d ∈ Finset.range k, gridCell (q * m) (a * m + d)) =
      Ico ((a * m : ℕ) / (q * m : ℕ) : ℝ)
        (((a * m + k : ℕ) : ℝ) / (q * m : ℕ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ m := by omega
      rw [Finset.range_add_one, Finset.set_biUnion_insert]
      · rw [ih hk']
        rw [union_comm]
        unfold gridCell
        rw [show a * m + k + 1 = a * m + (k + 1) by omega]
        apply Set.Ico_union_Ico_eq_Ico
        · gcongr <;> omega
        · gcongr <;> omega

private lemma union_all_children {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (a : ℕ) :
    (⋃ d ∈ Finset.range m, gridCell (q * m) (a * m + d)) = gridCell q a := by
  rw [union_initial_children hq hm a m le_rfl]
  unfold gridCell
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  congr 1 <;> push_cast <;> field_simp

private lemma gridSet_allChildren {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (A : Finset ℕ) :
    gridSet (q * m) (A.biUnion (allChildren m)) = gridSet q A := by
  rw [gridSet, Finset.set_biUnion_biUnion]
  apply iUnion_congr
  intro a
  apply iUnion_congr
  intro ha
  rw [← union_all_children hq hm a]
  have himage :
      (⋃ y ∈ (Finset.range m).image (fun d ↦ a * m + d), gridCell (q * m) y) =
        ⋃ d ∈ Finset.range m, gridCell (q * m) (a * m + d) := by
    ext x
    simp
  exact himage

/-- Refine each selected cell and retain only its digit-zero child. -/
def zeroRefine (m : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ a * m

private lemma zeroChild_subset_parent {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (a : ℕ) : gridCell (q * m) (a * m) ⊆ gridCell q a := by
  intro x hx
  unfold gridCell at hx ⊢
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · calc
      (a : ℝ) / q = ((a * m : ℕ) : ℝ) / (q * m : ℕ) := by
          push_cast
          field_simp
      _ ≤ x := hx.1
  · calc
      x < (((a * m + 1 : ℕ) : ℝ) / (q * m : ℕ)) := hx.2
      _ ≤ ((a + 1 : ℕ) : ℝ) / q := by
        push_cast
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < q * m) hqR).2
        have hm_one : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hqm : (q : ℝ) ≤ q * m := by
          calc
            (q : ℝ) = q * 1 := by ring
            _ ≤ q * m := mul_le_mul_of_nonneg_left hm_one hqR.le
        calc
          ((a : ℝ) * m + 1) * q = (a : ℝ) * m * q + q := by ring
          _ ≤ (a : ℝ) * m * q + q * m := by
            linarith
          _ = ((a : ℝ) + 1) * (q * m) := by ring

private lemma gridSet_zeroRefine_inter {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    {A : Finset ℕ} (hA : A ⊆ Finset.range q) :
    gridSet q A ∩ gridSet (q * m) (zeroRefine m (Finset.range q)) =
      gridSet (q * m) (zeroRefine m A) := by
  ext x
  constructor
  · rintro ⟨hxA, hxE⟩
    rw [gridSet] at hxA hxE
    simp only [Set.mem_iUnion] at hxA hxE
    obtain ⟨a, haA, hxa⟩ := hxA
    obtain ⟨z, hz, hxz⟩ := hxE
    rw [zeroRefine, Finset.mem_image] at hz
    obtain ⟨b, hbq, rfl⟩ := hz
    have hxb : x ∈ gridCell q b := zeroChild_subset_parent hq hm b hxz
    have hab : a = b := by
      by_contra hab
      exact (Set.disjoint_left.1
        (gridCell_pairwiseDisjoint hq (Set.mem_univ a) (Set.mem_univ b) hab)) hxa hxb
    subst b
    rw [gridSet]
    simp only [Set.mem_iUnion]
    refine ⟨a * m, ?_, hxz⟩
    rw [zeroRefine, Finset.mem_image]
    exact ⟨a, haA, rfl⟩
  · intro hx
    rw [gridSet] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    rw [zeroRefine, Finset.mem_image] at hz
    obtain ⟨a, haA, rfl⟩ := hz
    constructor
    · rw [gridSet]
      simp only [Set.mem_iUnion]
      exact ⟨a, haA, zeroChild_subset_parent hq hm a hxz⟩
    · rw [gridSet]
      simp only [Set.mem_iUnion]
      refine ⟨a * m, ?_, hxz⟩
      rw [zeroRefine, Finset.mem_image]
      exact ⟨a, hA haA, rfl⟩

lemma volume_gridSet_zeroRefine {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (A : Finset ℕ) :
    volume (gridSet (q * m) (zeroRefine m A)) =
      A.card * ENNReal.ofReal (1 / ((q * m : ℕ) : ℝ)) := by
  rw [volume_gridSet (Nat.mul_pos hq hm)]
  congr 1
  have hcard : (zeroRefine m A).card = A.card := by
    exact Finset.card_image_of_injective A (fun _ _ h ↦ Nat.mul_right_cancel hm h)
  exact_mod_cast hcard

/-- The digit-zero resonance event at block `j`. -/
def resonanceEvent (j : ℕ) : Set ℝ :=
  gridSet (frequency j * radix j) (zeroRefine (radix j) (Finset.range (frequency j)))

lemma resonanceEvent_measurable (j : ℕ) : MeasurableSet (resonanceEvent j) :=
  gridSet_measurable _ _

lemma resonanceEvent_eq (j : ℕ) :
    resonanceEvent j =
      gridSet (frequency (j + 1))
        (zeroRefine (radix j) (Finset.range (frequency j))) := by
  rw [resonanceEvent, frequency_succ, Nat.mul_comm]

/-! ## Finite intersections and independence -/

/-- Lebesgue measure restricted to the unit interval. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Ico 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  refine ⟨?_⟩
  rw [unitMeasure, Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Ico]

/-- The surviving cells after imposing precisely the digit conditions in `s`
through level `r`. -/
def allowedCells (s : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | r + 1 =>
      if r ∈ s then zeroRefine (radix r) (allowedCells s r)
      else (allowedCells s r).biUnion (allChildren (radix r))

private lemma allowedCells_subset (s : Finset ℕ) (r : ℕ) :
    allowedCells s r ⊆ Finset.range (frequency r) := by
  induction r with
  | zero => simp [allowedCells]
  | succ r ih =>
      rw [allowedCells]
      split_ifs with hrs
      · intro z hz
        rw [zeroRefine, Finset.mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        rw [Finset.mem_range, frequency_succ]
        simpa [Nat.mul_comm] using
          Nat.mul_lt_mul_of_pos_right (Finset.mem_range.1 (ih ha)) (radix_pos r)
      · intro z hz
        rw [Finset.mem_biUnion] at hz
        obtain ⟨a, ha, hz⟩ := hz
        rw [allChildren, Finset.mem_image] at hz
        obtain ⟨d, hd, rfl⟩ := hz
        rw [Finset.mem_range] at hd ⊢
        rw [frequency_succ]
        have ha' : a < frequency r := Finset.mem_range.1 (ih ha)
        have hm := radix_pos r
        have hle : (a + 1) * radix r ≤ frequency r * radix r := by
          exact Nat.mul_le_mul_right _ (by omega)
        have hlt : a * radix r + d < (a + 1) * radix r := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left hd _
        rw [Nat.mul_comm (radix r) (frequency r)]
        exact hlt.trans_le hle

/-- The unit interval with the events below level `r` imposed. -/
def prefixIntersection (s : Finset ℕ) (r : ℕ) : Set ℝ :=
  Ico 0 1 ∩ ⋂ j ∈ s.filter (fun j ↦ j < r), resonanceEvent j

private lemma prefixIntersection_zero (s : Finset ℕ) :
    prefixIntersection s 0 = gridSet 1 {0} := by
  ext x
  simp [prefixIntersection, gridSet, gridCell]

private lemma prefixIntersection_succ (s : Finset ℕ) (r : ℕ) :
    prefixIntersection s (r + 1) =
      if r ∈ s then prefixIntersection s r ∩ resonanceEvent r
      else prefixIntersection s r := by
  by_cases hrs : r ∈ s
  · have hf : s.filter (fun j ↦ j < r + 1) =
        insert r (s.filter (fun j ↦ j < r)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hjs, hj⟩
        rcases lt_or_eq_of_le (by omega : j ≤ r) with hjr | rfl
        · exact Or.inr ⟨hjs, hjr⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hjs, hjr⟩)
        · exact ⟨hrs, by omega⟩
        · exact ⟨hjs, by omega⟩
    rw [if_pos hrs]
    unfold prefixIntersection
    rw [hf]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_insert]
    aesop
  · have hf : s.filter (fun j ↦ j < r + 1) =
        s.filter (fun j ↦ j < r) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hjs, hj⟩
        refine ⟨hjs, ?_⟩
        have hjne : j ≠ r := by
          intro h
          subst j
          exact hrs hjs
        omega
      · rintro ⟨hjs, hj⟩
        exact ⟨hjs, by omega⟩
    rw [if_neg hrs]
    unfold prefixIntersection
    rw [hf]

private lemma prefixIntersection_grid (s : Finset ℕ) (r : ℕ) :
    prefixIntersection s r = gridSet (frequency r) (allowedCells s r) := by
  induction r with
  | zero => simpa [frequency_zero, allowedCells] using prefixIntersection_zero s
  | succ r ih =>
      rw [prefixIntersection_succ, allowedCells]
      by_cases hrs : r ∈ s
      · rw [if_pos hrs, if_pos hrs, ih, resonanceEvent]
        rw [frequency_succ, Nat.mul_comm (radix r) (frequency r)]
        exact gridSet_zeroRefine_inter (frequency_pos r) (radix_pos r)
          (allowedCells_subset s r)
      · rw [if_neg hrs, if_neg hrs, ih, frequency_succ, Nat.mul_comm]
        exact (gridSet_allChildren (frequency_pos r) (radix_pos r)
          (allowedCells s r)).symm

private lemma prefixIntersection_measurable (s : Finset ℕ) (r : ℕ) :
    MeasurableSet (prefixIntersection s r) := by
  rw [prefixIntersection_grid]
  exact gridSet_measurable _ _

private lemma resonanceEvent_subset_unit (j : ℕ) :
    resonanceEvent j ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  rw [resonanceEvent, gridSet] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  rw [zeroRefine, Finset.mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  have hparent := zeroChild_subset_parent (frequency_pos j) (radix_pos j) a hxz
  rw [Finset.mem_range] at ha
  unfold gridCell at hparent
  constructor
  · exact le_trans (by positivity) hparent.1
  · have hqR : (0 : ℝ) < frequency j := by exact_mod_cast frequency_pos j
    have haR : ((a + 1 : ℕ) : ℝ) ≤ frequency j := by
      exact_mod_cast (show a + 1 ≤ frequency j by omega)
    calc
      x < (((a + 1 : ℕ) : ℝ) / frequency j) := hparent.2
      _ ≤ 1 := (div_le_one hqR).2 haR

private lemma unitMeasure_resonanceEvent (j : ℕ) :
    unitMeasure (resonanceEvent j) =
      ENNReal.ofReal (1 / (radix j : ℝ)) := by
  rw [unitMeasure, Measure.restrict_apply (resonanceEvent_measurable j)]
  rw [inter_eq_left.2 (resonanceEvent_subset_unit j)]
  rw [resonanceEvent, volume_gridSet_zeroRefine (frequency_pos j) (radix_pos j)]
  have hqR : (0 : ℝ) < frequency j := by exact_mod_cast frequency_pos j
  have hmR : (0 : ℝ) < radix j := by exact_mod_cast radix_pos j
  have hreal :
      (frequency j : ℝ) * (1 / ((frequency j * radix j : ℕ) : ℝ)) =
        1 / (radix j : ℝ) := by
    push_cast
    field_simp
  rw [Finset.card_range]
  rw [show (frequency j : ℝ≥0∞) = ENNReal.ofReal (frequency j : ℝ) by simp]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ frequency j)]
  exact congrArg ENNReal.ofReal hreal

private lemma volume_prefixIntersection_selected (s : Finset ℕ) (r : ℕ)
    (hrs : r ∈ s) :
    volume (prefixIntersection s (r + 1)) =
      volume (prefixIntersection s r) *
        ENNReal.ofReal (1 / (radix r : ℝ)) := by
  rw [prefixIntersection_succ, if_pos hrs, prefixIntersection_grid, resonanceEvent]
  rw [gridSet_zeroRefine_inter (frequency_pos r) (radix_pos r)
    (allowedCells_subset s r)]
  rw [volume_gridSet_zeroRefine (frequency_pos r) (radix_pos r)]
  rw [volume_gridSet (frequency_pos r)]
  have hqR : (0 : ℝ) < frequency r := by exact_mod_cast frequency_pos r
  have hmR : (0 : ℝ) < radix r := by exact_mod_cast radix_pos r
  have hreal :
      1 / ((frequency r * radix r : ℕ) : ℝ) =
        (1 / (frequency r : ℝ)) * (1 / (radix r : ℝ)) := by
    push_cast
    field_simp
  rw [hreal, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / frequency r)]
  ring

private lemma filter_lt_succ_of_mem (s : Finset ℕ) {r : ℕ} (hrs : r ∈ s) :
    s.filter (fun j ↦ j < r + 1) = insert r (s.filter fun j ↦ j < r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hjs, hj⟩
    rcases lt_or_eq_of_le (by omega : j ≤ r) with hjr | rfl
    · exact Or.inr ⟨hjs, hjr⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hjs, hjr⟩)
    · exact ⟨hrs, by omega⟩
    · exact ⟨hjs, by omega⟩

private lemma filter_lt_succ_of_not_mem (s : Finset ℕ) {r : ℕ} (hrs : r ∉ s) :
    s.filter (fun j ↦ j < r + 1) = s.filter fun j ↦ j < r := by
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hjs, hj⟩
    refine ⟨hjs, ?_⟩
    have hjne : j ≠ r := by
      intro h
      subst j
      exact hrs hjs
    omega
  · rintro ⟨hjs, hj⟩
    exact ⟨hjs, by omega⟩

private lemma volume_prefixIntersection (s : Finset ℕ) (r : ℕ) :
    volume (prefixIntersection s r) =
      ∏ j ∈ s.filter (fun j ↦ j < r),
        ENNReal.ofReal (1 / (radix j : ℝ)) := by
  induction r with
  | zero =>
      rw [prefixIntersection_zero, volume_gridSet (by omega : 0 < 1)]
      simp
  | succ r ih =>
      by_cases hrs : r ∈ s
      · rw [volume_prefixIntersection_selected s r hrs, ih,
          filter_lt_succ_of_mem s hrs]
        simp [Finset.mem_filter, mul_comm]
      · rw [prefixIntersection_succ, if_neg hrs, ih,
          filter_lt_succ_of_not_mem s hrs]

lemma resonanceEvents_independent :
    ProbabilityTheory.iIndepSet resonanceEvent unitMeasure := by
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter resonanceEvent_measurable]
  intro s
  by_cases hs : s = ∅
  · subst s
    simp
  · let r := ∑ j ∈ s, (j + 1)
    have hjr : ∀ j ∈ s, j < r := by
      intro j hjs
      have hle : j + 1 ≤ r := by
        exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (i + 1)) hjs
      omega
    have hfilter : s.filter (fun j ↦ j < r) = s :=
      Finset.filter_eq_self.2 hjr
    have hmeas : MeasurableSet (⋂ j ∈ s, resonanceEvent j) :=
      s.measurableSet_biInter fun j _ ↦ resonanceEvent_measurable j
    calc
      unitMeasure (⋂ j ∈ s, resonanceEvent j) =
          volume ((⋂ j ∈ s, resonanceEvent j) ∩ Ico 0 1) := by
            rw [unitMeasure, Measure.restrict_apply hmeas]
      _ = volume (prefixIntersection s r) := by
            congr 1
            rw [prefixIntersection, hfilter]
            ac_rfl
      _ = ∏ j ∈ s, ENNReal.ofReal (1 / (radix j : ℝ)) := by
            rw [volume_prefixIntersection, hfilter]
      _ = ∏ j ∈ s, unitMeasure (resonanceEvent j) := by
            simp_rw [unitMeasure_resonanceEvent]

/-! ## Divergence of the event measures -/

private lemma phase_eq_of_dyadic_bounds {h j : ℕ}
    (hlo : 2 ^ h - 1 ≤ j) (hhi : j < 2 ^ (h + 1) - 1) :
    phase j = h := by
  rw [phase, Nat.log2_eq_log_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hp : 0 < 2 ^ h := by positivity
    omega
  · have hp : 0 < 2 ^ (h + 1) := by positivity
    omega

private lemma sum_eventProb_dyadic_phase (h : ℕ) :
    (∑ j ∈ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1),
        (1 / (radix j : ℝ))) = 1 / (12 * (h + 1) : ℝ) := by
  have hphase : ∀ j ∈ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1),
      phase j = h := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact phase_eq_of_dyadic_bounds hj.1 hj.2
  calc
    (∑ j ∈ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1),
        (1 / (radix j : ℝ))) =
        ∑ _j ∈ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1),
          (1 / ((12 * (2 ^ h * (h + 1)) : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [radix, blockLength, hphase j hj]
    _ = 1 / (12 * (h + 1) : ℝ) := by
      rw [Finset.sum_const, Nat.card_Ico]
      have hpow : 0 < (2 : ℕ) ^ h := by positivity
      have hcard : 2 ^ (h + 1) - 1 - (2 ^ h - 1) = 2 ^ h := by
        rw [pow_succ]
        omega
      rw [hcard]
      push_cast
      rw [nsmul_eq_mul]
      field_simp
      norm_num

private lemma sum_unitMeasure_dyadic_phase (h : ℕ) :
    (∑ j ∈ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1),
        unitMeasure (resonanceEvent j)) =
      ENNReal.ofReal (1 / (12 * (h + 1) : ℝ)) := by
  simp_rw [unitMeasure_resonanceEvent]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  rw [sum_eventProb_dyadic_phase]

private lemma sum_eventProb_through_phases (H : ℕ) :
    (∑ j ∈ Finset.range (2 ^ H - 1), unitMeasure (resonanceEvent j)) =
      ENNReal.ofReal ((1 / 12 : ℝ) *
        ∑ h ∈ Finset.range H, (1 / (h + 1) : ℝ)) := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hpow_le : 2 ^ H ≤ 2 ^ (H + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hbounds : 2 ^ H - 1 ≤ 2 ^ (H + 1) - 1 := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hbounds]
      rw [ih, sum_unitMeasure_dyadic_phase]
      rw [Finset.sum_range_succ]
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 12 : ℝ) *
        ∑ h ∈ Finset.range H, (1 / (h + 1) : ℝ))
        (by positivity : 0 ≤ 1 / (12 * (H + 1) : ℝ))]
      congr 1
      field_simp

lemma tsum_resonanceEvent_eq_top :
    ∑' j, unitMeasure (resonanceEvent j) = ⊤ := by
  by_contra htop
  have hbound (H : ℕ) :
      ENNReal.ofReal ((1 / 12 : ℝ) *
          ∑ h ∈ Finset.range H, (1 / (h + 1) : ℝ)) ≤
        ∑' j, unitMeasure (resonanceEvent j) := by
    rw [← sum_eventProb_through_phases H]
    exact ENNReal.sum_le_tsum _
  have hboundReal (H : ℕ) :
      (1 / 12 : ℝ) * ∑ h ∈ Finset.range H, (1 / (h + 1) : ℝ) ≤
        (∑' j, unitMeasure (resonanceEvent j)).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).2 (hbound H)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hevent := (tendsto_atTop.1 Real.tendsto_sum_range_one_div_nat_succ_atTop
    (12 * ((∑' j, unitMeasure (resonanceEvent j)).toReal + 1))).exists
  obtain ⟨H, hH⟩ := hevent
  have hnonneg : 0 ≤ (∑' j, unitMeasure (resonanceEvent j)).toReal :=
    ENNReal.toReal_nonneg
  have hlarge :
      (∑' j, unitMeasure (resonanceEvent j)).toReal + 1 ≤
        (1 / 12 : ℝ) * ∑ h ∈ Finset.range H, (1 / (h + 1) : ℝ) := by
    nlinarith
  linarith [hboundReal H]

lemma unitMeasure_limsup_resonanceEvent :
    unitMeasure (limsup resonanceEvent atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one resonanceEvent_measurable
    resonanceEvents_independent tsum_resonanceEvent_eq_top

lemma ae_frequently_resonant :
    ∀ᵐ α : ℝ ∂volume, α ∈ Ico 0 1 →
      ∃ᶠ j : ℕ in atTop, α ∈ resonanceEvent j := by
  have hmeas : MeasurableSet (limsup resonanceEvent atTop) :=
    MeasurableSet.measurableSet_limsup resonanceEvent_measurable
  have haeUnit : ∀ᵐ α : ℝ ∂unitMeasure, α ∈ limsup resonanceEvent atTop := by
    rw [MeasureTheory.ae_iff]
    change unitMeasure (limsup resonanceEvent atTop)ᶜ = 0
    rw [MeasureTheory.measure_compl hmeas]
    · rw [unitMeasure_limsup_resonanceEvent]
      simp
    · rw [unitMeasure_limsup_resonanceEvent]
      simp
  have haeVolume :
      ∀ᵐ α : ℝ ∂volume, α ∈ Ico 0 1 → α ∈ limsup resonanceEvent atTop := by
    have hiff :
        (∀ᵐ α : ℝ ∂volume.restrict (Ico 0 1),
            α ∈ limsup resonanceEvent atTop) ↔
          ∀ᵐ α : ℝ ∂volume,
            α ∈ Ico 0 1 → α ∈ limsup resonanceEvent atTop :=
      MeasureTheory.ae_restrict_iff hmeas
    apply hiff.1
    simpa only [unitMeasure] using haeUnit
  filter_upwards [haeVolume] with α hα hunit
  exact mem_limsup_iff_frequently_mem.1 (hα hunit)

/-! ## A resonant block forces a discrepancy jump -/

private lemma resonanceEvent_fract_frequency {α : ℝ} {j : ℕ}
    (hα : α ∈ resonanceEvent j) :
    Int.fract (α * frequency j) ∈ Ico 0 (1 / (radix j : ℝ)) := by
  rw [resonanceEvent, gridSet] at hα
  simp only [Set.mem_iUnion] at hα
  obtain ⟨z, hz, hxz⟩ := hα
  rw [zeroRefine, Finset.mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  unfold gridCell at hxz
  push_cast at hxz
  have hqR : (0 : ℝ) < frequency j := by exact_mod_cast frequency_pos j
  have hmR : (0 : ℝ) < radix j := by exact_mod_cast radix_pos j
  have hqmR : (0 : ℝ) < frequency j * radix j := mul_pos hqR hmR
  have hloCross := (div_le_iff₀ hqmR).1 hxz.1
  have hhiCross := (lt_div_iff₀ hqmR).1 hxz.2
  have hβ0 : 0 ≤ α * frequency j - a := by
    nlinarith
  have hβm : α * frequency j - a < 1 / (radix j : ℝ) := by
    rw [lt_div_iff₀ hmR]
    nlinarith
  have hβ1 : α * frequency j - a < 1 := by
    have hmOne : (1 : ℝ) ≤ radix j := by exact_mod_cast radix_pos j
    have hone : 1 / (radix j : ℝ) ≤ 1 := by
      exact (div_le_one hmR).2 hmOne
    exact hβm.trans_le hone
  have hfract : Int.fract (α * frequency j) = α * frequency j - a := by
    rw [Int.fract_eq_iff]
    refine ⟨hβ0, hβ1, (a : ℤ), ?_⟩
    push_cast
    ring
  rw [hfract]
  exact ⟨hβ0, hβm⟩

private lemma resonanceEvent_fract_block {α : ℝ} {j k : ℕ}
    (hα : α ∈ resonanceEvent j) (hk0 : 0 < k) (hk : k ≤ blockLength j) :
    Int.fract (α * ((k * frequency j : ℕ) : ℝ)) ∈ Ico 0 (1 / 12 : ℝ) := by
  let β := Int.fract (α * frequency j)
  have hβ := resonanceEvent_fract_frequency hα
  change β ∈ Ico 0 (1 / (radix j : ℝ)) at hβ
  have hL0 : (0 : ℝ) < blockLength j := by exact_mod_cast blockLength_pos j
  have hkR : (k : ℝ) ≤ blockLength j := by exact_mod_cast hk
  have hβL : β * blockLength j < 1 / 12 := by
    rw [radix] at hβ
    push_cast at hβ
    have hcross := (lt_div_iff₀ (by positivity : (0 : ℝ) < 12 * blockLength j)).1 hβ.2
    nlinarith
  have hβk : β * k < 1 / 12 :=
    (mul_le_mul_of_nonneg_left hkR hβ.1).trans_lt hβL
  have hβk1 : β * k < 1 := hβk.trans (by norm_num)
  have hfract :
      Int.fract (α * ((k * frequency j : ℕ) : ℝ)) = β * k := by
    calc
      Int.fract (α * ((k * frequency j : ℕ) : ℝ)) =
          Int.fract ((α * frequency j) * k) := by
            congr 1
            push_cast
            ring
      _ = Int.fract ((β + (⌊α * frequency j⌋ : ℝ)) * k) := by
            rw [Int.fract_add_floor]
      _ = Int.fract (((⌊α * frequency j⌋ * (k : ℤ) : ℤ) : ℝ) + β * k) := by
            congr 1
            push_cast
            ring
      _ = Int.fract (β * k) := Int.fract_intCast_add _ _
      _ = β * k := Int.fract_eq_self.2 ⟨mul_nonneg hβ.1 (by positivity), hβk1⟩
  rw [hfract]
  exact ⟨mul_nonneg hβ.1 (by positivity), hβk⟩

private lemma block_data_at_offset (j t : ℕ) (ht : t < blockLength j) :
    blockIndex (endpoint j + t) = j ∧
      blockPosition (endpoint j + t) = t + 1 ∧
      naturalSequence (endpoint j + t) = (t + 1) * frequency j := by
  have hindex : blockIndex (endpoint j + t) = j := by
    apply blockIndex_eq_of_mem
    · omega
    · rw [endpoint_succ]
      omega
  constructor
  · exact hindex
  · constructor
    · simp [blockPosition, hindex]
    · simp [naturalSequence, blockPosition, hindex]

private lemma intervalCount_succ_of_mem (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    {a b : ℝ} (hN : Int.fract (α * (x N : ℝ)) ∈ Ico a b) :
    intervalCount x α (N + 1) a b = intervalCount x α N a b + 1 := by
  unfold intervalCount
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [hN.1, hN.2]

private lemma resonant_block_count_jump {α : ℝ} {j : ℕ}
    (hα : α ∈ resonanceEvent j) :
    intervalCount integerSequence α (endpoint (j + 1)) 0 (1 / 12) =
      intervalCount integerSequence α (endpoint j) 0 (1 / 12) + blockLength j := by
  have haux : ∀ t ≤ blockLength j,
      intervalCount integerSequence α (endpoint j + t) 0 (1 / 12) =
        intervalCount integerSequence α (endpoint j) 0 (1 / 12) + t := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
        have ht' : t < blockLength j := by omega
        have hdata := block_data_at_offset j t ht'
        have hmem : Int.fract
            (α * (integerSequence (endpoint j + t) : ℝ)) ∈ Ico 0 (1 / 12) := by
          rw [integerSequence, hdata.2.2]
          exact resonanceEvent_fract_block hα (by omega) (by omega)
        rw [show endpoint j + (t + 1) = (endpoint j + t) + 1 by omega]
        rw [intervalCount_succ_of_mem _ _ _ hmem, ih (by omega)]
        omega
  rw [endpoint_succ]
  exact haux (blockLength j) le_rfl

private lemma resonant_block_error_jump {α : ℝ} {j : ℕ}
    (hα : α ∈ resonanceEvent j) :
    (11 / 12 : ℝ) * blockLength j ≤
      ((intervalCount integerSequence α (endpoint (j + 1)) 0 (1 / 12) : ℝ) -
          (1 / 12 : ℝ) * endpoint (j + 1)) -
        ((intervalCount integerSequence α (endpoint j) 0 (1 / 12) : ℝ) -
          (1 / 12 : ℝ) * endpoint j) := by
  rw [resonant_block_count_jump hα, endpoint_succ]
  push_cast
  ring_nf
  norm_num

private lemma resonant_block_discrepancy {α : ℝ} {j : ℕ}
    (hα : α ∈ resonanceEvent j) :
    (11 / 24 : ℝ) * blockLength j ≤
      max (intervalDiscrepancy integerSequence α (endpoint j))
        (intervalDiscrepancy integerSequence α (endpoint (j + 1))) := by
  let A : ℕ → ℝ := fun N ↦
    (intervalCount integerSequence α N 0 (1 / 12) : ℝ) - (1 / 12 : ℝ) * N
  have hlarge : (11 / 24 : ℝ) * blockLength j ≤
      max |A (endpoint j)| |A (endpoint (j + 1))| := by
    have h := one_endpoint_large (A := A) (s := endpoint j) (L := blockLength j)
      (t := (11 / 12 : ℝ) * blockLength j) (by
        simpa only [A, endpoint_succ] using resonant_block_error_jump hα)
    have hcoeff : (11 / 24 : ℝ) * blockLength j =
        ((11 / 12 : ℝ) * blockLength j) / 2 := by ring
    rw [hcoeff]
    simpa only [endpoint_succ] using h
  have hstart : |A (endpoint j)| ≤
      intervalDiscrepancy integerSequence α (endpoint j) := by
    simpa [A] using concrete_interval_le_discrepancy integerSequence α
      (endpoint j) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1)
  have hend : |A (endpoint (j + 1))| ≤
      intervalDiscrepancy integerSequence α (endpoint (j + 1)) := by
    simpa [A] using concrete_interval_le_discrepancy integerSequence α
      (endpoint (j + 1)) (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num : (1 / 12 : ℝ) ≤ 1)
  exact hlarge.trans (max_le_max hstart hend)

private lemma resonant_block_has_large_endpoint {α : ℝ} {j : ℕ}
    (hα : α ∈ resonanceEvent j) :
    ∃ N, (N = endpoint j ∨ N = endpoint (j + 1)) ∧
      (11 / 24 : ℝ) * blockLength j ≤ intervalDiscrepancy integerSequence α N := by
  rcases (le_max_iff.1 (resonant_block_discrepancy hα)) with h | h
  · exact ⟨endpoint j, Or.inl rfl, h⟩
  · exact ⟨endpoint (j + 1), Or.inr rfl, h⟩

/-! ## Growth of block endpoints -/

private lemma phase_mono : Monotone phase := by
  intro i j hij
  rw [phase, phase, Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right (by omega)

private lemma blockLength_mono : Monotone blockLength := by
  intro i j hij
  have hp := phase_mono hij
  unfold blockLength
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hp) (Nat.succ_le_succ hp)

private lemma endpoint_succ_le_mul_blockLength (j : ℕ) :
    endpoint (j + 1) ≤ (j + 1) * blockLength j := by
  induction j with
  | zero => simp [endpoint_succ]
  | succ j ih =>
      rw [endpoint_succ]
      calc
        endpoint (j + 1) + blockLength (j + 1) ≤
            (j + 1) * blockLength j + blockLength (j + 1) :=
          Nat.add_le_add_right ih _
        _ ≤ (j + 1) * blockLength (j + 1) + blockLength (j + 1) := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left (j + 1) (blockLength_mono (by omega))) _
        _ = (j + 1 + 1) * blockLength (j + 1) := by ring

private lemma index_lt_phase_power (j : ℕ) :
    j + 1 < 2 ^ (phase j + 1) := by
  simpa only [phase, Nat.log2_eq_log_two] using
    Nat.lt_pow_succ_log_self (by omega : 1 < 2) (j + 1)

private lemma endpoint_succ_dyadic_bound (j : ℕ) :
    endpoint (j + 1) ≤
      2 * (2 ^ phase j * 2 ^ phase j) * (phase j + 1) := by
  calc
    endpoint (j + 1) ≤ (j + 1) * blockLength j :=
      endpoint_succ_le_mul_blockLength j
    _ ≤ 2 ^ (phase j + 1) * blockLength j := by
      exact Nat.mul_le_mul_right _ (index_lt_phase_power j).le
    _ = 2 * (2 ^ phase j * 2 ^ phase j) * (phase j + 1) := by
      rw [blockLength, pow_succ]
      ring

private lemma sqrt_endpoint_log_le (j N : ℕ)
    (hNlow : 1 ≤ N) (hN : N ≤ endpoint (j + 1)) :
    Real.sqrt ((N : ℝ) * Real.log N) ≤ (3 : ℝ) * blockLength j := by
  let h := phase j
  have hupperNat : N ≤ 2 * (2 ^ h * 2 ^ h) * (h + 1) := by
    exact hN.trans (by simpa only [h] using endpoint_succ_dyadic_bound j)
  have hupper : (N : ℝ) ≤
      2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) * (h + 1) := by
    exact_mod_cast hupperNat
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNlow
  have hUpos : (0 : ℝ) <
      2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) * (h + 1) := by positivity
  have hlogMono : Real.log N ≤
      Real.log (2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) * (h + 1)) :=
    Real.strictMonoOn_log.monotoneOn hNpos hUpos hupper
  have hlogTwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    exact ht
  have hlogH : Real.log ((h + 1 : ℕ) : ℝ) ≤ h := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (h + 1 : ℕ))
    simpa using this
  have hlogExpand :
      Real.log (2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) * (h + 1)) =
        Real.log 2 + h * Real.log 2 + h * Real.log 2 + Real.log (h + 1) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    ring
  have hlog : Real.log N ≤ 3 * (h + 1 : ℝ) := by
    rw [hlogExpand] at hlogMono
    push_cast at hlogMono hlogH ⊢
    nlinarith
  have hlogNonneg : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hNlow)
  have hprod : (N : ℝ) * Real.log N ≤
      (3 * (blockLength j : ℝ)) ^ 2 := by
    have hmul := mul_le_mul hupper hlog hlogNonneg hUpos.le
    dsimp [h] at hmul
    rw [blockLength]
    push_cast
    nlinarith [sq_nonneg (((2 : ℝ) ^ phase j) * (phase j + 1))]
  rw [Real.sqrt_le_iff]
  exact ⟨by positivity, hprod⟩

private lemma frequently_large_discrepancy {α : ℝ}
    (hfreq : ∃ᶠ j : ℕ in atTop, α ∈ resonanceEvent j) :
    ∃ᶠ N : ℕ in atTop,
      (1 / 8 : ℝ) * Real.sqrt ((N : ℝ) * Real.log N) ≤
        intervalDiscrepancy integerSequence α N := by
  rw [Filter.frequently_atTop]
  intro K
  obtain ⟨j, hj, hα⟩ := (Filter.frequently_atTop.1 hfreq) (max K 1)
  have hjK : K ≤ j := (le_max_left K 1).trans hj
  have hj1 : 1 ≤ j := (le_max_right K 1).trans hj
  obtain ⟨N, hNcases, hdisc⟩ := resonant_block_has_large_endpoint hα
  have hNK : K ≤ N := by
    rcases hNcases with rfl | rfl
    · exact hjK.trans (self_le_endpoint j)
    · exact hjK.trans (Nat.le_succ j) |>.trans (self_le_endpoint (j + 1))
  have hNlow : 1 ≤ N := by
    rcases hNcases with rfl | rfl
    · exact hj1.trans (self_le_endpoint j)
    · exact hj1.trans (Nat.le_succ j) |>.trans (self_le_endpoint (j + 1))
  have hNupper : N ≤ endpoint (j + 1) := by
    rcases hNcases with rfl | rfl
    · exact endpoint_strictMono.monotone (Nat.le_succ j)
    · exact le_rfl
  have hsqrt := sqrt_endpoint_log_le j N hNlow hNupper
  refine ⟨N, hNK, ?_⟩
  calc
    (1 / 8 : ℝ) * Real.sqrt ((N : ℝ) * Real.log N) ≤
        (1 / 8 : ℝ) * (3 * blockLength j) := by
      exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ (11 / 24 : ℝ) * blockLength j := by
      have hL : (0 : ℝ) ≤ blockLength j := by positivity
      nlinarith
    _ ≤ intervalDiscrepancy integerSequence α N := hdisc

/-! ## Resolution of Erdős Problem 992 -/

/-- There is a strictly increasing sequence of integers whose discrepancy is
at least a fixed positive multiple of `sqrt (N log N)` infinitely often for
Lebesgue-almost every `α ∈ [0,1]`.  This is the negative resolution of both
questions in Erdős Problem 992. -/
theorem not_erdos_992 :
    ∃ x : ℕ → ℤ, StrictMono x ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ α : ℝ ∂volume, α ∈ Icc 0 1 →
          ∃ᶠ N : ℕ in atTop,
            c * Real.sqrt ((N : ℝ) * Real.log N) ≤
              intervalDiscrepancy x α N := by
  refine ⟨integerSequence, integerSequence_strictMono, 1 / 8, by norm_num, ?_⟩
  have haeOne : ∀ᵐ α : ℝ ∂volume, α ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (Real.volume_singleton (a := (1 : ℝ)))
  filter_upwards [ae_frequently_resonant, haeOne] with α hres hαone hα
  apply frequently_large_discrepancy
  apply hres
  exact ⟨hα.1, lt_of_le_of_ne hα.2 hαone⟩

end Erdos992

#print axioms Erdos992.not_erdos_992

alias _root_.Erdos992.erdos_992 := _root_.Erdos992.not_erdos_992
