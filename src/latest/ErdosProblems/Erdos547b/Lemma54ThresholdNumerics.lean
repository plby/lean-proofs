/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54ThresholdOrientation

/-!
# The actual-load cutoff in Zhao Lemma 5.4

The cutoff in Zhao's proof is chosen *after* the prefix-balanced orientation:
it is the last prefix for which both actual endpoint loads fit the low-density
budget.  This is slightly sharper than testing
`prefixOrder + slack ≤ 2 * lowBudget`; in particular it does not lose a unit
to parity or to rounding the real density budget down to a natural number.

This file isolates that exact finite construction.  The real-valued displays
in Parts 1 and 2 only have to bound the fixed suffix at the resulting cutoff.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma54ThresholdNumerics

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation

/-- Both actual loads of a balanced prefix fit the low endpoint budget. -/
def prefixFits {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ)
    (t : Fin (b + 1)) : Prop :=
  ∀ c, sideLoadPrefix F orient t c ≤ lowBudget

/-- The finite set of source prefixes which fit on both physical sides. -/
def fittingCutoffs {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ) :
    Finset (Fin (b + 1)) := by
  classical
  exact Finset.univ.filter (prefixFits F orient lowBudget)

theorem zero_mem_fittingCutoffs {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ) :
    (0 : Fin (b + 1)) ∈ fittingCutoffs F orient lowBudget := by
  simp [fittingCutoffs, prefixFits]

/-- Zhao's `i₀`: the last prefix whose two actual loads fit the low budget. -/
def maximalFittingCutoff {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ) : Fin (b + 1) :=
  (fittingCutoffs F orient lowBudget).max'
    ⟨0, zero_mem_fittingCutoffs F orient lowBudget⟩

theorem sideLoadPrefix_mono {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) {s t : Fin (b + 1)}
    (hst : s ≤ t) (c : Fin 2) :
    sideLoadPrefix F orient s c ≤ sideLoadPrefix F orient t c := by
  classical
  unfold sideLoadPrefix
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < s.val
  · have hit : i.val < t.val := hi.trans_le (Fin.le_def.mp hst)
    simp [hi, hit]
  · simp [hi]

theorem maximalFittingCutoff_mem {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ) :
    maximalFittingCutoff F orient lowBudget ∈
      fittingCutoffs F orient lowBudget := by
  exact Finset.max'_mem _ _

theorem maximalFittingCutoff_fits {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (lowBudget : ℕ) :
    prefixFits F orient lowBudget
      (maximalFittingCutoff F orient lowBudget) := by
  classical
  exact Finset.mem_filter.mp
    (maximalFittingCutoff_mem F orient lowBudget) |>.2

theorem prefixFits_of_le_maximalFittingCutoff {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (lowBudget : ℕ) {t : Fin (b + 1)}
    (ht : t ≤ maximalFittingCutoff F orient lowBudget) :
    prefixFits F orient lowBudget t := by
  intro c
  exact (sideLoadPrefix_mono F orient ht c).trans
    (maximalFittingCutoff_fits F orient lowBudget c)

theorem not_prefixFits_of_maximalFittingCutoff_lt {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (lowBudget : ℕ) {t : Fin (b + 1)}
    (ht : maximalFittingCutoff F orient lowBudget < t) :
    ¬prefixFits F orient lowBudget t := by
  classical
  intro hfit
  have htmem : t ∈ fittingCutoffs F orient lowBudget := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfit⟩
  have hle := Finset.le_max' (fittingCutoffs F orient lowBudget) t htmem
  exact (not_le_of_gt ht) hle

/-- Either every branch belongs to the fitting prefix, or the very next
prefix overloads at least one of the two low sides.  This is the literal
maximality statement used in Zhao's inequalities (5.1) and (5.2). -/
theorem maximalFittingCutoff_eq_last_or_next_overflow {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2)
    (lowBudget : ℕ) :
    maximalFittingCutoff F orient lowBudget = Fin.last b ∨
      ∃ (next : Fin (b + 1)) (c : Fin 2),
        next.val = (maximalFittingCutoff F orient lowBudget).val + 1 ∧
        lowBudget < sideLoadPrefix F orient next c := by
  let cutoff := maximalFittingCutoff F orient lowBudget
  by_cases hlast : cutoff = Fin.last b
  · exact Or.inl hlast
  · have hcutoff : cutoff.val < b := by
      have hle : cutoff.val ≤ b := Nat.le_of_lt_succ cutoff.isLt
      exact lt_of_le_of_ne hle (by
        intro h
        apply hlast
        apply Fin.ext
        simpa using h)
    let next : Fin (b + 1) := ⟨cutoff.val + 1, by omega⟩
    have hlt : cutoff < next := by
      exact Fin.lt_iff_val_lt_val.mpr (by simp [next])
    have hnot : ¬prefixFits F orient lowBudget next :=
      not_prefixFits_of_maximalFittingCutoff_lt F orient lowBudget hlt
    simp only [prefixFits, not_forall, not_le] at hnot
    obtain ⟨c, hc⟩ := hnot
    exact Or.inr ⟨next, c, by simp [next, cutoff], hc⟩

/-- With zero capacity on both low sides, the only fitting prefix is the
empty prefix.  Every rooted tree in an `OrderedRootedForest` has positive
order, so a nonempty prefix has positive total two-colour load. -/
theorem maximalFittingCutoff_eq_zero_of_budget_zero {b : ℕ}
    (F : OrderedRootedForest b) (orient : Fin b → Fin 2 ≃ Fin 2) :
    maximalFittingCutoff F orient 0 = 0 := by
  apply Fin.ext
  by_contra hzero
  have hcutPos : 0 < (maximalFittingCutoff F orient 0).val :=
    Nat.pos_of_ne_zero (by simpa using hzero)
  have hb : 0 < b := by
    have hcutLt := (maximalFittingCutoff F orient 0).isLt
    omega
  let i : Fin b := ⟨0, hb⟩
  have hi : i.val < (maximalFittingCutoff F orient 0).val := by
    simp only [i]
    exact hcutPos
  have hterm : F.size i ≤
      prefixOrder F (maximalFittingCutoff F orient 0) := by
    rw [prefixOrder]
    calc
      F.size i = if i.val < (maximalFittingCutoff F orient 0).val
          then F.size i else 0 := by simp [hi]
      _ ≤ ∑ j, if j.val < (maximalFittingCutoff F orient 0).val
          then F.size j else 0 := by
        change (if i.val < (maximalFittingCutoff F orient 0).val
            then F.size i else 0) ≤
          (Finset.univ : Finset (Fin b)).sum (fun j ↦
            if j.val < (maximalFittingCutoff F orient 0).val
              then F.size j else 0)
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin b)))
          (f := fun j : Fin b ↦
            if j.val < (maximalFittingCutoff F orient 0).val
              then F.size j else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hfit := maximalFittingCutoff_fits F orient 0
  have hloads := sideLoadPrefix_zero_add_one F orient
    (maximalFittingCutoff F orient 0)
  have hsizePos : 0 < F.size i := Nat.zero_lt_of_lt (F.root i).isLt
  have hprefixPos : 0 < prefixOrder F
      (maximalFittingCutoff F orient 0) := hsizePos.trans_le hterm
  have hzero0 := hfit 0
  have hzero1 := hfit 1
  omega

/-- The canonical switch produced from one prefix-balanced base orientation.
Keeping the base in the constructor lets graph-side callers ask for parent
degree only on the endpoint used by this literal maximal-cutoff orientation,
rather than for every abstract `ThresholdSwitchOrientation`. -/
noncomputable def actualThresholdSwitchOrientation
    {b : ℕ} (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        lowBudget + fixedSuffixLoad F
            (maximalFittingCutoff F base lowBudget) highSide c ≤
          highBudget)
    (base : Fin b → Fin 2 ≃ Fin 2)
    (hbase : ∀ t c,
      2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) :
    ThresholdSwitchOrientation F lowSide lowBudget highBudget := by
  let cutoff := maximalFittingCutoff F base lowBudget
  let orient := thresholdOrientation F base cutoff highSide
  refine {
    orient := orient
    cutoff := cutoff
    early_prefix := ?_
    late_root_high := ?_
    final_load := ?_
  }
  · intro i hi c
    rw [show orient = thresholdOrientation F base cutoff highSide from rfl,
      sideLoadBefore_thresholdOrientation_of_lt F base cutoff highSide i hi c,
      sideLoadBefore_eq_sideLoadPrefix F base i c]
    apply prefixFits_of_le_maximalFittingCutoff F base lowBudget
    exact Fin.le_def.mpr (Nat.le_of_lt hi)
  · intro i hi
    have hnot : ¬i.val < cutoff.val := Nat.not_lt.mpr hi
    simpa [orient, thresholdOrientation, hnot, branchRootSide] using hsides
  · intro c
    rw [show orient = thresholdOrientation F base cutoff highSide from rfl,
      sideLoad_thresholdOrientation]
    exact Nat.add_le_add
      (maximalFittingCutoff_fits F base lowBudget c)
      (Nat.le_refl _) |>.trans (hfinal base hbase c)

/-- Source-exact threshold switch.  The caller proves only the suffix display
at the actual maximal fitting cutoff; no coarse integral estimate
`prefixOrder + slack ≤ 2 * lowBudget` is imposed. -/
theorem exists_actualThresholdSwitchOrientation
    {b : ℕ} (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        lowBudget + fixedSuffixLoad F
            (maximalFittingCutoff F base lowBudget) highSide c ≤
          highBudget) :
    Nonempty (ThresholdSwitchOrientation F lowSide lowBudget highBudget) := by
  obtain ⟨base, hbase⟩ :=
    exists_prefix_balanced_orientation F slack hsmall
  exact ⟨actualThresholdSwitchOrientation F slack lowBudget highBudget
    lowSide highSide hsmall hsides hfinal base hbase⟩

/-- In the zero-low-budget case the canonical switch sends every branch root
to the high endpoint. -/
theorem actualThresholdSwitchOrientation_root_high_of_lowBudget_zero
    {b : ℕ} (F : OrderedRootedForest b)
    (slack highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        fixedSuffixLoad F (maximalFittingCutoff F base 0) highSide c ≤
          highBudget)
    (base : Fin b → Fin 2 ≃ Fin 2)
    (hbase : ∀ t c,
      2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack)
    (i : Fin b) :
    let O := actualThresholdSwitchOrientation F slack 0 highBudget
      lowSide highSide hsmall hsides (by simpa using hfinal) base hbase
    branchRootSide F O.orient i = highSide := by
  let O := actualThresholdSwitchOrientation F slack 0 highBudget
    lowSide highSide hsmall hsides (by simpa using hfinal) base hbase
  change branchRootSide F O.orient i = highSide
  have hcut : O.cutoff = 0 := by
    change maximalFittingCutoff F base 0 = 0
    exact maximalFittingCutoff_eq_zero_of_budget_zero F base
  have hrootNe : branchRootSide F O.orient i ≠ lowSide :=
    O.late_root_high i (by rw [hcut]; exact Nat.zero_le _)
  have hrootValNe : (branchRootSide F O.orient i).val ≠ lowSide.val := by
    intro h
    exact hrootNe (Fin.ext h)
  have hsidesValNe : highSide.val ≠ lowSide.val := by
    intro h
    exact hsides (Fin.ext h)
  apply Fin.ext
  omega

#print axioms actualThresholdSwitchOrientation
#print axioms exists_actualThresholdSwitchOrientation

end Erdos547b.ZhaoLemma54ThresholdNumerics
