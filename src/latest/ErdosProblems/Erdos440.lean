/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 440.
https://www.erdosproblems.com/forum/thread/440

Informal authors:
- Paul Erdős
- Endre Szemerédi

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos440.md
-/
import Mathlib
import ErdosProblems.Erdos440.Liminf
import ErdosProblems.Erdos440.SharpConstruction
import ErdosProblems.Erdos440.SharpUpper

/-!
# Erdős Problem 440

For a strictly increasing sequence of positive natural numbers, let its
counting function be the number of indices whose adjacent least common
multiple is at most the threshold.

The file proves the square-root upper bound, the sharp universal limsup
constant of Erdős--Szemerédi, and that the largest possible liminf is one.

References:

* P. Erdős and E. Szemerédi, *Megjegyzések az American Mathematical
  Monthly egy problémájáról*, Matematikai Lapok 28 (1980), 121--124.
* W. van Doorn, *Sequences with bounded lcm for consecutive elements*.
-/

open scoped BigOperators NNReal Topology
open Filter Finset

namespace Erdos440

/-- The data of an infinite increasing sequence of positive integers. -/
structure IncreasingSequence where
  value : ℕ → ℕ
  positive : ∀ i, 0 < value i
  strictMono : StrictMono value

namespace IncreasingSequence

instance : CoeFun IncreasingSequence (fun _ => ℕ → ℕ) :=
  ⟨IncreasingSequence.value⟩

/-- The least common multiple attached to the edge from i to i + 1. -/
def edgeLcm (A : IncreasingSequence) (i : ℕ) : ℕ :=
  Nat.lcm (A i) (A (i + 1))

/-- The finite set of all good edges at threshold x.

The range x is exact: an edge with least common multiple at most x has
index strictly below x.
-/
def goodEdges (A : IncreasingSequence) (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i => edgeLcm A i ≤ x

/-- The counting function in Erdős Problem 440. -/
def count (A : IncreasingSequence) (x : ℕ) : ℕ :=
  (goodEdges A x).card

/-- The normalized counting function.  At x = 0 this is zero. -/
noncomputable def ratio (A : IncreasingSequence) (x : ℕ) : ℝ :=
  (count A x : ℝ) / Real.sqrt x

lemma index_succ_le (A : IncreasingSequence) (i : ℕ) : i + 1 ≤ A i := by
  induction i with
  | zero =>
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.positive 0))
  | succ i ih =>
      have hstep : A i < A (i + 1) := A.strictMono (Nat.lt_succ_self i)
      omega

lemma index_add_two_le (A : IncreasingSequence) (i : ℕ) : i + 2 ≤ A (i + 1) := by
  simpa [Nat.add_assoc] using A.index_succ_le (i + 1)

lemma value_dvd_edgeLcm_left (A : IncreasingSequence) (i : ℕ) :
    A i ∣ A.edgeLcm i :=
  Nat.dvd_lcm_left _ _

lemma value_dvd_edgeLcm_right (A : IncreasingSequence) (i : ℕ) :
    A (i + 1) ∣ A.edgeLcm i :=
  Nat.dvd_lcm_right _ _

lemma value_le_edgeLcm_left (A : IncreasingSequence) (i : ℕ) :
    A i ≤ A.edgeLcm i := by
  exact Nat.le_of_dvd (Nat.lcm_pos (A.positive i) (A.positive (i + 1)))
    (A.value_dvd_edgeLcm_left i)

lemma value_le_edgeLcm_right (A : IncreasingSequence) (i : ℕ) :
    A (i + 1) ≤ A.edgeLcm i := by
  exact Nat.le_of_dvd (Nat.lcm_pos (A.positive i) (A.positive (i + 1)))
    (A.value_dvd_edgeLcm_right i)

lemma index_add_two_le_edgeLcm (A : IncreasingSequence) (i : ℕ) :
    i + 2 ≤ A.edgeLcm i :=
  (A.index_add_two_le i).trans (A.value_le_edgeLcm_right i)

lemma edge_lt_threshold {A : IncreasingSequence} {i x : ℕ}
    (hi : A.edgeLcm i ≤ x) : i < x := by
  have := A.index_add_two_le_edgeLcm i
  omega

lemma mem_goodEdges_iff {A : IncreasingSequence} {i x : ℕ} :
    i ∈ A.goodEdges x ↔ A.edgeLcm i ≤ x := by
  simp only [goodEdges, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro hi
    exact ⟨edge_lt_threshold hi, hi⟩

lemma count_eq_card_filter_range (A : IncreasingSequence) (x N : ℕ) (hxN : x ≤ N) :
    A.count x = ((Finset.range N).filter fun i => A.edgeLcm i ≤ x).card := by
  have heq :
      (Finset.range N).filter (fun i => A.edgeLcm i ≤ x) = A.goodEdges x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, mem_goodEdges_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(edge_lt_threshold h).trans_le hxN, h⟩
  rw [count, heq]

lemma count_eq_ncard (A : IncreasingSequence) (x : ℕ) :
    A.count x = {i : ℕ | A.edgeLcm i ≤ x}.ncard := by
  let hfinite : Set.Finite {i : ℕ | A.edgeLcm i ≤ x} :=
    Set.Finite.subset (Set.finite_Iio x) fun i hi => edge_lt_threshold hi
  rw [count, Set.ncard_eq_toFinset_card _ hfinite]
  congr 1
  ext i
  simp [mem_goodEdges_iff]

/-- The gcd of two consecutive entries is at most their positive gap. -/
lemma gcd_le_gap (A : IncreasingSequence) (i : ℕ) :
    Nat.gcd (A i) (A (i + 1)) ≤ A (i + 1) - A i := by
  have hlt : A i < A (i + 1) := A.strictMono (Nat.lt_succ_self i)
  apply Nat.le_of_dvd (Nat.sub_pos_of_lt hlt)
  exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

/-- The reciprocal of an edge lcm is at most the reciprocal drop of its
endpoints. -/
lemma reciprocal_edgeLcm_le_drop (A : IncreasingSequence) (i : ℕ) :
    (1 : ℝ) / A.edgeLcm i ≤ (1 : ℝ) / A i - (1 : ℝ) / A (i + 1) := by
  have hai : 0 < (A i : ℝ) := by
    exact_mod_cast A.positive i
  have haj : 0 < (A (i + 1) : ℝ) := by
    exact_mod_cast A.positive (i + 1)
  have hlcm : 0 < (A.edgeLcm i : ℝ) := by
    exact_mod_cast Nat.lcm_pos (A.positive i) (A.positive (i + 1))
  have hgap :
      (Nat.gcd (A i) (A (i + 1)) : ℝ) ≤ (A (i + 1) : ℝ) - (A i : ℝ) := by
    rw [← Nat.cast_sub (Nat.le_of_lt (A.strictMono (Nat.lt_succ_self i)))]
    exact_mod_cast A.gcd_le_gap i
  calc
    (1 : ℝ) / A.edgeLcm i =
        (Nat.gcd (A i) (A (i + 1)) : ℝ) / ((A i : ℝ) * A (i + 1)) := by
      field_simp
      unfold edgeLcm
      exact_mod_cast (by
        calc
          A i * A (i + 1) = Nat.gcd (A i) (A (i + 1)) * Nat.lcm (A i) (A (i + 1)) :=
            (Nat.gcd_mul_lcm (A i) (A (i + 1))).symm
          _ = Nat.lcm (A i) (A (i + 1)) * Nat.gcd (A i) (A (i + 1)) :=
            Nat.mul_comm _ _)
    _ ≤ ((A (i + 1) : ℝ) - A i) / ((A i : ℝ) * A (i + 1)) := by
      exact div_le_div_of_nonneg_right hgap (mul_nonneg hai.le haj.le)
    _ = (1 : ℝ) / A i - (1 : ℝ) / A (i + 1) := by
      field_simp

/-- A finite subset of consecutive reciprocal drops is bounded by the full
telescoping interval. -/
lemma sum_subset_drops_le (A : IncreasingSequence) {k N : ℕ} (s : Finset ℕ)
    (hkN : k ≤ N) (hs : ∀ i ∈ s, k ≤ i ∧ i < N) :
    ∑ i ∈ s, ((1 : ℝ) / A i - (1 : ℝ) / A (i + 1)) ≤
      (1 : ℝ) / A k - (1 : ℝ) / A N := by
  classical
  have hsubset : s ⊆ Finset.Ico k N := by
    intro i hi
    exact Finset.mem_Ico.mpr (hs i hi)
  calc
    ∑ i ∈ s, ((1 : ℝ) / A i - (1 : ℝ) / A (i + 1)) ≤
        ∑ i ∈ Finset.Ico k N, ((1 : ℝ) / A i - (1 : ℝ) / A (i + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro i hi _
      have hmono : A i ≤ A (i + 1) :=
        Nat.le_of_lt (A.strictMono (Nat.lt_succ_self i))
      have hpos : 0 < (A i : ℝ) := by
        exact_mod_cast A.positive i
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hpos (by exact_mod_cast hmono))
    _ = (1 : ℝ) / A k - (1 : ℝ) / A N := by
      rw [Finset.sum_Ico_eq_sub _ hkN, Finset.sum_range_sub', Finset.sum_range_sub']
      ring

/-- The reciprocal mass of any finite family of edges in an index interval
is at most the reciprocal of the first sequence element. -/
lemma sum_subset_edgeLcm_le (A : IncreasingSequence) {k N : ℕ} (s : Finset ℕ)
    (hkN : k ≤ N) (hs : ∀ i ∈ s, k ≤ i ∧ i < N) :
    ∑ i ∈ s, (1 : ℝ) / A.edgeLcm i ≤ (1 : ℝ) / A k := by
  calc
    ∑ i ∈ s, (1 : ℝ) / A.edgeLcm i ≤
        ∑ i ∈ s, ((1 : ℝ) / A i - (1 : ℝ) / A (i + 1)) := by
      exact Finset.sum_le_sum fun i _ => A.reciprocal_edgeLcm_le_drop i
    _ ≤ (1 : ℝ) / A k - (1 : ℝ) / A N := A.sum_subset_drops_le s hkN hs
    _ ≤ (1 : ℝ) / A k := sub_le_self _ (by positivity)

private lemma reciprocal_drop_rat {m n : ℕ} (hm : 0 < m) (h : m < n) :
    (1 : ℚ) / Nat.lcm m n ≤ 1 / m - 1 / n := by
  have hn : 0 < n := hm.trans h
  have hgcd_dvd : Nat.gcd m n ∣ n - m :=
    Nat.dvd_sub (Nat.gcd_dvd_right m n) (Nat.gcd_dvd_left m n)
  have hgcd_le : Nat.gcd m n ≤ n - m :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt h) hgcd_dvd
  calc
    (1 : ℚ) / Nat.lcm m n = Nat.gcd m n / (m * n) := by
      field_simp
      exact_mod_cast (by
        calc
          m * n = Nat.gcd m n * Nat.lcm m n := (Nat.gcd_mul_lcm m n).symm
          _ = Nat.lcm m n * Nat.gcd m n := Nat.mul_comm _ _)
    _ ≤ (n - m : ℕ) / (m * n) := by
      exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ) < m * n)).2
        (by exact_mod_cast hgcd_le)
    _ = 1 / m - 1 / n := by
      rw [Nat.cast_sub h.le]
      field_simp

private lemma reciprocal_lcm_le_drop_rat {m n x : ℕ} (hm : 0 < m) (h : m < n)
    (hl : Nat.lcm m n ≤ x) :
    (1 : ℚ) / x ≤ 1 / m - 1 / n := by
  have hn : 0 < n := hm.trans h
  have hlcm : 0 < Nat.lcm m n := Nat.lcm_pos hm hn
  exact (one_div_le_one_div_of_le (by exact_mod_cast hlcm) (by exact_mod_cast hl)).trans
    (reciprocal_drop_rat hm h)

private lemma high_goodEdges_card_le_sqrt (A : IncreasingSequence) (x : ℕ) :
    ((A.goodEdges x).filter fun i => Nat.sqrt x < A i).card ≤ Nat.sqrt x := by
  classical
  let s := Nat.sqrt x
  let H := (A.goodEdges x).filter fun i => s < A i
  change H.card ≤ s
  by_cases hx : x = 0
  · subst x
    simp [H, goodEdges]
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx
  have hex : ∃ i, s < A i := by
    refine ⟨s + 1, ?_⟩
    exact (Nat.lt_succ_self s).trans_le (A.strictMono.id_le (s + 1))
  let k := Nat.find hex
  have hk : s < A k := Nat.find_spec hex
  have hcut : (Finset.range x).filter (fun i => s < A i) = Finset.Ico k x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hix, hai⟩
      exact ⟨Nat.find_min' hex hai, hix⟩
    · rintro ⟨hki, hix⟩
      exact ⟨hix, hk.trans_le (A.strictMono.monotone hki)⟩
  by_cases hH : H.Nonempty
  · obtain ⟨j, hjH⟩ := hH
    have hjGood : j ∈ A.goodEdges x := (Finset.mem_filter.mp hjH).1
    have hjHigh : s < A j := (Finset.mem_filter.mp hjH).2
    have hjx : j < x := Finset.mem_range.mp (Finset.mem_filter.mp hjGood).1
    have hkj : k ≤ j := Nat.find_min' hex hjHigh
    have hkx : k ≤ x := hkj.trans hjx.le
    have hHsub : H ⊆ (Finset.range x).filter (fun i => s < A i) := by
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi'.1).1, hi'.2⟩
    have hterm_nonneg (i : ℕ) :
        (0 : ℚ) ≤ 1 / A i - 1 / A (i + 1) := by
      apply sub_nonneg.mpr
      exact one_div_le_one_div_of_le (by exact_mod_cast A.positive i)
        (by exact_mod_cast (A.strictMono (Nat.lt_succ_self i)).le)
    have heach (i : ℕ) (hi : i ∈ H) :
        (1 : ℚ) / x ≤ 1 / A i - 1 / A (i + 1) := by
      have hiGood : i ∈ A.goodEdges x := (Finset.mem_filter.mp hi).1
      have hilcm : A.edgeLcm i ≤ x := (Finset.mem_filter.mp hiGood).2
      exact reciprocal_lcm_le_drop_rat (A.positive i)
        (A.strictMono (Nat.lt_succ_self i)) hilcm
    have hsum_lower :
        (H.card : ℚ) / x ≤ ∑ i ∈ H, (1 / A i - 1 / A (i + 1) : ℚ) := by
      calc
        (H.card : ℚ) / x = ∑ _i ∈ H, (1 : ℚ) / x := by
          simp [div_eq_mul_inv]
        _ ≤ ∑ i ∈ H, (1 / A i - 1 / A (i + 1) : ℚ) := by
          exact Finset.sum_le_sum fun i hi => heach i hi
    have hsum_subset :
        (∑ i ∈ H, (1 / A i - 1 / A (i + 1) : ℚ)) ≤
          ∑ i ∈ Finset.Ico k x, (1 / A i - 1 / A (i + 1) : ℚ) := by
      rw [← hcut]
      exact Finset.sum_le_sum_of_subset_of_nonneg hHsub fun i _ _ => hterm_nonneg i
    have htel :
        (∑ i ∈ Finset.Ico k x, (1 / A i - 1 / A (i + 1) : ℚ)) =
          1 / A k - 1 / A x := by
      calc
        (∑ i ∈ Finset.Ico k x, (1 / A i - 1 / A (i + 1) : ℚ)) =
            -∑ i ∈ Finset.Ico k x, (1 / A (i + 1) - 1 / A i : ℚ) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = -(1 / A x - 1 / A k) := by
          rw [Finset.sum_Ico_sub (fun i => (1 : ℚ) / A i) hkx]
        _ = 1 / A k - 1 / A x := by ring
    have hak : s + 1 ≤ A k := Nat.succ_le_iff.mpr hk
    have htail : (1 / A k - 1 / A x : ℚ) ≤ 1 / (s + 1) := by
      have hkrecip : (1 : ℚ) / A k ≤ 1 / (s + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hak)
      have haxnonneg : (0 : ℚ) ≤ 1 / A x := by positivity
      linarith
    have hfrac : (H.card : ℚ) / x ≤ 1 / (s + 1) :=
      hsum_lower.trans (hsum_subset.trans (htel.le.trans htail))
    have hmulQ : (H.card : ℚ) * (s + 1) ≤ x := by
      have h := (div_le_div_iff₀ (by exact_mod_cast hxpos : (0 : ℚ) < x)
        (by positivity : (0 : ℚ) < s + 1)).mp hfrac
      simpa using h
    have hmul : H.card * (s + 1) ≤ x := by
      exact_mod_cast hmulQ
    have hxsq : x < (s + 1) * (s + 1) := by
      simpa [s, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt x
    have hstrict : H.card * (s + 1) < (s + 1) * (s + 1) := hmul.trans_lt hxsq
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right (Nat.succ_pos s)).mp hstrict)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hH
    simp [hH]

/-- Tao's elementary square-root bound, in a rounded all-natural form. -/
theorem count_le_two_sqrt_add_two (A : IncreasingSequence) (x : ℕ) :
    A.count x ≤ 2 * Nat.sqrt x + 2 := by
  classical
  let G := A.goodEdges x
  let s := Nat.sqrt x
  have hlow : (G.filter fun i => A i ≤ s).card ≤ s + 1 := by
    calc
      (G.filter fun i => A i ≤ s).card ≤ (Finset.range (s + 1)).card := by
        apply Finset.card_le_card
        intro i hi
        have hais : A i ≤ s := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((A.strictMono.id_le i).trans hais))
      _ = s + 1 := Finset.card_range _
  have hhigh : (G.filter fun i => ¬A i ≤ s).card ≤ s := by
    simpa only [G, s, Nat.not_le] using high_goodEdges_card_le_sqrt A x
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G) (fun i => A i ≤ s)
  change G.card ≤ 2 * s + 2
  omega

/-- The literal affirmative answer to the first question: the counting
function is big-O of the square root. -/
theorem count_isBigO_sqrt (A : IncreasingSequence) :
    (fun x : ℕ => (A.count x : ℝ)) =O[atTop]
      (fun x : ℕ => Real.sqrt x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨4, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt x := by
    have hcast : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    simpa using Real.sqrt_le_sqrt hcast
  have hnat_sqrt : (Nat.sqrt x : ℝ) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    have hs : Nat.sqrt x ^ 2 ≤ x := Nat.sqrt_le' x
    exact_mod_cast hs
  have hcountNat := A.count_le_two_sqrt_add_two x
  have hcount : (A.count x : ℝ) ≤ 2 * Nat.sqrt x + 2 := by
    exact_mod_cast hcountNat
  have hcount_nonneg : (0 : ℝ) ≤ A.count x := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hcount_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith

end IncreasingSequence

/-- The summand in the sharp Erdős--Szemerédi constant.  Its value at zero is
zero in Lean, so summing over all naturals is the same as summing from one. -/
noncomputable abbrev sharpKernel : ℕ → ℝ :=
  Erdos440SharpUpper.IncreasingSequence.sharpKernel

/-- The sharp universal coefficient given by the sum from d = 1 to infinity
of 1 / (sqrt d * (d + 1)). -/
noncomputable abbrev sharpConstant : ℝ :=
  Erdos440SharpUpper.IncreasingSequence.sharpConstant

private def toSharpUpper (A : IncreasingSequence) :
    Erdos440SharpUpper.IncreasingSequence where
  val := A.value
  positive := A.positive
  strictMono := A.strictMono

private lemma toSharpUpper_count (A : IncreasingSequence) (x : ℕ) :
    (toSharpUpper A).countingFunction x = A.count x := rfl

/-- Finite form of the sharp Erdős--Szemerédi upper estimate. -/
theorem count_le_sharp_partial (A : IncreasingSequence) (x : ℕ) (hx : 0 < x) :
    (A.count x : ℝ) ≤ 1 +
      Real.sqrt x * (∑ j ∈ Finset.Ico 1 x, sharpKernel j) +
      ∑ j ∈ Finset.Ico 1 x, (1 : ℝ) / (j + 1 : ℕ) := by
  simpa only [toSharpUpper_count,
    Erdos440SharpUpper.IncreasingSequence.harmonicKernel] using
    (toSharpUpper A).countingFunction_le_sharp_partial x hx

/-- Epsilon form of the sharp asymptotic universal bound. -/
theorem eventually_ratio_le_sharpConstant (A : IncreasingSequence)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, A.ratio x ≤ sharpConstant + ε := by
  simpa only [IncreasingSequence.ratio, toSharpUpper_count] using
    (toSharpUpper A).eventually_countingFunction_div_sqrt_le ε hε

/-- Every sequence has normalized limsup at most the sharp constant. -/
theorem limsup_ratio_le_sharpConstant (A : IncreasingSequence) :
    atTop.limsup A.ratio ≤ sharpConstant := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le atTop fun x =>
      div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    (eventually_ratio_le_sharpConstant A ε hε)

private def toLiminfSequence (A : IncreasingSequence) :
    Erdos440Liminf.IncreasingPositiveSequence where
  val := A.value
  pos := A.positive
  strictMono := A.strictMono

private lemma toLiminfSequence_count (A : IncreasingSequence) (x : ℕ) :
    Erdos440Liminf.count (toLiminfSequence A) x = A.count x := rfl

/-- Erdős and Szemerédi's universal liminf theorem. -/
theorem liminf_ratio_le_one (A : IncreasingSequence) :
    atTop.liminf A.ratio ≤ 1 := by
  have hfun : Erdos440Liminf.normalizedCount (toLiminfSequence A) = A.ratio := by
    funext x
    rw [Erdos440Liminf.normalizedCount, IncreasingSequence.ratio,
      toLiminfSequence_count]
  rw [← hfun]
  exact Erdos440Liminf.liminf_normalizedCount_le_one (toLiminfSequence A)

/-- The increasing sequence of all positive natural numbers. -/
def positiveNaturals : IncreasingSequence where
  value := Nat.succ
  positive := Nat.succ_pos
  strictMono := fun _ _ hij => Nat.succ_lt_succ hij

@[simp] lemma positiveNaturals_apply (i : ℕ) : positiveNaturals i = i + 1 := rfl

/-- Adjacent positive integers are coprime, so their lcm is their product. -/
theorem positiveNaturals_edgeLcm (i : ℕ) :
    positiveNaturals.edgeLcm i = (i + 1) * (i + 2) := by
  have hcop : Nat.Coprime (i + 1) (i + 2) := by
    rw [show i + 2 = 1 + (i + 1) by omega, Nat.coprime_add_self_right]
    simp
  simpa [IncreasingSequence.edgeLcm, positiveNaturals, Nat.add_assoc] using hcop.lcm_eq_mul

/-- The largest n at most x satisfying n(n+1) ≤ x. -/
def triangularRoot (x : ℕ) : ℕ :=
  Nat.findGreatest (fun n => n * (n + 1) ≤ x) x

lemma triangularRoot_le (x : ℕ) : triangularRoot x ≤ x :=
  Nat.findGreatest_le x

lemma triangularRoot_spec (x : ℕ) :
    triangularRoot x * (triangularRoot x + 1) ≤ x :=
  Nat.findGreatest_spec (P := fun n => n * (n + 1) ≤ x)
    (m := 0) (n := x) (Nat.zero_le x) (by simp)

lemma le_triangularRoot_of_mul_succ_le {n x : ℕ} (hnx : n ≤ x)
    (h : n * (n + 1) ≤ x) : n ≤ triangularRoot x :=
  Nat.le_findGreatest hnx h

lemma lt_succ_mul_succ_triangularRoot (x : ℕ) :
    x < (triangularRoot x + 1) * (triangularRoot x + 2) := by
  apply Nat.lt_of_not_ge
  intro hnext
  have hbound : triangularRoot x + 1 ≤ x := by
    have hfactor : triangularRoot x + 1 ≤
        (triangularRoot x + 1) * (triangularRoot x + 2) := by
      nlinarith
    omega
  have hnot := (Nat.findGreatest_eq_iff.mp
    (rfl : Nat.findGreatest (fun n => n * (n + 1) ≤ x) x = triangularRoot x)).2.2
      (Nat.lt_succ_self (triangularRoot x)) hbound
  exact hnot (by simpa [Nat.add_assoc] using hnext)

theorem positiveNaturals_goodEdges (x : ℕ) :
    positiveNaturals.goodEdges x = Finset.range (triangularRoot x) := by
  ext i
  simp only [IncreasingSequence.goodEdges, Finset.mem_filter, Finset.mem_range]
  rw [positiveNaturals_edgeLcm]
  constructor
  · rintro ⟨hix, hi⟩
    have hip : i + 1 ≤ x := by omega
    have hir : i + 1 ≤ triangularRoot x :=
      le_triangularRoot_of_mul_succ_le hip (by simpa [Nat.add_assoc] using hi)
    omega
  · intro hir
    have hix : i < x := lt_of_lt_of_le hir (triangularRoot_le x)
    have hi1 : i + 1 ≤ triangularRoot x := by omega
    have hi2 : i + 2 ≤ triangularRoot x + 1 := by omega
    refine ⟨hix, ?_⟩
    exact le_trans (Nat.mul_le_mul hi1 hi2) (triangularRoot_spec x)

/-- Exact evaluation of the counting function for the positive integers. -/
theorem positiveNaturals_count (x : ℕ) :
    positiveNaturals.count x = triangularRoot x := by
  rw [IncreasingSequence.count, positiveNaturals_goodEdges, Finset.card_range]

lemma positiveNaturals_count_le_sqrt (x : ℕ) :
    (positiveNaturals.count x : ℝ) ≤ Real.sqrt x := by
  rw [positiveNaturals_count]
  apply Real.le_sqrt_of_sq_le
  have hsq : triangularRoot x * triangularRoot x ≤ x := le_trans
    (Nat.mul_le_mul_left (triangularRoot x) (Nat.le_succ (triangularRoot x)))
    (triangularRoot_spec x)
  have hsq' : (triangularRoot x : ℝ) * triangularRoot x ≤ x := by
    exact_mod_cast hsq
  simpa [pow_two] using hsq'

lemma sqrt_lt_positiveNaturals_count_add_two (x : ℕ) :
    Real.sqrt x < positiveNaturals.count x + 2 := by
  rw [positiveNaturals_count]
  rw [Real.sqrt_lt' (by positivity)]
  have hnext := lt_succ_mul_succ_triangularRoot x
  exact_mod_cast lt_of_lt_of_le hnext (by nlinarith :
    (triangularRoot x + 1) * (triangularRoot x + 2) ≤
      (triangularRoot x + 2) ^ 2)

/-- The positive integers attain the universal liminf coefficient one. -/
theorem positiveNaturals_ratio_tendsto_one :
    Tendsto positiveNaturals.ratio atTop (𝓝 1) := by
  have hsqrt : Tendsto (fun x : ℕ => Real.sqrt (x : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℕ => (Real.sqrt (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hlower : Tendsto
      (fun x : ℕ => 1 - 2 * (Real.sqrt (x : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hspos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hx)
    have hsupper := sqrt_lt_positiveNaturals_count_add_two x
    rw [IncreasingSequence.ratio, le_div_iff₀ hspos]
    have hinv_mul : (Real.sqrt (x : ℝ))⁻¹ * Real.sqrt (x : ℝ) = 1 :=
      inv_mul_cancel₀ hspos.ne'
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hspos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hx)
    rw [IncreasingSequence.ratio, div_le_one hspos]
    exact positiveNaturals_count_le_sqrt x

/-- Hence the liminf coefficient one is attained. -/
theorem positiveNaturals_liminf_eq_one :
    atTop.liminf positiveNaturals.ratio = 1 :=
  positiveNaturals_ratio_tendsto_one.liminf_eq

/-! ## Sharpness of the universal limsup constant -/

/-- The explicit diagonal block construction attaining the sharp
Erdős--Szemerédi constant. -/
noncomputable def sharpSequenceWitness : IncreasingSequence where
  value := Erdos440SharpConstruction.sharpSequence
  positive := Erdos440SharpConstruction.sharpSequence_pos
  strictMono := Erdos440SharpConstruction.sharpSequence_strictMono

@[simp] theorem sharpSequenceWitness_apply (i : ℕ) :
    sharpSequenceWitness i = Erdos440SharpConstruction.sharpSequence i := rfl

/-- The public normalized counting function agrees with the one used in the
construction module. -/
theorem sharpSequenceWitness_ratio (x : ℕ) :
    sharpSequenceWitness.ratio x =
      Erdos440SharpConstruction.sharpNormalizedCount x := rfl

/-- The sharp constant is attained by one explicit increasing sequence. -/
theorem sharpSequenceWitness_limsup_eq_sharpConstant :
    atTop.limsup sharpSequenceWitness.ratio = sharpConstant := by
  apply le_antisymm
  · exact limsup_ratio_le_sharpConstant sharpSequenceWitness
  · have hratio : sharpSequenceWitness.ratio =
        Erdos440SharpConstruction.sharpNormalizedCount := by
      funext x
      exact sharpSequenceWitness_ratio x
    rw [hratio]
    exact Erdos440SharpConstruction.universalSharpConstant_le_limsup_sharpNormalizedCount

/-! ## Complete resolution -/

/-- The complete resolution of Erdős Problem 440.

The five conjuncts say respectively that every counting function is
`O(√x)`, that the Erdős--Szemerédi series is the universal limsup
coefficient, that this coefficient is sharp, that every normalized liminf
is at most one, and that one is attained by the positive integers. -/
theorem erdos_440 :
    (∀ A : IncreasingSequence,
      (fun x : ℕ ↦ (A.count x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.sqrt x)) ∧
    (∀ A : IncreasingSequence, atTop.limsup A.ratio ≤ sharpConstant) ∧
    (∃ A : IncreasingSequence, atTop.limsup A.ratio = sharpConstant) ∧
    (∀ A : IncreasingSequence, atTop.liminf A.ratio ≤ 1) ∧
    (∃ A : IncreasingSequence, atTop.liminf A.ratio = 1) := by
  exact ⟨IncreasingSequence.count_isBigO_sqrt, limsup_ratio_le_sharpConstant,
    ⟨sharpSequenceWitness, sharpSequenceWitness_limsup_eq_sharpConstant⟩,
    liminf_ratio_le_one, ⟨positiveNaturals, positiveNaturals_liminf_eq_one⟩⟩

end Erdos440

#print axioms Erdos440.erdos_440
