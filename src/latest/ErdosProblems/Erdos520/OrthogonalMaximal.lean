import ErdosProblems.Erdos520.FreshExpansion
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Probability.Independence.Integration

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal symmDiff

namespace Erdos
namespace Problem520

/-!
# Orthogonality and finite maximal inequalities

This file develops the unconditional `L²` input available for interpolation
of the squarefree Rademacher partial sums.  It deliberately uses only exact
orthogonality, and therefore also records the quantitative limit of what this
method can supply on a sparse test mesh.
-/

theorem measurable_f (n : ℕ) : Measurable fun omega : Omega => f omega n := by
  by_cases hn : Squarefree n
  · simp only [f, if_pos hn]
    exact Finset.measurable_fun_prod n.primeFactors fun p _ => measurable_ε p
  · simp [f, hn]

theorem integrable_f (n : ℕ) : Integrable (fun omega : Omega => f omega n) μ := by
  apply Integrable.of_bound (measurable_f n).aestronglyMeasurable 1
  filter_upwards [] with omega
  by_cases hn : Squarefree n
  · simp [f, hn]
  · simp [f, hn]

@[simp] theorem f_sq (omega : Omega) (n : ℕ) :
    f omega n ^ 2 = if Squarefree n then 1 else 0 := by
  by_cases hn : Squarefree n
  · rw [if_pos hn, f_eq_prod_primeFactors_of_squarefree omega hn,
      ← Finset.prod_pow]
    simp
  · simp [f, hn]

theorem integral_freshCharacter_of_nonempty (S : Finset ℕ)
    (hS : S.Nonempty) :
    ∫ omega, freshCharacter omega S ∂μ = 0 := by
  let X : S → Omega → ℝ := fun p omega => ε omega p.1
  have hX : iIndepFun X μ := by
    exact iIndepFun.precomp Subtype.val_injective iIndepFun_ε
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p => (measurable_ε p.1).aestronglyMeasurable)
  have hzero : ∏ p : S, ∫ omega, X p omega ∂μ = 0 := by
    apply Finset.prod_eq_zero (i := ⟨hS.choose, hS.choose_spec⟩)
    · exact Finset.mem_univ _
    · exact integral_ε hS.choose
  calc
    (∫ omega, freshCharacter omega S ∂μ) =
        ∫ omega, ∏ p : S, ε omega p.1 ∂μ := by
      congr 1
      funext omega
      exact (Finset.prod_coe_sort S (fun p => ε omega p)).symm
    _ = ∏ p : S, ∫ omega, X p omega ∂μ := hprod
    _ = 0 := hzero

theorem freshCharacter_mul (omega : Omega) (S T : Finset ℕ) :
    freshCharacter omega S * freshCharacter omega T =
      freshCharacter omega (S ∆ T) := by
  classical
  have hS : S = (S \ T) ∪ (S ∩ T) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hT : T = (T \ S) ∪ (S ∩ T) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdS : Disjoint (S \ T) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mp hq).2
  have hdT : Disjoint (T \ S) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mp hq).1
  have hdST : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  have hsymm : S ∆ T = (S \ T) ∪ (T \ S) := rfl
  have hcommon : freshCharacter omega (S ∩ T) ^ 2 = 1 := by
    unfold freshCharacter
    rw [← Finset.prod_pow]
    simp
  have hcharS : freshCharacter omega S =
      freshCharacter omega (S \ T) * freshCharacter omega (S ∩ T) := by
    calc
      freshCharacter omega S =
          freshCharacter omega ((S \ T) ∪ (S ∩ T)) :=
        congrArg (freshCharacter omega) hS
      _ = freshCharacter omega (S \ T) *
          freshCharacter omega (S ∩ T) := by
        unfold freshCharacter
        rw [Finset.prod_union hdS]
  have hcharT : freshCharacter omega T =
      freshCharacter omega (T \ S) * freshCharacter omega (S ∩ T) := by
    calc
      freshCharacter omega T =
          freshCharacter omega ((T \ S) ∪ (S ∩ T)) :=
        congrArg (freshCharacter omega) hT
      _ = freshCharacter omega (T \ S) *
          freshCharacter omega (S ∩ T) := by
        unfold freshCharacter
        rw [Finset.prod_union hdT]
  have hcharSymm : freshCharacter omega (S ∆ T) =
      freshCharacter omega (S \ T) * freshCharacter omega (T \ S) := by
    calc
      freshCharacter omega (S ∆ T) =
          freshCharacter omega ((S \ T) ∪ (T \ S)) :=
        congrArg (freshCharacter omega) hsymm
      _ = freshCharacter omega (S \ T) *
          freshCharacter omega (T \ S) := by
        unfold freshCharacter
        rw [Finset.prod_union hdST]
  rw [hcharS, hcharT, hcharSymm]
  calc
    freshCharacter omega (S \ T) * freshCharacter omega (S ∩ T) *
        (freshCharacter omega (T \ S) * freshCharacter omega (S ∩ T)) =
      freshCharacter omega (S \ T) * freshCharacter omega (T \ S) *
        freshCharacter omega (S ∩ T) ^ 2 := by ring
    _ = freshCharacter omega (S \ T) * freshCharacter omega (T \ S) := by
      rw [hcommon]
      ring

/-- Exact Walsh orthogonality for the squarefree Rademacher model. -/
theorem integral_f_mul_f (m n : ℕ) :
    ∫ omega, f omega m * f omega n ∂μ =
      if Squarefree m ∧ Squarefree n ∧ m = n then 1 else 0 := by
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · simp only [f, if_pos hm, if_pos hn]
      change (∫ omega,
        freshCharacter omega m.primeFactors *
          freshCharacter omega n.primeFactors ∂μ) = _
      simp_rw [freshCharacter_mul]
      by_cases hmn : m = n
      · subst n
        simp [hm, freshCharacter]
      · have hpf : m.primeFactors ≠ n.primeFactors := by
          intro h
          have hprod : (∏ p ∈ m.primeFactors, p) =
              ∏ p ∈ n.primeFactors, p :=
            congrArg (fun S : Finset ℕ => ∏ p ∈ S, p) h
          exact hmn ((Nat.prod_primeFactors_of_squarefree hm).symm.trans
            (hprod.trans (Nat.prod_primeFactors_of_squarefree hn)))
        rw [if_neg (by tauto)]
        exact integral_freshCharacter_of_nonempty _
          (Finset.symmDiff_nonempty.mpr hpf)
    · rw [if_neg (by tauto)]
      simp_rw [f_eq_zero_of_not_squarefree _ hn]
      simp
  · rw [if_neg (by tauto)]
    simp_rw [f_eq_zero_of_not_squarefree _ hm]
    simp

theorem integrable_f_mul_f (m n : ℕ) :
    Integrable (fun omega : Omega => f omega m * f omega n) μ := by
  apply Integrable.of_bound
    ((measurable_f m).mul (measurable_f n)).aestronglyMeasurable 1
  filter_upwards [] with omega
  change |f omega m * f omega n| ≤ 1
  rw [abs_mul]
  have hm : |f omega m| ≤ 1 := by
    by_cases h : Squarefree m
    · rw [f_eq_prod_primeFactors_of_squarefree omega h, abs_prod]
      simp
    · simp [f, h]
  have hn : |f omega n| ≤ 1 := by
    by_cases h : Squarefree n
    · rw [f_eq_prod_primeFactors_of_squarefree omega h, abs_prod]
      simp
    · simp [f, h]
  nlinarith [abs_nonneg (f omega m), abs_nonneg (f omega n)]

/-- Sum of the `L` terms immediately after the partial-sum endpoint `a`. -/
noncomputable def fIntervalSum (omega : Omega) (a L : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L, f omega (a + k + 1)

theorem partialSum_add_sub (omega : Omega) (a L : ℕ) :
    partialSum omega (a + L) - partialSum omega a =
      fIntervalSum omega a L := by
  unfold partialSum fIntervalSum
  rw [Finset.sum_range_add]
  ring

theorem measurable_fIntervalSum (a L : ℕ) :
    Measurable fun omega : Omega => fIntervalSum omega a L := by
  unfold fIntervalSum
  exact Finset.measurable_fun_sum _ fun k _ => measurable_f _

theorem integrable_fIntervalSum_sq (a L : ℕ) :
    Integrable (fun omega : Omega => fIntervalSum omega a L ^ 2) μ := by
  unfold fIntervalSum
  rw [show (fun omega : Omega =>
      (∑ k ∈ Finset.range L, f omega (a + k + 1)) ^ 2) =
      fun omega =>
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          f omega (a + i + 1) * f omega (a + j + 1) by
    funext omega
    rw [pow_two, Finset.sum_mul_sum]]
  exact integrable_finset_sum _ fun i _ =>
    integrable_finset_sum _ fun j _ => integrable_f_mul_f _ _

/-- Exact interval second moment.  Nonsquarefree terms simply contribute
zero to the diagonal. -/
theorem integral_fIntervalSum_sq (a L : ℕ) :
    ∫ omega, fIntervalSum omega a L ^ 2 ∂μ =
      ∑ k ∈ Finset.range L, if Squarefree (a + k + 1) then 1 else 0 := by
  unfold fIntervalSum
  rw [show (fun omega : Omega =>
      (∑ k ∈ Finset.range L, f omega (a + k + 1)) ^ 2) =
      fun omega =>
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          f omega (a + i + 1) * f omega (a + j + 1) by
    funext omega
    rw [pow_two, Finset.sum_mul_sum],
    integral_finset_sum (Finset.range L)
      (fun i _ => integrable_finset_sum _ fun j _ =>
        integrable_f_mul_f _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum (Finset.range L)
    (fun j _ => integrable_f_mul_f _ _)]
  by_cases hs : Squarefree (a + i + 1)
  · rw [if_pos hs]
    have hdiag :
        (∫ omega, f omega (a + i + 1) * f omega (a + i + 1) ∂μ) = 1 := by
      rw [integral_f_mul_f]
      simp [hs]
    rw [← hdiag]
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [integral_f_mul_f]
      rw [if_neg]
      rintro ⟨_hsi, _hsj, heq⟩
      apply hji
      omega
    · intro hiNot
      exact (hiNot hi).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_f_mul_f]
    simp [hs]

theorem integral_fIntervalSum_sq_le (a L : ℕ) :
    ∫ omega, fIntervalSum omega a L ^ 2 ∂μ ≤ L := by
  rw [integral_fIntervalSum_sq]
  calc
    (∑ k ∈ Finset.range L, if Squarefree (a + k + 1) then 1 else 0) ≤
        ∑ _k ∈ Finset.range L, (1 : ℝ) := by
      gcongr with k hk
      split_ifs <;> norm_num
    _ = L := by simp

theorem abs_f_le_one (omega : Omega) (n : ℕ) : |f omega n| ≤ 1 := by
  by_cases hn : Squarefree n
  · rw [f_eq_prod_primeFactors_of_squarefree omega hn, abs_prod]
    simp
  · simp [f, hn]

theorem abs_fIntervalSum_le (omega : Omega) (a L : ℕ) :
    |fIntervalSum omega a L| ≤ L := by
  unfold fIntervalSum
  calc
    |∑ k ∈ Finset.range L, f omega (a + k + 1)| ≤
        ∑ k ∈ Finset.range L, |f omega (a + k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range L, (1 : ℝ) := by
      gcongr with k hk
      exact abs_f_le_one omega _
    _ = L := by simp

theorem fIntervalSum_add (omega : Omega) (a L R : ℕ) :
    fIntervalSum omega a (L + R) =
      fIntervalSum omega a L + fIntervalSum omega (a + L) R := by
  unfold fIntervalSum
  rw [Finset.sum_range_add]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  omega

/-- The largest absolute partial increment among the first `L` terms after
`a`, including the empty increment. -/
noncomputable def fIntervalPrefixMax (omega : Omega) (a L : ℕ) : ℝ :=
  (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one
    fun k => |fIntervalSum omega a k|

theorem fIntervalPrefixMax_nonneg (omega : Omega) (a L : ℕ) :
    0 ≤ fIntervalPrefixMax omega a L := by
  unfold fIntervalPrefixMax
  exact (abs_nonneg (fIntervalSum omega a 0)).trans
    (Finset.le_sup' (f := fun k => |fIntervalSum omega a k|)
      (by simp : 0 ∈ Finset.range (L + 1)))

theorem abs_fIntervalSum_le_prefixMax (omega : Omega) (a : ℕ)
    {k L : ℕ} (hk : k ≤ L) :
    |fIntervalSum omega a k| ≤ fIntervalPrefixMax omega a L := by
  unfold fIntervalPrefixMax
  exact Finset.le_sup' (fun k => |fIntervalSum omega a k|)
    (by simpa [Finset.mem_range] using! Nat.lt_succ_of_le hk)

theorem fIntervalPrefixMax_le (omega : Omega) (a L : ℕ) :
    fIntervalPrefixMax omega a L ≤ L := by
  unfold fIntervalPrefixMax
  apply Finset.sup'_le
  intro k hk
  exact (abs_fIntervalSum_le omega a k).trans (by
    exact_mod_cast (Nat.le_of_lt_succ (by simpa using! hk) : k ≤ L))

theorem measurable_fIntervalPrefixMax (a L : ℕ) :
    Measurable fun omega : Omega => fIntervalPrefixMax omega a L := by
  unfold fIntervalPrefixMax
  have hmeas : Measurable
      ((Finset.range (L + 1)).sup' Finset.nonempty_range_add_one
        (fun k => fun omega : Omega => |fIntervalSum omega a k|)) := by
    apply Finset.measurable_sup' Finset.nonempty_range_add_one
    intro k hk
    simpa only [Real.norm_eq_abs] using! (measurable_fIntervalSum a k).norm
  convert! hmeas using 1
  ext omega
  exact (Finset.sup'_apply Finset.nonempty_range_add_one
    (fun k => fun omega : Omega => |fIntervalSum omega a k|) omega).symm

theorem integrable_fIntervalPrefixMax_sq (a L : ℕ) :
    Integrable (fun omega : Omega => fIntervalPrefixMax omega a L ^ 2) μ := by
  refine Integrable.of_bound
    ((measurable_fIntervalPrefixMax a L).pow_const 2).aestronglyMeasurable
    ((L : ℝ) ^ 2) ?_
  filter_upwards [] with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a L)
    (fIntervalPrefixMax_le omega a L) 2

/-- Splitting an interval at `L`: a prefix either stays in the first piece,
or is the whole first piece followed by a prefix of the second. -/
theorem fIntervalPrefixMax_le_split (omega : Omega) (a L R : ℕ) :
    fIntervalPrefixMax omega a (L + R) ≤
      max (fIntervalPrefixMax omega a L)
        (|fIntervalSum omega a L| + fIntervalPrefixMax omega (a + L) R) := by
  unfold fIntervalPrefixMax
  apply Finset.sup'_le
  intro k hk
  have hkLR : k ≤ L + R := by
    exact Nat.le_of_lt_succ (by simpa using! hk)
  by_cases hkL : k ≤ L
  · exact (abs_fIntervalSum_le_prefixMax omega a hkL).trans
      (le_max_left _ _)
  · let r := k - L
    have hkr : k = L + r := by dsimp [r]; omega
    have hr : r ≤ R := by dsimp [r]; omega
    rw [hkr, fIntervalSum_add]
    calc
      |fIntervalSum omega a L + fIntervalSum omega (a + L) r| ≤
          |fIntervalSum omega a L| +
            |fIntervalSum omega (a + L) r| := abs_add_le _ _
      _ ≤ |fIntervalSum omega a L| +
          fIntervalPrefixMax omega (a + L) R :=
        add_le_add le_rfl
          (abs_fIntervalSum_le_prefixMax omega (a + L) hr)
      _ ≤ max (fIntervalPrefixMax omega a L)
          (|fIntervalSum omega a L| +
            fIntervalPrefixMax omega (a + L) R) := le_max_right _ _

private theorem max_sq_le_add_sq {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    max x y ^ 2 ≤ x ^ 2 + y ^ 2 := by
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy]
    nlinarith [sq_nonneg x]
  · rw [max_eq_left (le_of_not_ge hxy)]
    nlinarith [sq_nonneg y]

private theorem add_sq_le_weighted {q x y : ℝ} (hq : 0 < q) :
    (x + y) ^ 2 ≤ (q + 1) * x ^ 2 + (1 + 1 / q) * y ^ 2 := by
  have hmul : q * (x + y) ^ 2 ≤
      q * ((q + 1) * x ^ 2 + (1 + 1 / q) * y ^ 2) := by
    field_simp [hq.ne']
    nlinarith [sq_nonneg (q * x - y)]
  nlinarith [hmul]

theorem fIntervalPrefixMax_sq_le_split_weighted (omega : Omega)
    (a L R : ℕ) {q : ℝ} (hq : 0 < q) :
    fIntervalPrefixMax omega a (L + R) ^ 2 ≤
      fIntervalPrefixMax omega a L ^ 2 +
        (q + 1) * fIntervalSum omega a L ^ 2 +
        (1 + 1 / q) * fIntervalPrefixMax omega (a + L) R ^ 2 := by
  let A := fIntervalPrefixMax omega a L
  let B := fIntervalPrefixMax omega (a + L) R
  let S := fIntervalSum omega a L
  have hA : 0 ≤ A := fIntervalPrefixMax_nonneg omega a L
  have hB : 0 ≤ B := fIntervalPrefixMax_nonneg omega (a + L) R
  have hSB : 0 ≤ |S| + B := add_nonneg (abs_nonneg _) hB
  have hsplit : fIntervalPrefixMax omega a (L + R) ≤
      max A (|S| + B) := fIntervalPrefixMax_le_split omega a L R
  have hsquare : fIntervalPrefixMax omega a (L + R) ^ 2 ≤
      max A (|S| + B) ^ 2 :=
    pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a (L + R)) hsplit 2
  calc
    fIntervalPrefixMax omega a (L + R) ^ 2 ≤
        max A (|S| + B) ^ 2 := hsquare
    _ ≤ A ^ 2 + (|S| + B) ^ 2 := max_sq_le_add_sq hA hSB
    _ ≤ A ^ 2 +
        ((q + 1) * |S| ^ 2 + (1 + 1 / q) * B ^ 2) := by
      gcongr
      exact add_sq_le_weighted hq
    _ = fIntervalPrefixMax omega a L ^ 2 +
        (q + 1) * fIntervalSum omega a L ^ 2 +
        (1 + 1 / q) * fIntervalPrefixMax omega (a + L) R ^ 2 := by
      dsimp [A, B, S]
      rw [sq_abs]
      ring

theorem integral_fIntervalPrefixMax_sq_le_length_sq (a L : ℕ) :
    ∫ omega, fIntervalPrefixMax omega a L ^ 2 ∂μ ≤ (L : ℝ) ^ 2 := by
  calc
    (∫ omega, fIntervalPrefixMax omega a L ^ 2 ∂μ) ≤
        ∫ _omega : Omega, (L : ℝ) ^ 2 ∂μ := by
      exact integral_mono
        (integrable_fIntervalPrefixMax_sq a L)
        (integrable_const ((L : ℝ) ^ 2)) fun omega =>
          pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a L)
            (fIntervalPrefixMax_le omega a L) 2
    _ = (L : ℝ) ^ 2 := by simp

/-- Finite Rademacher--Menshov maximal inequality specialized to the exact
orthogonal system `f(a+1),...,f(a+2^d)`. -/
theorem integral_fIntervalPrefixMax_sq_pow_two_le (a d : ℕ) :
    ∫ omega, fIntervalPrefixMax omega a (2 ^ d) ^ 2 ∂μ ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 * (2 ^ d : ℕ) := by
  induction d generalizing a with
  | zero =>
      simpa using! integral_fIntervalPrefixMax_sq_le_length_sq a 1
  | succ d ih =>
      let N : ℕ := 2 ^ d
      let q : ℝ := (d + 1 : ℕ)
      have hq : 0 < q := by positivity
      have hpow : 2 ^ (d + 1) = N + N := by
        dsimp [N]
        rw [pow_succ]
        omega
      rw [hpow]
      have hpoint (omega : Omega) :
          fIntervalPrefixMax omega a (N + N) ^ 2 ≤
            fIntervalPrefixMax omega a N ^ 2 +
              (q + 1) * fIntervalSum omega a N ^ 2 +
              (1 + 1 / q) *
                fIntervalPrefixMax omega (a + N) N ^ 2 :=
        fIntervalPrefixMax_sq_le_split_weighted omega a N N hq
      have hAint := integrable_fIntervalPrefixMax_sq a N
      have hSint := integrable_fIntervalSum_sq a N
      have hBint := integrable_fIntervalPrefixMax_sq (a + N) N
      have hRint : Integrable (fun omega : Omega =>
          fIntervalPrefixMax omega a N ^ 2 +
            (q + 1) * fIntervalSum omega a N ^ 2 +
            (1 + 1 / q) * fIntervalPrefixMax omega (a + N) N ^ 2) μ :=
        (hAint.add (hSint.const_mul _)).add (hBint.const_mul _)
      calc
        (∫ omega, fIntervalPrefixMax omega a (N + N) ^ 2 ∂μ) ≤
            ∫ omega,
              fIntervalPrefixMax omega a N ^ 2 +
                (q + 1) * fIntervalSum omega a N ^ 2 +
                (1 + 1 / q) *
                  fIntervalPrefixMax omega (a + N) N ^ 2 ∂μ := by
          exact integral_mono
            (integrable_fIntervalPrefixMax_sq a (N + N)) hRint hpoint
        _ = (∫ omega, fIntervalPrefixMax omega a N ^ 2 ∂μ) +
              (q + 1) * (∫ omega, fIntervalSum omega a N ^ 2 ∂μ) +
              (1 + 1 / q) *
                (∫ omega, fIntervalPrefixMax omega (a + N) N ^ 2 ∂μ) := by
          calc
            (∫ omega,
                fIntervalPrefixMax omega a N ^ 2 +
                  (q + 1) * fIntervalSum omega a N ^ 2 +
                  (1 + 1 / q) *
                    fIntervalPrefixMax omega (a + N) N ^ 2 ∂μ) =
                (∫ omega,
                  fIntervalPrefixMax omega a N ^ 2 +
                    (q + 1) * fIntervalSum omega a N ^ 2 ∂μ) +
                ∫ omega, (1 + 1 / q) *
                  fIntervalPrefixMax omega (a + N) N ^ 2 ∂μ := by
              exact integral_add
                (hAint.add (hSint.const_mul _)) (hBint.const_mul _)
            _ = ((∫ omega, fIntervalPrefixMax omega a N ^ 2 ∂μ) +
                  ∫ omega, (q + 1) * fIntervalSum omega a N ^ 2 ∂μ) +
                ∫ omega, (1 + 1 / q) *
                  fIntervalPrefixMax omega (a + N) N ^ 2 ∂μ := by
              rw [integral_add hAint (hSint.const_mul _)]
            _ = _ := by rw [integral_const_mul, integral_const_mul]
        _ ≤ q ^ 2 * N + (q + 1) * N +
              (1 + 1 / q) * (q ^ 2 * N) := by
          gcongr
          · simpa [q, N] using! ih (a := a)
          · exact integral_fIntervalSum_sq_le a N
          · simpa [q, N] using! ih (a := a + N)
        _ ≤ (((d + 1) + 1 : ℕ) : ℝ) ^ 2 *
              ((N : ℝ) + (N : ℝ)) := by
          have hcast : (((d + 1) + 1 : ℕ) : ℝ) =
              ((d + 1 : ℕ) : ℝ) + 1 := by norm_num
          rw [hcast]
          dsimp [q]
          have hd : (0 : ℝ) < (d + 1 : ℕ) := by positivity
          field_simp
          nlinarith [show (0 : ℝ) ≤ N by positivity]
        _ = (((d + 1) + 1 : ℕ) : ℝ) ^ 2 * (N + N : ℕ) := by
          norm_cast

theorem fIntervalPrefixMax_mono_length (omega : Omega) (a : ℕ)
    {L R : ℕ} (hLR : L ≤ R) :
    fIntervalPrefixMax omega a L ≤ fIntervalPrefixMax omega a R := by
  unfold fIntervalPrefixMax
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' (fun k => |fIntervalSum omega a k|) (by
    have hkL : k ≤ L := Nat.le_of_lt_succ (by simpa using! hk)
    simpa using! Nat.lt_succ_of_le (hkL.trans hLR))

theorem integral_fIntervalPrefixMax_sq_le_of_le_pow_two
    (a L d : ℕ) (hL : L ≤ 2 ^ d) :
    ∫ omega, fIntervalPrefixMax omega a L ^ 2 ∂μ ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 * (2 ^ d : ℕ) := by
  calc
    (∫ omega, fIntervalPrefixMax omega a L ^ 2 ∂μ) ≤
        ∫ omega, fIntervalPrefixMax omega a (2 ^ d) ^ 2 ∂μ := by
      apply integral_mono
        (integrable_fIntervalPrefixMax_sq a L)
        (integrable_fIntervalPrefixMax_sq a (2 ^ d))
      intro omega
      exact pow_le_pow_left₀ (fIntervalPrefixMax_nonneg omega a L)
        (fIntervalPrefixMax_mono_length omega a hL) 2
    _ ≤ ((d + 1 : ℕ) : ℝ) ^ 2 * (2 ^ d : ℕ) :=
      integral_fIntervalPrefixMax_sq_pow_two_le a d

/-- Markov applied to the finite Rademacher--Menshov inequality. -/
theorem measureReal_fIntervalPrefixMax_ge_le_of_le_pow_two
    (a L d : ℕ) (hL : L ≤ 2 ^ d) {u : ℝ} (hu : 0 < u) :
    μ.real {omega | u ≤ fIntervalPrefixMax omega a L} ≤
      (((d + 1 : ℕ) : ℝ) ^ 2 * (2 ^ d : ℕ)) / u ^ 2 := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ)
    (ae_of_all μ fun omega =>
      sq_nonneg (fIntervalPrefixMax omega a L))
    (integrable_fIntervalPrefixMax_sq a L) (u ^ 2)
  have hset : {omega | u ^ 2 ≤ fIntervalPrefixMax omega a L ^ 2} =
      {omega | u ≤ fIntervalPrefixMax omega a L} := by
    ext omega
    simpa only [Set.mem_setOf_eq] using!
      (pow_le_pow_iff_left₀ hu.le
        (fIntervalPrefixMax_nonneg omega a L) (by norm_num : 2 ≠ 0))
  rw [hset] at hmarkov
  apply (le_div_iff₀ (sq_pos_of_pos hu)).2
  simpa only [mul_comm] using!
    hmarkov.trans (integral_fIntervalPrefixMax_sq_le_of_le_pow_two a L d hL)

end Problem520
end Erdos
