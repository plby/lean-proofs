/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos4.ResidualPrimeFiberMertens
import ErdosProblems.Erdos587.Erdos587Core
import ErdosProblems.Erdos13.Erdos13Kneser
import ErdosProblems.Erdos13.Erdos13Additive
import ErdosProblems.Erdos360.DiverseSampling
import ErdosProblems.Erdos360.ResolutionScale
import ErdosProblems.Erdos360.TernaryClosure
import ErdosProblems.Erdos360.StructuredSmallDoubling
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 360

For `n ≥ 2`, let `f(n)` be the least number of colors in a coloring of
`{1, …, n - 1}` for which `n` is not a sum of distinct integers of one color.
Conlon, Fox, and Pham proved

`f(n) ≍ n^(1/3) (n / φ(n)) / ((log n)^(1/3) (log log n)^(2/3))`.

The mathematical proof and the formalization plan are recorded in `tex/360.tex`.
-/

namespace Erdos360

open Filter
open scoped BigOperators Pointwise ComplexConjugate
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open Erdos851.BetaSieveFundamental

attribute [local instance] Classical.propDecidable

/-- The finite type corresponding to the positive integers strictly below `n`. -/
abbrev BelowTarget (n : ℕ) := {x : ℕ // x ∈ Finset.Ico 1 n}

/-- A finite set is monochromatic for `c` when all of its elements have the same color.
This pairwise formulation also treats the empty set as monochromatic. -/
def Monochromatic {n r : ℕ} (c : BelowTarget n → Fin r)
    (A : Finset (BelowTarget n)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → c x = c y

/-- A coloring avoids the target when no monochromatic finite subset has value-sum `n`. -/
def AvoidsTarget (n r : ℕ) (c : BelowTarget n → Fin r) : Prop :=
  ∀ A : Finset (BelowTarget n), Monochromatic c A →
    A.sum (fun x ↦ x.1) ≠ n

/-- There is an `r`-coloring of `{1, …, n - 1}` avoiding `n`. -/
def Colorable (n r : ℕ) : Prop :=
  ∃ c : BelowTarget n → Fin r, AvoidsTarget n r c

/-- Every `r`-coloring produces a monochromatic subset whose sum is the target. -/
def ForcesTarget (n r : ℕ) : Prop :=
  ∀ c : BelowTarget n → Fin r,
    ∃ A : Finset (BelowTarget n),
      Monochromatic c A ∧ A.sum (fun x ↦ x.1) = n

lemma forcesTarget_iff_not_colorable (n r : ℕ) :
    ForcesTarget n r ↔ ¬Colorable n r := by
  classical
  constructor
  · intro hforce hcolor
    obtain ⟨c, hc⟩ := hcolor
    obtain ⟨A, hmono, hsum⟩ := hforce c
    exact hc A hmono hsum
  · intro hnot c
    by_contra hfail
    apply hnot
    refine ⟨c, ?_⟩
    intro A hmono hsum
    exact hfail ⟨A, hmono, hsum⟩

/-- A set of integers below `n` contains no subset with value-sum `n`. -/
def TargetAvoiding (n : ℕ) (S : Finset (BelowTarget n)) : Prop :=
  ∀ A : Finset (BelowTarget n), A ⊆ S → A.sum (fun x ↦ x.1) ≠ n

/-- Forget the range proofs on a finite set of integers below the target. -/
def values {n : ℕ} (S : Finset (BelowTarget n)) : Finset ℕ :=
  S.image Subtype.val

lemma mem_values {n : ℕ} {S : Finset (BelowTarget n)} {a : ℕ} :
    a ∈ values S ↔ ∃ x ∈ S, x.1 = a := by
  simp [values]

lemma sum_values {n : ℕ} (S : Finset (BelowTarget n)) :
    (values S).sum id = S.sum (fun x ↦ x.1) := by
  simp [values, Finset.sum_image, Function.Injective.injOn Subtype.val_injective]

lemma sum_mem_subsetSum_values {n : ℕ} {A S : Finset (BelowTarget n)}
    (hAS : A ⊆ S) : A.sum (fun x ↦ x.1) ∈ (values S).subsetSum := by
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨values A, ?_, ?_⟩
  · simpa [values] using Finset.image_mono Subtype.val hAS
  exact sum_values A

/-- The universal formulation of `TargetAvoiding` is exactly nonmembership in
Mathlib's finite subset-sum set. -/
lemma targetAvoiding_iff_not_mem_subsetSum {n : ℕ} (S : Finset (BelowTarget n)) :
    TargetAvoiding n S ↔ n ∉ (values S).subsetSum := by
  classical
  constructor
  · intro havoid hn
    obtain ⟨B, hB, hsum⟩ := Finset.mem_subsetSum_iff.mp hn
    let A := S.filter fun x ↦ x.1 ∈ B
    have hAS : A ⊆ S := Finset.filter_subset _ _
    have hvalues : values A = B := by
      ext b
      constructor
      · rintro hb
        obtain ⟨x, hx, rfl⟩ := mem_values.mp hb
        exact (Finset.mem_filter.mp hx).2
      · intro hb
        obtain ⟨x, hxS, hxb⟩ := mem_values.mp (hB hb)
        subst b
        apply mem_values.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hxS, hb⟩, rfl⟩
    apply havoid A hAS
    calc
      A.sum (fun x ↦ x.1) = (values A).sum id := (sum_values A).symm
      _ = B.sum id := by rw [hvalues]
      _ = n := hsum
  · intro hn A hAS htarget
    apply hn
    simpa only [htarget] using sum_mem_subsetSum_values hAS

lemma exists_lt_of_two_le_card {B : Finset ℕ} {u : ℕ} (hcard : 2 ≤ B.card)
    (hB : ∀ x ∈ B, x ≤ u) : ∃ x ∈ B, x < u := by
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hBne
  have herase : (B.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := herase
  have hyB : y ∈ B := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  by_cases hxu : x < u
  · exact ⟨x, hx, hxu⟩
  · have hxeq : x = u := Nat.le_antisymm (hB x hx) (Nat.le_of_not_gt hxu)
    have hyu : y ≠ u := by
      intro hyu
      apply hyx
      omega
    exact ⟨y, hyB, (hB y hyB).lt_of_ne hyu⟩

lemma exists_gt_of_two_le_card {B : Finset ℕ} {l : ℕ} (hcard : 2 ≤ B.card)
    (hB : ∀ x ∈ B, l ≤ x) : ∃ x ∈ B, l < x := by
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hBne
  have herase : (B.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := herase
  have hyB : y ∈ B := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  by_cases hlx : l < x
  · exact ⟨x, hx, hlx⟩
  · have hxeq : x = l := Nat.le_antisymm (Nat.le_of_not_gt hlx) (hB x hx)
    have hyl : y ≠ l := by
      intro hyl
      apply hyx
      omega
    exact ⟨y, hyB, lt_of_le_of_ne (hB y hyB) hyl.symm⟩

lemma exists_lt_of_two_le_card_of_injective {α : Type*} [DecidableEq α]
    {B : Finset α} {f : α → ℕ} {u : ℕ} (hcard : 2 ≤ B.card)
    (hf : Function.Injective f) (hB : ∀ x ∈ B, f x ≤ u) :
    ∃ x ∈ B, f x < u := by
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hBne
  have herase : (B.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := herase
  have hyB : y ∈ B := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  by_cases hxu : f x < u
  · exact ⟨x, hx, hxu⟩
  · have hxeq : f x = u := Nat.le_antisymm (hB x hx) (Nat.le_of_not_gt hxu)
    have hyu : f y ≠ u := by
      intro hyu
      apply hyx
      apply hf
      omega
    exact ⟨y, hyB, (hB y hyB).lt_of_ne hyu⟩

lemma exists_gt_of_two_le_card_of_injective {α : Type*} [DecidableEq α]
    {B : Finset α} {f : α → ℕ} {l : ℕ} (hcard : 2 ≤ B.card)
    (hf : Function.Injective f) (hB : ∀ x ∈ B, l ≤ f x) :
    ∃ x ∈ B, l < f x := by
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hBne
  have herase : (B.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := herase
  have hyB : y ∈ B := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  by_cases hlx : l < f x
  · exact ⟨x, hx, hlx⟩
  · have hxeq : f x = l := Nat.le_antisymm (Nat.le_of_not_gt hlx) (hB x hx)
    have hyl : f y ≠ l := by
      intro hyl
      apply hyx
      apply hf
      omega
    exact ⟨y, hyB, lt_of_le_of_ne (hB y hyB) hyl.symm⟩

/-- Distinctness makes the usual bound by `card * maximum` strict once there
are at least two terms. -/
lemma sum_lt_card_mul_of_two_le_card {B : Finset ℕ} {u : ℕ} (hcard : 2 ≤ B.card)
    (hB : ∀ x ∈ B, x ≤ u) : B.sum id < B.card * u := by
  obtain ⟨x, hx, hxu⟩ := exists_lt_of_two_le_card hcard hB
  simpa using Finset.sum_lt_sum hB ⟨x, hx, hxu⟩

/-- The dual strict bound by `card * minimum`. -/
lemma card_mul_lt_sum_of_two_le_card {B : Finset ℕ} {l : ℕ} (hcard : 2 ≤ B.card)
    (hB : ∀ x ∈ B, l ≤ x) : B.card * l < B.sum id := by
  obtain ⟨x, hx, hlx⟩ := exists_gt_of_two_le_card hcard hB
  simpa using Finset.sum_lt_sum hB ⟨x, hx, hlx⟩

lemma targetAvoiding_of_total_lt {n : ℕ} {S : Finset (BelowTarget n)}
    (hS : S.sum (fun x ↦ x.1) < n) : TargetAvoiding n S := by
  intro A hAS hsum
  have hle : A.sum (fun x ↦ x.1) ≤ S.sum (fun x ↦ x.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hAS (fun _ _ _ ↦ Nat.zero_le _)
  omega

lemma targetAvoiding_of_common_dvd {n p : ℕ} {S : Finset (BelowTarget n)}
    (hpn : ¬p ∣ n) (hpS : ∀ x ∈ S, p ∣ x.1) : TargetAvoiding n S := by
  intro A hAS hsum
  apply hpn
  rw [← hsum]
  exact Finset.dvd_sum fun x hx ↦ hpS x (hAS hx)

/-- The size band used in the first step of the Alon--Erdős and
Conlon--Fox--Pham colorings.  Its multiplicative description avoids any
rounding convention for the endpoints. -/
def sizeBand (n k : ℕ) : Finset (BelowTarget n) :=
  Finset.univ.filter fun x ↦ k * x.1 ≤ n ∧ n ≤ (k + 1) * x.1

lemma mem_sizeBand {n k : ℕ} {x : BelowTarget n} :
    x ∈ sizeBand n k ↔ k * x.1 ≤ n ∧ n ≤ (k + 1) * x.1 := by
  simp [sizeBand]

/-- Every size band is target-avoiding.  The strict inequalities use the
fact that a subset is a set of distinct integers. -/
lemma targetAvoiding_sizeBand {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    TargetAvoiding n (sizeBand n k) := by
  intro A hA hsum
  by_cases hcard : A.card ≤ k
  · by_cases hone : A.card ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hone with hzero | hone
      · have hAempty : A = ∅ := Finset.card_eq_zero.mp hzero
        subst A
        simp_all
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
        have hxlt : x.1 < n := (Finset.mem_Ico.mp x.2).2
        apply hxlt.ne
        simpa using hsum
    · have htwo : 2 ≤ A.card := by omega
      have hpoint : ∀ x ∈ A, k * x.1 ≤ n := by
        intro x hx
        exact (mem_sizeBand.mp (hA hx)).1
      have hinj : Function.Injective (fun x : BelowTarget n ↦ k * x.1) := by
        intro x y hxy
        apply Subtype.ext
        exact Nat.eq_of_mul_eq_mul_left hk hxy
      obtain ⟨x, hx, hxstrict⟩ :=
        exists_lt_of_two_le_card_of_injective htwo hinj hpoint
      have hmul : k * A.sum (fun x ↦ x.1) < A.card * n := by
        rw [Finset.mul_sum]
        simpa using Finset.sum_lt_sum hpoint ⟨x, hx, hxstrict⟩
      have : k * A.sum (fun x ↦ x.1) < k * n :=
        hmul.trans_le (Nat.mul_le_mul_right n hcard)
      have : A.sum (fun x ↦ x.1) < n := (Nat.mul_lt_mul_left hk).mp this
      omega
  · have hkcard : k + 1 ≤ A.card := by omega
    have htwo : 2 ≤ A.card := by omega
    have hpoint : ∀ x ∈ A, n ≤ (k + 1) * x.1 := by
      intro x hx
      exact (mem_sizeBand.mp (hA hx)).2
    have hinj : Function.Injective (fun x : BelowTarget n ↦ (k + 1) * x.1) := by
      intro x y hxy
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
    obtain ⟨x, hx, hxstrict⟩ :=
      exists_gt_of_two_le_card_of_injective htwo hinj hpoint
    have hmul : A.card * n < (k + 1) * A.sum (fun x ↦ x.1) := by
      rw [Finset.mul_sum]
      simpa using Finset.sum_lt_sum hpoint ⟨x, hx, hxstrict⟩
    have : (k + 1) * n < (k + 1) * A.sum (fun x ↦ x.1) :=
      (Nat.mul_le_mul_right n hkcard).trans_lt hmul
    have : n < A.sum (fun x ↦ x.1) :=
      (Nat.mul_lt_mul_left (by omega : 0 < k + 1)).mp this
    omega

lemma mem_sizeBand_div {n : ℕ} (x : BelowTarget n) (hx : 0 < x.1) :
    x ∈ sizeBand n (n / x.1) := by
  apply mem_sizeBand.mpr
  constructor
  · exact Nat.div_mul_le_self n x.1
  · exact (Nat.div_lt_iff_lt_mul hx).mp (Nat.lt_succ_self (n / x.1)) |>.le

/-- The first `h` size bands, corresponding to the paper's indices
`1, ..., h`. -/
def firstBandFamily (n h : ℕ) (i : Fin h) : Finset (BelowTarget n) :=
  sizeBand n (i.1 + 1)

lemma firstBandFamily_avoiding {n h : ℕ} (hn : 0 < n) (i : Fin h) :
    TargetAvoiding n (firstBandFamily n h i) :=
  targetAvoiding_sizeBand hn (by omega)

/-- If `n < h*x`, then `x` belongs to one of the first `h` size bands. -/
lemma firstBandFamily_covers_of_lt_mul {n h : ℕ} (x : BelowTarget n)
    (hx : n < h * x.1) : ∃ i, x ∈ firstBandFamily n h i := by
  have hxpos : 0 < x.1 := (Finset.mem_Ico.mp x.2).1
  have hindex : n / x.1 < h := (Nat.div_lt_iff_lt_mul hxpos).mpr hx
  have hquot : 0 < n / x.1 :=
    Nat.div_pos (Finset.mem_Ico.mp x.2).2.le hxpos
  let i : Fin h := ⟨n / x.1 - 1, by omega⟩
  refine ⟨i, ?_⟩
  change x ∈ sizeBand n (i.1 + 1)
  have hi : i.1 + 1 = n / x.1 := by
    dsimp [i]
    omega
  rw [hi]
  exact mem_sizeBand_div x hxpos

/-- The `i`th prime in zero-based indexing. -/
noncomputable abbrev primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- The second family in the upper-bound coloring: multiples of one of the
first `h` primes, provided that prime does not divide the target. -/
noncomputable def primeMultipleFamily (n h : ℕ) (i : Fin h) : Finset (BelowTarget n) :=
  Finset.univ.filter fun x ↦ ¬primeAt i.1 ∣ n ∧ primeAt i.1 ∣ x.1

lemma mem_primeMultipleFamily {n h : ℕ} {i : Fin h} {x : BelowTarget n} :
    x ∈ primeMultipleFamily n h i ↔ ¬primeAt i.1 ∣ n ∧ primeAt i.1 ∣ x.1 := by
  simp [primeMultipleFamily]

lemma primeMultipleFamily_avoiding {n h : ℕ} (hn : 0 < n) (i : Fin h) :
    TargetAvoiding n (primeMultipleFamily n h i) := by
  by_cases hp : primeAt i.1 ∣ n
  · have hempty : primeMultipleFamily n h i = ∅ := by
      ext x
      simp [primeMultipleFamily, hp]
    apply targetAvoiding_of_total_lt
    simp [hempty, hn]
  · apply targetAvoiding_of_common_dvd hp
    intro x hx
    exact (mem_primeMultipleFamily.mp hx).2

lemma primeMultipleFamily_covers {n h : ℕ} (x : BelowTarget n) (i : Fin h)
    (hpn : ¬primeAt i.1 ∣ n) (hpx : primeAt i.1 ∣ x.1) :
    x ∈ primeMultipleFamily n h i :=
  mem_primeMultipleFamily.mpr ⟨hpn, hpx⟩

/-- Characterization of an integer left after the prime-multiple classes. -/
lemma not_primeMultipleFamily_covered_iff {n h : ℕ} (x : BelowTarget n) :
    (¬∃ i : Fin h, x ∈ primeMultipleFamily n h i) ↔
      ∀ i : Fin h, primeAt i.1 ∣ x.1 → primeAt i.1 ∣ n := by
  constructor
  · intro h i hpx
    by_contra hpn
    exact h ⟨i, primeMultipleFamily_covers x i hpn hpx⟩
  · intro h
    rintro ⟨i, hi⟩
    exact (mem_primeMultipleFamily.mp hi).1 (h i (mem_primeMultipleFamily.mp hi).2)

lemma Nat.ModEq.representative_le {d q x : ℕ} (hmod : q ≡ x [MOD d])
    (hq : 0 < q) (_hx : 0 < x) (hxd : x ≤ d) : x ≤ q := by
  by_contra h
  have hqx : q < x := by omega
  have := hmod.add_le_of_lt hqx
  omega

/-- Two positive congruent integers, the second chosen in `(0,d]`, are
either equal or differ by at least one full modulus. -/
lemma Nat.ModEq.eq_or_add_le {d q x : ℕ} (hmod : q ≡ x [MOD d])
    (hq : 0 < q) (hx : 0 < x) (hxd : x ≤ d) : q = x ∨ d + x ≤ q := by
  have hxq : x ≤ q := Nat.ModEq.representative_le hmod hq hx hxd
  by_cases heq : q = x
  · exact Or.inl heq
  · right
    by_contra h
    have hlt : q < x + d := by omega
    have hqx : q ≤ x := hmod.le_of_lt_add hlt
    omega

/-- If all selected integers have residue `s`, and `s*x` is the target
residue, coprimality of `s` and the modulus forces the number of selected
terms to be congruent to `x`. -/
lemma card_modEq_of_sum_eq_of_constant_modEq {n d s x : ℕ}
    {A : Finset (BelowTarget n)} (hcop : Nat.Coprime d s)
    (hres : ∀ a ∈ A, a.1 ≡ s [MOD d])
    (hsum : A.sum (fun a ↦ a.1) = n) (hx : s * x ≡ n [MOD d]) :
    A.card ≡ x [MOD d] := by
  have hsumMod : A.sum (fun a ↦ a.1) ≡ A.sum (fun _ ↦ s) [MOD d] :=
    Nat.ModEq.sum (s := A) hres
  have hcardMod : s * A.card ≡ n [MOD d] := by
    simpa [hsum, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using hsumMod.symm
  exact Nat.ModEq.cancel_left_of_coprime hcop (hcardMod.trans hx.symm)

/-- The high part of a fixed invertible residue class in Step 3. -/
def residueHigh (n d s x : ℕ) : Finset (BelowTarget n) :=
  Finset.univ.filter fun t ↦ t.1 ≡ s [MOD d] ∧ n ≤ x * t.1

/-- The middle part of a fixed invertible residue class in Step 3. -/
def residueMid (n d s x : ℕ) : Finset (BelowTarget n) :=
  Finset.univ.filter fun t ↦
    t.1 ≡ s [MOD d] ∧ x * t.1 < n ∧ n ≤ (d + x) * t.1

lemma mem_residueHigh {n d s x : ℕ} {t : BelowTarget n} :
    t ∈ residueHigh n d s x ↔ t.1 ≡ s [MOD d] ∧ n ≤ x * t.1 := by
  simp [residueHigh]

lemma mem_residueMid {n d s x : ℕ} {t : BelowTarget n} :
    t ∈ residueMid n d s x ↔
      t.1 ≡ s [MOD d] ∧ x * t.1 < n ∧ n ≤ (d + x) * t.1 := by
  simp [residueMid]

lemma residueHigh_avoiding {n d s x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hxd : x ≤ d) (hcop : Nat.Coprime d s) (hxs : s * x ≡ n [MOD d]) :
    TargetAvoiding n (residueHigh n d s x) := by
  intro A hA hsum
  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
    simp at hsum
    omega
  have hcardpos : 0 < A.card := Finset.card_pos.mpr hAne
  have hres : ∀ a ∈ A, a.1 ≡ s [MOD d] := by
    intro a ha
    exact (mem_residueHigh.mp (hA ha)).1
  have hcardMod : A.card ≡ x [MOD d] :=
    card_modEq_of_sum_eq_of_constant_modEq hcop hres hsum hxs
  have hxcard : x ≤ A.card :=
    Nat.ModEq.representative_le hcardMod hcardpos hx hxd
  by_cases hcard : A.card ≤ 1
  · have hcardeq : A.card = 1 := by omega
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcardeq
    have hxt : n ≤ x * t.1 := (mem_residueHigh.mp (hA (by simp))).2
    have hxone : x = 1 := by omega
    have htlt : t.1 < n := (Finset.mem_Ico.mp t.2).2
    simp [hxone] at hxt
    omega
  · have htwo : 2 ≤ A.card := by omega
    have hpoint : ∀ a ∈ A, n ≤ x * a.1 := by
      intro a ha
      exact (mem_residueHigh.mp (hA ha)).2
    have hinj : Function.Injective (fun a : BelowTarget n ↦ x * a.1) := by
      intro a b hab
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left hx hab
    obtain ⟨a, ha, hastrict⟩ :=
      exists_gt_of_two_le_card_of_injective htwo hinj hpoint
    have hmul : A.card * n < x * A.sum (fun a ↦ a.1) := by
      rw [Finset.mul_sum]
      simpa using Finset.sum_lt_sum hpoint ⟨a, ha, hastrict⟩
    have hxn : x * n < x * A.sum (fun a ↦ a.1) :=
      (Nat.mul_le_mul_right n hxcard).trans_lt hmul
    have : n < A.sum (fun a ↦ a.1) := (Nat.mul_lt_mul_left hx).mp hxn
    omega

lemma residueMid_avoiding {n d s x : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hxd : x ≤ d) (hcop : Nat.Coprime d s) (hxs : s * x ≡ n [MOD d]) :
    TargetAvoiding n (residueMid n d s x) := by
  intro A hA hsum
  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
    simp at hsum
    omega
  have hcardpos : 0 < A.card := Finset.card_pos.mpr hAne
  have hres : ∀ a ∈ A, a.1 ≡ s [MOD d] := by
    intro a ha
    exact (mem_residueMid.mp (hA ha)).1
  have hcardMod : A.card ≡ x [MOD d] :=
    card_modEq_of_sum_eq_of_constant_modEq hcop hres hsum hxs
  rcases Nat.ModEq.eq_or_add_le hcardMod hcardpos hx hxd with hcardeq | hlarge
  · have hpoint : ∀ a ∈ A, x * a.1 < n := by
      intro a ha
      exact (mem_residueMid.mp (hA ha)).2.1
    obtain ⟨a, ha⟩ := hAne
    have hmul : x * A.sum (fun a ↦ a.1) < A.card * n := by
      rw [Finset.mul_sum]
      simpa using
        Finset.sum_lt_sum (fun a ha ↦ (hpoint a ha).le) ⟨a, ha, hpoint a ha⟩
    rw [hcardeq] at hmul
    have : A.sum (fun a ↦ a.1) < n := (Nat.mul_lt_mul_left hx).mp hmul
    omega
  · have hdx : 0 < d + x := by omega
    have htwo : 2 ≤ A.card := by omega
    have hpoint : ∀ a ∈ A, n ≤ (d + x) * a.1 := by
      intro a ha
      exact (mem_residueMid.mp (hA ha)).2.2
    have hinj : Function.Injective (fun a : BelowTarget n ↦ (d + x) * a.1) := by
      intro a b hab
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left hdx hab
    obtain ⟨a, ha, hastrict⟩ :=
      exists_gt_of_two_le_card_of_injective htwo hinj hpoint
    have hmul : A.card * n < (d + x) * A.sum (fun a ↦ a.1) := by
      rw [Finset.mul_sum]
      simpa using Finset.sum_lt_sum hpoint ⟨a, ha, hastrict⟩
    have hdxn : (d + x) * n < (d + x) * A.sum (fun a ↦ a.1) :=
      (Nat.mul_le_mul_right n hlarge).trans_lt hmul
    have : n < A.sum (fun a ↦ a.1) := (Nat.mul_lt_mul_left hdx).mp hdxn
    omega

/-- The positive representative of `t⁻¹ n` modulo `d`, constructed as a
unit of `ZMod d`. -/
noncomputable def targetResidue (n t d : ℕ) (ht : Nat.Coprime t d)
    (hn : Nat.Coprime n d) : ℕ :=
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime t ht
  let v : (ZMod d)ˣ := ZMod.unitOfCoprime n hn
  (((u⁻¹ * v : (ZMod d)ˣ) : ZMod d)).val

lemma targetResidue_lt {n t d : ℕ} (hd : 0 < d) (ht : Nat.Coprime t d)
    (hn : Nat.Coprime n d) : targetResidue n t d ht hn < d := by
  let : NeZero d := ⟨hd.ne'⟩
  unfold targetResidue
  exact ZMod.val_lt _

lemma targetResidue_coprime {n t d : ℕ} (ht : Nat.Coprime t d)
    (hn : Nat.Coprime n d) : Nat.Coprime (targetResidue n t d ht hn) d := by
  unfold targetResidue
  exact ZMod.val_coe_unit_coprime
    ((ZMod.unitOfCoprime t ht)⁻¹ * ZMod.unitOfCoprime n hn)

lemma targetResidue_pos {n t d : ℕ} (hd : 1 < d) (ht : Nat.Coprime t d)
    (hn : Nat.Coprime n d) : 0 < targetResidue n t d ht hn := by
  have hcop := targetResidue_coprime ht hn
  by_contra h
  have hzero : targetResidue n t d ht hn = 0 := by omega
  have hd1 : d = 1 := by
    simpa [hzero] using hcop
  omega

lemma targetResidue_spec {n t d : ℕ} (hd : 0 < d) (ht : Nat.Coprime t d)
    (hn : Nat.Coprime n d) :
    t * targetResidue n t d ht hn ≡ n [MOD d] := by
  let : NeZero d := ⟨hd.ne'⟩
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime t ht
  let v : (ZMod d)ˣ := ZMod.unitOfCoprime n hn
  have hresidue : (targetResidue n t d ht hn : ZMod d) =
      ((u⁻¹ * v : (ZMod d)ˣ) : ZMod d) := by
    unfold targetResidue
    exact ZMod.natCast_zmod_val _
  apply (ZMod.natCast_eq_natCast_iff (t * targetResidue n t d ht hn) n d).mp
  push_cast
  rw [hresidue]
  rw [show (t : ZMod d) = (u : ZMod d) by
    exact (ZMod.coe_unitOfCoprime t ht).symm]
  rw [← Units.val_mul, mul_inv_cancel_left]
  exact ZMod.coe_unitOfCoprime n hn

/-- A reduced residue `t` at height at least `n/d` lies in one of its two
Step-3 classes. -/
lemma mem_residueHigh_or_mid {n d : ℕ} (hd : 1 < d) (hn : Nat.Coprime n d)
    (t : BelowTarget n) (ht : Nat.Coprime t.1 d) (htLower : n ≤ d * t.1) :
    let x := targetResidue n t.1 d ht hn
    t ∈ residueHigh n d t.1 x ∨ t ∈ residueMid n d t.1 x := by
  let x := targetResidue n t.1 d ht hn
  by_cases hhigh : n ≤ x * t.1
  · left
    exact mem_residueHigh.mpr ⟨Nat.ModEq.refl _, hhigh⟩
  · right
    apply mem_residueMid.mpr
    refine ⟨Nat.ModEq.refl _, Nat.lt_of_not_ge hhigh, ?_⟩
    calc
      n ≤ d * t.1 := htLower
      _ ≤ (d + x) * t.1 := Nat.mul_le_mul_right t.1 (Nat.le_add_right d x)

/-- The natural representative of a unit modulo `d`. -/
abbrev unitNat {d : ℕ} (u : (ZMod d)ˣ) : ℕ := (u : ZMod d).val

lemma unitNat_coprime {d : ℕ} (u : (ZMod d)ˣ) : Nat.Coprime (unitNat u) d :=
  ZMod.val_coe_unit_coprime u

/-- The target-cardinality representative associated with a unit residue. -/
noncomputable def unitTargetResidue {d : ℕ} (n : ℕ) (hn : Nat.Coprime n d)
    (u : (ZMod d)ˣ) : ℕ :=
  targetResidue n (unitNat u) d (unitNat_coprime u) hn

lemma unitTargetResidue_pos {n d : ℕ} (hd : 1 < d) (hn : Nat.Coprime n d)
    (u : (ZMod d)ˣ) : 0 < unitTargetResidue n hn u :=
  targetResidue_pos hd (unitNat_coprime u) hn

lemma unitTargetResidue_le {n d : ℕ} (hd : 0 < d) (hn : Nat.Coprime n d)
    (u : (ZMod d)ˣ) : unitTargetResidue n hn u ≤ d :=
  (targetResidue_lt hd (unitNat_coprime u) hn).le

lemma unitTargetResidue_spec {n d : ℕ} (hd : 0 < d) (hn : Nat.Coprime n d)
    (u : (ZMod d)ˣ) :
    unitNat u * unitTargetResidue n hn u ≡ n [MOD d] :=
  targetResidue_spec hd (unitNat_coprime u) hn

/-- Both Step-3 classes for every invertible residue modulo `d`. -/
noncomputable def residueClassFamily {d : ℕ} (n : ℕ) (hn : Nat.Coprime n d)
    (i : (ZMod d)ˣ × Fin 2) : Finset (BelowTarget n) :=
  if i.2.1 = 0 then
    residueHigh n d (unitNat i.1) (unitTargetResidue n hn i.1)
  else
    residueMid n d (unitNat i.1) (unitTargetResidue n hn i.1)

lemma residueClassFamily_avoiding {n d : ℕ} (hd : 1 < d)
    (hn : Nat.Coprime n d) (i : (ZMod d)ˣ × Fin 2) :
    TargetAvoiding n (residueClassFamily n hn i) := by
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnzero
    subst n
    have hd_one : d = 1 := by simpa using hn
    omega
  rcases i with ⟨u, j⟩
  fin_cases j
  · simp only [residueClassFamily, ↓reduceIte]
    exact residueHigh_avoiding hnpos (unitTargetResidue_pos hd hn u)
      (unitTargetResidue_le (by omega) hn u) (unitNat_coprime u).symm
      (unitTargetResidue_spec (by omega) hn u)
  · simp only [residueClassFamily, one_ne_zero, ↓reduceIte]
    exact residueMid_avoiding hnpos (unitTargetResidue_pos hd hn u)
      (unitTargetResidue_le (by omega) hn u) (unitNat_coprime u).symm
      (unitTargetResidue_spec (by omega) hn u)

lemma residueClassFamily_covers {n d : ℕ} (hd : 1 < d) (hn : Nat.Coprime n d)
    (t : BelowTarget n) (ht : Nat.Coprime t.1 d) (htLower : n ≤ d * t.1) :
    ∃ i : (ZMod d)ˣ × Fin 2, t ∈ residueClassFamily n hn i := by
  let : NeZero d := ⟨by omega⟩
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime t.1 ht
  have hres : t.1 ≡ unitNat u [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff t.1 (unitNat u) d).mp
    calc
      (t.1 : ZMod d) = (u : ZMod d) := (ZMod.coe_unitOfCoprime t.1 ht).symm
      _ = (unitNat u : ZMod d) := (ZMod.natCast_zmod_val _).symm
  let x := unitTargetResidue n hn u
  by_cases hhigh : n ≤ x * t.1
  · refine ⟨(u, 0), ?_⟩
    change t ∈ residueHigh n d (unitNat u) x
    exact mem_residueHigh.mpr ⟨hres, hhigh⟩
  · refine ⟨(u, 1), ?_⟩
    change t ∈ residueMid n d (unitNat u) x
    apply mem_residueMid.mpr
    refine ⟨hres, Nat.lt_of_not_ge hhigh, ?_⟩
    calc
      n ≤ d * t.1 := htLower
      _ ≤ (d + x) * t.1 := Nat.mul_le_mul_right t.1 (Nat.le_add_right d x)

lemma card_residueClassIndex (d : ℕ) [NeZero d] :
    Fintype.card ((ZMod d)ˣ × Fin 2) = 2 * Nat.totient d := by
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card_units_eq_totient]
  omega

/-- The fiber of a color in a finite coloring. -/
def colorFiber {n r : ℕ} (c : BelowTarget n → Fin r) (i : Fin r) :
    Finset (BelowTarget n) :=
  Finset.univ.filter fun x ↦ c x = i

lemma colorFiber_mem {n r : ℕ} (c : BelowTarget n → Fin r) (i : Fin r)
    (x : BelowTarget n) : x ∈ colorFiber c i ↔ c x = i := by
  simp [colorFiber]

lemma AvoidsTarget.targetAvoiding_colorFiber {n r : ℕ}
    {c : BelowTarget n → Fin r} (hc : AvoidsTarget n r c) (i : Fin r) :
    TargetAvoiding n (colorFiber c i) := by
  intro A hA
  apply hc A
  intro x hx y hy
  have hxi : c x = i := (colorFiber_mem c i x).mp (hA hx)
  have hyi : c y = i := (colorFiber_mem c i y).mp (hA hy)
  exact hxi.trans hyi.symm

lemma avoidsTarget_of_targetAvoiding_colorFiber {n r : ℕ} (hn : 0 < n)
    {c : BelowTarget n → Fin r}
    (hc : ∀ i, TargetAvoiding n (colorFiber c i)) : AvoidsTarget n r c := by
  intro A hmono
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst A
    simpa using hn.ne
  · obtain ⟨x, hx⟩ := hA
    apply hc (c x) A
    intro y hy
    apply (colorFiber_mem c (c x) y).mpr
    exact hmono hy hx

lemma avoidsTarget_iff_fibers {n r : ℕ} (hn : 0 < n)
    (c : BelowTarget n → Fin r) :
    AvoidsTarget n r c ↔ ∀ i, TargetAvoiding n (colorFiber c i) := by
  constructor
  · intro hc i
    exact hc.targetAvoiding_colorFiber i
  · exact avoidsTarget_of_targetAvoiding_colorFiber hn

/-- A finite family of target-avoiding sets which covers the whole domain. -/
def IsAvoidingCover {n r : ℕ} (S : Fin r → Finset (BelowTarget n)) : Prop :=
  (∀ x, ∃ i, x ∈ S i) ∧ ∀ i, TargetAvoiding n (S i)

/-- Assign an element to one member of a covering family. -/
noncomputable def colorOfCover {n r : ℕ} {S : Fin r → Finset (BelowTarget n)}
    (hS : IsAvoidingCover S) (x : BelowTarget n) : Fin r := by
  classical
  exact Classical.choose (hS.1 x)

lemma colorOfCover_mem {n r : ℕ} {S : Fin r → Finset (BelowTarget n)}
    (hS : IsAvoidingCover S) (x : BelowTarget n) : x ∈ S (colorOfCover hS x) := by
  classical
  exact Classical.choose_spec (hS.1 x)

/-- An avoiding cover can be made into a coloring by resolving overlaps. -/
lemma colorable_of_avoidingCover {n r : ℕ} (hn : 0 < n)
    {S : Fin r → Finset (BelowTarget n)} (hS : IsAvoidingCover S) :
    Colorable n r := by
  classical
  refine ⟨colorOfCover hS, ?_⟩
  apply avoidsTarget_of_targetAvoiding_colorFiber hn
  intro i A hA
  apply hS.2 i A
  intro x hx
  have hcolor : colorOfCover hS x = i := (colorFiber_mem _ i x).mp (hA hx)
  simpa [hcolor] using colorOfCover_mem hS x

lemma colorable_iff_exists_avoidingCover {n r : ℕ} (hn : 0 < n) :
    Colorable n r ↔ ∃ S : Fin r → Finset (BelowTarget n), IsAvoidingCover S := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨colorFiber c, ?_, ?_⟩
    · intro x
      exact ⟨c x, (colorFiber_mem c (c x) x).mpr rfl⟩
    · exact hc.targetAvoiding_colorFiber
  · rintro ⟨S, hS⟩
    exact colorable_of_avoidingCover hn hS

/-- The same cover notion with an arbitrary finite index type.  This lets the four
families in the upper-bound construction keep their natural index types. -/
def IsAvoidingCoverOn {n : ℕ} {ι : Type*}
    (S : ι → Finset (BelowTarget n)) : Prop :=
  (∀ x, ∃ i, x ∈ S i) ∧ ∀ i, TargetAvoiding n (S i)

/-- Reindex an arbitrary finite avoiding cover by `Fin (Fintype.card ι)`. -/
lemma colorable_of_fintype_avoidingCover {n : ℕ} {ι : Type*} [Fintype ι]
    (hn : 0 < n) {S : ι → Finset (BelowTarget n)} (hS : IsAvoidingCoverOn S) :
    Colorable n (Fintype.card ι) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  apply colorable_of_avoidingCover hn (S := fun j ↦ S (e.symm j))
  constructor
  · intro x
    obtain ⟨i, hi⟩ := hS.1 x
    exact ⟨e i, by simpa⟩
  · intro j
    exact hS.2 (e.symm j)

/-- Put two naturally indexed families next to one another. -/
def sumCoverFamily {n : ℕ} {ι κ : Type*}
    (S : ι → Finset (BelowTarget n)) (T : κ → Finset (BelowTarget n)) :
    ι ⊕ κ → Finset (BelowTarget n)
  | Sum.inl i => S i
  | Sum.inr j => T j

lemma sumCoverFamily_avoiding {n : ℕ} {ι κ : Type*}
    {S : ι → Finset (BelowTarget n)} {T : κ → Finset (BelowTarget n)}
    (hS : ∀ i, TargetAvoiding n (S i))
    (hT : ∀ j, TargetAvoiding n (T j)) :
    ∀ z, TargetAvoiding n (sumCoverFamily S T z) := by
  rintro (i | j)
  · exact hS i
  · exact hT j

lemma sumCoverFamily_covers {n : ℕ} {ι κ : Type*}
    {S : ι → Finset (BelowTarget n)} {T : κ → Finset (BelowTarget n)}
    (hcover : ∀ x, (∃ i, x ∈ S i) ∨ ∃ j, x ∈ T j) :
    ∀ x, ∃ z, x ∈ sumCoverFamily S T z := by
  intro x
  rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact ⟨Sum.inl i, hi⟩
  · exact ⟨Sum.inr j, hj⟩

/-- A set of at most `d` integers, each strictly below `n / d` in the
cross-multiplied sense, has total sum below `n`.  This is the elementary
reason the short leftover groups in Step 4 are valid color classes. -/
lemma targetAvoiding_of_card_le_of_mul_lt {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {S : Finset (BelowTarget n)} (hcard : S.card ≤ d)
    (hsmall : ∀ x ∈ S, d * x.1 < n) : TargetAvoiding n S := by
  intro A hAS hsum
  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst A
    simp_all
  have hstrict :
      A.sum (fun x ↦ d * x.1) < A.sum (fun _ ↦ n) := by
    apply Finset.sum_lt_sum
    · intro x hx
      exact (hsmall x (hAS hx)).le
    · obtain ⟨x, hx⟩ := hAne
      exact ⟨x, hx, hsmall x (hAS hx)⟩
  have hmul : d * A.sum (fun x ↦ x.1) < A.card * n := by
    simpa [Finset.mul_sum] using hstrict
  have hcardA : A.card ≤ d := (Finset.card_le_card hAS).trans hcard
  have : d * n < d * n := by
    calc
      d * n = d * A.sum (fun x ↦ x.1) := by rw [hsum]
      _ < A.card * n := hmul
      _ ≤ d * n := Nat.mul_le_mul_right n hcardA
  exact (Nat.lt_irrefl _ this)

/-- The position of an element in a fixed (noncanonical) enumeration of a
finset.  Only its injectivity on the finset is used. -/
noncomputable def rankIn {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℕ :=
  if hx : x ∈ S then (S.equivFin ⟨x, hx⟩).1 else 0

lemma rankIn_lt_card {α : Type*} [DecidableEq α] {S : Finset α} {x : α}
    (hx : x ∈ S) : rankIn S x < S.card := by
  simpa [rankIn, hx] using (S.equivFin ⟨x, hx⟩).2

lemma rankIn_injOn {α : Type*} [DecidableEq α] (S : Finset α) :
    Set.InjOn (rankIn S) S := by
  intro x hx y hy hxy
  change x ∈ S at hx
  change y ∈ S at hy
  have heq : S.equivFin ⟨x, hx⟩ = S.equivFin ⟨y, hy⟩ := by
    apply Fin.ext
    calc
      (S.equivFin ⟨x, hx⟩).1 = rankIn S x := by simp [rankIn, hx]
      _ = rankIn S y := hxy
      _ = (S.equivFin ⟨y, hy⟩).1 := by simp [rankIn, hy]
  exact congrArg Subtype.val (S.equivFin.injective heq)

/-- Divide a finite set into consecutive blocks of size at most `d`, using
an arbitrary enumeration of the set.  The harmless final empty block makes
the index cardinality `S.card / d + 1` uniform. -/
noncomputable def chunkFamily {α : Type*} [DecidableEq α]
    (S : Finset α) (d : ℕ) (i : Fin (S.card / d + 1)) : Finset α :=
  S.filter fun x ↦ rankIn S x / d = i.1

lemma mem_chunkFamily {α : Type*} [DecidableEq α] {S : Finset α} {d : ℕ}
    {i : Fin (S.card / d + 1)} {x : α} :
    x ∈ chunkFamily S d i ↔ x ∈ S ∧ rankIn S x / d = i.1 := by
  simp [chunkFamily]

lemma chunkFamily_covers {α : Type*} [DecidableEq α] (S : Finset α) {d : ℕ}
    (hd : 0 < d) {x : α} (hx : x ∈ S) :
    ∃ i : Fin (S.card / d + 1), x ∈ chunkFamily S d i := by
  have hq : rankIn S x / d ≤ S.card / d :=
    Nat.div_le_div_right (rankIn_lt_card hx).le
  let i : Fin (S.card / d + 1) := ⟨rankIn S x / d, by omega⟩
  exact ⟨i, mem_chunkFamily.mpr ⟨hx, rfl⟩⟩

lemma chunkFamily_card_le {α : Type*} [DecidableEq α] (S : Finset α) {d : ℕ}
    (hd : 0 < d) (i : Fin (S.card / d + 1)) :
    (chunkFamily S d i).card ≤ d := by
  let g : α → ℕ := fun x ↦ rankIn S x % d
  have hmap : Set.MapsTo g (chunkFamily S d i) (Finset.range d) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  have hinj : Set.InjOn g (chunkFamily S d i) := by
    intro x hx y hy hmod
    change rankIn S x % d = rankIn S y % d at hmod
    have hxmem := (mem_chunkFamily.mp hx).1
    have hymem := (mem_chunkFamily.mp hy).1
    have hdiv : rankIn S x / d = rankIn S y / d := by
      rw [(mem_chunkFamily.mp hx).2, (mem_chunkFamily.mp hy).2]
    apply rankIn_injOn S hxmem hymem
    calc
      rankIn S x = d * (rankIn S x / d) + rankIn S x % d :=
        (Nat.div_add_mod _ _).symm
      _ = d * (rankIn S y / d) + rankIn S y % d := by rw [hdiv, hmod]
      _ = rankIn S y := Nat.div_add_mod _ _
  simpa using Finset.card_le_card_of_injOn g hmap hinj

/-- A prime-factor class added for every prime divisor of the auxiliary
modulus.  This harmless extra family removes the paper's bookkeeping
requirement that all prime factors of `d` occur among the first `h` primes. -/
def factorPrimeFamily (n d : ℕ) (p : d.primeFactors) :
    Finset (BelowTarget n) :=
  Finset.univ.filter fun x ↦ (p : ℕ) ∣ x.1

lemma factorPrimeFamily_avoiding {n d : ℕ} (hn : Nat.Coprime n d)
    (p : d.primeFactors) : TargetAvoiding n (factorPrimeFamily n d p) := by
  apply targetAvoiding_of_common_dvd
  · intro hpn
    have hpd : (p : ℕ) ∣ d := (Nat.mem_primeFactors.mp p.2).2.1
    exact (Nat.not_coprime_of_dvd_of_dvd
      (Nat.prime_of_mem_primeFactors p.2).one_lt hpn hpd) hn
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- Natural index type for the first three families of the upper-bound cover:
size bands, prime multiples, auxiliary-modulus prime factors, and the two
classes for each reduced residue. -/
abbrev UpperMainIndex (h d : ℕ) :=
  Fin h ⊕ (Fin h ⊕ (d.primeFactors ⊕ ((ZMod d)ˣ × Fin 2)))

/-- The first three pieces of the Conlon--Fox--Pham upper-bound cover. -/
noncomputable def upperMainFamily (n h d : ℕ) (hn : Nat.Coprime n d) :
    UpperMainIndex h d → Finset (BelowTarget n)
  | Sum.inl i => firstBandFamily n h i
  | Sum.inr (Sum.inl i) => primeMultipleFamily n h i
  | Sum.inr (Sum.inr (Sum.inl p)) => factorPrimeFamily n d p
  | Sum.inr (Sum.inr (Sum.inr i)) => residueClassFamily n hn i

lemma upperMainFamily_avoiding {n h d : ℕ} (hnpos : 0 < n) (hd : 1 < d)
    (hn : Nat.Coprime n d) :
    ∀ i, TargetAvoiding n (upperMainFamily n h d hn i) := by
  rintro (i | i | p | i)
  · exact firstBandFamily_avoiding hnpos i
  · exact primeMultipleFamily_avoiding hnpos i
  · exact factorPrimeFamily_avoiding hn p
  · exact residueClassFamily_avoiding hd hn i

/-- The elements not captured by the first three cover families. -/
noncomputable def upperRemainder (n h d : ℕ) (hn : Nat.Coprime n d) :
    Finset (BelowTarget n) := by
  classical
  exact Finset.univ.filter fun x ↦
    ¬∃ i : UpperMainIndex h d, x ∈ upperMainFamily n h d hn i

lemma mem_upperRemainder {n h d : ℕ} {hn : Nat.Coprime n d} {x : BelowTarget n} :
    x ∈ upperRemainder n h d hn ↔
      ¬∃ i : UpperMainIndex h d, x ∈ upperMainFamily n h d hn i := by
  simp [upperRemainder]

/-- If every prime factor of `d` occurs among the first `h` primes, then an
uncovered element must be coprime to `d`: otherwise its common prime factor
would put it in a prime-multiple class. -/
lemma upperRemainder_coprime {n h d : ℕ} (hd : d ≠ 0) (hn : Nat.Coprime n d)
    {x : BelowTarget n}
    (hx : x ∈ upperRemainder n h d hn) : Nat.Coprime x.1 d := by
  by_contra hcop
  obtain ⟨p, hp, hpx, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpf : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩
  apply (mem_upperRemainder.mp hx)
  refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨p, hpf⟩)), ?_⟩
  change x ∈ factorPrimeFamily n d ⟨p, hpf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpx⟩

/-- Every genuine leftover is shorter than `n / d`. -/
lemma upperRemainder_mul_lt {n h d : ℕ} (hd : 1 < d) (hn : Nat.Coprime n d)
    {x : BelowTarget n} (hx : x ∈ upperRemainder n h d hn) : d * x.1 < n := by
  have hcop : Nat.Coprime x.1 d := upperRemainder_coprime (by omega) hn hx
  by_contra hshort
  have hlower : n ≤ d * x.1 := Nat.le_of_not_gt hshort
  obtain ⟨i, hi⟩ := residueClassFamily_covers hd hn x hcop hlower
  apply (mem_upperRemainder.mp hx)
  exact ⟨Sum.inr (Sum.inr (Sum.inr i)), hi⟩

/-- The size-band stage confines every leftover to the initial interval
`[1,n/h]`. -/
lemma upperRemainder_band_bound {n h d : ℕ} (hn : Nat.Coprime n d)
    {x : BelowTarget n} (hx : x ∈ upperRemainder n h d hn) :
    h * x.1 ≤ n := by
  by_contra hbound
  obtain ⟨i, hi⟩ := firstBandFamily_covers_of_lt_mul x (Nat.lt_of_not_ge hbound)
  apply (mem_upperRemainder.mp hx)
  exact ⟨Sum.inl i, hi⟩

/-- The prime-multiple stage says that a leftover can only be divisible by
one of the first `h` primes when that prime already divides the target. -/
lemma upperRemainder_prime_condition {n h d : ℕ} (hn : Nat.Coprime n d)
    {x : BelowTarget n} (hx : x ∈ upperRemainder n h d hn) (i : Fin h) :
    primeAt i.1 ∣ x.1 → primeAt i.1 ∣ n := by
  intro hpx
  by_contra hpn
  apply (mem_upperRemainder.mp hx)
  refine ⟨Sum.inr (Sum.inl i), ?_⟩
  exact mem_primeMultipleFamily.mpr ⟨hpn, hpx⟩

/-- The ordinary integer sieve set which contains the values of every
upper-bound remainder. -/
noncomputable def initialPrimeSurvivors (n h : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / h)).filter fun x ↦
    ∀ i : Fin h, primeAt i.1 ∣ x → primeAt i.1 ∣ n

lemma mem_initialPrimeSurvivors {n h x : ℕ} :
    x ∈ initialPrimeSurvivors n h ↔
      1 ≤ x ∧ x ≤ n / h ∧
        ∀ i : Fin h, primeAt i.1 ∣ x → primeAt i.1 ∣ n := by
  simp [initialPrimeSurvivors, and_assoc]

lemma values_upperRemainder_subset_initialPrimeSurvivors
    {n h d : ℕ} (hh : 0 < h) (hn : Nat.Coprime n d) :
    values (upperRemainder n h d hn) ⊆ initialPrimeSurvivors n h := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := mem_values.mp hx
  apply mem_initialPrimeSurvivors.mpr
  refine ⟨(Finset.mem_Ico.mp t.2).1, ?_, upperRemainder_prime_condition hn ht⟩
  exact (Nat.le_div_iff_mul_le hh).mpr (by
    simpa [Nat.mul_comm] using upperRemainder_band_bound hn ht)

lemma upperRemainder_card_le_initialPrimeSurvivors
    {n h d : ℕ} (hh : 0 < h) (hn : Nat.Coprime n d) :
    (upperRemainder n h d hn).card ≤ (initialPrimeSurvivors n h).card := by
  calc
    (upperRemainder n h d hn).card =
        (values (upperRemainder n h d hn)).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ (initialPrimeSurvivors n h).card :=
      Finset.card_le_card (values_upperRemainder_subset_initialPrimeSurvivors hh hn)

/-! ### The finite missing-prime sieve -/

/-- Odd primes among the first `h` primes which do not divide the target.
The prime `2` is omitted only to match the beta-sieve library's interval
`(2,y]`; this loses at most a constant factor. -/
noncomputable def oddFirstMissingPrimes (n h : ℕ) : Finset ℕ :=
  ((Finset.range h).image primeAt).filter fun p ↦ 2 < p ∧ ¬p ∣ n

lemma mem_oddFirstMissingPrimes {n h p : ℕ} :
    p ∈ oddFirstMissingPrimes n h ↔
      (∃ i < h, primeAt i = p) ∧ 2 < p ∧ ¬p ∣ n := by
  simp [oddFirstMissingPrimes, and_assoc]

lemma oddFirstMissingPrimes_prime {n h p : ℕ}
    (hp : p ∈ oddFirstMissingPrimes n h) : p.Prime := by
  obtain ⟨⟨i, _hi, rfl⟩, _⟩ := mem_oddFirstMissingPrimes.mp hp
  exact Nat.prime_nth_prime i

lemma oddFirstMissingPrimes_subset_sievePrimes (n h : ℕ) :
    oddFirstMissingPrimes n h ⊆ Erdos851.sievePrimes 2 (primeAt h) := by
  intro p hp
  obtain ⟨⟨i, hi, hip⟩, hp2, _hpn⟩ := mem_oddFirstMissingPrimes.mp hp
  apply Erdos851.mem_sievePrimes.mpr
  refine ⟨hp2, ?_, hip ▸ Nat.prime_nth_prime i⟩
  rw [← hip]
  exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hi |>.le

lemma oddFirstMissingPrimes_prod_squarefree (n h : ℕ) :
    Squarefree (∏ p ∈ oddFirstMissingPrimes n h, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (oddFirstMissingPrimes_prime hp)
      (oddFirstMissingPrimes_prime hq)).mpr hpq
  · intro p hp
    exact (oddFirstMissingPrimes_prime hp).squarefree

lemma oddFirstMissingPrimes_prod_dvd_sievePrimeProduct (n h : ℕ) :
    (∏ p ∈ oddFirstMissingPrimes n h, p) ∣
      Erdos387.sievePrimeProduct 2 (primeAt h) := by
  rw [Erdos387.sievePrimeProduct]
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  obtain ⟨⟨i, hi, hip⟩, hp2, _hpn⟩ := mem_oddFirstMissingPrimes.mp hp
  apply Erdos387.mem_sievePrimes.mpr
  refine ⟨hip ▸ Nat.prime_nth_prime i, hp2, ?_⟩
  rw [← hip]
  exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr hi

/-- The corresponding sifted interval. -/
noncomputable def missingPrimeSiftedInterval (n h X : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter fun x ↦
    Nat.Coprime x (∏ p ∈ oddFirstMissingPrimes n h, p)

lemma initialPrimeSurvivors_subset_missingPrimeSiftedInterval (n h : ℕ) :
    initialPrimeSurvivors n h ⊆ missingPrimeSiftedInterval n h (n / h) := by
  intro x hx
  obtain ⟨hx1, hxX, hprime⟩ := mem_initialPrimeSurvivors.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨by omega, hxX⟩, ?_⟩
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.symm
  apply (oddFirstMissingPrimes_prime hp).coprime_iff_not_dvd.mpr
  intro hpx
  obtain ⟨⟨i, hi, hip⟩, _hp2, hpn⟩ := mem_oddFirstMissingPrimes.mp hp
  let j : Fin h := ⟨i, hi⟩
  have hpdivn : primeAt i ∣ n := hprime j (by simpa [j, hip] using hpx)
  exact hpn (by simpa [hip] using hpdivn)

lemma upperRemainder_card_le_missingPrimeSiftedInterval
    {n h d : ℕ} (hh : 0 < h) (hn : Nat.Coprime n d) :
    (upperRemainder n h d hn).card ≤
      (missingPrimeSiftedInterval n h (n / h)).card := by
  exact (upperRemainder_card_le_initialPrimeSurvivors hh hn).trans
    (Finset.card_le_card (initialPrimeSurvivors_subset_missingPrimeSiftedInterval n h))

/-! ### An axiom-free filtered beta sieve for the leftover set

Only primes not dividing the target may be used to sift the remainder.  The
following finite set is the subcollection of the ordinary interval of sieve
primes with precisely those target primes removed. -/

/-- Odd primes at most `y` which do not divide the target. -/
def missingPrimesUpTo (n y : ℕ) : Finset ℕ :=
  (Erdos851.sievePrimes 2 y).filter fun p ↦ ¬p ∣ n

lemma mem_missingPrimesUpTo {n y p : ℕ} :
    p ∈ missingPrimesUpTo n y ↔ 2 < p ∧ p ≤ y ∧ p.Prime ∧ ¬p ∣ n := by
  simp [missingPrimesUpTo, Erdos851.mem_sievePrimes, and_assoc]

lemma missingPrimesUpTo_subset_oddFirstMissingPrimes
    {n h y : ℕ} (hyh : y < primeAt h) :
    missingPrimesUpTo n y ⊆ oddFirstMissingPrimes n h := by
  intro p hp
  obtain ⟨hp2, hpy, hpprime, hpnot⟩ := mem_missingPrimesUpTo.mp hp
  let i := Nat.count Nat.Prime p
  have hip : primeAt i = p := Nat.nth_count hpprime
  have hih : i < h := by
    by_contra hi
    have hle : h ≤ i := Nat.le_of_not_gt hi
    have hmono : primeAt h ≤ primeAt i :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hle
    rw [hip] at hmono
    omega
  apply mem_oddFirstMissingPrimes.mpr
  exact ⟨⟨i, hih, hip⟩, hp2, hpnot⟩

/-- Product of the sieving primes not dividing `n`. -/
def missingPrimeProduct (n y : ℕ) : ℕ :=
  ∏ p ∈ missingPrimesUpTo n y, p

lemma missingPrimeProduct_squarefree (n y : ℕ) :
    Squarefree (missingPrimeProduct n y) := by
  unfold missingPrimeProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (mem_missingPrimesUpTo.mp hp).2.2.1
      (mem_missingPrimesUpTo.mp hq).2.2.1).mpr hpq
  · intro p hp
    exact (mem_missingPrimesUpTo.mp hp).2.2.1.squarefree

lemma missingPrimeProduct_pos (n y : ℕ) : 0 < missingPrimeProduct n y := by
  unfold missingPrimeProduct
  exact Finset.prod_pos fun p hp ↦ (mem_missingPrimesUpTo.mp hp).2.2.1.pos

lemma primeFactors_missingPrimeProduct (n y : ℕ) :
    (missingPrimeProduct n y).primeFactors = missingPrimesUpTo n y := by
  unfold missingPrimeProduct
  exact Nat.primeFactors_prod fun p hp ↦
    (mem_missingPrimesUpTo.mp hp).2.2.1

lemma missingPrimeProduct_coprime_target (n y : ℕ) :
    Nat.Coprime (missingPrimeProduct n y) n := by
  unfold missingPrimeProduct
  apply Nat.Coprime.prod_left
  intro p hp
  exact ((mem_missingPrimesUpTo.mp hp).2.2.1.coprime_iff_not_dvd).mpr
    (mem_missingPrimesUpTo.mp hp).2.2.2

lemma missingPrimeProduct_dvd_primorial (n y : ℕ) :
    missingPrimeProduct n y ∣ primorial y := by
  rw [missingPrimeProduct, primorial_eq_prod_primesLE]
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by
        have := (mem_missingPrimesUpTo.mp hp).2.1
        omega),
      (mem_missingPrimesUpTo.mp hp).2.2.1⟩

lemma missingPrimeProduct_le_four_pow (n y : ℕ) :
    missingPrimeProduct n y ≤ 4 ^ y := by
  exact (Nat.le_of_dvd (primorial_pos y)
    (missingPrimeProduct_dvd_primorial n y)).trans (primorial_le_four_pow y)

/-- Logarithmic cutoff for the small-prime part of the tuned modulus. -/
def modulusPrimeCutoff (n : ℕ) : ℕ := Nat.log 2 n / 100

lemma modulusPrimeCutoff_cast_lower {n : ℕ}
    (hlogb : (400 : ℝ) ≤ Real.logb 2 (n : ℝ)) :
    Real.log (n : ℝ) / (400 * Real.log 2) ≤
      (modulusPrimeCutoff n : ℝ) := by
  let k := Nat.log 2 n
  have hfloor : Real.logb 2 (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))
    have heq : ⌊Real.logb (2 : ℝ) (n : ℝ)⌋₊ = Nat.log 2 n :=
      Real.natFloor_logb_natCast 2 n
    rw [heq] at h
    simpa [k] using h
  have hk200 : 200 ≤ k := by
    by_contra! h
    have hk : k ≤ 199 := by omega
    have hkR : (k : ℝ) ≤ 199 := by exact_mod_cast hk
    linarith
  have hkLower : Real.logb 2 (n : ℝ) / 2 ≤ (k : ℝ) := by
    linarith
  have hzNat : k ≤ 200 * (k / 100) := by
    have hmod : k % 100 < 100 := Nat.mod_lt _ (by omega)
    have hdecomp : k % 100 + 100 * (k / 100) = k :=
      Nat.mod_add_div k 100
    have hq : 2 ≤ k / 100 :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega
  have hzReal : (k : ℝ) / 200 ≤ (modulusPrimeCutoff n : ℝ) := by
    dsimp [modulusPrimeCutoff]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 200)).mpr (by
      have hzCast : (k : ℝ) ≤ 200 * (k / 100 : ℕ) := by
        exact_mod_cast hzNat
      simpa [mul_comm] using hzCast)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [Real.logb] at hlogb hkLower ⊢
  calc
    Real.log (n : ℝ) / (400 * Real.log 2) =
        (Real.log (n : ℝ) / Real.log 2) / 400 := by ring
    _ ≤ (k : ℝ) / 200 := by linarith
    _ ≤ (modulusPrimeCutoff n : ℝ) := hzReal

lemma eventually_log_modulusPrimeCutoff_lower :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        Real.log (modulusPrimeCutoff n : ℝ) := by
  let c := Real.log (400 * Real.log 2)
  have hlogbTop :
      Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (Real.log_pos one_lt_two)
  have hllTop :
      Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlogbTop.eventually (eventually_ge_atTop (400 : ℝ)),
    hllTop.eventually (eventually_ge_atTop (2 * c))] with n hlogb hll
  have hlogNpos : 0 < Real.log (n : ℝ) := by
    have hmul := (le_div_iff₀ (Real.log_pos one_lt_two)).mp (by
      simpa only [Real.logb] using hlogb)
    nlinarith [Real.log_pos one_lt_two]
  have hdenpos : 0 < 400 * Real.log 2 :=
    mul_pos (by norm_num) (Real.log_pos one_lt_two)
  have hzl := modulusPrimeCutoff_cast_lower hlogb
  have hzpos : 0 < (modulusPrimeCutoff n : ℝ) :=
    lt_of_lt_of_le (div_pos hlogNpos hdenpos) hzl
  have hlogzl := Real.log_le_log (div_pos hlogNpos hdenpos) hzl
  rw [Real.log_div hlogNpos.ne' hdenpos.ne'] at hlogzl
  change 2 * c ≤ Real.log (Real.log (n : ℝ)) at hll
  change Real.log (Real.log (n : ℝ)) - c ≤
    Real.log (modulusPrimeCutoff n : ℝ) at hlogzl
  nlinarith

lemma missingPrimeProduct_modulusCutoff_pow_fifty_le {n : ℕ} (hn : n ≠ 0) :
    (missingPrimeProduct n (modulusPrimeCutoff n)) ^ 50 ≤ n := by
  let z := modulusPrimeCutoff n
  calc
    (missingPrimeProduct n z) ^ 50 ≤ (4 ^ z) ^ 50 :=
      Nat.pow_le_pow_left (missingPrimeProduct_le_four_pow n z) 50
    _ = 2 ^ (100 * z) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ 2 ^ Nat.log 2 n := by
      apply Nat.pow_le_pow_right
      · norm_num
      · simpa [z, modulusPrimeCutoff, Nat.mul_comm] using
          Nat.mul_div_le (Nat.log 2 n) 100
    _ ≤ n := Nat.pow_log_le_self 2 hn

lemma missingPrimeProduct_modulusCutoff_cast_le_rpow {n : ℕ} (hn : n ≠ 0) :
    (missingPrimeProduct n (modulusPrimeCutoff n) : ℝ) ≤
      Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
  let M := missingPrimeProduct n (modulusPrimeCutoff n)
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast missingPrimeProduct_pos n _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpowNat := missingPrimeProduct_modulusCutoff_pow_fifty_le hn
  have hpow : (M : ℝ) ^ 50 ≤ (n : ℝ) := by exact_mod_cast hpowNat
  have hroot := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 50) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 50)
  calc
    (M : ℝ) = Real.rpow (M : ℝ) (1 : ℝ) := by simp
    _ = Real.rpow (M : ℝ) ((50 : ℝ) * (1 / 50 : ℝ)) := by norm_num
    _ = Real.rpow (Real.rpow (M : ℝ) (50 : ℝ)) (1 / 50 : ℝ) :=
      Real.rpow_mul hMpos.le _ _
    _ = Real.rpow ((M : ℝ) ^ 50) (1 / 50 : ℝ) := by
      congr 1
      exact Real.rpow_natCast (M : ℝ) 50
    _ ≤ Real.rpow (n : ℝ) (1 / 50 : ℝ) := hroot

lemma missingPrimeProduct_dvd_oddFirstMissingPrimes_product
    {n h y : ℕ} (hyh : y < primeAt h) :
    missingPrimeProduct n y ∣ ∏ p ∈ oddFirstMissingPrimes n h, p := by
  unfold missingPrimeProduct
  apply Finset.prod_dvd_prod_of_subset _ _ id
  exact missingPrimesUpTo_subset_oddFirstMissingPrimes hyh

/-- The interval `(0,X]` sifted only by odd primes not dividing `n`. -/
def selectedSiftedInterval (n y X : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter fun x ↦ Nat.Coprime x (missingPrimeProduct n y)

lemma missingPrimeSiftedInterval_subset_selectedSiftedInterval
    {n h y X : ℕ} (hyh : y < primeAt h) :
    missingPrimeSiftedInterval n h X ⊆ selectedSiftedInterval n y X := by
  intro x hx
  obtain ⟨hxIoc, hxcop⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxIoc, ?_⟩
  exact hxcop.of_dvd_right
    (missingPrimeProduct_dvd_oddFirstMissingPrimes_product hyh)

lemma upperRemainder_card_le_selectedSiftedInterval
    {n h d y : ℕ} (hh : 0 < h) (hn : Nat.Coprime n d)
    (hyh : y < primeAt h) :
    (upperRemainder n h d hn).card ≤
      (selectedSiftedInterval n y (n / h)).card := by
  exact (upperRemainder_card_le_missingPrimeSiftedInterval hh hn).trans
    (Finset.card_le_card
      (missingPrimeSiftedInterval_subset_selectedSiftedInterval hyh))

/-- The residue-class stage gives the sharper interval length `n / d` for
the final remainder.  This is essential when the tuned modulus is larger
than the number of size bands. -/
lemma upperRemainder_card_le_selectedSiftedInterval_modulus
    {n h d y : ℕ} (hd : 1 < d) (hn : Nat.Coprime n d)
    (hyh : y < primeAt h) :
    (upperRemainder n h d hn).card ≤
      (selectedSiftedInterval n y (n / d)).card := by
  have hvalues : values (upperRemainder n h d hn) ⊆
      selectedSiftedInterval n y (n / d) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_values.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ico.mp t.2).1, ?_⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr
        (Nat.le_of_lt (by simpa [Nat.mul_comm] using
          upperRemainder_mul_lt hd hn ht))
    · apply Nat.Coprime.prod_right
      intro p hp
      apply Nat.Coprime.symm
      apply ((mem_missingPrimesUpTo.mp hp).2.2.1.coprime_iff_not_dvd).mpr
      intro hpt
      have hpfirst := missingPrimesUpTo_subset_oddFirstMissingPrimes hyh hp
      obtain ⟨⟨i, hi, hip⟩, _hp2, hpn⟩ :=
        mem_oddFirstMissingPrimes.mp hpfirst
      let j : Fin h := ⟨i, hi⟩
      have hpdivn : primeAt i ∣ n := upperRemainder_prime_condition hn ht j (by
        simpa [j, hip] using hpt)
      exact hpn (by simpa [hip] using hpdivn)
  calc
    (upperRemainder n h d hn).card =
        (values (upperRemainder n h d hn)).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ (selectedSiftedInterval n y (n / d)).card :=
      Finset.card_le_card hvalues

/-- The filtered prime set in increasing order. -/
def ascendingMissingPrimes (n y : ℕ) : List ℕ :=
  (missingPrimesUpTo n y).sort (· ≤ ·)

/-- The filtered prime set in decreasing order, as used by the recursive
Rosser sieve. -/
def descendingMissingPrimes (n y : ℕ) : List ℕ :=
  (ascendingMissingPrimes n y).reverse

lemma ascendingMissingPrimes_prod (n y : ℕ) :
    (ascendingMissingPrimes n y).prod = missingPrimeProduct n y := by
  classical
  unfold ascendingMissingPrimes missingPrimeProduct
  symm
  simpa using List.prod_toFinset id
    (Finset.sort_nodup (missingPrimesUpTo n y) (· ≤ ·))

lemma descendingMissingPrimes_prod (n y : ℕ) :
    (descendingMissingPrimes n y).prod = missingPrimeProduct n y := by
  rw [descendingMissingPrimes, List.prod_reverse, ascendingMissingPrimes_prod]

lemma ascendingMissingPrimes_pairwise (n y : ℕ) :
    (ascendingMissingPrimes n y).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort (missingPrimesUpTo n y) (· ≤ ·)

lemma ascendingMissingPrimes_nodup (n y : ℕ) :
    (ascendingMissingPrimes n y).Nodup :=
  Finset.sort_nodup (missingPrimesUpTo n y) (· ≤ ·)

lemma descendingMissingPrimes_nodup (n y : ℕ) :
    (descendingMissingPrimes n y).Nodup := by
  simp [descendingMissingPrimes, ascendingMissingPrimes_nodup]

@[simp] lemma mem_ascendingMissingPrimes {n y p : ℕ} :
    p ∈ ascendingMissingPrimes n y ↔ p ∈ missingPrimesUpTo n y := by
  simp [ascendingMissingPrimes]

@[simp] lemma mem_descendingMissingPrimes {n y p : ℕ} :
    p ∈ descendingMissingPrimes n y ↔ p ∈ missingPrimesUpTo n y := by
  simp [descendingMissingPrimes]

lemma ascendingMissingPrimes_prime {n y : ℕ} :
    ∀ p ∈ ascendingMissingPrimes n y, p.Prime := by
  intro p hp
  exact (mem_missingPrimesUpTo.mp (mem_ascendingMissingPrimes.mp hp)).2.2.1

lemma descendingMissingPrimes_prime {n y : ℕ} :
    ∀ p ∈ descendingMissingPrimes n y, p.Prime := by
  intro p hp
  exact (mem_missingPrimesUpTo.mp (mem_descendingMissingPrimes.mp hp)).2.2.1

lemma pairwise_lt_of_pairwise_le_nodup_360 :
    ∀ l : List ℕ, l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·) := by
  intro l hle hnodup
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pairwise_cons] at hle ⊢
      simp only [List.nodup_cons] at hnodup
      refine ⟨?_, ih hle.2 hnodup.2⟩
      intro b hb
      exact lt_of_le_of_ne (hle.1 b hb)
        (Ne.symm (fun hab ↦ hnodup.1 (hab ▸ hb)))

lemma descendingMissingPrimes_pairwise (n y : ℕ) :
    (descendingMissingPrimes n y).Pairwise (fun p q ↦ q < p) := by
  rw [descendingMissingPrimes, List.pairwise_reverse]
  exact pairwise_lt_of_pairwise_le_nodup_360 _
    (ascendingMissingPrimes_pairwise n y)
    (ascendingMissingPrimes_nodup n y)

lemma missingPrimeProduct_dvd_sievePrimeProduct (n y : ℕ) :
    missingPrimeProduct n y ∣ Erdos387.sievePrimeProduct 2 (y + 1) := by
  rw [Erdos387.sievePrimeProduct]
  unfold missingPrimeProduct
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  obtain ⟨hp2, hpy, hpprime, _⟩ := mem_missingPrimesUpTo.mp hp
  exact Erdos387.mem_sievePrimes.mpr ⟨hpprime, hp2, by omega⟩

/-- The ordinary one-shift interval sieve with the prime product replaced by
the subproduct of primes not dividing `n`.  Its support, weights, density and
remainder are unchanged. -/
noncomputable def missingPrimeBoundingSieve (n y X : ℕ) : BoundingSieve := by
  let base := Erdos851.ShiftSieve.oneShiftBoundingSieve X X 2 (y + 1) (by omega)
  exact
    { support := base.support
      prodPrimes := missingPrimeProduct n y
      prodPrimes_squarefree := missingPrimeProduct_squarefree n y
      weights := base.weights
      weights_nonneg := base.weights_nonneg
      totalMass := base.totalMass
      nu := base.nu
      nu_mult := base.nu_mult
      nu_pos_of_prime := by
        intro p hp hpdvd
        exact base.nu_pos_of_prime p hp
          (hpdvd.trans (missingPrimeProduct_dvd_sievePrimeProduct n y))
      nu_lt_one_of_prime := by
        intro p hp hpdvd
        exact base.nu_lt_one_of_prime p hp
          (hpdvd.trans (missingPrimeProduct_dvd_sievePrimeProduct n y)) }

lemma missingPrimeBoundingSieve_totalMass (n y X : ℕ) :
    (missingPrimeBoundingSieve n y X).totalMass = X := rfl

lemma missingPrimeBoundingSieve_nu (n y X p : ℕ) (hp : p.Prime) :
    (missingPrimeBoundingSieve n y X).nu p =
      Erdos851.oneShiftDensity p := by
  change Erdos851.ShiftSieve.shiftNu {X} p = Erdos851.oneShiftDensity p
  exact Erdos851.shiftNu_singleton_prime X hp

lemma missingPrimeBoundingSieve_abs_rem_le_one
    {n y X d : ℕ} (hd : d ∣ missingPrimeProduct n y) :
    |(missingPrimeBoundingSieve n y X).rem d| ≤ 1 := by
  change |(Erdos851.ShiftSieve.oneShiftBoundingSieve
    X X 2 (y + 1) (by omega)).rem d| ≤ 1
  exact Erdos851.ShiftSieve.oneShiftBoundingSieve_abs_rem_le_one le_rfl
    (hd.trans (missingPrimeProduct_dvd_sievePrimeProduct n y))

lemma card_dyadic_sub_eq_initial_selected (n y X : ℕ) :
    ((Finset.Ioc X (2 * X)).filter fun a ↦
      Nat.Coprime (missingPrimeProduct n y) (a - X)).card =
        (selectedSiftedInterval n y X).card := by
  classical
  apply Finset.card_bij (fun a _ ↦ a - X)
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Ioc] at ha
    rw [selectedSiftedInterval, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, Nat.Coprime.symm ha.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_Ioc] at ha hb
    omega
  · intro q hq
    rw [selectedSiftedInterval, Finset.mem_filter, Finset.mem_Ioc] at hq
    refine ⟨q + X, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩,
      by simpa [Nat.add_sub_cancel_right] using Nat.Coprime.symm hq.2⟩

lemma missingPrimeBoundingSieve_siftedSum (n y X : ℕ) :
    (missingPrimeBoundingSieve n y X).siftedSum =
      ((selectedSiftedInterval n y X).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let g := Erdos851.ShiftSieve.shiftedProduct ({X} : Finset ℕ)
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image g,
      if Nat.Coprime (missingPrimeProduct n y) q then
        ((I.filter fun a ↦ g a = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image g).filter fun q ↦
          Nat.Coprime (missingPrimeProduct n y) q,
          (I.filter fun a ↦ g a = q).card) =
        (I.filter fun a ↦ Nat.Coprime (missingPrimeProduct n y) (g a)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast
  simpa [I, g, Erdos851.ShiftSieve.shiftedProduct] using
    card_dyadic_sub_eq_initial_selected n y X

/-- The depth-dependent prefix of the filtered decreasing prime list. -/
noncomputable def missingBetaCutoffPrefix (n y r : ℕ) : List ℕ := by
  classical
  exact (descendingMissingPrimes n y).filter fun p ↦
    decide (1 < p ∧ betaEligible y r p)

lemma filter_isPrefix_of_pairwise_upward_360
    {α : Type*} {R : α → α → Prop}
    (keep : α → Bool)
    (hup : ∀ {a b}, R a b → keep b = true → keep a = true) :
    ∀ {l : List α}, l.Pairwise R → l.filter keep <+: l := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pairwise_cons] at hl
      cases ha : keep a
      · have hnone : l.filter keep = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro b hb
          simp only [List.mem_filter] at hb
          have hab := hup (hl.1 b hb.1) hb.2
          simp [ha] at hab
        simp [ha, hnone]
      · simp only [List.filter_cons, ha, ↓reduceIte]
        obtain ⟨rest, hrest⟩ := ih hl.2
        exact ⟨rest, by simp [hrest]⟩

lemma missingBetaCutoffPrefix_isPrefix (n y r : ℕ) (hy : 1 ≤ y) :
    missingBetaCutoffPrefix n y r <+: descendingMissingPrimes n y := by
  classical
  apply filter_isPrefix_of_pairwise_upward_360
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
    (fun {p q} hqp hq ↦ by
      simp only [decide_eq_true_eq] at hq ⊢
      exact ⟨hq.1.trans hqp, betaEligible_of_lt hy hq.1 hqp hq.2⟩)
    (descendingMissingPrimes_pairwise n y)

lemma getLast_le_of_pairwise_desc_360 :
    ∀ {l : List ℕ} (hn : l ≠ []),
      l.Pairwise (fun p q ↦ q < p) →
      ∀ p ∈ l, l.getLast hn ≤ p := by
  intro l hn hdesc
  induction l with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · have htail := (List.pairwise_cons.mp hdesc).1
                ((b :: l).getLast (by simp)) (List.getLast_mem (by simp))
            simpa using htail.le
          · have htaildesc := (List.pairwise_cons.mp hdesc).2
            simpa using ih (by simp) htaildesc p (by simpa using hp)

lemma chain_sublist_missingBetaCutoffPrefix_of_terminal
    {n y r : ℕ} {chain : List ℕ}
    (hy : 1 ≤ y) (hsub : chain.Sublist (descendingMissingPrimes n y))
    (hnonempty : chain ≠ [])
    (hterminal : Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      betaRatio ^ (r - 1)) :
    chain.Sublist (missingBetaCutoffPrefix n y r) := by
  classical
  have hdesc : chain.Pairwise (fun p q ↦ q < p) :=
    (descendingMissingPrimes_pairwise n y).sublist hsub
  let q := chain.getLast hnonempty
  have hlenpos : 0 < chain.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnonempty (List.length_eq_zero_iff.mp hz)
  have hqmem : q ∈ chain := List.getLast_mem hnonempty
  have hqLarge : 1 < q := by
    have hqP : q ∈ descendingMissingPrimes n y := hsub.subset hqmem
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp hqP)).2.2.1.one_lt
  have hget : chain.getD (chain.length - 1) 2 = q := by
    calc
      chain.getD (chain.length - 1) 2 = chain[chain.length - 1] := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : chain.length - 1 < chain.length)]
      _ = q := (List.getLast_eq_getElem hnonempty).symm
  have hqEligible : betaEligible y r q := by
    unfold betaEligible
    rw [hget] at hterminal
    exact hterminal
  have hchainEligible : ∀ p ∈ chain, 1 < p ∧ betaEligible y r p := by
    intro p hp
    have hpP : p ∈ descendingMissingPrimes n y := hsub.subset hp
    have hpLarge : 1 < p :=
      (mem_missingPrimesUpTo.mp
        (mem_descendingMissingPrimes.mp hpP)).2.2.1.one_lt
    refine ⟨hpLarge, ?_⟩
    have hqp := getLast_le_of_pairwise_desc_360 hnonempty hdesc p hp
    rcases hqp.eq_or_lt with hEq | hlt
    · exact hEq ▸ hqEligible
    · exact betaEligible_of_lt hy hqLarge hlt hqEligible
  have hfiltered : chain.filter
      (fun p ↦ decide (1 < p ∧ betaEligible y r p)) = chain :=
    List.filter_eq_self.mpr (fun p hp ↦ by simp [hchainEligible p hp])
  have hf := hsub.filter
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
  simpa only [hfiltered, missingBetaCutoffPrefix] using hf

lemma upperFailureTerm_chain_sublist_missingBetaCutoffPrefix
    {n y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingMissingPrimes n y))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (missingBetaCutoffPrefix n y r) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingMissingPrimes n y) ht
  have hlarge : ∀ p ∈ descendingMissingPrimes n y, 1 < p := by
    intro p hp
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp hp)).2.2.1.one_lt
  have hupper : ∀ p ∈ descendingMissingPrimes n y, p ≤ y := by
    intro p hp
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp hp)).2.1
  have hcut := upperFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge hupper
    (descendingMissingPrimes_pairwise n y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨k, hk⟩ := upperFailureTerms_chain_length_odd
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingMissingPrimes n y) ht
    intro hempty
    rw [hempty] at hk
    simp at hk
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_missingBetaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

lemma lowerFailureTerm_chain_sublist_missingBetaCutoffPrefix
    {n y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingMissingPrimes n y))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (missingBetaCutoffPrefix n y r) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingMissingPrimes n y) ht
  have hlarge : ∀ p ∈ descendingMissingPrimes n y, 1 < p := by
    intro p hp
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp hp)).2.2.1.one_lt
  have hupper : ∀ p ∈ descendingMissingPrimes n y, p ≤ y := by
    intro p hp
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp hp)).2.1
  have hcut := lowerFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge hupper
    (descendingMissingPrimes_pairwise n y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop 100 (y ^ S))
        fuel [] (descendingMissingPrimes n y)).2 t ht).2
    rw [hchain]
    simp
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_missingBetaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

lemma upperFailureTerm_missing_start_depth
    {n y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingMissingPrimes n y)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    upperFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := upperFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingMissingPrimes n y) ht
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

lemma lowerFailureTerm_missing_start_depth
    {n y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingMissingPrimes n y)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    lowerFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := lowerFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingMissingPrimes n y) ht
    exact (mem_missingPrimesUpTo.mp
      (mem_descendingMissingPrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

/-- Euler product over the sieving primes which do not divide the target. -/
noncomputable def missingEulerProduct (n y : ℕ) : ℝ :=
  ∏ p ∈ missingPrimesUpTo n y, (1 - Erdos851.oneShiftDensity p)

lemma missingEulerProduct_pos (n y : ℕ) : 0 < missingEulerProduct n y := by
  unfold missingEulerProduct
  apply Finset.prod_pos
  intro p hp
  exact Erdos851.oneShift_localFactor_pos
    (mem_missingPrimesUpTo.mp hp).2.2.1

lemma totient_div_self_eq_primeFactorsProduct (M : ℕ) (hM : 0 < M) :
    (M.totient : ℝ) / M =
      ∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / p) := by
  have hR :
      (M.totient : ℝ) =
        M * ∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / p) := by
    have hN := Nat.totient_mul_prod_primeFactors M
    have hN' :
        (M.totient : ℝ) * (∏ p ∈ M.primeFactors, (p : ℝ)) =
          M * ∏ p ∈ M.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hN
      norm_num only [Nat.cast_mul, Nat.cast_prod] at hcast
      exact hcast
    have hden : (∏ p ∈ M.primeFactors, (p : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
    have hprod :
        (∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / p)) =
          (∏ p ∈ M.primeFactors, ((p - 1 : ℕ) : ℝ)) /
            ∏ p ∈ M.primeFactors, (p : ℝ) := by
      calc
        (∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / p)) =
            ∏ p ∈ M.primeFactors, (((p - 1 : ℕ) : ℝ) / p) := by
              apply Finset.prod_congr rfl
              intro p hp
              rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
                (Nat.pos_of_mem_primeFactors hp).ne')]
              have hp0 : (p : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
              field_simp [hp0]
              norm_num
        _ = _ := by simpa using
          (Finset.prod_div_distrib
            (s := M.primeFactors)
            (fun p : ℕ ↦ ((p - 1 : ℕ) : ℝ))
            (fun p : ℕ ↦ (p : ℝ)))
    rw [hprod]
    field_simp [hden]
    exact hN'
  rw [hR]
  field_simp [hM.ne']

lemma totient_missingPrimeProduct_div_self (n y : ℕ) :
    ((missingPrimeProduct n y).totient : ℝ) / missingPrimeProduct n y =
      missingEulerProduct n y := by
  rw [totient_div_self_eq_primeFactorsProduct _ (missingPrimeProduct_pos n y),
    primeFactors_missingPrimeProduct]
  unfold missingEulerProduct Erdos851.oneShiftDensity
  congr 1
  funext p
  rw [one_div]

lemma buchstabProduct_descendingMissingPrimes (n y : ℕ) :
    buchstabProduct Erdos851.oneShiftDensity (descendingMissingPrimes n y) =
      missingEulerProduct n y := by
  classical
  unfold buchstabProduct missingEulerProduct descendingMissingPrimes
    ascendingMissingPrimes
  rw [List.map_reverse, List.prod_reverse]
  symm
  simpa using List.prod_toFinset
    (fun p ↦ 1 - Erdos851.oneShiftDensity p)
    (Finset.sort_nodup (missingPrimesUpTo n y) (· ≤ ·))

lemma buchstabProduct_oneShift_pos_of_prime
    {P : List ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    0 < buchstabProduct Erdos851.oneShiftDensity P := by
  unfold buchstabProduct
  apply List.prod_pos
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact sub_pos.mpr (Erdos851.oneShiftDensity_lt_one (hprime p hp))

lemma missingBetaCutoffPrefix_subset_full (n y r : ℕ) :
    (missingBetaCutoffPrefix n y r).toFinset ⊆
      (betaCutoffPrefix 2 y r).toFinset := by
  intro p hp
  rw [List.mem_toFinset] at hp ⊢
  simp only [missingBetaCutoffPrefix, List.mem_filter, decide_eq_true_eq] at hp
  simp only [betaCutoffPrefix, List.mem_filter, decide_eq_true_eq]
  refine ⟨?_, hp.2⟩
  apply mem_descendingSievePrimes.mpr
  exact (Finset.mem_filter.mp
    (mem_descendingMissingPrimes.mp hp.1)).1

lemma missingBetaCutoffPrefix_nodup (n y r : ℕ) :
    (missingBetaCutoffPrefix n y r).Nodup := by
  exact (descendingMissingPrimes_nodup n y).filter _

lemma missingBetaCutoffPrefix_prime {n y r : ℕ} :
    ∀ p ∈ missingBetaCutoffPrefix n y r, p.Prime := by
  intro p hp
  exact descendingMissingPrimes_prime p
    ((List.mem_filter.mp hp).1)

lemma oneShift_missingBetaCutoffPrefix_inverse_bound
    {C : ℝ} (hC : 1 ≤ C)
    (hdimension : ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    {n y r : ℕ} (hy : 2 ≤ y) :
    (buchstabProduct Erdos851.oneShiftDensity
      (missingBetaCutoffPrefix n y r))⁻¹ ≤
        (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
  classical
  let Q := missingBetaCutoffPrefix n y r
  let P := betaCutoffPrefix 2 y r
  have hQnodup : Q.Nodup := missingBetaCutoffPrefix_nodup n y r
  have hPprefix := betaCutoffPrefix_isPrefix 2 y r (by omega)
  have hPnodup : P.Nodup :=
    (Erdos851.BetaSieveFundamental.descendingSievePrimes_nodup 2 y).sublist
      hPprefix.sublist
  have hQsubP : Q.toFinset ⊆ P.toFinset :=
    missingBetaCutoffPrefix_subset_full n y r
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hPprefix.subset hp))).2.2
  have hQprime : ∀ p ∈ Q, p.Prime := by
    exact missingBetaCutoffPrefix_prime
  have hPpos : 0 < buchstabProduct Erdos851.oneShiftDensity P :=
    buchstabProduct_oneShift_pos_of_prime hPprime
  have hQpos : 0 < buchstabProduct Erdos851.oneShiftDensity Q :=
    buchstabProduct_oneShift_pos_of_prime hQprime
  have hprod : buchstabProduct Erdos851.oneShiftDensity P ≤
      buchstabProduct Erdos851.oneShiftDensity Q := by
    unfold buchstabProduct
    rw [← List.prod_toFinset
      (fun p ↦ 1 - Erdos851.oneShiftDensity p) hPnodup]
    rw [← List.prod_toFinset
      (fun p ↦ 1 - Erdos851.oneShiftDensity p) hQnodup]
    apply Finset.prod_le_prod_of_subset_of_le_one hQsubP
    · intro p hp
      have hpP : p ∈ P := List.mem_toFinset.mp hp
      exact (sub_pos.mpr
        (Erdos851.oneShiftDensity_lt_one (hPprime p hpP))).le
    · intro p hp _hpQ
      have hpP : p ∈ P := List.mem_toFinset.mp hp
      have hnonneg := Erdos851.oneShiftDensity_pos (hPprime p hpP)
      linarith
  calc
    (buchstabProduct Erdos851.oneShiftDensity Q)⁻¹ ≤
        (buchstabProduct Erdos851.oneShiftDensity P)⁻¹ :=
      (inv_le_inv₀ hQpos hPpos).2 hprod
    _ ≤ (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) :=
      oneShift_betaCutoffPrefix_inverse_bound hC hdimension
        (z := 2) (y := y) (r := r) (by omega) hy

/-- The dimension-one product-ratio estimate remains valid after deleting
the primes which divide the target. -/
theorem exists_missing_concrete_hasDepthProductRatio :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S fuel : ℕ, 2 ≤ y → 101 ≤ S →
        let P := descendingMissingPrimes n y
        let stop := descendingRosserStop 100 (y ^ S)
        HasDepthProductRatio Erdos851.oneShiftDensity
            (upperFailureTerms stop fuel [] P)
            (missingEulerProduct n y) A 1 (S - 100) fuel ∧
          HasDepthProductRatio Erdos851.oneShiftDensity
            (lowerFailureTerms stop fuel [] P)
            (missingEulerProduct n y) A 1 (S - 100) fuel := by
  obtain ⟨C, hC, hdimension⟩ := exists_oneShift_dimension_bound_one_le
  refine ⟨3 * C, by nlinarith, ?_⟩
  intro n y S fuel hy hS
  dsimp only
  let P := descendingMissingPrimes n y
  let stop := descendingRosserStop 100 (y ^ S)
  have hx0 : ∀ p, 0 ≤ Erdos851.oneShiftDensity p := by
    intro p
    unfold Erdos851.oneShiftDensity
    positivity
  have hx1 : ∀ p ∈ P, Erdos851.oneShiftDensity p < 1 := by
    intro p hp
    exact Erdos851.oneShiftDensity_lt_one
      (descendingMissingPrimes_prime p hp)
  have hV : missingEulerProduct n y =
      buchstabProduct Erdos851.oneShiftDensity P := by
    exact (buchstabProduct_descendingMissingPrimes n y).symm
  have hprefix : ∀ r ≤ fuel, missingBetaCutoffPrefix n y r <+: P := by
    intro r _hr
    exact missingBetaCutoffPrefix_isPrefix n y r (by omega)
  constructor
  · apply upper_hasDepthProductRatio_of_prefixProductRatio
      stop Erdos851.oneShiftDensity fuel [] (missingBetaCutoffPrefix n y)
      hx0 hx1 (descendingMissingPrimes_nodup n y) hV hprefix
    · intro r _hr t ht hlen
      exact upperFailureTerm_chain_sublist_missingBetaCutoffPrefix ht hS hlen
    · intro t ht
      exact upperFailureTerm_missing_start_depth (by omega) ht
    · nlinarith
    · intro r _hr _hstart
      exact oneShift_missingBetaCutoffPrefix_inverse_bound
        hC hdimension hy
  · apply lower_hasDepthProductRatio_of_prefixProductRatio
      stop Erdos851.oneShiftDensity fuel [] (missingBetaCutoffPrefix n y)
      hx0 hx1 (descendingMissingPrimes_nodup n y) hV hprefix
    · intro r _hr t ht hlen
      exact lowerFailureTerm_chain_sublist_missingBetaCutoffPrefix ht hS hlen
    · intro t ht
      exact lowerFailureTerm_missing_start_depth (by omega) ht
    · nlinarith
    · intro r _hr _hstart
      exact oneShift_missingBetaCutoffPrefix_inverse_bound
        hC hdimension hy

/-- Recursive Rosser main terms for the filtered list satisfy the same
fundamental-lemma estimate. -/
theorem exists_missing_concrete_mainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S fuel : ℕ, 2 ≤ y → 101 ≤ S →
        (descendingMissingPrimes n y).length ≤ fuel →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := descendingMissingPrimes n y
        let stop := descendingRosserStop 100 (y ^ S)
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            rosserLowerEval stop Erdos851.oneShiftDensity fuel [] P ∧
          rosserUpperEval stop Erdos851.oneShiftDensity fuel [] P ≤
            (1 + eta) * V := by
  obtain ⟨A, hA, hdepth⟩ := exists_missing_concrete_hasDepthProductRatio
  refine ⟨A, hA, ?_⟩
  intro n y S fuel hy hS hfuel hlog
  dsimp only
  let P := descendingMissingPrimes n y
  let stop := descendingRosserStop 100 (y ^ S)
  let V := missingEulerProduct n y
  have hratios := hdepth n y S fuel hy hS
  have hVpos : 0 < V := by
    rw [show V = buchstabProduct Erdos851.oneShiftDensity P by
      exact (buchstabProduct_descendingMissingPrimes n y).symm]
    exact buchstabProduct_oneShift_pos_of_prime
      (fun p hp ↦ descendingMissingPrimes_prime p hp)
  have hbounds := rosserBoundaries_le_geometric_of_depthProductRatio
    stop Erdos851.oneShiftDensity ([] : List ℕ) P hVpos.le
    hA (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
    hratios.1 hratios.2 (by
      intro r hrstart _hrfuel
      have hstartR : ((S - 100 : ℕ) : ℝ) ≤ r := by exact_mod_cast hrstart
      norm_num
      nlinarith)
  have heq := rosser_eval_sub_product_eq_boundary
    stop Erdos851.oneShiftDensity fuel [] P hfuel
  have hV : buchstabProduct Erdos851.oneShiftDensity P = V :=
    buchstabProduct_descendingMissingPrimes n y
  rw [hV] at heq
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V ≤
        rosserLowerEval stop Erdos851.oneShiftDensity fuel [] P ∧
      rosserUpperEval stop Erdos851.oneShiftDensity fuel [] P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V
  constructor
  · nlinarith [hbounds.2, heq.2]
  · nlinarith [hbounds.1, heq.1]

/-- Ascending-list form consumed by the finite combinatorial sieve. -/
theorem exists_missing_concrete_finiteMainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S : ℕ, 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := ascendingMissingPrimes n y
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            lowerMainTerm (rosserStoppingPredicate 100 (y ^ S))
              Erdos851.oneShiftDensity P ∧
          upperMainTerm (rosserStoppingPredicate 100 (y ^ S))
              Erdos851.oneShiftDensity P ≤ (1 + eta) * V := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_missing_concrete_mainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro n y S hy hS hlog
  dsimp only
  let P := ascendingMissingPrimes n y
  have hrecursive := hmain n y S P.length hy hS (by
    simp [P, descendingMissingPrimes]) hlog
  have hstop : descendingRosserStop 100 (y ^ S) =
      (fun s ↦ decide (rosserStoppingPredicate 100 (y ^ S) s.reverse)) := by
    funext s
    rw [Bool.eq_iff_iff]
    simp [descendingRosserStoppingPredicate]
  rw [Erdos851.FiniteRecursiveBridge.lowerMainTerm_eq_rosserLowerEval,
    Erdos851.FiniteRecursiveBridge.upperMainTerm_eq_rosserUpperEval]
  rw [← hstop]
  simpa [P, descendingMissingPrimes] using hrecursive

/-- End-to-end beta-sieve estimate for the interval left after deleting the
target's prime divisors from the sifting set. -/
theorem exists_selectedSiftedInterval_card_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n X y S : ℕ, 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((selectedSiftedInterval n y X).card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_missing_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro n X y S hy hS hlog
  dsimp only
  let P := ascendingMissingPrimes n y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := missingPrimeBoundingSieve n y X
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = missingPrimeProduct n y
    exact ascendingMissingPrimes_prod n y
  have hsort : P.Pairwise (· ≤ ·) := ascendingMissingPrimes_pairwise n y
  have hnodup : P.Nodup := ascendingMissingPrimes_nodup n y
  have hprime : ∀ p ∈ P, p.Prime := ascendingMissingPrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hd' : d ∣ missingPrimeProduct n y := hd
    exact (missingPrimeBoundingSieve_abs_rem_le_one hd').trans
      (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hd0 ↦ by
            subst d
            have hp0 : missingPrimeProduct n y = 0 := by simpa using hd'
            exact (missingPrimeProduct_squarefree n y).ne_zero hp0))
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        hadm)
    hrem
  change _ ≤ sieve.totalMass *
      upperMainTerm stop (fun p ↦ sieve.nu p) P + (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (X : ℝ) by
      exact missingPrimeBoundingSieve_totalMass n y X,
    show sieve.siftedSum = ((selectedSiftedInterval n y X).card : ℝ) by
      exact missingPrimeBoundingSieve_siftedSum n y X] at hupper
  have hnu : ∀ p ∈ P,
      sieve.nu p = Erdos851.oneShiftDensity p := by
    intro p hp
    exact missingPrimeBoundingSieve_nu n y X p (hprime p hp)
  rw [upperMainTerm_congr_on stop (fun p ↦ sieve.nu p)
    Erdos851.oneShiftDensity P hnu] at hupper
  have hm := hmain n y S hy hS hlog
  dsimp only at hm
  calc
    ((selectedSiftedInterval n y X).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop Erdos851.oneShiftDensity P +
          (D : ℝ) ^ 2 := hupper
    _ ≤ (X : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            missingEulerProduct n y) + (D : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg X)) le_rfl

/-- Matching lower beta-sieve estimate for the interval sifted by the odd
primes not dividing the target.  The square-level error is explicit, so this
statement can be applied on each divisor fiber in the lower-bound
construction. -/
theorem exists_selectedSiftedInterval_card_lower_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n X y S : ℕ, 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X : ℝ) * ((1 - eta) * V) - (D : ℝ) ^ 2 ≤
          ((selectedSiftedInterval n y X).card : ℝ) := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_missing_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro n X y S hy hS hlog
  dsimp only
  let P := ascendingMissingPrimes n y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := missingPrimeBoundingSieve n y X
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = missingPrimeProduct n y
    exact ascendingMissingPrimes_prod n y
  have hsort : P.Pairwise (· ≤ ·) := ascendingMissingPrimes_pairwise n y
  have hnodup : P.Nodup := ascendingMissingPrimes_nodup n y
  have hprime : ∀ p ∈ P, p.Prime := ascendingMissingPrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hlevel : ∀ p ∈ P, p ≤ D := by
    intro p hp
    have hpy : p ≤ y :=
      (mem_missingPrimesUpTo.mp
        (mem_ascendingMissingPrimes.mp hp)).2.1
    exact hpy.trans (le_self_pow (by omega : 1 ≤ y) (by omega))
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hd' : d ∣ missingPrimeProduct n y := hd
    exact (missingPrimeBoundingSieve_abs_rem_le_one hd').trans
      (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hd0 ↦ by
            subst d
            have hp0 : missingPrimeProduct n y = 0 := by simpa using hd'
            exact (missingPrimeProduct_squarefree n y).ne_zero hp0))
  have hlower := boundingSieve_lowerMain_sub_sq_le_siftedSum
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_lowerAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        (by
          intro p hp
          exact hlevel p ((List.mem_sublists.mp ht).subset hp)) hadm)
    hrem
  change sieve.totalMass *
      lowerMainTerm stop (fun p ↦ sieve.nu p) P - (D : ℝ) ^ 2 ≤
        sieve.siftedSum at hlower
  rw [show sieve.totalMass = (X : ℝ) by
      exact missingPrimeBoundingSieve_totalMass n y X,
    show sieve.siftedSum = ((selectedSiftedInterval n y X).card : ℝ) by
      exact missingPrimeBoundingSieve_siftedSum n y X] at hlower
  have hnu : ∀ p ∈ P,
      sieve.nu p = Erdos851.oneShiftDensity p := by
    intro p hp
    exact missingPrimeBoundingSieve_nu n y X p (hprime p hp)
  rw [lowerMainTerm_congr_on stop (fun p ↦ sieve.nu p)
    Erdos851.oneShiftDensity P hnu] at hlower
  have hm := hmain n y S hy hS hlog
  dsimp only at hm
  calc
    (X : ℝ) *
          ((1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            missingEulerProduct n y) - (D : ℝ) ^ 2 ≤
        (X : ℝ) * lowerMainTerm stop Erdos851.oneShiftDensity P -
          (D : ℝ) ^ 2 := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_left hm.1 (Nat.cast_nonneg X)) _
    _ ≤ ((selectedSiftedInterval n y X).card : ℝ) := hlower

/-! ### Sifting arithmetic progressions

CFP Lemma 5.9 also needs the one-dimensional beta sieve on an arithmetic
progression.  The next constructor keeps occurrences rather than requiring
the progression map to be injective. -/

lemma exists_progression_bad_residue
    {a b d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime b d) :
    ∃ r < d, ∀ i : ℕ, d ∣ a + b * i ↔ i % d = r := by
  obtain ⟨r, hrlt, hr⟩ := Nat.exists_mul_mod_eq_of_coprime
    ((d - a % d) % d) hcop hd.ne'
  refine ⟨r, hrlt, ?_⟩
  have hrdiv : d ∣ a + b * r := by
    rw [← Nat.modEq_zero_iff_dvd]
    change (a + b * r) % d = 0 % d
    rw [Nat.add_mod, hr]
    have ha : a % d < d := Nat.mod_lt a hd
    by_cases hzero : a % d = 0
    · simp [hzero]
    · have hpos : 0 < a % d := Nat.pos_of_ne_zero hzero
      have hmodsub : (d - a % d) % d = d - a % d :=
        Nat.mod_eq_of_lt (Nat.sub_lt hd hpos)
      rw [hmodsub, hmodsub]
      have hsum : a % d + (d - a % d) = d := Nat.add_sub_of_le ha.le
      rw [hsum, Nat.mod_self]
      simp
  intro i
  constructor
  · intro hi
    have hsum : a + b * i ≡ a + b * r [MOD d] :=
      hi.modEq_zero_nat.trans hrdiv.zero_modEq_nat
    have hmul : b * i ≡ b * r [MOD d] :=
      Nat.ModEq.add_left_cancel' a hsum
    have hir : i ≡ r [MOD d] :=
      Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one hmul
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using hir
  · intro hir
    have hir' : i ≡ r [MOD d] := by
      change i % d = r % d
      simpa [Nat.mod_eq_of_lt hrlt] using hir
    have hsum : a + b * i ≡ a + b * r [MOD d] :=
      (hir'.mul_left b).add_left a
    exact (hsum.dvd_iff (dvd_refl d)).mpr hrdiv

def progressionDivisibleIndices (a b L d : ℕ) : Finset ℕ :=
  (Finset.range L).filter fun i ↦ d ∣ a + b * i

def progressionCoprimeIndices (a b L M : ℕ) : Finset ℕ :=
  (Finset.range L).filter fun i ↦ Nat.Coprime M (a + b * i)

lemma abs_card_progressionDivisibleIndices_sub_density
    {a b L d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime b d) :
    |((progressionDivisibleIndices a b L d).card : ℝ) -
        (L : ℝ) / d| ≤ 1 := by
  obtain ⟨r, hrlt, hr⟩ := exists_progression_bad_residue
    (a := a) hd hcop
  have heq : progressionDivisibleIndices a b L d =
      Erdos387.modularPreimage L d {r} := by
    ext i
    simp [progressionDivisibleIndices, Erdos387.modularPreimage, hr i]
  rw [heq]
  simpa using Erdos387.abs_card_modularPreimage_sub_density
    hd ({r} : Finset ℕ) (by simpa using hrlt)

/-- A weighted sieve whose underlying occurrences are the first `L` terms
of the arithmetic progression `a + b i`. -/
noncomputable def progressionBoundingSieve
    (a b L M : ℕ) (hM : Squarefree M) : BoundingSieve := by
  classical
  let I := Finset.range L
  let g := fun i : ℕ ↦ a + b * i
  exact
    { support := I.image g
      prodPrimes := M
      prodPrimes_squarefree := hM
      weights := fun q ↦ ((I.filter fun i ↦ g i = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := L
      nu := Erdos851.ShiftSieve.shiftNu {0}
      nu_mult := Erdos851.ShiftSieve.shiftNu_mult {0}
      nu_pos_of_prime := by
        intro p hp _hpM
        rw [Erdos851.shiftNu_singleton_prime 0 hp]
        exact Erdos851.oneShiftDensity_pos hp
      nu_lt_one_of_prime := by
        intro p hp _hpM
        rw [Erdos851.shiftNu_singleton_prime 0 hp]
        exact Erdos851.oneShiftDensity_lt_one hp }

lemma progressionBoundingSieve_totalMass
    (a b L M : ℕ) (hM : Squarefree M) :
    (progressionBoundingSieve a b L M hM).totalMass = L := rfl

lemma progressionBoundingSieve_multSum
    (a b L M d : ℕ) (hM : Squarefree M) :
    (progressionBoundingSieve a b L M hM).multSum d =
      ((progressionDivisibleIndices a b L d).card : ℝ) := by
  classical
  let I := Finset.range L
  let g := fun i : ℕ ↦ a + b * i
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image g,
      if d ∣ q then ((I.filter fun i ↦ g i = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image g).filter fun q ↦ d ∣ q,
          (I.filter fun i ↦ g i = q).card) =
        (I.filter fun i ↦ d ∣ g i).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

lemma progressionBoundingSieve_siftedSum
    (a b L M : ℕ) (hM : Squarefree M) :
    (progressionBoundingSieve a b L M hM).siftedSum =
      ((progressionCoprimeIndices a b L M).card : ℝ) := by
  classical
  let I := Finset.range L
  let g := fun i : ℕ ↦ a + b * i
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image g,
      if Nat.Coprime M q then
        ((I.filter fun i ↦ g i = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image g).filter fun q ↦ Nat.Coprime M q,
          (I.filter fun i ↦ g i = q).card) =
        (I.filter fun i ↦ Nat.Coprime M (g i)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

lemma progressionBoundingSieve_abs_rem_le_one
    {a b L M d : ℕ} {hM : Squarefree M}
    (hcop : Nat.Coprime b M) (hd : d ∣ M) :
    |(progressionBoundingSieve a b L M hM).rem d| ≤ 1 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd
    (Nat.pos_of_ne_zero hM.ne_zero)
  have hcbd : Nat.Coprime b d := Nat.Coprime.of_dvd_right hd hcop
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd hM
  rw [BoundingSieve.rem, progressionBoundingSieve_multSum,
    progressionBoundingSieve_totalMass]
  change |((progressionDivisibleIndices a b L d).card : ℝ) -
      Erdos851.ShiftSieve.shiftNu {0} d * (L : ℝ)| ≤ 1
  rw [Erdos851.ShiftSieve.shiftNu_squarefree hsq]
  have hclasses : Erdos851.ShiftSieve.nuClasses {0} d = 1 := by
    simp [Erdos851.ShiftSieve.nuClasses,
      Erdos851.ShiftSieve.localNu_singleton]
  rw [hclasses]
  simpa [div_eq_mul_inv, mul_comm] using
    abs_card_progressionDivisibleIndices_sub_density
      (a := a) (L := L) hdpos hcbd

/-- Upper beta-sieve estimate for the first `L` terms of a progression,
after retaining only sieving primes coprime to its common difference. -/
theorem exists_progressionCoprimeIndices_card_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n a b L y S : ℕ, 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        Nat.Coprime b (missingPrimeProduct n y) →
        let V := missingEulerProduct n y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((progressionCoprimeIndices a b L
          (missingPrimeProduct n y)).card : ℝ) ≤
          (L : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_missing_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro n a b L y S hy hS hlog hcop
  dsimp only
  let P := ascendingMissingPrimes n y
  let M := missingPrimeProduct n y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := progressionBoundingSieve a b L M
    (missingPrimeProduct_squarefree n y)
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = M
    exact ascendingMissingPrimes_prod n y
  have hsort : P.Pairwise (· ≤ ·) := ascendingMissingPrimes_pairwise n y
  have hnodup : P.Nodup := ascendingMissingPrimes_nodup n y
  have hprime : ∀ p ∈ P, p.Prime := ascendingMissingPrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hd' : d ∣ M := hd
    exact (progressionBoundingSieve_abs_rem_le_one hcop hd').trans
      (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hd0 ↦ by
            subst d
            have hM0 : M = 0 := by simpa using hd'
            exact (missingPrimeProduct_squarefree n y).ne_zero hM0))
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        hadm)
    hrem
  change _ ≤ sieve.totalMass *
      upperMainTerm stop (fun p ↦ sieve.nu p) P + (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (L : ℝ) by rfl,
    show sieve.siftedSum =
        ((progressionCoprimeIndices a b L M).card : ℝ) by
      exact progressionBoundingSieve_siftedSum a b L M
        (missingPrimeProduct_squarefree n y)] at hupper
  have hnu : ∀ p ∈ P,
      sieve.nu p = Erdos851.oneShiftDensity p := by
    intro p hp
    change Erdos851.ShiftSieve.shiftNu {0} p =
      Erdos851.oneShiftDensity p
    exact Erdos851.shiftNu_singleton_prime 0 (hprime p hp)
  rw [upperMainTerm_congr_on stop (fun p ↦ sieve.nu p)
    Erdos851.oneShiftDensity P hnu] at hupper
  have hm := hmain n y S hy hS hlog
  dsimp only at hm
  calc
    ((progressionCoprimeIndices a b L M).card : ℝ) ≤
        (L : ℝ) * upperMainTerm stop Erdos851.oneShiftDensity P +
          (D : ℝ) ^ 2 := hupper
    _ ≤ (L : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            missingEulerProduct n y) + (D : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg L)) le_rfl

lemma progression_step_coprime_missingPrimeProduct_mul
    (m b y : ℕ) :
    Nat.Coprime b (missingPrimeProduct (m * b) y) := by
  have hMb := missingPrimeProduct_coprime_target (m * b) y
  have hbdiv : b ∣ m * b := ⟨m, by simp [mul_comm]⟩
  exact (Nat.Coprime.of_dvd_right hbdiv hMb).symm

lemma missingPrimes_union_targetPrimes (n y : ℕ) :
    missingPrimesUpTo n y ∪ Erdos4.residualCofactorSievePrimes y n =
      Erdos851.sievePrimes 2 y := by
  ext p
  simp only [Finset.mem_union, missingPrimesUpTo,
    Erdos4.residualCofactorSievePrimes, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hpn : p ∣ n
    · exact Or.inr ⟨hp, hpn⟩
    · exact Or.inl ⟨hp, hpn⟩

lemma missingPrimes_disjoint_targetPrimes (n y : ℕ) :
    Disjoint (missingPrimesUpTo n y)
      (Erdos4.residualCofactorSievePrimes y n) := by
  rw [Finset.disjoint_left]
  intro p hp hptarget
  exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hptarget).2

lemma missingEulerProduct_eq_all_mul_targetInverse (n y : ℕ) :
    missingEulerProduct n y =
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y *
        Erdos4.residualCofactorOrdinaryInverseProduct y n := by
  let T := Erdos4.residualCofactorSievePrimes y n
  let R : ℝ := ∏ p ∈ T, (1 - Erdos851.oneShiftDensity p)
  have hRpos : 0 < R := by
    dsimp [R, T]
    apply Finset.prod_pos
    intro p hp
    have hpprime := (Erdos851.mem_sievePrimes.mp
      (Finset.mem_filter.mp hp).1).2.2
    exact Erdos851.oneShift_localFactor_pos hpprime
  have hmul : missingEulerProduct n y * R =
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y := by
    unfold missingEulerProduct Erdos851.localEulerProduct
    dsimp [R, T]
    rw [← Finset.prod_union (missingPrimes_disjoint_targetPrimes n y),
      missingPrimes_union_targetPrimes]
  calc
    missingEulerProduct n y =
        (missingEulerProduct n y * R) * R⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hRpos.ne', mul_one]
    _ = Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y * R⁻¹ := by
      rw [hmul]
    _ = Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y *
        Erdos4.residualCofactorOrdinaryInverseProduct y n := by
      congr 1
      unfold Erdos4.residualCofactorOrdinaryInverseProduct
      dsimp [R, T]
      rw [Finset.prod_inv_distrib]

/-- Mertens' estimate with the exact correction for prime divisors of the
target.  This is the analytic factor required by the fourth cover step. -/
theorem exists_missingEulerProduct_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n y : ℕ, 0 < n → 2 ≤ y →
      missingEulerProduct n y ≤
        C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ) := by
  obtain ⟨C, hC, hMertens⟩ := Erdos4.exists_oneShift_directMertens_bound
  refine ⟨C, hC, ?_⟩
  intro n y hn hy
  have hlog : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  have hratioNonneg : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  have hcorrNonneg : 0 ≤
      Erdos4.residualCofactorOrdinaryInverseProduct y n := by
    unfold Erdos4.residualCofactorOrdinaryInverseProduct
    apply Finset.prod_nonneg
    intro p hp
    exact (Erdos4.one_le_oneShift_inverseFactor
      ((Erdos851.mem_sievePrimes.mp
        (Finset.mem_filter.mp hp).1).2.2)).trans' (by norm_num)
  rw [missingEulerProduct_eq_all_mul_targetInverse]
  calc
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y *
        Erdos4.residualCofactorOrdinaryInverseProduct y n ≤
      (C / Real.log (y : ℝ)) *
        ((n : ℝ) / Nat.totient n) := by
          exact mul_le_mul (hMertens y hy)
            (Erdos4.residualCofactorOrdinaryInverseProduct_le_ratio hn)
            hcorrNonneg (by positivity)
    _ = C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ) := by
      field_simp [hlog.ne']

/-- Index type of the complete four-step cover. -/
abbrev UpperIndex (n h d : ℕ) (hn : Nat.Coprime n d) :=
  UpperMainIndex h d ⊕ Fin ((upperRemainder n h d hn).card / d + 1)

/-- The complete upper-bound cover, including the short leftover blocks. -/
noncomputable def upperFamily (n h d : ℕ) (hn : Nat.Coprime n d) :
    UpperIndex n h d hn → Finset (BelowTarget n)
  | Sum.inl i => upperMainFamily n h d hn i
  | Sum.inr j => chunkFamily (upperRemainder n h d hn) d j

lemma upperFamily_covers {n h d : ℕ} (hd : 0 < d) (hn : Nat.Coprime n d) :
    ∀ x, ∃ i : UpperIndex n h d hn, x ∈ upperFamily n h d hn i := by
  intro x
  by_cases hmain : ∃ i : UpperMainIndex h d, x ∈ upperMainFamily n h d hn i
  · obtain ⟨i, hi⟩ := hmain
    exact ⟨Sum.inl i, hi⟩
  · have hrem : x ∈ upperRemainder n h d hn := mem_upperRemainder.mpr hmain
    obtain ⟨j, hj⟩ := chunkFamily_covers (upperRemainder n h d hn) hd hrem
    exact ⟨Sum.inr j, hj⟩

lemma upperFamily_avoiding {n h d : ℕ} (hnpos : 0 < n) (hd : 1 < d)
    (hn : Nat.Coprime n d) :
    ∀ i : UpperIndex n h d hn, TargetAvoiding n (upperFamily n h d hn i) := by
  rintro (i | j)
  · exact upperMainFamily_avoiding hnpos hd hn i
  · change TargetAvoiding n (chunkFamily (upperRemainder n h d hn) d j)
    apply targetAvoiding_of_card_le_of_mul_lt (d := d) hnpos (by omega)
    · exact chunkFamily_card_le (upperRemainder n h d hn) (by omega) j
    · intro x hx
      have hxrem : x ∈ upperRemainder n h d hn :=
        (mem_chunkFamily.mp hx).1
      exact upperRemainder_mul_lt hd hn hxrem

lemma card_upperMainIndex (h d : ℕ) [NeZero d] :
    Fintype.card (UpperMainIndex h d) =
      2 * h + d.primeFactors.card + 2 * Nat.totient d := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_sum, Fintype.card_coe,
    card_residueClassIndex]
  omega

lemma card_upperIndex (n h d : ℕ) (hn : Nat.Coprime n d) [NeZero d] :
    Fintype.card (UpperIndex n h d hn) =
      2 * h + d.primeFactors.card + 2 * Nat.totient d +
        (upperRemainder n h d hn).card / d + 1 := by
  rw [Fintype.card_sum, card_upperMainIndex, Fintype.card_fin]
  omega

/-- The coloring which assigns each integer below `n` its own value as a color. -/
def selfColor (n : ℕ) : BelowTarget n → Fin n :=
  fun x ↦ ⟨x.1, (Finset.mem_Ico.mp x.2).2⟩

lemma selfColor_injective (n : ℕ) : Function.Injective (selfColor n) := by
  intro x y hxy
  exact Subtype.ext (congrArg Fin.val hxy)

lemma avoidsTarget_selfColor {n : ℕ} (hn : 0 < n) :
    AvoidsTarget n n (selfColor n) := by
  intro A hmono
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst A
    simpa using hn.ne
  · obtain ⟨x, hx⟩ := hA
    have hsingleton : A = {x} := by
      ext y
      constructor
      · intro hy
        have hxy : selfColor n y = selfColor n x := hmono hy hx
        have : y = x := selfColor_injective n hxy
        simpa [this]
      · intro hy
        have : y = x := Finset.mem_singleton.mp hy
        simpa [this] using hx
    rw [hsingleton]
    have hxlt : x.1 < n := by
      exact (Finset.mem_Ico.mp x.2).2
    simpa using (Nat.ne_of_lt hxlt)

lemma colorable_self {n : ℕ} (hn : 0 < n) : Colorable n n :=
  ⟨selfColor n, avoidsTarget_selfColor hn⟩

lemma Colorable.mono {n r s : ℕ} (hrs : r ≤ s) :
    Colorable n r → Colorable n s := by
  rintro ⟨c, hc⟩
  refine ⟨fun x ↦ Fin.castLE hrs (c x), ?_⟩
  intro A hmono
  apply hc A
  intro x hx y hy
  apply Fin.ext
  simpa using congrArg Fin.val (hmono hx hy)

lemma exists_colorable {n : ℕ} (hn : 0 < n) : ∃ r, Colorable n r :=
  ⟨n, colorable_self hn⟩

/-- The exact extremal function from Erdős Problem 360.  The auxiliary value at `0`
is immaterial to the eventual theorem. -/
noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact if hn : n = 0 then 0 else Nat.find (exists_colorable (Nat.pos_of_ne_zero hn))

@[simp] lemma f_zero : f 0 = 0 := by
  simp [f]

lemma colorable_f {n : ℕ} (hn : 0 < n) : Colorable n (f n) := by
  classical
  rw [f, dif_neg hn.ne']
  exact Nat.find_spec (exists_colorable hn)

lemma f_le_of_colorable {n r : ℕ} (hn : 0 < n) (h : Colorable n r) :
    f n ≤ r := by
  classical
  rw [f, dif_neg hn.ne']
  exact Nat.find_min' (exists_colorable hn) h

lemma colorable_iff_f_le {n r : ℕ} (hn : 0 < n) :
    Colorable n r ↔ f n ≤ r := by
  constructor
  · exact f_le_of_colorable hn
  · intro h
    exact (colorable_f hn).mono h

lemma forcesTarget_iff_lt_f {n r : ℕ} (hn : 0 < n) :
    ForcesTarget n r ↔ r < f n := by
  rw [forcesTarget_iff_not_colorable, colorable_iff_f_le hn, not_le]

lemma f_le_iff_exists_avoidingCover {n r : ℕ} (hn : 0 < n) :
    f n ≤ r ↔ ∃ S : Fin r → Finset (BelowTarget n), IsAvoidingCover S := by
  rw [← colorable_iff_f_le hn, colorable_iff_exists_avoidingCover hn]

lemma f_le_self {n : ℕ} (hn : 0 < n) : f n ≤ n :=
  f_le_of_colorable hn (colorable_self hn)

lemma not_colorable_zero {n : ℕ} (hn : 2 ≤ n) : ¬Colorable n 0 := by
  rintro ⟨c, _⟩
  have hlt : 1 < n := by omega
  exact Fin.elim0 (c ⟨1, Finset.mem_Ico.mpr ⟨by omega, hlt⟩⟩)

lemma f_pos {n : ℕ} (hn : 2 ≤ n) : 0 < f n := by
  have hn0 : 0 < n := by omega
  by_contra h
  have hf0 : f n = 0 := by omega
  exact not_colorable_zero hn (hf0 ▸ colorable_f hn0)

/-- Exact finite upper bound supplied by the four-step cover.  All analytic
number theory in the asymptotic upper bound is now concentrated in choosing
`h,d` and bounding `upperRemainder.card`. -/
lemma f_le_upperCoverCount {n h d : ℕ} (hnpos : 0 < n) (hd : 1 < d)
    (hn : Nat.Coprime n d) :
    f n ≤ 2 * h + d.primeFactors.card + 2 * Nat.totient d +
      (upperRemainder n h d hn).card / d + 1 := by
  let : NeZero d := ⟨by omega⟩
  have hcolor : Colorable n (Fintype.card (UpperIndex n h d hn)) :=
    colorable_of_fintype_avoidingCover hnpos
      ⟨upperFamily_covers (by omega) hn,
        upperFamily_avoiding hnpos hd hn⟩
  rw [card_upperIndex] at hcolor
  exact f_le_of_colorable hnpos hcolor

/-- Fully finite real-valued upper estimate obtained by combining the four
covering families with the filtered beta sieve.  What remains for the
asymptotic upper bound is only the choice of `h,d,y`. -/
theorem exists_f_upperCover_real_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n h d y S : ℕ, 0 < n → 0 < h → 1 < d → Nat.Coprime n d →
        y < primeAt h → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (f n : ℝ) ≤
          2 * h + d.primeFactors.card + 2 * Nat.totient d +
            (((n / h : ℕ) : ℝ) *
                ((1 + eta) * missingEulerProduct n y) +
              ((D : ℕ) : ℝ) ^ 2) / d + 1 := by
  obtain ⟨A, hA, hsieve⟩ := exists_selectedSiftedInterval_card_bound
  refine ⟨A, hA, ?_⟩
  intro n h d y S hn hh hd hcop hyh hy hS hlog
  dsimp only
  have hfNat := f_le_upperCoverCount (h := h) hn hd hcop
  have hremCard :
      ((upperRemainder n h d hcop).card : ℝ) ≤
        (((n / h : ℕ) : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              missingEulerProduct n y) +
          (((y ^ S : ℕ) : ℝ) ^ 2)) := by
    calc
      ((upperRemainder n h d hcop).card : ℝ) ≤
          ((selectedSiftedInterval n y (n / h)).card : ℝ) := by
        exact_mod_cast upperRemainder_card_le_selectedSiftedInterval
          hh hcop hyh
      _ ≤ (((n / h : ℕ) : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              missingEulerProduct n y) +
          (((y ^ S : ℕ) : ℝ) ^ 2)) := hsieve n (n / h) y S hy hS hlog
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdivCast :
      (((upperRemainder n h d hcop).card / d : ℕ) : ℝ) ≤
        ((upperRemainder n h d hcop).card : ℝ) / d := by
    exact Nat.cast_div_le
  calc
    (f n : ℝ) ≤
        ((2 * h + d.primeFactors.card + 2 * Nat.totient d +
          (upperRemainder n h d hcop).card / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast hfNat
    _ = 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          (((upperRemainder n h d hcop).card / d : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    _ ≤ 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          ((upperRemainder n h d hcop).card : ℝ) / d + 1 := by
      gcongr
    _ ≤ 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          ((((n / h : ℕ) : ℝ) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  missingEulerProduct n y) +
              (((y ^ S : ℕ) : ℝ) ^ 2)) / d) + 1 := by
      gcongr

/-- Strengthened finite upper estimate using the modulus cutoff `n / d` in
the final sieve.  This is the form used in the asymptotic parameter
assembly. -/
theorem exists_f_upperCover_real_bound_modulus :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n h d y S : ℕ, 0 < n → 1 < d → Nat.Coprime n d →
        y < primeAt h → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (f n : ℝ) ≤
          2 * h + d.primeFactors.card + 2 * Nat.totient d +
            (((n / d : ℕ) : ℝ) *
                ((1 + eta) * missingEulerProduct n y) +
              ((D : ℕ) : ℝ) ^ 2) / d + 1 := by
  obtain ⟨A, hA, hsieve⟩ := exists_selectedSiftedInterval_card_bound
  refine ⟨A, hA, ?_⟩
  intro n h d y S hn hd hcop hyh hy hS hlog
  dsimp only
  have hfNat := f_le_upperCoverCount (h := h) hn hd hcop
  have hremCard :
      ((upperRemainder n h d hcop).card : ℝ) ≤
        (((n / d : ℕ) : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              missingEulerProduct n y) +
          (((y ^ S : ℕ) : ℝ) ^ 2)) := by
    calc
      ((upperRemainder n h d hcop).card : ℝ) ≤
          ((selectedSiftedInterval n y (n / d)).card : ℝ) := by
        exact_mod_cast upperRemainder_card_le_selectedSiftedInterval_modulus
          hd hcop hyh
      _ ≤ (((n / d : ℕ) : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              missingEulerProduct n y) +
          (((y ^ S : ℕ) : ℝ) ^ 2)) := hsieve n (n / d) y S hy hS hlog
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdivCast :
      (((upperRemainder n h d hcop).card / d : ℕ) : ℝ) ≤
        ((upperRemainder n h d hcop).card : ℝ) / d := by
    exact Nat.cast_div_le
  calc
    (f n : ℝ) ≤
        ((2 * h + d.primeFactors.card + 2 * Nat.totient d +
          (upperRemainder n h d hcop).card / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast hfNat
    _ = 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          (((upperRemainder n h d hcop).card / d : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    _ ≤ 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          ((upperRemainder n h d hcop).card : ℝ) / d + 1 := by
      gcongr
    _ ≤ 2 * h + d.primeFactors.card + 2 * Nat.totient d +
          ((((n / d : ℕ) : ℝ) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  missingEulerProduct n y) +
              (((y ^ S : ℕ) : ℝ) ^ 2)) / d) + 1 := by
      gcongr

/-! ## Lower-bound subset-sum growth infrastructure -/

/-- Residues modulo `t` occupied by a finite set of natural numbers. -/
noncomputable def occupiedResidues (S : Finset ℕ) (t : ℕ) : Finset (ZMod t) :=
  S.image fun x : ℕ ↦ (x : ZMod t)

/-- The largest representative in `S` of an occupied residue. -/
noncomputable def topRepresentative (S : Finset ℕ) (t : ℕ)
    (r : occupiedResidues S t) : ℕ := by
  classical
  let F : Finset ℕ := S.filter fun x : ℕ ↦ (x : ZMod t) = r.1
  have hF : F.Nonempty := by
    obtain ⟨x, hxS, hxr⟩ := Finset.mem_image.mp r.2
    refine ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩⟩
    exact hxr
  exact F.max' hF

lemma topRepresentative_mem (S : Finset ℕ) (t : ℕ)
    (r : occupiedResidues S t) : topRepresentative S t r ∈ S := by
  classical
  unfold topRepresentative
  dsimp only
  exact Finset.filter_subset _ _ (Finset.max'_mem _ _)

lemma topRepresentative_residue (S : Finset ℕ) (t : ℕ)
    (r : occupiedResidues S t) :
    (topRepresentative S t r : ZMod t) = r.1 := by
  classical
  unfold topRepresentative
  dsimp only
  exact (Finset.mem_filter.mp
    (Finset.max'_mem (S.filter fun x : ℕ ↦ (x : ZMod t) = r.1) _)).2

lemma le_topRepresentative_of_mem {S : Finset ℕ} {t x : ℕ}
    (r : occupiedResidues S t) (hxS : x ∈ S)
    (hxr : (x : ZMod t) = r.1) : x ≤ topRepresentative S t r := by
  classical
  unfold topRepresentative
  dsimp only
  exact Finset.le_max' _ x (Finset.mem_filter.mpr ⟨hxS, hxr⟩)

lemma topRepresentative_add_not_mem {S : Finset ℕ} {t : ℕ} [NeZero t]
    (ht : 0 < t) (r : occupiedResidues S t) :
    topRepresentative S t r + t ∉ S := by
  intro hmem
  have hres : ((topRepresentative S t r + t : ℕ) : ZMod t) = r.1 := by
    rw [Nat.cast_add, topRepresentative_residue]
    simp
  have hle := le_topRepresentative_of_mem r hmem hres
  omega

lemma topRepresentative_add_injective {S : Finset ℕ} {t : ℕ} [NeZero t] :
    Function.Injective
      (fun r : occupiedResidues S t ↦ topRepresentative S t r + t) := by
  intro r s hrs
  have htop : topRepresentative S t r = topRepresentative S t s :=
    Nat.add_right_cancel hrs
  apply Subtype.ext
  rw [← topRepresentative_residue S t r,
    ← topRepresentative_residue S t s, htop]

/-- Adjoining `t` creates at least one new ordinary subset sum for every
residue modulo `t` already represented.  This is Lemma 2.5 of CFP in finite
form. -/
lemma subsetSum_card_add_occupiedResidues_le {A : Finset ℕ} {t : ℕ}
    [NeZero t] (ht : 0 < t) (htA : t ∉ A) :
    A.subsetSum.card + (occupiedResidues A.subsetSum t).card ≤
      (insert t A).subsetSum.card := by
  classical
  let R := occupiedResidues A.subsetSum t
  let N : Finset ℕ := (Finset.univ : Finset R).image
    (fun r : R ↦ topRepresentative A.subsetSum t r + t)
  have hNcard : N.card = R.card := by
    change ((Finset.univ : Finset R).image
      (fun r : R ↦ topRepresentative A.subsetSum t r + t)).card = R.card
    calc
      _ = (Finset.univ : Finset R).card :=
        Finset.card_image_of_injective _
          (topRepresentative_add_injective (S := A.subsetSum) (t := t))
      _ = R.card := by simp
  have hdisj : Disjoint A.subsetSum N := by
    rw [Finset.disjoint_left]
    intro x hxS hxN
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hxN
    exact topRepresentative_add_not_mem ht r hxS
  have hsubset : A.subsetSum ∪ N ⊆ (insert t A).subsetSum := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact Finset.subsetSum_mono (Finset.subset_insert t A) hx
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_subsetSum_iff] at ⊢
      obtain ⟨B, hBA, hsum⟩ := Finset.mem_subsetSum_iff.mp
        (topRepresentative_mem A.subsetSum t r)
      refine ⟨insert t B, Finset.insert_subset_insert t hBA, ?_⟩
      rw [Finset.sum_insert]
      · simpa [hsum, add_comm]
      · exact fun htB ↦ htA (hBA htB)
  calc
    A.subsetSum.card + (occupiedResidues A.subsetSum t).card =
        (A.subsetSum ∪ N).card := by
      rw [Finset.card_union_of_disjoint hdisj, hNcard]
    _ ≤ (insert t A).subsetSum.card := Finset.card_le_card hsubset

/-- Reducing modulo `t` preserves inclusion. -/
lemma occupiedResidues_mono {S T : Finset ℕ} {t : ℕ} (hST : S ⊆ T) :
    occupiedResidues S t ⊆ occupiedResidues T t := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_image.mpr ⟨x, hST hx, rfl⟩

/-- The number of represented residues cannot decrease when the underlying
integer set is enlarged. -/
lemma card_occupiedResidues_mono {S T : Finset ℕ} {t : ℕ} (hST : S ⊆ T) :
    (occupiedResidues S t).card ≤ (occupiedResidues T t).card :=
  Finset.card_le_card (occupiedResidues_mono hST)

/-- Repeated form of CFP Lemma 2.5.  If the subset sums of a fixed seed `A`
occupy at least `h t` residue classes modulo every `t` in a disjoint set
`B`, adjoining all members of `B` creates at least `∑ t ∈ B, h t` new
ordinary subset sums. -/
lemma subsetSum_card_add_sum_le_union
    {A B : Finset ℕ} (hAB : Disjoint A B) (h : ℕ → ℕ)
    (hpos : ∀ t ∈ B, 0 < t)
    (hres : ∀ t ∈ B, h t ≤ (occupiedResidues A.subsetSum t).card) :
    A.subsetSum.card + ∑ t ∈ B, h t ≤ (A ∪ B).subsetSum.card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert t B htB ih =>
      have htA : t ∉ A := by
        intro htA
        exact Finset.disjoint_left.mp hAB htA (Finset.mem_insert_self t B)
      have hAB' : Disjoint A B := hAB.mono_right (Finset.subset_insert t B)
      have hres' : ∀ s ∈ B, h s ≤
          (occupiedResidues A.subsetSum s).card := by
        intro s hs
        exact hres s (Finset.mem_insert_of_mem hs)
      have hpos' : ∀ s ∈ B, 0 < s := by
        intro s hs
        exact hpos s (Finset.mem_insert_of_mem hs)
      have hseed : A.subsetSum.card + ∑ s ∈ B, h s ≤
          (A ∪ B).subsetSum.card := ih hAB' hpos' hres'
      have hsubsetSums : A.subsetSum ⊆ (A ∪ B).subsetSum :=
        Finset.subsetSum_mono Finset.subset_union_left
      have htResidues : h t ≤
          (occupiedResidues (A ∪ B).subsetSum t).card :=
        (hres t (Finset.mem_insert_self t B)).trans
          (card_occupiedResidues_mono hsubsetSums)
      have htNot : t ∉ A ∪ B := by simp [htA, htB]
      have htPos : 0 < t := hpos t (Finset.mem_insert_self t B)
      let : NeZero t := ⟨htPos.ne'⟩
      have hstep := subsetSum_card_add_occupiedResidues_le
        (A := A ∪ B) (t := t) htPos htNot
      calc
        A.subsetSum.card + ∑ s ∈ insert t B, h s =
            (A.subsetSum.card + ∑ s ∈ B, h s) + h t := by
              rw [Finset.sum_insert htB]
              omega
        _ ≤ (A ∪ B).subsetSum.card + h t := Nat.add_le_add_right hseed _
        _ ≤ (A ∪ B).subsetSum.card +
            (occupiedResidues (A ∪ B).subsetSum t).card :=
          Nat.add_le_add_left htResidues _
        _ ≤ (insert t (A ∪ B)).subsetSum.card := hstep
        _ = (A ∪ insert t B).subsetSum.card := by
          congr 2
          ext x
          simp [or_left_comm, or_assoc]

/-! ### Almost-period estimates -/

/-- Translations which add at most `e` points to a finite set. -/
def almostPeriods {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : Finset G :=
  Finset.univ.filter fun x ↦
    (T ∪ Erdos587.addTranslate x T).card ≤ T.card + e

lemma mem_almostPeriods_iff {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] {T : Finset G} {e : ℕ} {x : G} :
    x ∈ almostPeriods T e ↔
      (T ∪ Erdos587.addTranslate x T).card ≤ T.card + e := by
  simp [almostPeriods]

/-- An almost period overlaps the original set in at least `|T| - e`
points. -/
lemma card_sub_le_card_inter_translate_of_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e : ℕ} {x : G} (hx : x ∈ almostPeriods T e) :
    T.card - e ≤ (T ∩ Erdos587.addTranslate x T).card := by
  have hunion := (mem_almostPeriods_iff.mp hx)
  have hcard := Finset.card_inter_add_card_union
    T (Erdos587.addTranslate x T)
  rw [Erdos587.card_addTranslate] at hcard
  omega

/-- The incidence finset used in the double count for CFP Lemma 2.6. -/
def almostPeriodIncidences
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : Finset (Σ _x : G, G) :=
  (almostPeriods T e).sigma fun x ↦
    T ∩ Erdos587.addTranslate x T

/-- An overlap incidence `(x,z)` is encoded by the ordered pair
`(z,z-x)`.  This encoding is injective. -/
lemma almostPeriodIncidence_encode_injective
    {G : Type*} [AddCommGroup G] :
    Function.Injective
      (fun p : Σ _x : G, G ↦ (p.2, -p.1 + p.2)) := by
  rintro ⟨x, z⟩ ⟨y, w⟩ hp
  have hzw : z = w := congrArg Prod.fst hp
  have hsecond : -x + z = -y + w := congrArg Prod.snd hp
  subst w
  have hneg : -x = -y := add_right_cancel hsecond
  have hxy : x = y := neg_injective hneg
  subst y
  rfl

/-- The elementary double-counting bound for almost periods (CFP Lemma
2.6): `( |T| - e ) |G_e| ≤ |T|²`. -/
lemma card_sub_mul_card_almostPeriods_le_sq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) :
    (T.card - e) * (almostPeriods T e).card ≤ T.card ^ 2 := by
  classical
  let I := almostPeriodIncidences T e
  let enc : (Σ _x : G, G) → G × G :=
    fun p ↦ (p.2, -p.1 + p.2)
  have hLower : (T.card - e) * (almostPeriods T e).card ≤ I.card := by
    change (T.card - e) * (almostPeriods T e).card ≤
      ((almostPeriods T e).sigma fun x ↦
        T ∩ Erdos587.addTranslate x T).card
    rw [Finset.card_sigma]
    calc
      (T.card - e) * (almostPeriods T e).card =
          ∑ _x ∈ almostPeriods T e, (T.card - e) := by
        simp [mul_comm]
      _ ≤ ∑ x ∈ almostPeriods T e,
          (T ∩ Erdos587.addTranslate x T).card := by
        exact Finset.sum_le_sum fun x hx ↦
          card_sub_le_card_inter_translate_of_mem_almostPeriods hx
  have hMaps : Set.MapsTo enc (I : Set (Σ _x : G, G))
      ((T ×ˢ T : Finset (G × G)) : Set (G × G)) := by
    intro p hp
    rw [Finset.mem_coe, show I = almostPeriodIncidences T e by rfl,
      almostPeriodIncidences, Finset.mem_sigma] at hp
    obtain ⟨_hx, hz⟩ := hp
    rw [Finset.mem_inter] at hz
    change enc p ∈ (T ×ˢ T : Finset (G × G))
    rw [Finset.mem_product]
    exact ⟨hz.1, (Erdos587.mem_addTranslate.mp hz.2)⟩
  have hInjective : (I : Set (Σ _x : G, G)).InjOn enc :=
    (almostPeriodIncidence_encode_injective : Function.Injective enc).injOn
  have hUpper : I.card ≤ (T ×ˢ T).card :=
    Finset.card_le_card_of_injOn enc hMaps hInjective
  calc
    (T.card - e) * (almostPeriods T e).card ≤ I.card := hLower
    _ ≤ (T ×ˢ T).card := hUpper
    _ = T.card ^ 2 := by simp [pow_two]

/-- Points introduced by translating `T` by `x`. -/
def translationNew {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T : Finset G) (x : G) : Finset G :=
  Erdos587.addTranslate x T \ T

lemma mem_almostPeriods_iff_card_translationNew_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e : ℕ} {x : G} :
    x ∈ almostPeriods T e ↔ (translationNew T x).card ≤ e := by
  rw [mem_almostPeriods_iff]
  have hcard := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  rw [Finset.union_comm] at hcard
  simp only [translationNew]
  omega

/-- Translation error is subadditive. -/
lemma card_translationNew_add_le
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T : Finset G) (x y : G) :
    (translationNew T (x + y)).card ≤
      (translationNew T x).card + (translationNew T y).card := by
  classical
  let D := Erdos587.addTranslate x (Erdos587.addTranslate y T) \
    Erdos587.addTranslate x T
  have hsubset : translationNew T (x + y) ⊆ D ∪ translationNew T x := by
    intro z hz
    rw [translationNew, Finset.mem_sdiff] at hz
    rw [Finset.mem_union]
    by_cases hzx : z ∈ Erdos587.addTranslate x T
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hzx, hz.2⟩)
    · apply Or.inl
      rw [Finset.mem_sdiff]
      refine ⟨?_, hzx⟩
      rw [Erdos587.addTranslate_add]
      exact hz.1
  have hD : D.card ≤ (translationNew T y).card := by
    let f : G → G := fun z ↦ -x + z
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      rw [Finset.mem_coe, show D =
        Erdos587.addTranslate x (Erdos587.addTranslate y T) \
          Erdos587.addTranslate x T by rfl,
        Finset.mem_sdiff] at hz
      rw [Finset.mem_coe, translationNew, Finset.mem_sdiff]
      exact ⟨Erdos587.mem_addTranslate.mp hz.1,
        fun hzT ↦ hz.2 (Erdos587.mem_addTranslate.mpr hzT)⟩
    · exact (fun _ _ _ _ h ↦ add_left_cancel h)
  calc
    (translationNew T (x + y)).card ≤
        (D ∪ translationNew T x).card := Finset.card_le_card hsubset
    _ ≤ D.card + (translationNew T x).card := Finset.card_union_le _ _
    _ ≤ (translationNew T y).card + (translationNew T x).card :=
      Nat.add_le_add_right hD _
    _ = (translationNew T x).card + (translationNew T y).card := by omega

/-- Sums of almost periods have the sum of the two error budgets. -/
lemma add_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e d : ℕ} {x y : G}
    (hx : x ∈ almostPeriods T e) (hy : y ∈ almostPeriods T d) :
    x + y ∈ almostPeriods T (e + d) := by
  rw [mem_almostPeriods_iff_card_translationNew_le] at hx hy ⊢
  exact (card_translationNew_add_le T x y).trans (Nat.add_le_add hx hy)

@[simp] lemma zero_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : 0 ∈ almostPeriods T e := by
  rw [mem_almostPeriods_iff_card_translationNew_le]
  simp [translationNew]

/-- The almost-period set is symmetric.  Translating the two-set union by
`x` exchanges the conditions for `x` and `-x`. -/
lemma neg_mem_almostPeriods_iff
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e : ℕ} {x : G} :
    -x ∈ almostPeriods T e ↔ x ∈ almostPeriods T e := by
  rw [mem_almostPeriods_iff, mem_almostPeriods_iff]
  have hcard :
      (T ∪ Erdos587.addTranslate (-x) T).card =
        (T ∪ Erdos587.addTranslate x T).card := by
    calc
      (T ∪ Erdos587.addTranslate (-x) T).card =
          (Erdos587.addTranslate x
            (T ∪ Erdos587.addTranslate (-x) T)).card :=
        (Erdos587.card_addTranslate _ _).symm
      _ = (Erdos587.addTranslate x T ∪ T).card := by
        rw [Erdos587.addTranslate_union, Erdos587.addTranslate_add]
        simp
      _ = (T ∪ Erdos587.addTranslate x T).card := by
        rw [Finset.union_comm]
  rw [hcard]

/-- Iterated form of CFP Lemma 2.7: `k G_e ⊆ G_{ke}`. -/
lemma nsmul_almostPeriods_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e k : ℕ) :
    k • almostPeriods T e ⊆ almostPeriods T (k * e) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul]
      intro x hx
      rw [Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have ha' := ih ha
      have hab := add_mem_almostPeriods ha' hb
      simpa [Nat.succ_mul, Nat.add_comm] using hab

/-! ### Extending an interval of subset sums -/

/-- If the subset sums of `A` contain `[a,b]`, adjoining a new element no
larger than the interval length extends the interval by that element. -/
lemma Icc_subset_subsetSum_insert_of_le_length
    {A : Finset ℕ} {a b t : ℕ} (hab : a ≤ b)
    (hI : Finset.Icc a b ⊆ A.subsetSum)
    (htA : t ∉ A) (ht : t ≤ b + 1 - a) :
    Finset.Icc a (b + t) ⊆ (insert t A).subsetSum := by
  intro x hx
  have hax : a ≤ x := (Finset.mem_Icc.mp hx).1
  have hxb : x ≤ b + t := (Finset.mem_Icc.mp hx).2
  by_cases hxold : x ≤ b
  · exact Finset.subsetSum_mono (Finset.subset_insert t A)
      (hI (Finset.mem_Icc.mpr ⟨hax, hxold⟩))
  · have htx : t ≤ x := by omega
    have hdiff : x - t ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨B, hBA, hsum⟩ := Finset.mem_subsetSum_iff.mp (hI hdiff)
    rw [Finset.mem_subsetSum_iff]
    refine ⟨insert t B, Finset.insert_subset_insert t hBA, ?_⟩
    rw [Finset.sum_insert]
    · rw [hsum]
      omega
    · exact fun htB ↦ htA (hBA htB)

/-- CFP Lemma 2.1 in finset form.  Once `[a,b]` occurs among the subset
sums of `A`, a disjoint set `B` of terms bounded by the original interval
length extends it all the way to `[a,b + ∑ B]`. -/
lemma Icc_subset_subsetSum_union_of_le_length
    {A B : Finset ℕ} {a b : ℕ} (hab : a ≤ b)
    (hAB : Disjoint A B)
    (hI : Finset.Icc a b ⊆ A.subsetSum)
    (hB : ∀ t ∈ B, t ≤ b + 1 - a) :
    Finset.Icc a (b + ∑ t ∈ B, t) ⊆ (A ∪ B).subsetSum := by
  classical
  induction B using Finset.induction_on with
  | empty => simpa using hI
  | @insert t B htB ih =>
      have htA : t ∉ A := by
        intro htA
        exact Finset.disjoint_left.mp hAB htA (Finset.mem_insert_self t B)
      have hAB' : Disjoint A B :=
        hAB.mono_right (Finset.subset_insert t B)
      have hB' : ∀ s ∈ B, s ≤ b + 1 - a := by
        intro s hs
        exact hB s (Finset.mem_insert_of_mem hs)
      have ihI := ih hAB' hB'
      have htBound : t ≤ (b + ∑ s ∈ B, s) + 1 - a := by
        have := hB t (Finset.mem_insert_self t B)
        omega
      have hext := Icc_subset_subsetSum_insert_of_le_length
        (show a ≤ b + ∑ s ∈ B, s by omega) ihI
        (by simpa [Finset.mem_union, htA, htB]) htBound
      simpa [Finset.sum_insert, htB, Finset.union_insert, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hext

/-! ### Kneser growth for a set escaping proper cosets -/

/-- A finite set escapes every proper stabilizer coset.  This is the exact
form of the hypothesis needed in the iterative Kneser argument: whenever a
nonempty finite set `C` is proper, no translate of `C.addStab` contains all
of `A`. -/
def EscapesProperStabilizerCosets
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) : Prop :=
  ∀ C : Finset G, C.Nonempty → C ≠ Finset.univ →
    ∀ a ∈ A, ∃ b ∈ A, b ∉ a +ᵥ C.addStab

/-- The usual additive-combinatorial formulation: `A` is not contained in
any coset of a proper additive subgroup. -/
def NotContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) : Prop :=
  ∀ H : AddSubgroup G, H ≠ ⊤ → ∀ a : G,
    ¬(A : Set G) ⊆ a +ᵥ (H : Set G)

/-- The standard proper-coset hypothesis implies the stabilizer form used
by Kneser's theorem. -/
lemma escapesProperStabilizerCosets_of_notContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hcoset : NotContainedInProperCoset A) :
    EscapesProperStabilizerCosets A := by
  intro C hC hCproper a ha
  have hCstab := hC
  have hCwitness := hC
  let H : AddSubgroup G := AddAction.stabilizer G (C : Set G)
  have hHproper : H ≠ ⊤ := by
    intro hHtop
    apply hCproper
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨c, hc⟩ := hCwitness
    have hxStab : x - c ∈ C.addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hCstab]
      change x - c ∈ H
      rw [hHtop]
      trivial
    have hxC := (Finset.mem_addStab' hCstab).mp hxStab hc
    simpa using hxC
  by_contra hnone
  push Not at hnone
  have hfin : A ⊆ a +ᵥ C.addStab := fun b hb ↦ hnone b hb
  have hset : (A : Set G) ⊆ a +ᵥ (H : Set G) := by
    intro b hb
    have hbfin := hfin (by simpa using hb)
    rw [Finset.mem_vadd_finset] at hbfin
    obtain ⟨y, hy, hsum⟩ := hbfin
    refine ⟨y, ?_, hsum⟩
    have hyset : y ∈ (C.addStab : Set G) := hy
    rw [Finset.coe_addStab hCstab] at hyset
    exact hyset
  exact hcoset H hHproper a hset

/-- Escaping a stabilizer coset forces `A + H` to occupy at least two
`H`-cosets. -/
lemma two_mul_card_addStab_le_card_add
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A C : Finset G} (hA : A.Nonempty)
    (hesc : EscapesProperStabilizerCosets A)
    (hC : C.Nonempty) (hCproper : C ≠ Finset.univ) :
    2 * C.addStab.card ≤ (A + C.addStab).card := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hbA, hbcoset⟩ := hesc C hC hCproper a ha
  have hcosetSubset : a +ᵥ C.addStab ⊆ A + C.addStab :=
    Finset.vadd_finset_subset_add ha
  have hbSum : b ∈ A + C.addStab :=
    Finset.subset_add_left A (Finset.zero_mem_addStab.mpr hC) hbA
  have hstrict : a +ᵥ C.addStab ⊂ A + C.addStab := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hcosetSubset, ?_⟩
    intro heq
    exact hbcoset (heq ▸ hbSum)
  have hlt : C.addStab.card < (A + C.addStab).card := by
    rw [← Finset.card_vadd_finset a C.addStab]
    exact Finset.card_lt_card hstrict
  have hdvd : C.addStab.card ∣ (A + C.addStab).card :=
    Finset.card_addStab_dvd_card_add_addStab A C
  obtain ⟨q, hq⟩ := hdvd
  have hHpos : 0 < C.addStab.card := hC.addStab.card_pos
  rw [hq] at hlt ⊢
  have hq2 : 2 ≤ q := by
    by_contra hqnot
    interval_cases q <;> simp_all
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right C.addStab.card hq2

/-- One Kneser step: unless `S+A` is the whole group, its doubled
cardinality exceeds twice the previous cardinality by `|A|`. -/
lemma two_mul_card_add_le_of_escape
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (hesc : EscapesProperStabilizerCosets A)
    (hproper : S + A ≠ Finset.univ) :
    2 * S.card + A.card ≤ 2 * (S + A).card := by
  let C := S + A
  have hC : C.Nonempty := hS.add hA
  have hHnonempty : C.addStab.Nonempty := hC.addStab
  have hHtwo : 2 * C.addStab.card ≤ (A + C.addStab).card :=
    two_mul_card_addStab_le_card_add hA hesc hC hproper
  have hAcard : A.card ≤ (A + C.addStab).card :=
    Finset.card_le_card_add_right hHnonempty
  have hSCard : S.card ≤ (S + C.addStab).card :=
    Finset.card_le_card_add_right hHnonempty
  have hK := Finset.add_kneser S A
  change (S + C.addStab).card + (A + C.addStab).card ≤
    C.card + C.addStab.card at hK
  change 2 * S.card + A.card ≤ 2 * C.card
  omega

/-- Sums of `k` copies, with the zero-fold sum equal to `{0}`.  Mathlib's
pointwise scalar operation uses the empty finset at zero, so the explicit
definition is preferable for additive-combinatorial iteration. -/
def iteratedFinsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : ℕ → Finset G
  | 0 => {0}
  | k + 1 => iteratedFinsetSum A k + A

@[simp] lemma iteratedFinsetSum_zero
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    iteratedFinsetSum A 0 = {0} := rfl

@[simp] lemma iteratedFinsetSum_succ
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (k : ℕ) :
    iteratedFinsetSum A (k + 1) = iteratedFinsetSum A k + A := rfl

lemma iteratedFinsetSum_nonempty
    {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    (hA : A.Nonempty) (k : ℕ) : (iteratedFinsetSum A k).Nonempty := by
  induction k with
  | zero => simp
  | succ k ih => exact ih.add hA

/-- CFP Lemma 2.3 in cross-multiplied form.  If `A` escapes every proper
coset, then a positive iterated sum grows by at least half of `|A|` at each
step, until it fills the group. -/
lemma min_group_card_iteratedFinsetSum_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty)
    (hesc : EscapesProperStabilizerCosets A) :
    ∀ k : ℕ, 1 ≤ k →
      min (2 * Fintype.card G) ((k + 1) * A.card) ≤
        2 * (iteratedFinsetSum A k).card := by
  intro k hk
  induction k using Nat.case_strong_induction_on with
  | hz => omega
  | hi k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [iteratedFinsetSum]
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have ih' := ih k (Nat.le_refl k) hkpos
        let S := iteratedFinsetSum A k
        let C := S + A
        have hS : S.Nonempty := iteratedFinsetSum_nonempty hA k
        by_cases hCuniv : C = Finset.univ
        · rw [iteratedFinsetSum_succ]
          change min (2 * Fintype.card G) ((k + 1 + 1) * A.card) ≤
            2 * C.card
          rw [hCuniv, Finset.card_univ]
          exact min_le_left _ _
        · have hgrowth : 2 * S.card + A.card ≤ 2 * C.card :=
            two_mul_card_add_le_of_escape hA hS hesc hCuniv
          have ihMain : (k + 1) * A.card ≤ 2 * S.card := by
            rcases le_total (2 * Fintype.card G) ((k + 1) * A.card) with
                hgroup | htarget
            · have hfullLower : 2 * Fintype.card G ≤ 2 * S.card := by
                simpa [min_eq_left hgroup] using ih'
              have hfullUpper : 2 * S.card ≤ 2 * Fintype.card G := by
                exact Nat.mul_le_mul_left 2 (Finset.card_le_univ S)
              have hScard : S.card = Fintype.card G := by omega
              have hSuniv : S = Finset.univ :=
                Finset.eq_univ_of_card S hScard
              exfalso
              apply hCuniv
              dsimp [C]
              rw [hSuniv]
              ext x
              simp only [Finset.mem_add, Finset.mem_univ]
              obtain ⟨a, ha⟩ := hA
              constructor
              · intro _
                trivial
              · intro _
                exact ⟨x - a, trivial, a, ha, by abel⟩
            · simpa [min_eq_right htarget] using ih'
          change min (2 * Fintype.card G) ((k + 1 + 1) * A.card) ≤
            2 * C.card
          apply (min_le_right _ _).trans
          calc
            (k + 1 + 1) * A.card = (k + 1) * A.card + A.card := by ring
            _ ≤ 2 * S.card + A.card := Nat.add_le_add_right ihMain _
            _ ≤ 2 * C.card := hgrowth

/-- CFP Lemma 2.3, stated with its customary proper-coset hypothesis. -/
theorem min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty)
    (hcoset : NotContainedInProperCoset A) (k : ℕ) (hk : 1 ≤ k) :
    min (2 * Fintype.card G) ((k + 1) * A.card) ≤
      2 * (iteratedFinsetSum A k).card :=
  min_group_card_iteratedFinsetSum_lower hA
    (escapesProperStabilizerCosets_of_notContainedInProperCoset hcoset) k hk

/-! ### The two Kneser corollaries used by Deshouillers--Freiman

The following arithmetic core packages the argument common to Propositions
1 and 2 of Balasubramanian--Pandey.  Write `H` for the stabilizer of `A+B`
and write the three `H`-saturated cardinalities as `alpha |H|`,
`beta |H|`, and `mu |H|`.  Kneser gives `alpha + beta ≤ mu + 1`, while
the two strict hypotheses give `2 mu < 3 alpha` and `mu < 2 beta`.
These integer inequalities force `mu = 1`.
-/

lemma small_sumset_stabilizer_coset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hleft : 2 * (A + B).card < 3 * A.card)
    (hright : (A + B).card < 2 * B.card) :
    ∃ H : AddSubgroup G, ∃ c : G,
      ((A + B : Finset G) : Set G) ⊆ c +ᵥ (H : Set G) ∧
      Nat.card H = (A + B).card := by
  classical
  let C := A + B
  let Hf := C.addStab
  have hC : C.Nonempty := hA.add hB
  have hHf : Hf.Nonempty := hC.addStab
  have hHpos : 0 < Hf.card := Finset.card_pos.mpr hHf
  have hAcard : A.card ≤ (A + Hf).card :=
    Finset.card_le_card_add_right hHf
  have hBcard : B.card ≤ (B + Hf).card :=
    Finset.card_le_card_add_right hHf
  obtain ⟨alpha, halpha⟩ :=
    (Finset.card_addStab_dvd_card_add_addStab A C)
  obtain ⟨beta, hbeta⟩ :=
    (Finset.card_addStab_dvd_card_add_addStab B C)
  obtain ⟨mu, hmu⟩ := Finset.card_addStab_dvd_card C
  have hk : (A + Hf).card + (B + Hf).card ≤ C.card + Hf.card := by
    have hk' := Finset.add_kneser A B
    simpa [C, Hf] using hk'
  have h2mu3alpha : 2 * mu < 3 * alpha := by
    apply (Nat.mul_lt_mul_right hHpos).mp
    calc
      (2 * mu) * Hf.card = 2 * C.card := by rw [hmu]; ring
      _ < 3 * A.card := by simpa [C] using hleft
      _ ≤ 3 * (A + Hf).card := Nat.mul_le_mul_left 3 hAcard
      _ = (3 * alpha) * Hf.card := by rw [halpha]; ring
  have hmu2beta : mu < 2 * beta := by
    apply (Nat.mul_lt_mul_right hHpos).mp
    calc
      mu * Hf.card = C.card := by rw [hmu]; ring
      _ < 2 * B.card := by simpa [C] using hright
      _ ≤ 2 * (B + Hf).card := Nat.mul_le_mul_left 2 hBcard
      _ = (2 * beta) * Hf.card := by rw [hbeta]; ring
  have hab : alpha + beta ≤ mu + 1 := by
    have hmul : (alpha + beta) * Hf.card ≤ (mu + 1) * Hf.card := by
      calc
        (alpha + beta) * Hf.card =
            (A + Hf).card + (B + Hf).card := by rw [halpha, hbeta]; ring
        _ ≤ C.card + Hf.card := hk
        _ = (mu + 1) * Hf.card := by rw [hmu]; ring
    exact Nat.le_of_mul_le_mul_right hmul hHpos
  have hmuone : mu = 1 := by
    have hmupos : 0 < mu := by
      by_contra hmu0
      have : mu = 0 := Nat.eq_zero_of_not_pos hmu0
      rw [this] at hmu
      simp at hmu
      exact hC.ne_empty hmu
    omega
  have hCcard : C.card = Hf.card := by
    change C.card = C.addStab.card
    rw [hmu, hmuone]
    simp
  have hCne := hC
  obtain ⟨c, hc⟩ := hC
  have hcosub : c +ᵥ Hf ⊆ C := by
    have hs : c +ᵥ Hf ⊆ C + Hf := Finset.vadd_finset_subset_add hc
    simpa [Hf, Finset.add_addStab] using hs
  have hcoeq : C = c +ᵥ Hf := by
    symm
    apply Finset.eq_of_subset_of_card_le hcosub
    rw [Finset.card_vadd_finset, hCcard]
  let H : AddSubgroup G := AddAction.stabilizer G (C : Set G)
  have hcoe : (Hf : Set G) = (H : Set G) := by
    dsimp [Hf, H]
    exact Finset.coe_addStab hCne
  refine ⟨H, c, ?_, ?_⟩
  · intro x hx
    have hxf : x ∈ C := hx
    rw [hcoeq, Finset.mem_vadd_finset] at hxf
    obtain ⟨y, hy, hxy⟩ := hxf
    refine ⟨y, ?_, hxy⟩
    have hys : y ∈ (Hf : Set G) := hy
    rw [hcoe] at hys
    exact hys
  · rw [Nat.card_eq_fintype_card]
    change Fintype.card ↥H = C.card
    calc
      Fintype.card ↥H = Fintype.card ↥Hf :=
        Fintype.card_congr (Equiv.setCongr hcoe.symm)
      _ = Hf.card := Fintype.card_coe Hf
      _ = C.card := hCcard.symm

/-- Balasubramanian--Pandey Proposition 1: if `A+B` is below the
`3|A|/2` threshold while `A` and `B` have comparable sizes, it is contained
in one coset of a subgroup smaller than `3|A|/2`. -/
lemma deshouillersFreiman_kneser_corollary_one
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (_hAB : B.card ≤ A.card)
    (hsmall : 2 * (A + B).card < 3 * A.card)
    (hbalance : 3 * A.card < 4 * B.card) :
    ∃ H : AddSubgroup G, ∃ c : G,
      ((A + B : Finset G) : Set G) ⊆ c +ᵥ (H : Set G) ∧
      2 * Nat.card H < 3 * A.card := by
  have hright : (A + B).card < 2 * B.card := by omega
  obtain ⟨H, c, hcos, hcard⟩ :=
    small_sumset_stabilizer_coset hA hB hsmall hright
  exact ⟨H, c, hcos, by omega⟩

/-- Balasubramanian--Pandey Proposition 2: at the complementary
`2|B|` threshold and under the stated imbalance, the sumset is contained
in one coset of a subgroup of size below `2|B|`. -/
lemma deshouillersFreiman_kneser_corollary_two
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card < 2 * B.card)
    (hbalance : 4 * B.card < 3 * A.card) :
    ∃ H : AddSubgroup G, ∃ c : G,
      ((A + B : Finset G) : Set G) ⊆ c +ᵥ (H : Set G) ∧
      Nat.card H < 2 * B.card := by
  have hleft : 2 * (A + B).card < 3 * A.card := by omega
  obtain ⟨H, c, hcos, hcard⟩ :=
    small_sumset_stabilizer_coset hA hB hleft hsmall
  exact ⟨H, c, hcos, by omega⟩

/-! The two Kneser corollaries initially control a sumset coset.  The next
three elementary lemmas convert that information into the fibre-coset
language used in the Deshouillers--Freiman argument. -/

/-- A finite set is contained in a translate of `H`. -/
def ContainedInAddCoset {G : Type*} [AddGroup G]
    (H : AddSubgroup G) (A : Finset G) : Prop :=
  ∃ a : G, (A : Set G) ⊆ a +ᵥ (H : Set G)

/-- If a nonempty sumset is contained in one `H`-coset, then each summand is
contained in an `H`-coset. -/
lemma summands_subset_cosets_of_sumset_subset_coset
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    {H : AddSubgroup G} {c : G}
    (hAB : ((A + B : Finset G) : Set G) ⊆ c +ᵥ (H : Set G)) :
    ContainedInAddCoset H A ∧ ContainedInAddCoset H B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  refine ⟨⟨a₀, ?_⟩, ⟨b₀, ?_⟩⟩
  · intro a ha
    have hs : a + b₀ ∈ c +ᵥ (H : Set G) :=
      hAB (by exact Finset.add_mem_add (by simpa using ha) hb₀)
    have hs₀ : a₀ + b₀ ∈ c +ᵥ (H : Set G) :=
      hAB (by exact Finset.add_mem_add ha₀ hb₀)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs hs₀
    have hs' : a + b₀ - c ∈ H := by
      convert hs using 1 <;> simp [vadd_eq_add] <;> abel_nf
    have hs₀' : a₀ + b₀ - c ∈ H := by
      convert hs₀ using 1 <;> simp [vadd_eq_add] <;> abel_nf
    have hd : (a + b₀ - c) - (a₀ + b₀ - c) ∈ H :=
      H.sub_mem hs' hs₀'
    refine ⟨a - a₀, ?_, ?_⟩
    · simpa using (show a - a₀ ∈ H by convert hd using 1 <;> abel)
    · simp
  · intro b hb
    have hs : a₀ + b ∈ c +ᵥ (H : Set G) :=
      hAB (by exact Finset.add_mem_add ha₀ (by simpa using hb))
    have hs₀ : a₀ + b₀ ∈ c +ᵥ (H : Set G) :=
      hAB (by exact Finset.add_mem_add ha₀ hb₀)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs hs₀
    have hs' : a₀ + b - c ∈ H := by
      convert hs using 1 <;> simp [vadd_eq_add] <;> abel_nf
    have hs₀' : a₀ + b₀ - c ∈ H := by
      convert hs₀ using 1 <;> simp [vadd_eq_add] <;> abel_nf
    have hd : (a₀ + b - c) - (a₀ + b₀ - c) ∈ H :=
      H.sub_mem hs' hs₀'
    refine ⟨b - b₀, ?_, ?_⟩
    · simpa using (show b - b₀ ∈ H by convert hd using 1 <;> abel)
    · simp

/-- A nonempty set escaping all `H`-cosets contains two elements in
different `H`-cosets. -/
lemma exists_sub_not_mem_of_not_containedInAddCoset
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : AddSubgroup G} {B : Finset G} (hB : B.Nonempty)
    (hnot : ¬ ContainedInAddCoset H B) :
    ∃ y ∈ B, ∃ z ∈ B, z - y ∉ H := by
  obtain ⟨y, hy⟩ := hB
  by_contra hnone
  push Not at hnone
  apply hnot
  refine ⟨y, ?_⟩
  intro z hz
  refine ⟨z - y, hnone y hy z hz, ?_⟩
  simp

/-- If `A` is in one `H`-coset but `B` is not, then two disjoint translates
of `A` occur inside `A+B`. -/
lemma two_mul_card_le_add_of_coset_and_not_coset
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : AddSubgroup G} {A B : Finset G}
    (_hA : A.Nonempty) (hB : B.Nonempty)
    (hAcos : ContainedInAddCoset H A)
    (hBnot : ¬ ContainedInAddCoset H B) :
    2 * A.card ≤ (A + B).card := by
  obtain ⟨a, ha⟩ := hAcos
  obtain ⟨y, hy, z, hz, hzy⟩ :=
    exists_sub_not_mem_of_not_containedInAddCoset hB hBnot
  have hdisj : Disjoint (y +ᵥ A) (z +ᵥ A) := by
    rw [Finset.disjoint_left]
    intro w hwy hwz
    rw [Finset.mem_vadd_finset] at hwy hwz
    obtain ⟨u, hu, rfl⟩ := hwy
    obtain ⟨v, hv, huv⟩ := hwz
    have huH : u - a ∈ H := by
      have hu' := ha (by simpa using hu)
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hu'
      convert hu' using 1 <;> simp [vadd_eq_add] <;> abel_nf
    have hvH : v - a ∈ H := by
      have hv' := ha (by simpa using hv)
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hv'
      convert hv' using 1 <;> simp [vadd_eq_add] <;> abel_nf
    apply hzy
    have huvH : u - v ∈ H := by
      have := H.sub_mem huH hvH
      convert this using 1 <;> abel
    have heq : z - y = u - v := by
      have heq' : z + v = y + u := by simpa [vadd_eq_add] using huv
      calc
        z - y = (z + v) - (y + v) := by abel
        _ = (y + u) - (y + v) := by rw [heq']
        _ = u - v := by abel
    rw [heq]
    exact huvH
  have hsub : (y +ᵥ A) ∪ (z +ᵥ A) ⊆ A + B := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwy | hwz
    · rw [Finset.mem_vadd_finset] at hwy
      obtain ⟨u, hu, rfl⟩ := hwy
      simpa [vadd_eq_add, add_comm] using Finset.add_mem_add hu hy
    · rw [Finset.mem_vadd_finset] at hwz
      obtain ⟨v, hv, rfl⟩ := hwz
      simpa [vadd_eq_add, add_comm] using Finset.add_mem_add hv hz
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_vadd_finset, Finset.card_vadd_finset] at hcard
  simpa [two_mul] using hcard

/-- Uniform fibre-sum alternative.  If `A` is the larger summand, either it
lies in a subgroup coset whose order is less than `3|A|/2`, or its sum with
`B` has the lower bound `2|A+B| \ge |A|+2|B|`.  The small-`B` case is just
translation injectivity; otherwise the two strict failures are exactly the
hypotheses of the Kneser corollary above. -/
lemma small_coset_or_uniform_pair_sum_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) :
    (∃ H : AddSubgroup G,
      ContainedInAddCoset H A ∧ 2 * Nat.card H < 3 * A.card) ∨
      A.card + 2 * B.card ≤ 2 * (A + B).card := by
  by_cases hsmallB : 2 * B.card ≤ A.card
  · right
    have hAadd : A.card ≤ (A + B).card :=
      Finset.card_le_card_add_right hB
    omega
  by_cases hlower : A.card + 2 * B.card ≤ 2 * (A + B).card
  · exact Or.inr hlower
  · left
    have hleft : 2 * (A + B).card < 3 * A.card := by omega
    have hright : (A + B).card < 2 * B.card := by omega
    obtain ⟨H, c, hcoset, hHcard⟩ :=
      small_sumset_stabilizer_coset hA hB hleft hright
    have hsum :=
      summands_subset_cosets_of_sumset_subset_coset hA hB hcoset
    refine ⟨H, hsum.1, ?_⟩
    omega

/-! ### Quantitative translation growth in an unsaturated phase -/

/-- A finite set containing zero and generating the ambient finite group is
not contained in a coset of a proper subgroup.  This is the bridge from the
gcd-normalization in CFP's modular process to the sumset-growth lemma above. -/
lemma notContainedInProperCoset_of_zero_mem_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P)
    (hclosure : AddSubgroup.closure (P : Set G) = ⊤) :
    NotContainedInProperCoset P := by
  intro H hH a hsub
  have hPa : ∀ x ∈ P, ∃ y : G, y ∈ H ∧ a + y = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hsub (by simpa using hx)
    exact ⟨y, by simpa using hy, by simpa using hxy⟩
  obtain ⟨y₀, hy₀, hay₀⟩ := hPa 0 hzero
  have hPsub : (P : Set G) ⊆ H := by
    intro x hx
    obtain ⟨y, hy, hay⟩ := hPa x (by simpa using hx)
    have haH : a ∈ H := by
      have hneg : -y₀ ∈ H := H.neg_mem hy₀
      have haeq : a = -y₀ := by
        rw [← add_left_inj y₀]
        simpa [add_comm] using hay₀
      simpa [haeq] using hneg
    have hsum : a + y ∈ H := H.add_mem haH hy
    simpa [hay] using hsum
  have htop_le : (⊤ : AddSubgroup G) ≤ H := by
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPsub
  exact hH (top_unique htop_le)

/-- Iterated sums of shifts which each introduce at most `e` points introduce
at most `k * e` points. -/
lemma iteratedFinsetSum_almostPeriods_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (U : Finset G) (e k : ℕ) :
    iteratedFinsetSum (almostPeriods U e) k ⊆
      almostPeriods U (k * e) := by
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      rw [iteratedFinsetSum_succ, Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have hab := add_mem_almostPeriods (ih ha) hb
      simpa [Nat.succ_mul, Nat.add_comm] using hab

/-- CFP's first unsaturated-phase estimate.  If the translation set `X`
generates the group, while `U` is below one quarter of the group and `X` is
not much larger than `U`, then some translate by `X` adds at least
`|X| / 16` new points. -/
lemma exists_translationNew_large_of_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {U X : Finset G} (hU : U.Nonempty) (hX : X.Nonempty)
    (hXU : X.card < 4 * U.card)
    (hUG : 4 * U.card < Fintype.card G)
    (hclosure : AddSubgroup.closure (X : Set G) = ⊤) :
    ∃ x ∈ X, X.card ≤ 16 * (translationNew U x).card := by
  classical
  by_contra hnone
  push Not at hnone
  let e := X.card / 16
  let k := 4 * U.card / X.card
  let P := almostPeriods U e
  have hXpos : 0 < X.card := Finset.card_pos.mpr hX
  have hUpos : 0 < U.card := Finset.card_pos.mpr hU
  have hXP : X ⊆ P := by
    intro x hx
    rw [mem_almostPeriods_iff_card_translationNew_le]
    have hsmall := hnone x hx
    dsimp [e]
    omega
  have hzeroP : 0 ∈ P := by simp [P]
  have hclosureP : AddSubgroup.closure (P : Set G) = ⊤ := by
    apply top_unique
    rw [← hclosure]
    apply AddSubgroup.closure_mono
    exact_mod_cast hXP
  have hPcoset : NotContainedInProperCoset P :=
    notContainedInProperCoset_of_zero_mem_closure_eq_top hzeroP hclosureP
  have hkpos : 1 ≤ k := by
    dsimp [k]
    rw [Nat.le_div_iff_mul_le hXpos]
    omega
  have hke : 2 * (k * e) ≤ U.card := by
    have he : 16 * e ≤ X.card := by
      dsimp [e]
      exact Nat.mul_div_le _ _
    have hkX : k * X.card ≤ 4 * U.card := by
      dsimp [k]
      exact Nat.div_mul_le_self _ _
    nlinarith
  have hiterSub : iteratedFinsetSum P k ⊆
      almostPeriods U (k * e) := by
    simpa [P] using iteratedFinsetSum_almostPeriods_subset U e k
  have hAPbound := card_sub_mul_card_almostPeriods_le_sq U (k * e)
  have hden : U.card ≤ 2 * (U.card - k * e) := by omega
  have hAPcard : (almostPeriods U (k * e)).card ≤ 2 * U.card := by
    have hmul : U.card * (almostPeriods U (k * e)).card ≤
        U.card * (2 * U.card) := by
      calc
        U.card * (almostPeriods U (k * e)).card ≤
            2 * ((U.card - k * e) *
              (almostPeriods U (k * e)).card) := by nlinarith
        _ ≤ 2 * U.card ^ 2 := Nat.mul_le_mul_left 2 hAPbound
        _ = U.card * (2 * U.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hUpos
  have hiterCard : (iteratedFinsetSum P k).card ≤ 2 * U.card :=
    (Finset.card_le_card hiterSub).trans hAPcard
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroP⟩ hPcoset k hkpos
  have hiter4 : 2 * (iteratedFinsetSum P k).card ≤
      4 * U.card := by omega
  have htarget : (k + 1) * P.card ≤ 4 * U.card := by
    rcases le_total (2 * Fintype.card G) ((k + 1) * P.card) with hle | hle
    · have hgroup : 2 * Fintype.card G ≤
          2 * (iteratedFinsetSum P k).card := by
        simpa [min_eq_left hle] using hlower
      have : 2 * Fintype.card G ≤ 4 * U.card := hgroup.trans hiter4
      omega
    · have hmain : (k + 1) * P.card ≤
          2 * (iteratedFinsetSum P k).card := by
        simpa [min_eq_right hle] using hlower
      exact hmain.trans hiter4
  have hXcardP : X.card ≤ P.card := Finset.card_le_card hXP
  have hupper : (k + 1) * X.card ≤ 4 * U.card :=
    (Nat.mul_le_mul_left (k + 1) hXcardP).trans htarget
  have hstrict : 4 * U.card < X.card * (k + 1) := by
    dsimp [k]
    exact Nat.lt_mul_div_succ (4 * U.card) hXpos
  nlinarith [hupper]

/-- If the current subset-sum set has fewer than half as many points as the
remaining translations, one of those translations grows it by a factor at
least `3/2`. -/
lemma exists_three_halves_translation_growth
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T X : Finset G} (hT : T.Nonempty) (_hX : X.Nonempty)
    (hsmall : 2 * T.card < X.card) :
    ∃ x ∈ X,
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  let e := T.card / 2
  let P := almostPeriods T e
  have hTpos : 0 < T.card := Finset.card_pos.mpr hT
  have hden : T.card ≤ 2 * (T.card - e) := by
    dsimp [e]
    omega
  have hAPbound := card_sub_mul_card_almostPeriods_le_sq T e
  have hPcard : P.card ≤ 2 * T.card := by
    have hmul : T.card * P.card ≤ T.card * (2 * T.card) := by
      calc
        T.card * P.card ≤ 2 * ((T.card - e) * P.card) := by nlinarith
        _ ≤ 2 * T.card ^ 2 := by
          exact Nat.mul_le_mul_left 2 (by simpa [P] using hAPbound)
        _ = T.card * (2 * T.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hTpos
  have hnot : ¬ X ⊆ P := by
    intro hXP
    have := (Finset.card_le_card hXP).trans hPcard
    omega
  obtain ⟨x, hxX, hxP⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hxX, ?_⟩
  have hnew : e < (translationNew T x).card := by
    contrapose! hxP
    exact mem_almostPeriods_iff_card_translationNew_le.mpr hxP
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  have hunion : (T ∪ Erdos587.addTranslate x T).card =
      T.card + (translationNew T x).card := by
    dsimp [translationNew] at hsdiff ⊢
    rw [Finset.union_comm] at hsdiff
    omega
  rw [hunion]
  dsimp [e] at hnew
  omega

/-! ## Modular completeness from diversity

This is the elementary modular engine used in the lower bound.  It is the
contrapositive of the common-divisor extraction lemma: if subset sums miss a
residue modulo `q`, all but fewer than `q` terms have a common divisor
`d > 1`.  A `k`-diverse set with `q ≤ k` rules this out. -/

/-- `A` is `k`-diverse when every possible common divisor `d > 1` misses at
least `k` elements of `A`. -/
abbrev Diverse (A : Finset ℕ) (k : ℕ) : Prop :=
  DiverseSampling.DiverseNat A k

/-- A finite integer set is contained in a nontrivial arithmetic progression
when all of its elements occupy one residue class modulo some `d ≥ 2`.
The progression may be extended in either direction; only its common
difference matters in the Lev sumset lemma. -/
def ContainedInNontrivialAP (S : Finset ℕ) : Prop :=
  ∃ d a : ℕ, 2 ≤ d ∧ ∀ x ∈ S, x % d = a % d

/-- If a nonempty left summand and `T` have a sumset occupying one residue
class modulo `d > 1`, then `T` itself occupies one residue class. -/
lemma containedInNontrivialAP_of_sum_inOneResidue_right
    {S T : Finset ℕ} {d : ℕ}
    (hS : S.Nonempty) (hd : 2 ≤ d)
    (hST : Erdos13Additive.InOneResidue (S + T) d) :
    ContainedInNontrivialAP T := by
  by_cases hT : T.Nonempty
  · obtain ⟨s, hs⟩ := hS
    obtain ⟨t, ht⟩ := hT
    obtain ⟨r, hr⟩ := hST
    refine ⟨d, t, hd, ?_⟩
    intro x hx
    have hsx : s + x ∈ S + T := by
      rw [Finset.mem_add]
      exact ⟨s, hs, x, hx, rfl⟩
    have hst : s + t ∈ S + T := by
      rw [Finset.mem_add]
      exact ⟨s, hs, t, ht, rfl⟩
    have heq : ((s + x : ℕ) : ZMod d) = ((s + t : ℕ) : ZMod d) :=
      (hr _ hsx).trans (hr _ hst).symm
    have hxt : (x : ZMod d) = (t : ZMod d) := by
      push_cast at heq
      exact add_left_cancel heq
    exact (ZMod.natCast_eq_natCast_iff' x t d).mp hxt
  · refine ⟨d, 0, hd, ?_⟩
    intro x hx
    exact False.elim (hT ⟨x, hx⟩)

/-- Aperiodicity turns the Bardaji--Grynkiewicz progression alternative into
an ordinary interval.  This is the local additive step in Lev's lemma. -/
lemma growth_or_interval_of_notContainedInNontrivialAP_right
    {S T : Finset ℕ} (hS : S.Nonempty) (hT : T.Nonempty)
    (haper : ¬ ContainedInNontrivialAP T) :
    S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨
      ∃ a : ℕ,
        Finset.Icc a (a + (S.card + T.card - 2)) ⊆ S + T := by
  rcases Erdos13Additive.growth_or_long_AP hS hT with hgrowth | hprog
  · exact Or.inl hgrowth
  · right
    obtain ⟨a, d, hd, hAP, hres⟩ := hprog
    have hd1 : d = 1 := by
      by_contra hdne
      have hd2 : 2 ≤ d := by omega
      exact haper
        (containedInNontrivialAP_of_sum_inOneResidue_right hS hd2 hres)
    subst d
    refine ⟨a, ?_⟩
    intro x hx
    apply hAP
    rw [Erdos13Additive.mem_natAP]
    have hScard : 0 < S.card := Finset.card_pos.mpr hS
    have hTcard : 0 < T.card := Finset.card_pos.mpr hT
    refine ⟨x - a, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hx
      omega
    · rw [Finset.mem_Icc] at hx
      simp only [one_mul]
      omega

/-- A positive amount of diversity forces the ordinary subset-sum set to be
aperiodic: it cannot lie in one residue class modulo any `d > 1`. -/
lemma subsetSum_not_containedInNontrivialAP_of_diverse
    {A : Finset ℕ} {k : ℕ} (hk : 0 < k) (hA : Diverse A k) :
    ¬ ContainedInNontrivialAP A.subsetSum := by
  rintro ⟨d, a, hd, hclass⟩
  have hzero : 0 % d = a % d := hclass 0 (by simp)
  have hfilter : (A.filter fun x ↦ ¬d ∣ x).Nonempty := by
    apply Finset.card_pos.mp
    exact hk.trans_le (hA d hd)
  obtain ⟨x, hx⟩ := hfilter
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
  have hxNot : ¬d ∣ x := (Finset.mem_filter.mp hx).2
  have hxSubset : x ∈ A.subsetSum := by
    rw [Finset.mem_subsetSum_iff]
    refine ⟨{x}, ?_, by simp⟩
    simpa using hxA
  have hxmod : x % d = a % d := hclass x hxSubset
  apply hxNot
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [hxmod, ← hzero]
  exact Nat.zero_mod d

/-- A diverse finite set is complete modulo every modulus no larger than its
diversity parameter. -/
lemma modularSubsetSums_complete_of_diverse {A : Finset ℕ} {k q : ℕ}
    [NeZero q] (hq : 0 < q) (hqk : q ≤ k) (hA : Diverse A k) :
    Erdos587.listSubsetSums
        (A.toList.map fun a : ℕ ↦ (a : ZMod q)) = Finset.univ := by
  by_contra hproper
  obtain ⟨d, B, hBA, hd, _hdq, hlen, hdiv⟩ :=
    Erdos587.exists_large_sublist_with_common_divisor_of_not_complete
      hq A.toList hproper
  have hBnodup : B.Nodup := A.nodup_toList.sublist hBA
  have hBsub : B.toFinset ⊆ A := by
    intro b hb
    have hbB : b ∈ B := by simpa using hb
    have hbL : b ∈ A.toList := hBA.subset hbB
    simpa using hbL
  have hdisj : Disjoint B.toFinset (A.filter fun a ↦ ¬d ∣ a) := by
    rw [Finset.disjoint_left]
    intro b hbB hbA
    have hbB' : b ∈ B := by simpa using hbB
    exact (Finset.mem_filter.mp hbA).2 (hdiv b hbB')
  have hunion : B.toFinset ∪ (A.filter fun a ↦ ¬d ∣ a) ⊆ A :=
    Finset.union_subset hBsub (Finset.filter_subset _ _)
  have hcards : B.length + (A.filter fun a ↦ ¬d ∣ a).card ≤ A.card := by
    rw [← List.toFinset_card_of_nodup hBnodup,
      ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hsmall : (A.filter fun a ↦ ¬d ∣ a).card < q := by
    have hAlen : A.toList.length = A.card := Finset.length_toList A
    rw [hAlen] at hlen
    omega
  exact (not_lt_of_ge (hqk.trans (hA d hd))) hsmall

/-! ### Subgroups of a finite cyclic group -/

/-- Every additive subgroup of `ZMod d` consists exactly of the multiples
of a positive divisor `q` of `d`. -/
lemma exists_generator_modulus {d : ℕ} (hd : 0 < d)
    (K : AddSubgroup (ZMod d)) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧
      (∀ x : ZMod d, x ∈ K → q ∣ x.val) ∧
      (∀ i : ℕ, (i * q : ZMod d) ∈ K) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  let V := Finset.univ.filter fun x : ZMod d ↦ x ∈ K ∧ x ≠ 0
  by_cases hV : V.Nonempty
  · obtain ⟨g, hgV, hgmin⟩ := Finset.exists_min_image V ZMod.val hV
    have hgK : g ∈ K := (Finset.mem_filter.mp hgV).2.1
    have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgV).2.2
    let q := g.val
    have hqpos : 0 < q :=
      Nat.pos_of_ne_zero (fun h ↦ hg0 ((ZMod.val_eq_zero g).mp h))
    have hqd : q < d := g.val_lt
    have hmin : ∀ x : ZMod d, x ∈ K → x ≠ 0 → q ≤ x.val := by
      intro x hxK hx0
      exact hgmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hx0⟩)
    have hcastg : (q : ZMod d) = g := ZMod.natCast_zmod_val g
    have hqdvd : q ∣ d := by
      let r := d % q
      have hrq : r < q := Nat.mod_lt d hqpos
      have hrd : r < d := hrq.trans hqd
      have hsumZ : ((d / q * q : ℕ) : ZMod d) + (r : ZMod d) = 0 := by
        have hsum := congrArg (fun n : ℕ ↦ (n : ZMod d)) (Nat.div_add_mod' d q)
        push_cast at hsum
        simpa [r] using hsum
      have hcast : (r : ZMod d) = -((d / q : ℕ) • g) := by
        rw [← hcastg]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        apply (eq_neg_iff_add_eq_zero).2
        simpa [add_comm] using hsumZ
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.neg_mem (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    refine ⟨q, hqpos, hqdvd, ?_, ?_⟩
    · intro x hxK
      let r := x.val % q
      have hrq : r < q := Nat.mod_lt x.val hqpos
      have hrd : r < d := hrq.trans hqd
      have hmul : x.val / q * q ≤ x.val := by
        simpa [mul_comm] using Nat.mul_div_le x.val q
      have hdecomp : x.val % q + x.val / q * q = x.val := by
        simpa [mul_comm] using Nat.mod_add_div x.val q
      have hsub : x.val - x.val / q * q = r := by
        dsimp [r]
        omega
      have hcast : (r : ZMod d) = x - (x.val / q : ℕ) • g := by
        calc
          (r : ZMod d) = ((x.val - x.val / q * q : ℕ) : ZMod d) := by rw [hsub]
          _ = (x.val : ZMod d) - (x.val / q * q : ℕ) := by
            rw [Nat.cast_sub hmul]
          _ = x - (x.val / q : ℕ) • g := by
            rw [ZMod.natCast_zmod_val x, Nat.cast_mul, hcastg]
            simp [nsmul_eq_mul]
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.sub_mem hxK (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    · intro i
      have hi : (i * q : ZMod d) = i • g := by
        rw [← hcastg]
        simp [nsmul_eq_mul]
      rw [hi]
      exact K.nsmul_mem hgK i
  · refine ⟨d, hd, dvd_rfl, ?_, ?_⟩
    · intro x hxK
      have hx0 : x = 0 := by
        by_contra hxne
        exact hV ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hxne⟩⟩
      rw [hx0]
      simp
    · intro i
      simp

lemma subgroup_eq_zmultiples_of_generator_modulus
    {d q : ℕ} [NeZero d] (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    H = AddSubgroup.zmultiples (q : ZMod d) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := hHdiv x hx
    rw [← ZMod.natCast_zmod_val x, hi, Nat.cast_mul]
    change ((q : ZMod d) * (i : ZMod d)) ∈
      AddSubgroup.zmultiples (q : ZMod d)
    rw [mul_comm]
    simpa [nsmul_eq_mul] using
      ((AddSubgroup.zmultiples (q : ZMod d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q : ZMod d)) i)
  · intro x hx
    obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    cases i with
    | ofNat i =>
        simpa [nsmul_eq_mul, mul_comm] using hmult i
    | negSucc i =>
        have hi : (i + 1) • (q : ZMod d) ∈ H := by
          simpa [nsmul_eq_mul, mul_comm] using hmult (i + 1)
        have hneg := H.neg_mem hi
        convert hneg using 1 <;> simp [nsmul_eq_mul] <;> ring

lemma natCard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (_hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    Nat.card H = d / q := by
  let : NeZero d := ⟨hd.ne'⟩
  rw [subgroup_eq_zmultiples_of_generator_modulus H hHdiv hmult,
    Nat.card_zmultiples, ZMod.addOrderOf_coe q hd.ne']
  have hgcd : d.gcd q = q := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr hqd
  rw [hgcd]

lemma ncard_addSubgroup_eq_natCard {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : (H : Set G).ncard = Nat.card H := by
  rw [← Set.ncard_univ H]
  apply Set.ncard_congr (fun x hx ↦ (⟨x, hx⟩ : H))
  · simp
  · intro a b ha hb hab
    exact congrArg Subtype.val hab
  · intro b _
    exact ⟨b.1, b.2, Subtype.ext rfl⟩

lemma ncard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    (H : Set (ZMod d)).ncard = d / q := by
  rw [ncard_addSubgroup_eq_natCard H]
  exact natCard_subgroup_of_generator_modulus hd hq hqd H hHdiv hmult

/-! ### The ordered rank-one inverse theorem

This is the Lev--Smieliński/Ruzsa integer small-doubling theorem used after
rectifying a small subset of a finite cyclic group.  It is kept here rather
than imported from Erdos 344 because that file imports this development. -/

private lemma integer_small_sumset_contained_AP_of_diameter_le
    {S T : Finset ℕ} {m : ℕ}
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hScard : S.card = m) (hTcard : T.card = m) (hm : 30 ≤ m)
    (hsmall : 10 * (S + T).card ≤ 21 * m)
    (hdiam : S.max' hSne - S.min' hSne ≤ T.max' hTne - T.min' hTne) :
    ∃ a b d L : ℕ, 0 < d ∧ 10 * L ≤ 11 * m + 10 ∧
      S ⊆ Erdos13Additive.natAP a d L ∧
      T ⊆ Erdos13Additive.natAP b d L := by
  let s := S.min' hSne
  let t := T.min' hTne
  let sM := S.max' hSne
  let tM := T.max' hTne
  let u := sM - s
  let v := tM - t
  have hsS : s ∈ S := S.min'_mem hSne
  have htT : t ∈ T := T.min'_mem hTne
  have hsMS : sM ∈ S := S.max'_mem hSne
  have htMT : tM ∈ T := T.max'_mem hTne
  have hSmin : ∀ x ∈ S, s ≤ x := fun x hx ↦ S.min'_le x hx
  have hTmin : ∀ x ∈ T, t ≤ x := fun x hx ↦ T.min'_le x hx
  have hSmax : ∀ x ∈ S, x ≤ sM := fun x hx ↦ S.le_max' x hx
  have hTmax : ∀ x ∈ T, x ≤ tM := fun x hx ↦ T.le_max' x hx
  have huv : u ≤ v := by simpa [u, v, s, t, sM, tM] using hdiam
  have hvpos : 0 < v := by
    by_contra hv
    have hvzero : v = 0 := Nat.eq_zero_of_not_pos hv
    have hTeq : T = {t} := by
      ext x
      constructor
      · intro hx
        have hxmin := hTmin x hx
        have hxmax := hTmax x hx
        have htMt : tM = t := by dsimp [v] at hvzero; omega
        simp only [Finset.mem_singleton]
        omega
      · intro hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact htT
    have : T.card = 1 := by simp [hTeq]
    omega
  let S₁ := Erdos13Additive.normalizeNat S s 1
  let T₁ := Erdos13Additive.normalizeNat T t 1
  let W := S₁ ∪ T₁
  let d := W.gcd (fun n : ℕ ↦ n)
  have huS₁ : u ∈ S₁ := by
    have h := Erdos13Additive.top_mem_normalizeNat (m := s) (d := 1) hsMS
    simpa [S₁, u, sM, s] using h
  have hvT₁ : v ∈ T₁ := by
    have h := Erdos13Additive.top_mem_normalizeNat (m := t) (d := 1) htMT
    simpa [T₁, v, tM, t] using h
  have hvW : v ∈ W := Finset.mem_union_right S₁ hvT₁
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz := (Finset.gcd_eq_zero_iff.mp hd) v hvW
    omega
  have hSdiv : ∀ x ∈ S, d ∣ x - s := by
    intro x hx
    apply Finset.gcd_dvd
    apply Finset.mem_union_left T₁
    apply Erdos13Additive.mem_normalizeNat.mpr
    exact ⟨x, hx, by simp⟩
  have hTdiv : ∀ x ∈ T, d ∣ x - t := by
    intro x hx
    apply Finset.gcd_dvd
    apply Finset.mem_union_right S₁
    apply Erdos13Additive.mem_normalizeNat.mpr
    exact ⟨x, hx, by simp⟩
  have hdv : d ∣ v := Finset.gcd_dvd hvW
  have hdvle : d ≤ v := Nat.le_of_dvd hvpos hdv
  have hvqpos : 0 < v / d := Nat.div_pos hdvle hdpos
  let A := Erdos13Additive.normalizeNat S s d
  let B := Erdos13Additive.normalizeNat T t d
  have hAint : A ⊆ Finset.Icc 0 (u / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hSmin x hx, hSmax x hx⟩
  have hBint : B ⊆ Finset.Icc 0 (v / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hTmin x hx, hTmax x hx⟩
  have hAzero : 0 ∈ A := Erdos13Additive.zero_mem_normalizeNat hsS
  have hBzero : 0 ∈ B := Erdos13Additive.zero_mem_normalizeNat htT
  have hAtop : u / d ∈ A := by
    simpa [A, u, sM, s] using
      (Erdos13Additive.top_mem_normalizeNat (m := s) (d := d) hsMS)
  have hBtop : v / d ∈ B := by
    simpa [B, v, tM, t] using
      (Erdos13Additive.top_mem_normalizeNat (m := t) (d := d) htMT)
  have hqorder : u / d ≤ v / d := Nat.div_le_div_right huv
  have hABW : A ∪ B = W.image (fun z ↦ z / d) := by
    ext q
    simp only [A, B, W, S₁, T₁, Erdos13Additive.normalizeNat,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact ⟨x - s, Or.inl ⟨x, hx, by simp⟩, rfl⟩
      · exact ⟨y - t, Or.inr ⟨y, hy, by simp⟩, rfl⟩
    · rintro ⟨z, (⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩), rfl⟩
      · left
        refine ⟨x, hx, ?_⟩
        simpa using congrArg (fun n ↦ n / d) hxz
      · right
        refine ⟨y, hy, ?_⟩
        simpa using congrArg (fun n ↦ n / d) hyz
  have hWgcd : W.gcd (fun z ↦ z / d) = 1 := by
    exact Finset.gcd_div_id_eq_one hvW hvpos.ne'
  have hABgcdNat : (A ∪ B).gcd (fun n : ℕ ↦ n) = 1 := by
    rw [hABW, Finset.gcd_image]
    exact hWgcd
  have hABgcdInt : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [Erdos13Additive.nat_int_finset_gcd, hABgcdNat]
    norm_num
  have hAcard : A.card = m := by
    rw [Erdos13Additive.card_normalizeNat hdpos hSmin hSdiv, hScard]
  have hBcard : B.card = m := by
    rw [Erdos13Additive.card_normalizeNat hdpos hTmin hTdiv, hTcard]
  have hsumcard : (A + B).card = (S + T).card := by
    symm
    exact Erdos13Additive.card_sumset_eq_card_normalized
      hdpos hSmin hTmin hSdiv hTdiv
  have hruzsa := Erdos13Additive.ruzsa_normalized_diameter_bound
    hAint hBint hqorder hvqpos hAzero hAtop hBzero hBtop hABgcdInt
  have hthree : (A + B).card < 3 * m - 3 := by
    rw [hsumcard]
    omega
  have hdiameter : m + v / d ≤ (A + B).card := by
    rw [hAcard, hBcard] at hruzsa
    by_contra hnot
    have hfirst : (A + B).card < m + v / d := Nat.lt_of_not_ge hnot
    have hminlt : (A + B).card <
        min (m + v / d) (m + m + min m m - 3) := by
      apply lt_min
      · exact hfirst
      · have heq : m + m + min m m - 3 = 3 * m - 3 := by
          simp only [min_self]
          omega
        simpa only [heq] using hthree
    exact (not_lt_of_ge hruzsa) hminlt
  have hvbound : 10 * (v / d + 1) ≤ 11 * m + 10 := by
    rw [hsumcard] at hdiameter
    omega
  refine ⟨s, t, d, v / d + 1, hdpos, hvbound, ?_, ?_⟩
  · intro x hx
    have hqmem : (x - s) / d ∈ A :=
      Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hqle : (x - s) / d ≤ v / d :=
      (Finset.mem_Icc.mp (hAint hqmem)).2.trans hqorder
    apply Erdos13Additive.mem_natAP.mpr
    refine ⟨(x - s) / d, by omega, ?_⟩
    have hsx : s ≤ x := hSmin x hx
    calc
      s + d * ((x - s) / d) = s + (x - s) := by
        rw [Nat.mul_div_cancel' (hSdiv x hx)]
      _ = x := Nat.add_sub_of_le hsx
  · intro x hx
    have hqmem : (x - t) / d ∈ B :=
      Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hqle : (x - t) / d ≤ v / d :=
      (Finset.mem_Icc.mp (hBint hqmem)).2
    apply Erdos13Additive.mem_natAP.mpr
    refine ⟨(x - t) / d, by omega, ?_⟩
    have htx : t ≤ x := hTmin x hx
    calc
      t + d * ((x - t) / d) = t + (x - t) := by
        rw [Nat.mul_div_cancel' (hTdiv x hx)]
      _ = x := Nat.add_sub_of_le htx

/-- Symmetric small-doubling containment lemma. -/
lemma integer_small_sumset_contained_AP
    {S T : Finset ℕ} {m : ℕ}
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hScard : S.card = m) (hTcard : T.card = m) (hm : 30 ≤ m)
    (hsmall : 10 * (S + T).card ≤ 21 * m) :
    ∃ a d L : ℕ, 0 < d ∧ 10 * L ≤ 11 * m + 10 ∧
      S ⊆ Erdos13Additive.natAP a d L := by
  rcases le_total (S.max' hSne - S.min' hSne) (T.max' hTne - T.min' hTne) with h | h
  · obtain ⟨a, -, d, L, hd, hL, hS, -⟩ :=
      integer_small_sumset_contained_AP_of_diameter_le
        hSne hTne hScard hTcard hm hsmall h
    exact ⟨a, d, L, hd, hL, hS⟩
  · obtain ⟨-, a, d, L, hd, hL, -, hS⟩ :=
      integer_small_sumset_contained_AP_of_diameter_le
        hTne hSne hTcard hScard hm (by simpa [add_comm] using hsmall) h
    exact ⟨a, d, L, hd, hL, hS⟩

/-- A concrete order-two Freiman model of a cyclic finset by nonnegative
integers. -/
def HasNatFreimanModel {t : ℕ} [NeZero t] (B : Finset (ZMod t)) : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ A.card = B.card ∧
    A.image (fun x : ℕ ↦ (x : ZMod t)) = B ∧
    (A + A).card = (B + B).card

/-- Two functions with the same collision relation on a finite set have
images of the same cardinality. -/
lemma card_image_eq_card_image_of_eq_iff
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (hker : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
  classical
  let pre : ∀ b : β, b ∈ S.image f → α := fun b hb ↦
    Classical.choose (Finset.mem_image.mp hb)
  have hpre_mem : ∀ b hb, pre b hb ∈ S := fun b hb ↦
    (Classical.choose_spec (Finset.mem_image.mp hb)).1
  have hf_pre : ∀ b hb, f (pre b hb) = b := fun b hb ↦
    (Classical.choose_spec (Finset.mem_image.mp hb)).2
  apply Finset.card_bij (fun b hb ↦ g (pre b hb))
  · intro b hb
    exact Finset.mem_image.mpr ⟨pre b hb, hpre_mem b hb, rfl⟩
  · intro b₁ hb₁ b₂ hb₂ heq
    have hf : f (pre b₁ hb₁) = f (pre b₂ hb₂) :=
      (hker _ (hpre_mem b₁ hb₁) _ (hpre_mem b₂ hb₂)).mpr heq
    simpa [hf_pre] using hf
  · intro c hc
    obtain ⟨x, hxS, hxc⟩ := Finset.mem_image.mp hc
    have hfx : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
    refine ⟨f x, hfx, ?_⟩
    have hf : f (pre (f x) hfx) = f x := hf_pre (f x) hfx
    have hg : g (pre (f x) hfx) = g x :=
      (hker _ (hpre_mem (f x) hfx) _ hxS).mp hf
    exact hg.trans hxc

def zmodNatAP (t a d L : ℕ) [NeZero t] : Finset (ZMod t) :=
  (Erdos13Additive.natAP a d L).image fun x : ℕ ↦ (x : ZMod t)

lemma natFreimanModel_short_zmodAP
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 30 ≤ B.card)
    (hsmall : 10 * (B + B).card ≤ 21 * B.card) :
    ∃ a d L : ℕ, 0 < d ∧ 10 * L ≤ 11 * B.card + 10 ∧
      B ⊆ zmodNatAP t a d L := by
  obtain ⟨A, hAne, hAcard, hAB, hsum⟩ := hmodel
  obtain ⟨a, d, L, hd, hL, hAprog⟩ :=
    integer_small_sumset_contained_AP hAne hAne hAcard hAcard hcard
      (by simpa [hsum, hAcard] using hsmall)
  refine ⟨a, d, L, hd, by simpa [hAcard] using hL, ?_⟩
  intro x hx
  rw [← hAB] at hx
  obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y, hAprog hyA, rfl⟩


/-! ### Cyclic coset progressions -/

/-- The finite carrier of an additive subgroup of a nontrivial cyclic group. -/
noncomputable def subgroupFinset {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) : Finset (ZMod b) := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ H

@[simp] lemma mem_subgroupFinset {b : ℕ} [NeZero b]
    {H : AddSubgroup (ZMod b)} {x : ZMod b} :
    x ∈ subgroupFinset H ↔ x ∈ H := by
  simp [subgroupFinset]

lemma card_subgroupFinset {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) :
    (subgroupFinset H).card = Nat.card H := by
  classical
  have heq : subgroupFinset H = (H : Set (ZMod b)).toFinite.toFinset := by
    ext x
    simp [subgroupFinset]
  rw [heq, ← ncard_addSubgroup_eq_natCard H]
  exact (Set.ncard_eq_toFinset_card (H : Set (ZMod b))).symm

/-- A subset occupying more than half of a cyclic subgroup coset has the
whole subgroup as its difference set.  The fibre theorem supplies the
stronger density `2 * |H| < 3 * |A|`; this half-density form is the exact
input used by the subsequent Ruzsa covering step. -/
lemma dense_coset_sub_eq_subgroup
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    {A : Finset (ZMod b)}
    (hcos : ContainedInAddCoset H A)
    (hdense : Nat.card H < 2 * A.card) :
    A - A = subgroupFinset H := by
  classical
  obtain ⟨c, hc⟩ := hcos
  let E : Finset (ZMod b) := (-c) +ᵥ A
  have hEA : E.card = A.card := by simp [E]
  have hEH : E ⊆ subgroupFinset H := by
    intro x hx
    rw [Finset.mem_vadd_finset] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [mem_subgroupFinset]
    have ha' := hc (by simpa using ha)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ha'
    convert ha' using 1 <;> simp [vadd_eq_add]
  have hcardH : (subgroupFinset H).card < E.card + E.card := by
    simpa [card_subgroupFinset, hEA, two_mul] using hdense
  have hsub : subgroupFinset H ⊆ E - E := by
    intro h hh
    let T : Finset (ZMod b) := h +ᵥ E
    have hTH : T ⊆ subgroupFinset H := by
      intro x hx
      rw [Finset.mem_vadd_finset] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [mem_subgroupFinset] at hh ⊢
      exact H.add_mem hh (mem_subgroupFinset.mp (hEH he))
    have hinter : (E ∩ T).Nonempty := by
      apply Finset.inter_nonempty_of_card_lt_card_add_card hEH hTH
      simpa [T] using hcardH
    let z := hinter.choose
    have hz := Finset.mem_inter.mp hinter.choose_spec
    have hzE : z ∈ E := hz.1
    have hzT : z ∈ T := hz.2
    rw [Finset.mem_vadd_finset] at hzT
    obtain ⟨e, heE, heq⟩ := hzT
    apply Finset.mem_sub.mpr
    refine ⟨z, hzE, e, heE, ?_⟩
    rw [← heq]
    simp only [vadd_eq_add, sub_eq_add_neg]
    abel
  have hrev : E - E ⊆ subgroupFinset H := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    rw [mem_subgroupFinset]
    exact H.sub_mem (mem_subgroupFinset.mp (hEH ha))
      (mem_subgroupFinset.mp (hEH hb))
  have hEE : E - E = subgroupFinset H :=
    Finset.Subset.antisymm hrev hsub
  rw [← hEE]
  dsimp [E]
  ext x
  simp only [Finset.mem_sub, Finset.mem_vadd_finset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨-c + a, ⟨a, ha, rfl⟩, -c + b, ⟨b, hb, rfl⟩, by abel⟩
  · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
    refine ⟨a', ha', b', hb', ?_⟩
    simp only [vadd_eq_add]
    abel

/-- The union of the `length` consecutive `H`-cosets
`a + i • d + H` in a cyclic group.  Repetitions are deliberately allowed in
the parameterization and removed by the outer image. -/
noncomputable def cyclicCosetProgression {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (a d : ZMod b) (length : ℕ) :
    Finset (ZMod b) :=
  ((Finset.range length) ×ˢ subgroupFinset H).image
    (fun p ↦ a + p.1 • d + p.2)

/-- Properness means that the displayed constituent cosets are pairwise
distinct. -/
def IsProperCyclicCosetProgression {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (a d : ZMod b) (length : ℕ) : Prop :=
  ∀ i < length, ∀ j < length,
    (a + i • d) - (a + j • d) ∈ H → i = j

/-- Natural multiples below the additive order of an element are distinct. -/
lemma nsmul_injective_below_addOrderOf {t : ℕ} [NeZero t]
    (d : ZMod t) {i j : ℕ}
    (hi : i < addOrderOf d) (hj : j < addOrderOf d)
    (heq : i • d = j • d) : i = j := by
  rcases le_total j i with hji | hij
  · have hz : (i - j) • d = 0 := by
      rw [sub_nsmul d hji, heq]
      simp
    have hdvd : addOrderOf d ∣ i - j :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    have hlt : i - j < addOrderOf d :=
      lt_of_le_of_lt (Nat.sub_le i j) hi
    have hzero : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hz : (j - i) • d = 0 := by
      rw [sub_nsmul d hij, heq]
      simp
    have hdvd : addOrderOf d ∣ j - i :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    have hlt : j - i < addOrderOf d :=
      lt_of_le_of_lt (Nat.sub_le j i) hj
    have hzero : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-- A progression shorter than the order of its step is proper modulo the
trivial subgroup. -/
lemma isProperCyclicCosetProgression_bot_of_le_addOrderOf
    {t length : ℕ} [NeZero t] (a d : ZMod t)
    (hlength : length ≤ addOrderOf d) :
    IsProperCyclicCosetProgression (⊥ : AddSubgroup (ZMod t))
      a d length := by
  intro i hi j hj hbot
  have heq : i • d = j • d := by
    simpa only [AddSubgroup.mem_bot, add_sub_add_left_eq_sub,
      sub_eq_zero] using hbot
  exact nsmul_injective_below_addOrderOf d
    (hi.trans_le hlength) (hj.trans_le hlength) heq

lemma mem_cyclicCosetProgression_iff {b : ℕ} [NeZero b]
    {H : AddSubgroup (ZMod b)} {a d x : ZMod b} {length : ℕ} :
    x ∈ cyclicCosetProgression H a d length ↔
      ∃ i < length, x - (a + i • d) ∈ H := by
  classical
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hi : p.1 < length := by
      simpa using (Finset.mem_product.mp hp).1
    have hh : p.2 ∈ H := by
      simpa using (Finset.mem_product.mp hp).2
    refine ⟨p.1, hi, ?_⟩
    convert hh using 1 <;> abel
  · rintro ⟨i, hi, hx⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, x - (a + i • d)), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨Finset.mem_range.mpr hi, mem_subgroupFinset.mpr hx⟩
    · simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

lemma zmodNatAP_subset_cyclicCosetProgression_bot
    {t a d L : ℕ} [NeZero t] :
    zmodNatAP t a d L ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod t))
        (a : ZMod t) (d : ZMod t) L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, rfl⟩ := Erdos13Additive.mem_natAP.mp hy
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i, hi, ?_⟩
  simp [nsmul_eq_mul]
  ring

/-- A rectified cyclic set is either contained in a short proper ordinary
progression or is dense in a single coset of the subgroup generated by the
progression step.  This is the cyclic form of the integer inverse theorem
needed after producing a Freiman model. -/
lemma natFreimanModel_cyclic_progression_dichotomy
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 30 ≤ B.card)
    (hsmall : 10 * (B + B).card ≤ 21 * B.card) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression H a d L ∧
      IsProperCyclicCosetProgression H a d L ∧
      ((H = ⊥ ∧ 10 * L ≤ 11 * B.card + 10) ∨
        (L = 1 ∧ 5 * Nat.card H ≤ 6 * B.card)) := by
  obtain ⟨a, d, L, _hd, hL, hB⟩ :=
    natFreimanModel_short_zmodAP hmodel hcard hsmall
  by_cases hproper : L ≤ addOrderOf (d : ZMod t)
  · refine ⟨⊥, (a : ZMod t), (d : ZMod t), L,
      hB.trans zmodNatAP_subset_cyclicCosetProgression_bot,
      isProperCyclicCosetProgression_bot_of_le_addOrderOf _ _ hproper,
      Or.inl ⟨rfl, hL⟩⟩
  · have horder : addOrderOf (d : ZMod t) ≤ L := le_of_not_ge hproper
    let H : AddSubgroup (ZMod t) := AddSubgroup.zmultiples (d : ZMod t)
    refine ⟨H, (a : ZMod t), (d : ZMod t), 1, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hB hx)
      obtain ⟨i, _hi, rfl⟩ := Erdos13Additive.mem_natAP.mp hy
      apply mem_cyclicCosetProgression_iff.mpr
      refine ⟨0, by omega, ?_⟩
      have hiH : i • (d : ZMod t) ∈ H := by
        exact H.nsmul_mem (AddSubgroup.mem_zmultiples (d : ZMod t)) i
      convert hiH using 1 <;> simp [nsmul_eq_mul] <;> ring
    · intro i hi j hj _
      omega
    · change 5 * Nat.card (AddSubgroup.zmultiples (d : ZMod t)) ≤
        6 * B.card
      rw [Nat.card_zmultiples]
      omega

/-- In the sparse range, the dense single-coset branch of the rectified
cyclic dichotomy is either a coset of a proper subgroup or is impossible.
Thus a rectified sparse set which is not trapped in a proper coset lies in a
short proper ordinary progression modulo `t`. -/
lemma natFreimanModel_progression_or_properSubgroup
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 30 ≤ B.card)
    (hsmall : 10 * (B + B).card ≤ 21 * B.card)
    (hsparse : 6 * B.card < 5 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧ ∃ a : ZMod t,
      (B : Set (ZMod t)) ⊆ a +ᵥ (K : Set (ZMod t))) ∨
    (∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L ∧
      IsProperCyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L ∧
      10 * L ≤ 11 * B.card + 10) := by
  obtain ⟨H, a, d, L, hB, hproper, hcase⟩ :=
    natFreimanModel_cyclic_progression_dichotomy hmodel hcard hsmall
  rcases hcase with ⟨rfl, hL⟩ | ⟨rfl, hHcard⟩
  · exact Or.inr ⟨a, d, L, hB, hproper, hL⟩
  · by_cases hH : H = ⊤
    · subst H
      have hcardTop : Nat.card (⊤ : AddSubgroup (ZMod t)) = t := by simp
      rw [hcardTop] at hHcard
      omega
    · left
      refine ⟨H, hH, a, ?_⟩
      intro x hx
      have hx' := hB hx
      obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp hx'
      have hi0 : i = 0 := by omega
      subst i
      rw [Set.mem_vadd_set]
      refine ⟨x - a, ?_, ?_⟩
      · simpa using hxi
      · simp [vadd_eq_add, sub_eq_add_neg]

lemma cyclicCosetProgression_card_le {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (a d : ZMod b) (length : ℕ) :
    (cyclicCosetProgression H a d length).card ≤
      length * Nat.card H := by
  classical
  calc
    (cyclicCosetProgression H a d length).card ≤
        ((Finset.range length) ×ˢ subgroupFinset H).card :=
      Finset.card_image_le
    _ = length * Nat.card H := by
      rw [Finset.card_product, Finset.card_range, card_subgroupFinset]

lemma cyclicCosetProgression_card_eq_of_proper
    {b length : ℕ} [NeZero b] (H : AddSubgroup (ZMod b))
    (a d : ZMod b) (hproper : IsProperCyclicCosetProgression H a d length) :
    (cyclicCosetProgression H a d length).card =
      length * Nat.card H := by
  classical
  rw [cyclicCosetProgression, Finset.card_image_iff.mpr]
  · rw [Finset.card_product, Finset.card_range, card_subgroupFinset]
  · intro p hp q hq hpq
    have hpi : p.1 < length :=
      Finset.mem_range.mp (Finset.mem_product.mp hp).1
    have hqi : q.1 < length :=
      Finset.mem_range.mp (Finset.mem_product.mp hq).1
    have hpH : p.2 ∈ H :=
      mem_subgroupFinset.mp (Finset.mem_product.mp hp).2
    have hqH : q.2 ∈ H :=
      mem_subgroupFinset.mp (Finset.mem_product.mp hq).2
    change a + p.1 • d + p.2 = a + q.1 • d + q.2 at hpq
    have hdiff : (a + p.1 • d) - (a + q.1 • d) ∈ H := by
      have heq : (a + p.1 • d) - (a + q.1 • d) = q.2 - p.2 := by
        calc
          (a + p.1 • d) - (a + q.1 • d) =
              (a + p.1 • d + p.2) - p.2 -
                (a + q.1 • d) := by abel
          _ = (a + q.1 • d + q.2) - p.2 -
                (a + q.1 • d) := by rw [hpq]
          _ = q.2 - p.2 := by abel
      rw [heq]
      exact H.sub_mem hqH hpH
    have hij : p.1 = q.1 := hproper p.1 hpi q.1 hqi hdiff
    rcases p with ⟨pi, ph⟩
    rcases q with ⟨qi, qh⟩
    simp only [Prod.fst, Prod.snd] at hij hpq ⊢
    subst qi
    simp only [Prod.mk.injEq, true_and]
    exact add_left_cancel hpq

lemma cyclicCosetProgression_nonempty_of_length_pos
    {b length : ℕ} [NeZero b] (H : AddSubgroup (ZMod b))
    (a d : ZMod b) (hlength : 0 < length) :
    (cyclicCosetProgression H a d length).Nonempty := by
  refine ⟨a, mem_cyclicCosetProgression_iff.mpr ⟨0, hlength, ?_⟩⟩
  simp

lemma cyclicCosetProgression_zero {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (a d : ZMod b) :
    cyclicCosetProgression H a d 0 = ∅ := by
  simp [cyclicCosetProgression]

lemma cyclicCosetProgression_succ {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (a d : ZMod b) (length : ℕ) :
    cyclicCosetProgression H a d (length + 1) =
      cyclicCosetProgression H a d length ∪
        (subgroupFinset H).image (fun h ↦ a + length • d + h) := by
  classical
  ext x
  simp only [mem_cyclicCosetProgression_iff, Finset.mem_union,
    Finset.mem_image, mem_subgroupFinset]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hil : i < length
    · exact Or.inl ⟨i, hil, hx⟩
    · right
      have hieq : i = length := by omega
      subst i
      refine ⟨x - (a + length • d), hx, ?_⟩
      abel
  · rintro (⟨i, hi, hx⟩ | ⟨h, hh, rfl⟩)
    · exact ⟨i, by omega, hx⟩
    · refine ⟨length, by omega, ?_⟩
      convert hh using 1 <;> abel

/-- A finite ordinary progression `a, a+q, ..., a+q(length-1)`. -/
def natProgression (a q length : ℕ) : Finset ℕ :=
  (Finset.range length).image fun i ↦ a + q * i

lemma mem_natProgression_iff {a q length x : ℕ} :
    x ∈ natProgression a q length ↔
      ∃ i < length, x = a + q * i := by
  simp [natProgression, eq_comm]

lemma card_natProgression {a q length : ℕ} (hq : 0 < q) :
    (natProgression a q length).card = length := by
  rw [natProgression, Finset.card_image_iff.mpr (by
    intro i hi j hj hij
    apply mul_left_cancel₀ hq.ne'
    exact Nat.add_left_cancel hij), Finset.card_range]

/-- Least nonnegative integer representatives of a finite subset of a
nontrivial cyclic group. -/
def zmodValues {b : ℕ} [NeZero b] (R : Finset (ZMod b)) : Finset ℕ :=
  R.image ZMod.val

lemma mem_zmodValues_iff {b : ℕ} [NeZero b]
    {R : Finset (ZMod b)} {x : ℕ} :
    x ∈ zmodValues R ↔ ∃ r ∈ R, r.val = x := by
  simp [zmodValues]

lemma card_zmodValues {b : ℕ} [NeZero b] (R : Finset (ZMod b)) :
    (zmodValues R).card = R.card := by
  rw [zmodValues, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact ZMod.val_injective b hxy

/-- A cyclic set contained in the lower open half of the standard residue
interval has a concrete order-two Freiman model in the natural numbers.
Every sum of two least representatives is still below the modulus, so
reduction modulo `t` is injective on the ordinary sumset. -/
lemma hasNatFreimanModel_of_double_val_lt
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)} (hB : B.Nonempty)
    (hnowrap : ∀ x ∈ B, 2 * x.val < t) : HasNatFreimanModel B := by
  classical
  let A := zmodValues B
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x.val, mem_zmodValues_iff.mpr ⟨x, hx, rfl⟩⟩
  have hAcard : A.card = B.card := card_zmodValues B
  have hAB : A.image (fun x : ℕ ↦ (x : ZMod t)) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hyA, hyx⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hzB, hzy⟩ := mem_zmodValues_iff.mp hyA
      subst y
      have hcast : (z.val : ZMod t) = z := ZMod.natCast_zmod_val z
      rw [hcast] at hyx
      simpa [← hyx] using hzB
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨x.val, mem_zmodValues_iff.mpr ⟨x, hx, rfl⟩, ?_⟩
      exact ZMod.natCast_zmod_val x
  have hsumBound : ∀ s ∈ A + A, s < t := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨x, hxB, hxa⟩ := mem_zmodValues_iff.mp ha
    obtain ⟨y, hyB, hyb⟩ := mem_zmodValues_iff.mp hb
    subst a
    subst b
    have hx := hnowrap x hxB
    have hy := hnowrap y hyB
    omega
  have hinj : Set.InjOn (fun s : ℕ ↦ (s : ZMod t))
      (↑(A + A) : Set ℕ) := by
    intro a ha b hb hab
    apply CharP.natCast_injOn_Iio (ZMod t) t
    · exact hsumBound a ha
    · exact hsumBound b hb
    · exact hab
  have himage : (A + A).image (fun s : ℕ ↦ (s : ZMod t)) = B + B := by
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
      rw [Nat.cast_add]
      apply Finset.add_mem_add
      · rw [← hAB]
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · rw [← hAB]
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      rw [← hAB] at hx hy
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
      rw [Nat.cast_add, hax, hby]
  refine ⟨A, hAne, hAcard, hAB, ?_⟩
  rw [← himage, Finset.card_image_iff.mpr hinj]

/-! ### Quotient--remainder partial lifts -/

/-- Quotient--remainder coordinates for the factorization `m * d`.  These
are the coordinates used in the Deshouillers--Freiman partial lift: the first
coordinate records the residue modulo `m`, while the second records the
quotient modulo `d`. -/
def zmodQuotRemLift (m d : ℕ) (x : ZMod (m * d)) : ℕ × ZMod d :=
  (x.val % m, (x.val / m : ZMod d))

/-- Euclidean reconstruction in the order used by `zmodQuotRemLift`. -/
lemma zmod_val_quot_rem (m : ℕ) (x : ZMod n) :
    m * (x.val / m) + x.val % m = x.val := by
  simpa [add_comm] using Nat.mod_add_div x.val m

/-- The additive embedding of the quotient coordinate in the factorization
`m * d`: a class `q` modulo `d` is sent to `m * q` modulo `m * d`. -/
def zmodQuotientEmbedding (m d : ℕ) : ZMod d →+ ZMod (m * d) :=
  ZMod.lift d ⟨
    (AddMonoidHom.mulRight (m : ZMod (m * d))).comp
      (Int.castAddHom (ZMod (m * d))),
    by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.mulRight_apply]
      have hdcast : (Int.castAddHom (ZMod (m * d))) (d : ℤ) =
          (d : ZMod (m * d)) := by norm_num
      rw [hdcast]
      convert ZMod.natCast_self (m * d) using 1 <;> push_cast <;> ring⟩

@[simp] lemma zmodQuotientEmbedding_natCast (m d q : ℕ) :
    zmodQuotientEmbedding m d (q : ZMod d) =
      (m * q : ZMod (m * d)) := by
  unfold zmodQuotientEmbedding
  rw [show (q : ZMod d) = ((q : ℤ) : ZMod d) by norm_num]
  rw [ZMod.lift_coe]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.mulRight_apply]
  norm_num
  ring

lemma zmodQuotientEmbedding_injective {m d : ℕ} [NeZero d]
    (hm : 0 < m) :
    Function.Injective (zmodQuotientEmbedding m d) := by
  intro x y hxy
  apply ZMod.val_injective d
  have hmod : m * x.val ≡ m * y.val [MOD m * d] := by
    apply ZMod.natCast_eq_natCast_iff _ _ (m * d) |>.mp
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y] at hxy
    simpa only [zmodQuotientEmbedding_natCast, Nat.cast_mul] using hxy
  have hcancel := Nat.ModEq.mul_left_cancel' hm.ne' hmod
  exact Nat.ModEq.eq_of_lt_of_lt hcancel (ZMod.val_lt x) (ZMod.val_lt y)

/-- Mapping a quotient subgroup into the ambient cyclic group preserves its
cardinality. -/
lemma natCard_map_zmodQuotientEmbedding {m d : ℕ}
    [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (K : AddSubgroup (ZMod d)) :
    Nat.card (K.map (zmodQuotientEmbedding m d)) = Nat.card K := by
  have himage : (zmodQuotientEmbedding m d) '' (K : Set (ZMod d)) =
      (K.map (zmodQuotientEmbedding m d) : Set (ZMod (m * d))) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_map]
  let e : K ≃ K.map (zmodQuotientEmbedding m d) :=
    (Equiv.Set.image (zmodQuotientEmbedding m d) (K : Set (ZMod d))
      (zmodQuotientEmbedding_injective hm)).trans (Equiv.setCongr himage)
  exact (Nat.card_congr e).symm

/-- Reconstruct an ambient class from its quotient and remainder
coordinates. -/
lemma zmodQuotientEmbedding_quotient_add_remainder
    {m d : ℕ} [NeZero (m * d)] (z : ZMod (m * d)) :
    zmodQuotientEmbedding m d (z.val / m : ZMod d) +
        (z.val % m : ZMod (m * d)) = z := by
  rw [zmodQuotientEmbedding_natCast]
  rw [← Nat.cast_mul]
  rw [← Nat.cast_add]
  rw [zmod_val_quot_rem]
  exact ZMod.natCast_zmod_val z

/-- An affine subgroup fibre in quotient--remainder coordinates pulls back
to a cyclic coset progression in the original cyclic group. -/
lemma zmodQuotRem_affineFiber_subset_cyclicCosetProgression
    {m d L : ℕ} [NeZero d] [NeZero (m * d)]
    {K : AddSubgroup (ZMod d)} {x y : ZMod d}
    {D : Finset (ZMod (m * d))}
    (hD : ∀ z ∈ D,
      z.val % m < L ∧
        (z.val / m : ZMod d) - ((z.val % m) • x + y) ∈ K) :
    D ⊆ cyclicCosetProgression
      (K.map (zmodQuotientEmbedding m d))
      (zmodQuotientEmbedding m d y)
      ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d x) L := by
  intro z hz
  obtain ⟨hr, hk⟩ := hD z hz
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨z.val % m, hr, ?_⟩
  apply AddSubgroup.mem_map.mpr
  refine ⟨(z.val / m : ZMod d) - ((z.val % m) • x + y), hk, ?_⟩
  rw [map_sub, map_add, map_nsmul]
  have hzrec := zmodQuotientEmbedding_quotient_add_remainder
    (m := m) (d := d) z
  calc
    zmodQuotientEmbedding m d (z.val / m : ZMod d) -
          ((z.val % m) • zmodQuotientEmbedding m d x +
            zmodQuotientEmbedding m d y) =
        (zmodQuotientEmbedding m d (z.val / m : ZMod d) +
            (z.val % m : ZMod (m * d))) -
          (zmodQuotientEmbedding m d y + (z.val % m) •
            ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d x)) := by
      simp only [nsmul_eq_mul]
      ring
    _ = z - (zmodQuotientEmbedding m d y + (z.val % m) •
          ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d x)) := by
      rw [hzrec]

/-- On a no-carry region for the first coordinate, quotient--remainder
coordinates preserve and reflect every relation between two pair sums. -/
lemma zmodQuotRemLift_add_eq_iff
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m)
    {a b c e : ZMod (m * d)}
    (hab : a.val % m + b.val % m < m)
    (hce : c.val % m + e.val % m < m) :
    zmodQuotRemLift m d a + zmodQuotRemLift m d b =
        zmodQuotRemLift m d c + zmodQuotRemLift m d e ↔
      a + b = c + e := by
  let ra := a.val % m
  let rb := b.val % m
  let rc := c.val % m
  let re := e.val % m
  let qa := a.val / m
  let qb := b.val / m
  let qc := c.val / m
  let qe := e.val / m
  have ha : a.val = m * qa + ra := by
    dsimp [qa, ra]
    exact (zmod_val_quot_rem m a).symm
  have hb : b.val = m * qb + rb := by
    dsimp [qb, rb]
    exact (zmod_val_quot_rem m b).symm
  have hc : c.val = m * qc + rc := by
    dsimp [qc, rc]
    exact (zmod_val_quot_rem m c).symm
  have he : e.val = m * qe + re := by
    dsimp [qe, re]
    exact (zmod_val_quot_rem m e).symm
  constructor
  · intro hlift
    have hr : ra + rb = rc + re := congrArg Prod.fst hlift
    have hqz : (qa + qb : ZMod d) = (qc + qe : ZMod d) := by
      simpa [zmodQuotRemLift, qa, qb, qc, qe] using congrArg Prod.snd hlift
    have hq : qa + qb ≡ qc + qe [MOD d] := by
      apply ZMod.natCast_eq_natCast_iff _ _ d |>.mp
      simpa only [Nat.cast_add] using hqz
    have hmul : m * (qa + qb) ≡ m * (qc + qe) [MOD m * d] :=
      Nat.ModEq.mul_left' m hq
    have habval : a.val + b.val = m * (qa + qb) + (ra + rb) := by
      rw [ha, hb, Nat.mul_add]
      omega
    have hceval : c.val + e.val = m * (qc + qe) + (rc + re) := by
      rw [hc, he, Nat.mul_add]
      omega
    have htotal : a.val + b.val ≡ c.val + e.val [MOD m * d] := by
      have hadd := hmul.add_right (ra + rb)
      rw [habval, hceval, ← hr]
      exact hadd
    have hcast' : ((a.val + b.val : ℕ) : ZMod (m * d)) =
        ((c.val + e.val : ℕ) : ZMod (m * d)) :=
      ZMod.natCast_eq_natCast_iff _ _ _ |>.mpr htotal
    have hcast : (a.val : ZMod (m * d)) + b.val =
        (c.val : ZMod (m * d)) + e.val := by
      simpa only [Nat.cast_add] using hcast'
    simpa only [ZMod.natCast_zmod_val] using hcast
  · intro hsum
    have hcast : (a.val : ZMod (m * d)) + b.val =
        (c.val : ZMod (m * d)) + e.val := by
      simpa only [ZMod.natCast_zmod_val] using hsum
    have hcast' : ((a.val + b.val : ℕ) : ZMod (m * d)) =
        ((c.val + e.val : ℕ) : ZMod (m * d)) := by
      simpa only [Nat.cast_add] using hcast
    have htotal : a.val + b.val ≡ c.val + e.val [MOD m * d] :=
      ZMod.natCast_eq_natCast_iff _ _ _ |>.mp hcast'
    have hsmallmod : a.val + b.val ≡ c.val + e.val [MOD m] :=
      Nat.ModEq.of_dvd (by exact dvd_mul_right m d) htotal
    have hrmod : ra + rb ≡ rc + re [MOD m] := by
      rw [Nat.ModEq] at hsmallmod ⊢
      simpa [ra, rb, rc, re, Nat.add_mod] using hsmallmod
    have hr : ra + rb = rc + re := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hce] at hrmod
      exact hrmod
    have habval : a.val + b.val = m * (qa + qb) + (ra + rb) := by
      rw [ha, hb, Nat.mul_add]
      omega
    have hceval : c.val + e.val = m * (qc + qe) + (rc + re) := by
      rw [hc, he, Nat.mul_add]
      omega
    have hexpanded :
        m * (qa + qb) + (ra + rb) ≡
          m * (qc + qe) + (ra + rb) [MOD m * d] := by
      have h := htotal
      rw [habval, hceval, ← hr] at h
      exact h
    have hmul : m * (qa + qb) ≡ m * (qc + qe) [MOD m * d] :=
      Nat.ModEq.add_right_cancel' (ra + rb) hexpanded
    have hq : qa + qb ≡ qc + qe [MOD d] :=
      Nat.ModEq.mul_left_cancel' hm.ne' hmul
    have hqz : ((qa + qb : ℕ) : ZMod d) = ((qc + qe : ℕ) : ZMod d) :=
      ZMod.natCast_eq_natCast_iff _ _ _ |>.mpr hq
    apply Prod.ext hr
    simpa [zmodQuotRemLift, qa, qb, qc, qe, Nat.cast_add] using hqz

/-- Quotient--remainder coordinates are globally injective. -/
lemma zmodQuotRemLift_injective
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m) :
    Function.Injective (zmodQuotRemLift m d) := by
  intro x y hxy
  have hx : x.val % m + (0 : ZMod (m * d)).val % m < m := by
    simpa using Nat.mod_lt x.val hm
  have hy : y.val % m + (0 : ZMod (m * d)).val % m < m := by
    simpa using Nat.mod_lt y.val hm
  have hsum : x + 0 = y + 0 :=
    (zmodQuotRemLift_add_eq_iff hm hx hy).mp (by simpa [hxy])
  simpa using hsum

/-- A finite no-carry set is order-two Freiman-isomorphic to its
quotient--remainder image. -/
lemma zmodQuotRemLift_isAddFreimanIso
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d)))
    (hnowrap : ∀ x ∈ B, ∀ y ∈ B,
      x.val % m + y.val % m < m) :
    IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
      ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
      (zmodQuotRemLift m d) := by
  rw [isAddFreimanIso_two]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · exact (zmodQuotRemLift_injective hm).injOn
    · intro y hy
      exact hy
  · intro a ha b hb c hc e he
    exact zmodQuotRemLift_add_eq_iff hm
      (hnowrap a ha b hb) (hnowrap c hc e he)

/-- The convenient half-interval criterion for the partial lift. -/
lemma zmodQuotRemLift_isAddFreimanIso_of_double_mod_lt
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d)))
    (hhalf : ∀ x ∈ B, 2 * (x.val % m) < m) :
    IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
      ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
      (zmodQuotRemLift m d) := by
  apply zmodQuotRemLift_isAddFreimanIso hm B
  intro x hx y hy
  have hxx := hhalf x hx
  have hyy := hhalf y hy
  omega

/-- The finite quotient--remainder image of a cyclic set. -/
def zmodQuotRemImage (m d : ℕ) (B : Finset (ZMod (m * d))) :
    Finset (ℕ × ZMod d) :=
  B.image (zmodQuotRemLift m d)

lemma zmodQuotRemImage_card
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d))) :
    (zmodQuotRemImage m d B).card = B.card := by
  rw [zmodQuotRemImage, Finset.card_image_iff.mpr
    (fun _ _ _ _ h ↦ zmodQuotRemLift_injective hm h)]

/-- The completed no-carry calculation also identifies the two double
sumsets cardinality-for-cardinality. -/
lemma zmodQuotRemImage_add_card
    {m d : ℕ} [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d)))
    (hnowrap : ∀ x ∈ B, ∀ y ∈ B,
      x.val % m + y.val % m < m) :
    (zmodQuotRemImage m d B + zmodQuotRemImage m d B).card =
      (B + B).card := by
  classical
  let P := B ×ˢ B
  let f : ZMod (m * d) × ZMod (m * d) → ZMod (m * d) :=
    fun p ↦ p.1 + p.2
  let g : ZMod (m * d) × ZMod (m * d) → ℕ × ZMod d :=
    fun p ↦ zmodQuotRemLift m d p.1 + zmodQuotRemLift m d p.2
  have hker : ∀ x ∈ P, ∀ y ∈ P, f x = f y ↔ g x = g y := by
    intro x hx y hy
    have hxp := Finset.mem_product.mp hx
    have hyp := Finset.mem_product.mp hy
    exact (zmodQuotRemLift_add_eq_iff hm
      (hnowrap x.1 hxp.1 x.2 hxp.2)
      (hnowrap y.1 hyp.1 y.2 hyp.2)).symm
  have hcard := card_image_eq_card_image_of_eq_iff P f g hker
  have hf : P.image f = B + B := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.add_mem_add
        (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      exact Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  have hg : P.image g = zmodQuotRemImage m d B + zmodQuotRemImage m d B := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.add_mem_add
      · exact Finset.mem_image.mpr
          ⟨p.1, (Finset.mem_product.mp hp).1, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨p.2, (Finset.mem_product.mp hp).2, rfl⟩
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  rw [hf, hg] at hcard
  exact hcard.symm

/-! ### Fibres of finite subsets of `ℕ × ZMod d` -/

/-- First coordinates occupied by a finite subset of a product. -/
def firstCoordinateSet {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) : Finset ℕ :=
  X.image Prod.fst

/-- The second-coordinate fibre above `a`. -/
def coordinateFiber {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) (a : ℕ) : Finset (ZMod d) :=
  (X.filter fun p ↦ p.1 = a).image Prod.snd

lemma firstCoordinateSet_zmodQuotRemImage
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (B : Finset (ZMod (m * d))) :
    firstCoordinateSet (zmodQuotRemImage m d B) =
      B.image fun z ↦ z.val % m := by
  classical
  ext a
  simp [firstCoordinateSet, zmodQuotRemImage, zmodQuotRemLift]

lemma zero_mem_firstCoordinateSet_zmodQuotRemImage
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    {B : Finset (ZMod (m * d))} (hzero : 0 ∈ B) :
    0 ∈ firstCoordinateSet (zmodQuotRemImage m d B) := by
  rw [firstCoordinateSet_zmodQuotRemImage]
  exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩

lemma firstCoordinateSet_zmodQuotRemImage_subset_range
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d))) :
    firstCoordinateSet (zmodQuotRemImage m d B) ⊆ Finset.range m := by
  rw [firstCoordinateSet_zmodQuotRemImage]
  intro a ha
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_range.mpr (Nat.mod_lt _ hm)

@[simp] lemma mem_firstCoordinateSet {d : ℕ} [NeZero d]
    {X : Finset (ℕ × ZMod d)} {a : ℕ} :
    a ∈ firstCoordinateSet X ↔ ∃ y, (a, y) ∈ X := by
  simp [firstCoordinateSet]

@[simp] lemma mem_coordinateFiber {d : ℕ} [NeZero d]
    {X : Finset (ℕ × ZMod d)} {a : ℕ} {y : ZMod d} :
    y ∈ coordinateFiber X a ↔ (a, y) ∈ X := by
  simp [coordinateFiber]

/-- Elements of a cyclic set lying above one quotient--remainder first
coordinate. -/
def cyclicRemainderFiber {m d : ℕ} [NeZero (m * d)]
    (B : Finset (ZMod (m * d))) (a : ℕ) : Finset (ZMod (m * d)) :=
  B.filter fun z ↦ z.val % m = a

/-- The second-coordinate fibre of the quotient--remainder image is exactly
the image of the corresponding cyclic remainder fibre. -/
lemma coordinateFiber_zmodQuotRemImage_eq_image
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (B : Finset (ZMod (m * d))) (a : ℕ) :
    coordinateFiber (zmodQuotRemImage m d B) a =
      (cyclicRemainderFiber B a).image
        (fun z ↦ ((z.val / m : ℕ) : ZMod d)) := by
  classical
  ext y
  simp [cyclicRemainderFiber, coordinateFiber,
    zmodQuotRemImage, zmodQuotRemLift]
  aesop

/-- Quotient--remainder coordinates preserve the cardinality of each
individual fibre. -/
lemma card_cyclicRemainderFiber
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d))) (a : ℕ) :
    (cyclicRemainderFiber B a).card =
      (coordinateFiber (zmodQuotRemImage m d B) a).card := by
  rw [coordinateFiber_zmodQuotRemImage_eq_image]
  symm
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  apply zmodQuotRemLift_injective hm
  apply Prod.ext
  · exact (Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm
  · exact hxy

/-- A quotient fibre contained in an `H`-coset pulls back to a coset of the
embedded subgroup in the original cyclic group. -/
lemma cyclicRemainderFiber_containedIn_map
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (B : Finset (ZMod (m * d))) (a : ℕ)
    (H : AddSubgroup (ZMod d))
    (hcos : ContainedInAddCoset H
      (coordinateFiber (zmodQuotRemImage m d B) a)) :
    ContainedInAddCoset (H.map (zmodQuotientEmbedding m d))
      (cyclicRemainderFiber B a) := by
  classical
  obtain ⟨c, hc⟩ := hcos
  refine ⟨(a : ZMod (m * d)) + zmodQuotientEmbedding m d c, ?_⟩
  intro z hz
  have hzdata := Finset.mem_filter.mp hz
  have hy : ((z.val / m : ℕ) : ZMod d) ∈
      coordinateFiber (zmodQuotRemImage m d B) a := by
    rw [coordinateFiber_zmodQuotRemImage_eq_image]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hycos := hc hy
  rw [Set.mem_vadd_set] at hycos ⊢
  obtain ⟨k, hk, hck⟩ := hycos
  refine ⟨zmodQuotientEmbedding m d k, ?_, ?_⟩
  · exact AddSubgroup.mem_map.mpr ⟨k, hk, rfl⟩
  · have hzrec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) z
    rw [hzdata.2] at hzrec
    simp only [vadd_eq_add] at hck ⊢
    have he := congrArg (zmodQuotientEmbedding m d) hck
    rw [map_add] at he
    calc
      (a : ZMod (m * d)) + zmodQuotientEmbedding m d c +
          zmodQuotientEmbedding m d k =
          zmodQuotientEmbedding m d c +
            zmodQuotientEmbedding m d k + (a : ZMod (m * d)) := by abel
      _ = zmodQuotientEmbedding m d ((z.val / m : ℕ) : ZMod d) +
          (a : ZMod (m * d)) := by rw [he]
      _ = z := hzrec

lemma coordinateFiber_nonempty_iff {d : ℕ} [NeZero d]
    {X : Finset (ℕ × ZMod d)} {a : ℕ} :
    (coordinateFiber X a).Nonempty ↔ a ∈ firstCoordinateSet X := by
  constructor
  · rintro ⟨y, hy⟩
    exact mem_firstCoordinateSet.mpr ⟨y, mem_coordinateFiber.mp hy⟩
  · intro ha
    obtain ⟨y, hy⟩ := mem_firstCoordinateSet.mp ha
    exact ⟨y, mem_coordinateFiber.mpr hy⟩

lemma card_coordinateFiber {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) (a : ℕ) :
    (coordinateFiber X a).card = (X.filter fun p ↦ p.1 = a).card := by
  rw [coordinateFiber, Finset.card_image_iff.mpr]
  intro p hp q hq hpq
  change p ∈ X.filter (fun p ↦ p.1 = a) at hp
  change q ∈ X.filter (fun p ↦ p.1 = a) at hq
  rw [Finset.mem_filter] at hp hq
  apply Prod.ext
  · exact hp.2.trans hq.2.symm
  · exact hpq

/-- Cardinality decomposes as the sum of the occupied fibre cardinalities. -/
lemma card_eq_sum_card_coordinateFiber {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) :
    X.card = ∑ a ∈ firstCoordinateSet X, (coordinateFiber X a).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (s := X) (t := firstCoordinateSet X) (f := Prod.fst)
    (fun p hp ↦ Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
  apply Finset.sum_congr rfl
  intro a ha
  exact (card_coordinateFiber X a).symm

/-- Pairwise addition of fibres lands in the fibre above the sum of the
first coordinates. -/
lemma coordinateFiber_add_subset {d : ℕ} [NeZero d]
    (X Y : Finset (ℕ × ZMod d)) (a b : ℕ) :
    coordinateFiber X a + coordinateFiber Y b ⊆
      coordinateFiber (X + Y) (a + b) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  rw [mem_coordinateFiber] at hx hy ⊢
  exact Finset.add_mem_add hx hy

lemma add_firstCoordinate_mem {d : ℕ} [NeZero d]
    {X Y : Finset (ℕ × ZMod d)} {a b : ℕ}
    (ha : a ∈ firstCoordinateSet X) (hb : b ∈ firstCoordinateSet Y) :
    a + b ∈ firstCoordinateSet (X + Y) := by
  obtain ⟨x, hx⟩ := mem_firstCoordinateSet.mp ha
  obtain ⟨y, hy⟩ := mem_firstCoordinateSet.mp hb
  exact mem_firstCoordinateSet.mpr ⟨x + y, Finset.add_mem_add hx hy⟩

lemma firstCoordinateSet_add_eq {d : ℕ} [NeZero d]
    (X Y : Finset (ℕ × ZMod d)) :
    firstCoordinateSet (X + Y) = firstCoordinateSet X + firstCoordinateSet Y := by
  ext a
  constructor
  · intro ha
    obtain ⟨z, hz⟩ := mem_firstCoordinateSet.mp ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz
    apply Finset.mem_add.mpr
    refine ⟨x.1, mem_firstCoordinateSet.mpr ⟨x.2, hx⟩,
      y.1, mem_firstCoordinateSet.mpr ⟨y.2, hy⟩, ?_⟩
    exact congrArg Prod.fst hxy
  · intro ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_add.mp ha
    exact add_firstCoordinate_mem ha₁ ha₂

/-- Ruzsa's diameter estimate specialized to a subset `U` of a normalized
integer set `A`.  This is the precise numerical lower bound used to verify
Hall's condition for the layer-pair selection. -/
lemma ruzsa_subset_sum_card_lower_of_zero_mem
    {A U : Finset ℕ}
    (hA : A.Nonempty) (hU : U.Nonempty) (hUA : U ⊆ A)
    (hUzero : 0 ∈ U) (hAzero : 0 ∈ A)
    (hAcard : 2 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1) :
    min (U.card + A.max' hA)
        (U.card + A.card + U.card - 3) ≤
      (U + A).card := by
  have hAmaxpos : 0 < A.max' hA := by
    by_contra hnot
    have hmax0 : A.max' hA = 0 := Nat.eq_zero_of_not_pos hnot
    have hAsub : A ⊆ {0} := by
      intro x hx
      have hxle := A.le_max' x hx
      simp [hmax0] at hxle
      simpa [hxle]
    have := Finset.card_le_card hAsub
    simp at this
    omega
  have hUint : U ⊆ Finset.Icc 0 (U.max' hU) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le x, U.le_max' x hx⟩
  have hAint : A ⊆ Finset.Icc 0 (A.max' hA) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le x, A.le_max' x hx⟩
  have huv : U.max' hU ≤ A.max' hA :=
    A.le_max' _ (hUA (U.max'_mem hU))
  have hUtop : U.max' hU ∈ U := U.max'_mem hU
  have hAtop : A.max' hA ∈ A := A.max'_mem hA
  have hunion : U ∪ A = A := Finset.union_eq_right.mpr hUA
  have hgcd' : (U ∪ A).gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [hunion]
    exact hgcd
  simpa [min_eq_left (Finset.card_le_card hUA)] using
    (Erdos13Additive.ruzsa_normalized_diameter_bound
      hUint hAint huv hAmaxpos hUzero hUtop hAzero hAtop hgcd')

/-- Ruzsa's subset sumset estimate without requiring the smaller set to
contain the normalized endpoint.  Translating `U` by its minimum supplies
the missing zero; the gcd hypothesis is retained because the untranslated
set `A` is still one of the two summands.  This is the form needed when the
Hall construction is anchored at a largest fibre in an interior layer. -/
lemma ruzsa_subset_sum_card_lower
    {A U : Finset ℕ}
    (hA : A.Nonempty) (hU : U.Nonempty) (hUA : U ⊆ A)
    (hAzero : 0 ∈ A) (hAcard : 2 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1) :
    min (U.card + A.max' hA)
        (U.card + A.card + U.card - 3) ≤
      (U + A).card := by
  let u₀ := U.min' hU
  let U₀ := Erdos13Additive.normalizeNat U u₀ 1
  have hUmin : ∀ x ∈ U, u₀ ≤ x := fun x hx ↦ U.min'_le x hx
  have hUmax : ∀ x ∈ U, x ≤ U.max' hU := fun x hx ↦ U.le_max' x hx
  have hUdiv : ∀ x ∈ U, 1 ∣ x - u₀ := by simp
  have hUinterval : U ⊆ Finset.Icc u₀ (U.max' hU) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hUmin x hx, hUmax x hx⟩
  have hU₀interval : U₀ ⊆ Finset.Icc 0 (U.max' hU - u₀) := by
    simpa [U₀] using
      (Erdos13Additive.normalizeNat_subset_Icc
        (m := u₀) (d := 1) hUinterval)
  have hAinterval : A ⊆ Finset.Icc 0 (A.max' hA) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le x, A.le_max' x hx⟩
  have hU₀zero : 0 ∈ U₀ := by
    simpa [U₀, u₀] using
      (Erdos13Additive.zero_mem_normalizeNat (U.min'_mem hU) :
        0 ∈ Erdos13Additive.normalizeNat U (U.min' hU) 1)
  have hU₀top : U.max' hU - u₀ ∈ U₀ := by
    simpa [U₀, u₀] using
      (Erdos13Additive.top_mem_normalizeNat
        (m := U.min' hU) (d := 1) (U.max'_mem hU))
  have hAtop : A.max' hA ∈ A := A.max'_mem hA
  have hdiameter : U.max' hU - u₀ ≤ A.max' hA := by
    exact (Nat.sub_le _ _).trans
      (A.le_max' _ (hUA (U.max'_mem hU)))
  have hAmaxpos : 0 < A.max' hA := by
    by_contra hnot
    have hmax0 : A.max' hA = 0 := Nat.eq_zero_of_not_pos hnot
    have hAsub : A ⊆ {0} := by
      intro x hx
      have hxle := A.le_max' x hx
      simp [hmax0] at hxle
      simpa [hxle]
    have := Finset.card_le_card hAsub
    simp at this
    omega
  have hU₀card : U₀.card = U.card := by
    simpa [U₀] using
      (Erdos13Additive.card_normalizeNat
        (S := U) (m := u₀) (d := 1) (by omega) hUmin hUdiv)
  have hAnorm : Erdos13Additive.normalizeNat A 0 1 = A := by
    ext x
    simp [Erdos13Additive.normalizeNat]
  have hsumcard : (U + A).card = (U₀ + A).card := by
    have h := Erdos13Additive.card_sumset_eq_card_normalized
      (S := U) (T := A) (s := u₀) (t := 0) (d := 1)
      (by omega) hUmin (fun x _ ↦ Nat.zero_le x) hUdiv (by simp)
    simpa [U₀, hAnorm] using h
  have hgcd' : (U₀ ∪ A).gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [Finset.gcd_union, hgcd]
    simp
  have hbound := Erdos13Additive.ruzsa_normalized_diameter_bound
    hU₀interval hAinterval hdiameter hAmaxpos hU₀zero hU₀top
    hAzero hAtop hgcd'
  rw [hU₀card] at hbound
  rw [hsumcard]
  simpa [min_eq_left (Finset.card_le_card hUA)] using hbound

lemma sum_if_mem_two_one (S D : Finset ℕ) :
    ∑ a ∈ S, (if a ∈ D then 2 else 1) = S.card + (S ∩ D).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases haD : a ∈ D <;> simp [ha, haD, ih] <;> omega

/-- The Hall condition needed in the Deshouillers--Freiman layer selection.
The distinguished base layer may occur in at most `|A|-1` slots, the layers
in `D` in at most two slots, and every other layer in at most one.  Ruzsa's
diameter estimate and the bound on `|D|` then supply enough distinct sums. -/
lemma hall_condition_of_layer_multiplicity
    {ι : Type*} [Fintype ι]
    (A D : Finset ℕ) (base : ℕ) (anchor : ι → ℕ)
    (hA : A.Nonempty) (hAzero : 0 ∈ A) (hAcard : 3 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ A) (hDA : D ⊆ A) (hDbase : base ∉ D)
    (hDcard : D.card ≤ A.max' hA + 2 - A.card)
    (hanchor : ∀ i, anchor i ∈ A)
    (hbaseCap : ((Finset.univ : Finset ι).filter
      fun i ↦ anchor i = base).card ≤ A.card - 1)
    (hdoubleCap : ∀ a ∈ D,
      ((Finset.univ : Finset ι).filter
        fun i ↦ anchor i = a).card ≤ 2)
    (hsingleCap : ∀ a ∈ A, a ≠ base → a ∉ D →
      ((Finset.univ : Finset ι).filter
        fun i ↦ anchor i = a).card ≤ 1) :
    ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
  classical
  intro J
  by_cases hJ : J.Nonempty
  · let U := J.image anchor
    have hU : U.Nonempty := hJ.image anchor
    have hUA : U ⊆ A := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact hanchor i
    have hUnion : (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b) =
        U + A := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_add]
      constructor
      · rintro ⟨i, hiJ, b, hbA, rfl⟩
        exact ⟨anchor i, Finset.mem_image.mpr ⟨i, hiJ, rfl⟩,
          b, hbA, rfl⟩
      · rintro ⟨a, haU, b, hbA, rfl⟩
        obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp haU
        exact ⟨i, hiJ, b, hbA, rfl⟩
    let cap : ℕ → ℕ := fun a ↦
      if a = base then A.card - 1 else if a ∈ D then 2 else 1
    have hfiber : ∀ a ∈ U,
        (J.filter fun i ↦ anchor i = a).card ≤ cap a := by
      intro a haU
      have hsub : (J.filter fun i ↦ anchor i = a) ⊆
          ((Finset.univ : Finset ι).filter fun i ↦ anchor i = a) := by
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, hi.2⟩
      have hle := Finset.card_le_card hsub
      by_cases ha0 : a = base
      · subst a
        simpa [cap] using hle.trans hbaseCap
      · by_cases haD : a ∈ D
        · simpa [cap, ha0, haD] using hle.trans (hdoubleCap a haD)
        · have haA : a ∈ A := hUA haU
          simpa [cap, ha0, haD] using
            hle.trans (hsingleCap a haA ha0 haD)
    have hJsum : J.card = ∑ a ∈ U,
        (J.filter fun i ↦ anchor i = a).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hJcap : J.card ≤ ∑ a ∈ U, cap a := by
      rw [hJsum]
      exact Finset.sum_le_sum hfiber
    let Q := U ∩ D
    have hQleD : Q.card ≤ D.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hDle : A.card + D.card ≤ A.max' hA + 2 := by
      have hAmax : A.card ≤ A.max' hA + 1 := by
        have hsub : A ⊆ Finset.Icc 0 (A.max' hA) := by
          intro a ha
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, A.le_max' a ha⟩
        have hc := Finset.card_le_card hsub
        simpa using hc
      omega
    have hlowerBase (_hUbase : base ∈ U) :
        min (U.card + A.max' hA)
            (U.card + A.card + U.card - 3) ≤
          (U + A).card :=
      ruzsa_subset_sum_card_lower hA hU hUA hAzero (by omega) hgcd
    by_cases hUbase : base ∈ U
    · have hQerase : Q ⊆ U.erase base := by
        intro a ha
        have haU := (Finset.mem_inter.mp ha).1
        have haD := (Finset.mem_inter.mp ha).2
        exact Finset.mem_erase.mpr
          ⟨fun ha0 ↦ hDbase (ha0 ▸ haD), haU⟩
      have hQsmall : Q.card + 1 ≤ U.card := by
        have hle := Finset.card_le_card hQerase
        rw [Finset.card_erase_of_mem hUbase] at hle
        have hUpos : 0 < U.card := Finset.card_pos.mpr hU
        omega
      have hcapEq : (∑ a ∈ U, cap a) =
          (A.card - 1) + (U.card - 1) + Q.card := by
        rw [← Finset.sum_erase_add U cap hUbase]
        have hcapBase : cap base = A.card - 1 := by simp [cap]
        rw [hcapBase]
        have hsumErase : (∑ a ∈ U.erase base, cap a) =
            ∑ a ∈ U.erase base, (if a ∈ D then 2 else 1) := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha0 : a ≠ base := (Finset.mem_erase.mp ha).1
          simp [cap, ha0]
        rw [hsumErase, sum_if_mem_two_one]
        have hcardErase : (U.erase base).card = U.card - 1 :=
          Finset.card_erase_of_mem hUbase
        have hinter : U.erase base ∩ D = Q := by
          ext a
          simp only [Finset.mem_inter, Finset.mem_erase, Q]
          constructor
          · rintro ⟨⟨_, haU⟩, haD⟩
            exact ⟨haU, haD⟩
          · rintro ⟨haU, haD⟩
            exact ⟨⟨fun ha0 ↦ hDbase (ha0 ▸ haD), haU⟩, haD⟩
        rw [hcardErase, hinter]
        omega
      have hJbound : J.card ≤ A.card + U.card + Q.card - 2 := by
        rw [hcapEq] at hJcap
        omega
      have hfirst : J.card ≤ U.card + A.max' hA := by omega
      have hsecond : J.card ≤ U.card + A.card + U.card - 3 := by omega
      rw [hUnion]
      exact (le_min hfirst hsecond).trans (hlowerBase hUbase)
    · have hcapEq : (∑ a ∈ U, cap a) = U.card + Q.card := by
        have hbaseAll : ∀ a ∈ U, a ≠ base := by
          intro a haU ha0
          exact hUbase (ha0 ▸ haU)
        calc
          (∑ a ∈ U, cap a) =
              ∑ a ∈ U, (if a ∈ D then 2 else 1) := by
                apply Finset.sum_congr rfl
                intro a haU
                simp [cap, hbaseAll a haU]
          _ = U.card + Q.card := by
            simpa [Q] using sum_if_mem_two_one U D
      have hJbound : J.card ≤ U.card + Q.card := by
        rw [hcapEq] at hJcap
        exact hJcap
      have hfirst : J.card ≤ U.card + A.max' hA := by omega
      have hsecond : J.card ≤ U.card + A.card - 1 := by
        have hDproper : D ⊂ A := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hDA, ?_⟩
          intro hEq
          apply hDbase
          rw [hEq]
          exact hbase
        have hDlt : D.card < A.card := Finset.card_lt_card hDproper
        omega
      have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hU hA
      have hsum : U.card + A.card - 1 ≤ (U + A).card := hcauchy
      rw [hUnion]
      exact hsecond.trans hsum
  · simp only [Finset.not_nonempty_iff_eq_empty] at hJ
    subst J
    simp

/-- Hall's theorem, packaged for selecting distinct sums from a family of
translates `anchor i + A`.  The returned second coordinates make the
representatives usable by the fibre bookkeeping below. -/
lemma exists_injective_sum_representatives_of_hall
    {ι : Type*} [Fintype ι]
    (A : Finset ℕ) (anchor : ι → ℕ)
    (_hanchor : ∀ i, anchor i ∈ A)
    (hHall : ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card) :
    ∃ choice : ι → ℕ,
      (∀ i, choice i ∈ A) ∧
      Function.Injective (fun i ↦ anchor i + choice i) := by
  classical
  let T : ι → Finset ℕ := fun i ↦ A.image fun b ↦ anchor i + b
  obtain ⟨f, hf, hfT⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp (by
      simpa [T] using hHall)
  let choice : ι → ℕ := fun i ↦
    Classical.choose (Finset.mem_image.mp (hfT i))
  have hchoice (i : ι) : choice i ∈ A ∧ anchor i + choice i = f i :=
    Classical.choose_spec (Finset.mem_image.mp (hfT i))
  refine ⟨choice, fun i ↦ (hchoice i).1, ?_⟩
  intro i j hij
  apply hf
  rw [← (hchoice i).2, ← (hchoice j).2]
  exact hij

/-- Finite-set form of `exists_injective_sum_representatives_of_hall`.
It produces a set of ordered layer pairs whose sums are pairwise distinct. -/
lemma exists_pairSelection_of_hall
    {ι : Type*} [Fintype ι]
    (A : Finset ℕ) (anchor : ι → ℕ)
    (hanchor : ∀ i, anchor i ∈ A)
    (hHall : ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card) :
    ∃ P : Finset (ℕ × ℕ),
      P.card = Fintype.card ι ∧
      (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
  classical
  obtain ⟨choice, hchoice, hinj⟩ :=
    exists_injective_sum_representatives_of_hall A anchor hanchor hHall
  let pair : ι → ℕ × ℕ := fun i ↦ (anchor i, choice i)
  let P := Finset.univ.image pair
  have hpair : Function.Injective pair := by
    intro i j hp
    apply hinj
    exact congrArg (fun p : ℕ × ℕ ↦ p.1 + p.2) hp
  refine ⟨P, ?_, ?_, ?_⟩
  · dsimp [P]
    rw [Finset.card_image_iff.mpr hpair.injOn, Finset.card_univ]
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hanchor i, hchoice i⟩
  · intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := hinj hpq
    subst j
    rfl

/-- The slot type used to apply Hall's theorem to a normalized integer layer
set `A`.  There are `|A|-1` copies of `base`, one copy of every other
anchor, and one additional copy of every anchor in `D`. -/
abbrev LayerHallSlot (A D : Finset ℕ) (base : ℕ) :=
  Fin (A.card - 1) ⊕ ({a // a ∈ A.erase base} ⊕ {a // a ∈ D})

def layerHallAnchor (A D : Finset ℕ) (base : ℕ) :
    LayerHallSlot A D base → ℕ
  | Sum.inl _ => base
  | Sum.inr (Sum.inl a) => a.1
  | Sum.inr (Sum.inr a) => a.1

lemma layerHallAnchor_mem
    {A D : Finset ℕ} {base : ℕ} (hbase : base ∈ A) (hDA : D ⊆ A)
    (i : LayerHallSlot A D base) : layerHallAnchor A D base i ∈ A := by
  rcases i with i | i
  · exact hbase
  · rcases i with a | a
    · exact Finset.mem_of_mem_erase a.2
    · exact hDA a.2

lemma layerHallAnchor_base_fiber_cap
    {A D : Finset ℕ} {base : ℕ}
    (hAcard : 3 ≤ A.card) (hDbase : base ∉ D) :
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
      fun i => layerHallAnchor A D base i = base).card ≤ A.card - 1 := by
  classical
  let f : LayerHallSlot A D base → Fin (A.card - 1) := fun i =>
    match i with
    | Sum.inl j => j
    | Sum.inr _ => ⟨0, by omega⟩
  calc
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
        fun i => layerHallAnchor A D base i = base).card ≤
        (Finset.univ : Finset (Fin (A.card - 1))).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        rcases i with i | i
        · rcases j with j | j
          · exact congrArg Sum.inl hij
          · rcases j with j | j
            · have hj0 : (j : ℕ) = base := by simpa [layerHallAnchor] using hj
              exact False.elim ((Finset.mem_erase.mp j.2).1 hj0)
            · have hj0 : (j : ℕ) = base := by simpa [layerHallAnchor] using hj
              exact False.elim (hDbase (hj0 ▸ j.2))
        · rcases i with i | i
          · have hi0 : (i : ℕ) = base := by simpa [layerHallAnchor] using hi
            exact False.elim ((Finset.mem_erase.mp i.2).1 hi0)
          · have hi0 : (i : ℕ) = base := by simpa [layerHallAnchor] using hi
            exact False.elim (hDbase (hi0 ▸ i.2))
    _ = A.card - 1 := by simp

lemma layerHallAnchor_double_fiber_cap
    {A D : Finset ℕ} {base a : ℕ} (hDbase : base ∉ D) (haD : a ∈ D) :
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
      fun i => layerHallAnchor A D base i = a).card ≤ 2 := by
  classical
  have ha0 : a ≠ base := fun ha => hDbase (ha ▸ haD)
  let f : LayerHallSlot A D base → Fin 2 := fun i =>
    match i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr _) => 1
  calc
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
        fun i => layerHallAnchor A D base i = a).card ≤
        (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        rcases i with i | i
        · exact False.elim (ha0 (by simpa [layerHallAnchor] using hi.symm))
        · rcases j with j | j
          · exact False.elim (ha0 (by simpa [layerHallAnchor] using hj.symm))
          · rcases i with i | i <;> rcases j with j | j
            · have hii : (i : ℕ) = a := by simpa [layerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by simpa [layerHallAnchor] using hj
              have : i = j := Subtype.ext (hii.trans hjj.symm)
              subst j
              rfl
            · simp [f] at hij
            · simp [f] at hij
            · have hii : (i : ℕ) = a := by simpa [layerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by simpa [layerHallAnchor] using hj
              have : i = j := Subtype.ext (hii.trans hjj.symm)
              subst j
              rfl
    _ = 2 := by simp

lemma layerHallAnchor_single_fiber_cap
    {A D : Finset ℕ} {base a : ℕ} (_haA : a ∈ A)
    (ha0 : a ≠ base) (haD : a ∉ D) :
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
      fun i => layerHallAnchor A D base i = a).card ≤ 1 := by
  classical
  let f : LayerHallSlot A D base → Fin 1 := fun _ => 0
  calc
    ((Finset.univ : Finset (LayerHallSlot A D base)).filter
        fun i => layerHallAnchor A D base i = a).card ≤
        (Finset.univ : Finset (Fin 1)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj _
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        rcases i with i | i
        · exact False.elim (ha0 (by simpa [layerHallAnchor] using hi.symm))
        · rcases j with j | j
          · exact False.elim (ha0 (by simpa [layerHallAnchor] using hj.symm))
          · rcases i with i | i <;> rcases j with j | j
            · have hii : (i : ℕ) = a := by simpa [layerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by simpa [layerHallAnchor] using hj
              have : i = j := Subtype.ext (hii.trans hjj.symm)
              subst j
              rfl
            · exact False.elim (haD (by simpa [layerHallAnchor] using hj ▸ j.2))
            · exact False.elim (haD (by simpa [layerHallAnchor] using hi ▸ i.2))
            · exact False.elim (haD (by simpa [layerHallAnchor] using hi ▸ i.2))
    _ = 1 := by simp

lemma card_layerHallSlot {A D : Finset ℕ} {base : ℕ} (hbase : base ∈ A) :
    Fintype.card (LayerHallSlot A D base) =
      2 * A.card + D.card - 2 := by
  classical
  calc
    Fintype.card (LayerHallSlot A D base) =
        (A.card - 1) + ((A.erase base).card + D.card) := by
      simp [LayerHallSlot]
    _ = 2 * A.card + D.card - 2 := by
      rw [Finset.card_erase_of_mem hbase]
      have hApos : 0 < A.card := Finset.card_pos.mpr ⟨base, hbase⟩
      omega

/-- The explicit slot multiset satisfies Hall's condition, so it selects
`2|A|+|D|-2` ordered pairs from `A × A` having distinct sums. -/
theorem exists_layerHall_pairSelection
    {A D : Finset ℕ} {base : ℕ}
    (hA : A.Nonempty) (hAzero : 0 ∈ A) (hAcard : 3 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ A) (hDA : D ⊆ A) (hDbase : base ∉ D)
    (hDcard : D.card ≤ A.max' hA + 2 - A.card) :
    ∃ P : Finset (ℕ × ℕ),
      P.card = 2 * A.card + D.card - 2 ∧
      (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
  classical
  let anchor : LayerHallSlot A D base → ℕ := layerHallAnchor A D base
  have hanchor : ∀ i, anchor i ∈ A :=
    layerHallAnchor_mem hbase hDA
  have hHall : ∀ J : Finset (LayerHallSlot A D base),
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
    apply hall_condition_of_layer_multiplicity A D base anchor hA hAzero hAcard
      hgcd hbase hDA hDbase hDcard hanchor
    · simpa [anchor] using layerHallAnchor_base_fiber_cap hAcard hDbase
    · intro a haD
      simpa [anchor] using layerHallAnchor_double_fiber_cap hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using layerHallAnchor_single_fiber_cap haA ha0 haD
  obtain ⟨P, hPcard, hP, hinj⟩ :=
    exists_pairSelection_of_hall A anchor hanchor hHall
  refine ⟨P, ?_, hP, hinj⟩
  rw [hPcard, card_layerHallSlot hbase]

/-- A distinguished set of positive layers of the largest size permitted by
the Hall multiplicity estimate.  The maximum-cardinality bound is written
with natural subtraction, so the proof records that `|A| ≤ max A + 1`. -/
theorem exists_distinguishedLayerSet
    {A : Finset ℕ} (hA : A.Nonempty) (hAzero : 0 ∈ A) :
    ∃ D : Finset ℕ,
      D ⊆ A ∧ 0 ∉ D ∧
      D.card = min (A.max' hA + 3 - A.card) A.card - 1 ∧
      D.card ≤ A.max' hA + 2 - A.card := by
  classical
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.Icc 0 (A.max' hA) := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, A.le_max' a ha⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  let R := min (A.max' hA + 3 - A.card) A.card
  have hRle : R ≤ A.card := Nat.min_le_right _ _
  have hRerase : R - 1 ≤ (A.erase 0).card := by
    rw [Finset.card_erase_of_mem hAzero]
    omega
  obtain ⟨D, hDerase, hDcard⟩ :=
    (A.erase 0).exists_subset_card_eq hRerase
  have hDA : D ⊆ A := hDerase.trans (Finset.erase_subset 0 A)
  have hDzero : 0 ∉ D := by
    intro h0D
    exact (Finset.mem_erase.mp (hDerase h0D)).1 rfl
  refine ⟨D, hDA, hDzero, ?_, ?_⟩
  · simpa [R] using hDcard
  · rw [hDcard]
    have hRleft : R ≤ A.max' hA + 3 - A.card := Nat.min_le_left _ _
    omega

/-- Sharp cardinality form of the integer-layer Hall construction. -/
theorem exists_sharp_layerHall_pairSelection
    {A : Finset ℕ}
    (hA : A.Nonempty) (hAzero : 0 ∈ A) (hAcard : 3 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1) :
    ∃ P : Finset (ℕ × ℕ),
      P.card =
        2 * A.card + min (A.max' hA + 3 - A.card) A.card - 3 ∧
      (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
  obtain ⟨D, hDA, hDzero, hDcard, hDle⟩ :=
    exists_distinguishedLayerSet hA hAzero
  obtain ⟨P, hPcard, hP, hinj⟩ :=
    exists_layerHall_pairSelection hA hAzero hAcard hgcd hAzero hDA hDzero hDle
  refine ⟨P, ?_, hP, hinj⟩
  rw [hPcard, hDcard]
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.Icc 0 (A.max' hA) := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, A.le_max' a ha⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hRpos : 0 < min (A.max' hA + 3 - A.card) A.card := by
    apply Nat.lt_of_lt_of_le Nat.zero_lt_one
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  omega

/-- Fiberwise sumsets over pairwise distinct first-coordinate sums are
disjoint inside `X + X`.  This is the counting interface used after Hall's
theorem selects a family of pairs of occupied layers. -/
lemma sum_card_coordinateFiber_add_le_card_add_of_pairSelection
    {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X)
    (hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P) :
    ∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
      (X + X).card := by
  classical
  let f : ℕ × ℕ → ℕ := fun p ↦ p.1 + p.2
  have hterm : ∀ p ∈ P,
      (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        (coordinateFiber (X + X) (f p)).card := by
    intro p hp
    exact Finset.card_le_card (coordinateFiber_add_subset X X p.1 p.2)
  have himage : P.image f ⊆ firstCoordinateSet (X + X) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact add_firstCoordinate_mem (hP p hp).1 (hP p hp).2
  calc
    ∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        ∑ p ∈ P, (coordinateFiber (X + X) (f p)).card :=
      Finset.sum_le_sum hterm
    _ = ∑ a ∈ P.image f, (coordinateFiber (X + X) a).card := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      exact hinj hp hq hpq
    _ ≤ ∑ a ∈ firstCoordinateSet (X + X),
        (coordinateFiber (X + X) a).card := by
      exact Finset.sum_le_sum_of_subset himage
    _ = (X + X).card :=
      (card_eq_sum_card_coordinateFiber (X + X)).symm

/-- The sharp Hall family, instantiated with the occupied integer layers of a
product-set lift, and immediately converted into a lower bound for `|X+X|`. -/
theorem exists_sharp_layerHall_fiber_bound
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1) :
    ∃ P : Finset (ℕ × ℕ),
      P.card =
          2 * (firstCoordinateSet X).card +
            min ((firstCoordinateSet X).max' hA + 3 -
              (firstCoordinateSet X).card) (firstCoordinateSet X).card - 3 ∧
      (∀ p ∈ P,
        p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
      ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        (X + X).card := by
  obtain ⟨P, hPcard, hP, hinj⟩ :=
    exists_sharp_layerHall_pairSelection hA hAzero hAcard hgcd
  exact ⟨P, hPcard, hP, hinj,
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hP hinj⟩

/-- Among the `k`-element subsets of `S`, choose one with maximal total
weight.  A one-element exchange shows that every chosen weight dominates
every unchosen weight. -/
theorem exists_maximalWeight_subset
    {S : Finset ℕ} {k : ℕ} (g : ℕ → ℕ) (hks : k ≤ S.card) :
    ∃ D : Finset ℕ, D ⊆ S ∧ D.card = k ∧
      ∀ a ∈ S \ D, ∀ b ∈ D, g a ≤ g b := by
  classical
  obtain ⟨D₀, hD₀S, hD₀card⟩ := S.exists_subset_card_eq hks
  let candidates := S.powersetCard k
  let weights := candidates.image fun D ↦ ∑ a ∈ D, g a
  have hD₀mem : D₀ ∈ candidates := by
    simpa [candidates, Finset.mem_powersetCard] using ⟨hD₀S, hD₀card⟩
  have hweights : weights.Nonempty := by
    refine ⟨∑ a ∈ D₀, g a, ?_⟩
    exact Finset.mem_image.mpr ⟨D₀, hD₀mem, rfl⟩
  let M := weights.max' hweights
  have hMmem : M ∈ weights := weights.max'_mem hweights
  obtain ⟨D, hDmem, hDsum⟩ := Finset.mem_image.mp hMmem
  have hDdata := Finset.mem_powersetCard.mp hDmem
  refine ⟨D, hDdata.1, hDdata.2, ?_⟩
  intro a ha b hb
  by_contra hnot
  have hba : g b < g a := Nat.lt_of_not_ge hnot
  let E := insert a (D.erase b)
  have haD : a ∉ D := (Finset.mem_sdiff.mp ha).2
  have hES : E ⊆ S := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (Finset.mem_sdiff.mp ha).1
    · exact hDdata.1 (Finset.mem_of_mem_erase hx)
  have haErase : a ∉ D.erase b := fun h ↦ haD (Finset.mem_of_mem_erase h)
  have hEcard : E.card = k := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem haErase,
      Finset.card_erase_of_mem hb, hDdata.2]
    have hk : 0 < k := by
      rw [← hDdata.2]
      exact Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hEmem : E ∈ candidates := by
    exact Finset.mem_powersetCard.mpr ⟨hES, hEcard⟩
  have hEle : (∑ x ∈ E, g x) ≤ M := by
    apply weights.le_max' _
    exact Finset.mem_image.mpr ⟨E, hEmem, rfl⟩
  have hsumD : (∑ x ∈ D.erase b, g x) + g b = ∑ x ∈ D, g x :=
    Finset.sum_erase_add D g hb
  have hsumE : ∑ x ∈ E, g x = g a + ∑ x ∈ D.erase b, g x := by
    dsimp [E]
    rw [Finset.sum_insert haErase]
  have hDltE : (∑ x ∈ D, g x) < ∑ x ∈ E, g x := by
    rw [hsumE, ← hsumD]
    omega
  rw [← hDsum] at hEle
  omega

/-- A maximal `k`-element subset has at least the average `k/|S|` share of
the total weight.  This finite exchange proof avoids any division. -/
theorem exists_subset_card_eq_mul_sum_le
    {S : Finset ℕ} {k : ℕ} (g : ℕ → ℕ) (hks : k ≤ S.card) :
    ∃ D : Finset ℕ, D ⊆ S ∧ D.card = k ∧
      k * (∑ a ∈ S, g a) ≤ S.card * ∑ a ∈ D, g a := by
  classical
  obtain ⟨D, hDS, hDcard, hmax⟩ :=
    exists_maximalWeight_subset g hks
  have hpoint : ∀ a ∈ S \ D,
      k * g a ≤ ∑ b ∈ D, g b := by
    intro a ha
    calc
      k * g a = ∑ b ∈ D, g a := by simp [hDcard]
      _ ≤ ∑ b ∈ D, g b := by
        exact Finset.sum_le_sum (fun b hb ↦ hmax a ha b hb)
  have hout : k * (∑ a ∈ S \ D, g a) ≤
      (S \ D).card * ∑ b ∈ D, g b := by
    rw [Finset.mul_sum]
    calc
      ∑ a ∈ S \ D, k * g a ≤
          ∑ _a ∈ S \ D, ∑ b ∈ D, g b := by
        exact Finset.sum_le_sum (fun a ha ↦ hpoint a ha)
      _ = (S \ D).card * ∑ b ∈ D, g b := by simp
  have hsplit : ∑ a ∈ D, g a + ∑ a ∈ S \ D, g a =
      ∑ a ∈ S, g a := by
    rw [add_comm]
    exact Finset.sum_sdiff hDS
  have hcardDiff : (S \ D).card = S.card - k := by
    rw [Finset.card_sdiff_of_subset hDS, hDcard]
  refine ⟨D, hDS, hDcard, ?_⟩
  rw [← hsplit, mul_add]
  calc
    k * ∑ a ∈ D, g a + k * ∑ a ∈ S \ D, g a ≤
        k * ∑ a ∈ D, g a + (S \ D).card * ∑ a ∈ D, g a :=
      Nat.add_le_add_left hout _
    _ = S.card * ∑ a ∈ D, g a := by
      rw [hcardDiff]
      have hk : k + (S.card - k) = S.card := Nat.add_sub_of_le hks
      rw [← add_mul, hk]

/-- Hall representatives weighted by the cardinality of their anchor fibres.
Each selected fibre sumset contains a translate of its anchor fibre, while
distinct selected first-coordinate sums remain disjoint in `X + X`. -/
lemma sum_card_coordinateFiber_le_add_of_hall
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (X : Finset (ℕ × ZMod d)) (anchor : ι → ℕ)
    (hanchor : ∀ i, anchor i ∈ firstCoordinateSet X)
    (hHall : ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦
        (firstCoordinateSet X).image fun b ↦ anchor i + b).card) :
    ∑ i : ι, (coordinateFiber X (anchor i)).card ≤ (X + X).card := by
  classical
  obtain ⟨choice, hchoice, hinj⟩ :=
    exists_injective_sum_representatives_of_hall
      (firstCoordinateSet X) anchor hanchor hHall
  let pair : ι → ℕ × ℕ := fun i ↦ (anchor i, choice i)
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpair : Function.Injective pair := by
    intro i j hp
    apply hinj
    exact congrArg (fun p : ℕ × ℕ ↦ p.1 + p.2) hp
  have hP : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hanchor i, hchoice i⟩
  have hinjP : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := hinj hpq
    subst j
    rfl
  calc
    ∑ i : ι, (coordinateFiber X (anchor i)).card ≤
        ∑ i : ι,
          (coordinateFiber X (anchor i) +
            coordinateFiber X (choice i)).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr (hchoice i))
    _ = ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
      dsimp [P]
      rw [Finset.sum_image]
      exact hpair.injOn
    _ ≤ (X + X).card :=
      sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hP hinjP

/-- Choice-level version of the preceding Hall estimate.  Retaining the
chosen partner layer is essential for the quantitative Kneser alternative:
the repeated base slots have distinct partners, and hence see all but at
most one occupied fibre. -/
lemma exists_choice_sum_card_coordinateFiber_add_le_of_hall
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (X : Finset (ℕ × ZMod d)) (anchor : ι → ℕ)
    (hanchor : ∀ i, anchor i ∈ firstCoordinateSet X)
    (hHall : ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦
        (firstCoordinateSet X).image fun b ↦ anchor i + b).card) :
    ∃ choice : ι → ℕ,
      (∀ i, choice i ∈ firstCoordinateSet X) ∧
      Function.Injective (fun i ↦ anchor i + choice i) ∧
      ∑ i : ι,
          (coordinateFiber X (anchor i) +
            coordinateFiber X (choice i)).card ≤ (X + X).card := by
  classical
  obtain ⟨choice, hchoice, hinj⟩ :=
    exists_injective_sum_representatives_of_hall
      (firstCoordinateSet X) anchor hanchor hHall
  let pair : ι → ℕ × ℕ := fun i ↦ (anchor i, choice i)
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpair : Function.Injective pair := by
    intro i j hp
    apply hinj
    exact congrArg (fun p : ℕ × ℕ ↦ p.1 + p.2) hp
  have hP : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hanchor i, hchoice i⟩
  have hinjP : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := hinj hpq
    subst j
    rfl
  refine ⟨choice, hchoice, hinj, ?_⟩
  calc
    ∑ i : ι,
        (coordinateFiber X (anchor i) +
          coordinateFiber X (choice i)).card =
        ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
      dsimp [P]
      rw [Finset.sum_image]
      exact hpair.injOn
    _ ≤ (X + X).card :=
      sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hP hinjP

lemma sum_layerHallAnchor
    {A D : Finset ℕ} {base : ℕ} (g : ℕ → ℕ) :
    ∑ i : LayerHallSlot A D base, g (layerHallAnchor A D base i) =
      (A.card - 1) * g base +
        ∑ a ∈ A.erase base, g a + ∑ a ∈ D, g a := by
  classical
  simp [LayerHallSlot, layerHallAnchor, Finset.sum_attach, add_assoc]

/-- The precise weighted Hall inequality (the inequality labelled (SD1) in
the mathematical reconstruction), before choosing `D` to consist of the
largest distinguished fibres. -/
theorem layerHall_weighted_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {D : Finset ℕ} {base : ℕ}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ firstCoordinateSet X)
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : base ∉ D)
    (hDcard : D.card ≤
      (firstCoordinateSet X).max' hA + 2 - (firstCoordinateSet X).card) :
    ((firstCoordinateSet X).card - 2) * (coordinateFiber X base).card +
        ∑ a ∈ D, (coordinateFiber X a).card + X.card ≤
      (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let anchor : LayerHallSlot A D base → ℕ := layerHallAnchor A D base
  have hanchor : ∀ i, anchor i ∈ A :=
    layerHallAnchor_mem hbase hDA
  have hHall : ∀ J : Finset (LayerHallSlot A D base),
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
    apply hall_condition_of_layer_multiplicity A D base anchor hA hAzero hAcard
      hgcd hbase hDA hDbase hDcard hanchor
    · simpa [anchor] using layerHallAnchor_base_fiber_cap hAcard hDbase
    · intro a haD
      simpa [anchor] using layerHallAnchor_double_fiber_cap hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using layerHallAnchor_single_fiber_cap haA ha0 haD
  have hweighted := sum_card_coordinateFiber_le_add_of_hall X anchor hanchor hHall
  dsimp only [anchor] at hweighted
  have hanchorSum := sum_layerHallAnchor (A := A) (D := D) (base := base)
    (fun a ↦ (coordinateFiber X a).card)
  rw [hanchorSum] at hweighted
  have hXcard : X.card = ∑ a ∈ A, (coordinateFiber X a).card :=
    card_eq_sum_card_coordinateFiber X
  have hsplit : ∑ a ∈ A, (coordinateFiber X a).card =
      (coordinateFiber X base).card +
        ∑ a ∈ A.erase base, (coordinateFiber X a).card := by
    rw [add_comm]
    exact (Finset.sum_erase_add A
      (fun a ↦ (coordinateFiber X a).card) hbase).symm
  dsimp only [A] at hXcard hsplit hweighted ⊢
  rw [hXcard, hsplit]
  have hcoeff :
      ((firstCoordinateSet X).card - 2) * (coordinateFiber X base).card +
          (coordinateFiber X base).card =
        ((firstCoordinateSet X).card - 1) * (coordinateFiber X base).card := by
    have hs : (firstCoordinateSet X).card - 2 + 1 =
        (firstCoordinateSet X).card - 1 := by omega
    calc
      ((firstCoordinateSet X).card - 2) * (coordinateFiber X base).card +
          (coordinateFiber X base).card =
        ((firstCoordinateSet X).card - 2 + 1) *
          (coordinateFiber X base).card := by ring
      _ = ((firstCoordinateSet X).card - 1) *
          (coordinateFiber X base).card := by rw [hs]
  calc
    ((firstCoordinateSet X).card - 2) * (coordinateFiber X base).card +
          ∑ a ∈ D, (coordinateFiber X a).card +
          ((coordinateFiber X base).card +
            ∑ a ∈ (firstCoordinateSet X).erase base,
              (coordinateFiber X a).card) =
        (((firstCoordinateSet X).card - 2) *
            (coordinateFiber X base).card + (coordinateFiber X base).card) +
          ∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card +
          ∑ a ∈ D, (coordinateFiber X a).card := by
      omega
    _ = ((firstCoordinateSet X).card - 1) *
          (coordinateFiber X base).card +
          ∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card +
          ∑ a ∈ D, (coordinateFiber X a).card := by rw [hcoeff]
    _ ≤ (X + X).card := hweighted

/-- Hall condition with a variable number of copies of the base anchor. -/
lemma hall_condition_of_flexible_layer_multiplicity
    {ι : Type*} [Fintype ι]
    (A D : Finset ℕ) (base baseCopies : ℕ) (anchor : ι → ℕ)
    (hA : A.Nonempty) (hAzero : 0 ∈ A) (hAcard : 3 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ A) (hDA : D ⊆ A) (hDbase : base ∉ D)
    (hCopiesPos : 1 ≤ baseCopies)
    (hCopiesCard : baseCopies ≤ A.card - 1)
    (hbudget : baseCopies + D.card ≤ A.max' hA + 1)
    (hanchor : ∀ i, anchor i ∈ A)
    (hbaseCap : ((Finset.univ : Finset ι).filter
      fun i ↦ anchor i = base).card ≤ baseCopies)
    (hdoubleCap : ∀ a ∈ D,
      ((Finset.univ : Finset ι).filter
        fun i ↦ anchor i = a).card ≤ 2)
    (hsingleCap : ∀ a ∈ A, a ≠ base → a ∉ D →
      ((Finset.univ : Finset ι).filter
        fun i ↦ anchor i = a).card ≤ 1) :
    ∀ J : Finset ι,
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
  classical
  intro J
  by_cases hJ : J.Nonempty
  · let U := J.image anchor
    have hU : U.Nonempty := hJ.image anchor
    have hUA : U ⊆ A := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact hanchor i
    have hUnion : (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b) =
        U + A := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_add]
      constructor
      · rintro ⟨i, hiJ, b, hbA, rfl⟩
        exact ⟨anchor i, Finset.mem_image.mpr ⟨i, hiJ, rfl⟩,
          b, hbA, rfl⟩
      · rintro ⟨a, haU, b, hbA, rfl⟩
        obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp haU
        exact ⟨i, hiJ, b, hbA, rfl⟩
    let cap : ℕ → ℕ := fun a ↦
      if a = base then baseCopies else if a ∈ D then 2 else 1
    have hfiber : ∀ a ∈ U,
        (J.filter fun i ↦ anchor i = a).card ≤ cap a := by
      intro a haU
      have hsub : (J.filter fun i ↦ anchor i = a) ⊆
          ((Finset.univ : Finset ι).filter fun i ↦ anchor i = a) := by
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, hi.2⟩
      have hle := Finset.card_le_card hsub
      by_cases ha0 : a = base
      · subst a
        simpa [cap] using hle.trans hbaseCap
      · by_cases haD : a ∈ D
        · simpa [cap, ha0, haD] using hle.trans (hdoubleCap a haD)
        · have haA : a ∈ A := hUA haU
          simpa [cap, ha0, haD] using
            hle.trans (hsingleCap a haA ha0 haD)
    have hJsum : J.card = ∑ a ∈ U,
        (J.filter fun i ↦ anchor i = a).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hJcap : J.card ≤ ∑ a ∈ U, cap a := by
      rw [hJsum]
      exact Finset.sum_le_sum hfiber
    let Q := U ∩ D
    have hQleD : Q.card ≤ D.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hlower :
        min (U.card + A.max' hA)
            (U.card + A.card + U.card - 3) ≤
          (U + A).card :=
      ruzsa_subset_sum_card_lower hA hU hUA hAzero (by omega) hgcd
    by_cases hUbase : base ∈ U
    · have hQerase : Q ⊆ U.erase base := by
        intro a ha
        have haU := (Finset.mem_inter.mp ha).1
        have haD := (Finset.mem_inter.mp ha).2
        exact Finset.mem_erase.mpr
          ⟨fun ha0 ↦ hDbase (ha0 ▸ haD), haU⟩
      have hQsmall : Q.card + 1 ≤ U.card := by
        have hle := Finset.card_le_card hQerase
        rw [Finset.card_erase_of_mem hUbase] at hle
        have hUpos : 0 < U.card := Finset.card_pos.mpr hU
        omega
      have hcapEq : (∑ a ∈ U, cap a) =
          baseCopies + (U.card - 1) + Q.card := by
        rw [← Finset.sum_erase_add U cap hUbase]
        have hcapBase : cap base = baseCopies := by simp [cap]
        rw [hcapBase]
        have hsumErase : (∑ a ∈ U.erase base, cap a) =
            ∑ a ∈ U.erase base, (if a ∈ D then 2 else 1) := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha0 : a ≠ base := (Finset.mem_erase.mp ha).1
          simp [cap, ha0]
        rw [hsumErase, sum_if_mem_two_one]
        have hcardErase : (U.erase base).card = U.card - 1 :=
          Finset.card_erase_of_mem hUbase
        have hinter : U.erase base ∩ D = Q := by
          ext a
          simp only [Finset.mem_inter, Finset.mem_erase, Q]
          constructor
          · rintro ⟨⟨_, haU⟩, haD⟩
            exact ⟨haU, haD⟩
          · rintro ⟨haU, haD⟩
            exact ⟨⟨fun ha0 ↦ hDbase (ha0 ▸ haD), haU⟩, haD⟩
        rw [hcardErase, hinter]
        omega
      have hJbound : J.card ≤ baseCopies + U.card + Q.card - 1 := by
        rw [hcapEq] at hJcap
        omega
      have hfirst : J.card ≤ U.card + A.max' hA := by
        have : baseCopies + Q.card ≤ A.max' hA + 1 :=
          (Nat.add_le_add_left hQleD baseCopies).trans hbudget
        omega
      have hsecond : J.card ≤ U.card + A.card + U.card - 3 := by
        omega
      rw [hUnion]
      exact (le_min hfirst hsecond).trans hlower
    · have hcapEq : (∑ a ∈ U, cap a) = U.card + Q.card := by
        have hbaseAll : ∀ a ∈ U, a ≠ base := by
          intro a haU ha0
          exact hUbase (ha0 ▸ haU)
        calc
          (∑ a ∈ U, cap a) =
              ∑ a ∈ U, (if a ∈ D then 2 else 1) := by
                apply Finset.sum_congr rfl
                intro a haU
                simp [cap, hbaseAll a haU]
          _ = U.card + Q.card := by
            simpa [Q] using sum_if_mem_two_one U D
      have hJbound : J.card ≤ U.card + Q.card := by
        rw [hcapEq] at hJcap
        exact hJcap
      have hDmax : D.card ≤ A.max' hA := by omega
      have hfirst : J.card ≤ U.card + A.max' hA := by omega
      have hsecond : J.card ≤ U.card + A.card - 1 := by
        have hDproper : D ⊂ A := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hDA, ?_⟩
          intro hEq
          apply hDbase
          rw [hEq]
          exact hbase
        have hDlt : D.card < A.card := Finset.card_lt_card hDproper
        omega
      have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hU hA
      have hsum : U.card + A.card - 1 ≤ (U + A).card := hcauchy
      rw [hUnion]
      exact hsecond.trans hsum
  · simp only [Finset.not_nonempty_iff_eq_empty] at hJ
    subst J
    simp

/-- Slots for the variable-budget Hall construction. -/
abbrev FlexibleLayerHallSlot (A D : Finset ℕ) (base copies : ℕ) :=
  Fin copies ⊕ ({a // a ∈ A.erase base} ⊕ {a // a ∈ D})

def flexibleLayerHallAnchor (A D : Finset ℕ) (base copies : ℕ) :
    FlexibleLayerHallSlot A D base copies → ℕ
  | Sum.inl _ => base
  | Sum.inr (Sum.inl a) => a.1
  | Sum.inr (Sum.inr a) => a.1

lemma flexibleLayerHallAnchor_mem
    {A D : Finset ℕ} {base copies : ℕ} (hbase : base ∈ A) (hDA : D ⊆ A)
    (i : FlexibleLayerHallSlot A D base copies) :
    flexibleLayerHallAnchor A D base copies i ∈ A := by
  rcases i with i | i
  · exact hbase
  · rcases i with a | a
    · exact Finset.mem_of_mem_erase a.2
    · exact hDA a.2

lemma flexibleLayerHallAnchor_base_fiber_cap
    {A D : Finset ℕ} {base copies : ℕ} (hcopies : 1 ≤ copies)
    (hDbase : base ∉ D) :
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
      fun i => flexibleLayerHallAnchor A D base copies i = base).card ≤ copies := by
  classical
  let f : FlexibleLayerHallSlot A D base copies → Fin copies := fun i =>
    match i with
    | Sum.inl j => j
    | Sum.inr _ => ⟨0, by omega⟩
  calc
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
        fun i => flexibleLayerHallAnchor A D base copies i = base).card ≤
        (Finset.univ : Finset (Fin copies)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi hj
        rcases i with i | i
        · rcases j with j | j
          · exact congrArg Sum.inl hij
          · rcases j with j | j
            · have hj0 : (j : ℕ) = base := by
                simpa [flexibleLayerHallAnchor] using hj
              exact False.elim ((Finset.mem_erase.mp j.2).1 hj0)
            · have hj0 : (j : ℕ) = base := by
                simpa [flexibleLayerHallAnchor] using hj
              exact False.elim (hDbase (hj0 ▸ j.2))
        · rcases i with i | i
          · have hi0 : (i : ℕ) = base := by
              simpa [flexibleLayerHallAnchor] using hi
            exact False.elim ((Finset.mem_erase.mp i.2).1 hi0)
          · have hi0 : (i : ℕ) = base := by
              simpa [flexibleLayerHallAnchor] using hi
            exact False.elim (hDbase (hi0 ▸ i.2))
    _ = copies := by simp

lemma flexibleLayerHallAnchor_double_fiber_cap
    {A D : Finset ℕ} {base copies a : ℕ} (hDbase : base ∉ D) (haD : a ∈ D) :
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
      fun i => flexibleLayerHallAnchor A D base copies i = a).card ≤ 2 := by
  classical
  have ha0 : a ≠ base := fun ha => hDbase (ha ▸ haD)
  let f : FlexibleLayerHallSlot A D base copies → Fin 2 := fun i =>
    match i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr _) => 1
  calc
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
        fun i => flexibleLayerHallAnchor A D base copies i = a).card ≤
        (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi hj
        rcases i with i | i
        · exact False.elim (ha0 (by
            simpa [flexibleLayerHallAnchor] using hi.symm))
        · rcases j with j | j
          · exact False.elim (ha0 (by
              simpa [flexibleLayerHallAnchor] using hj.symm))
          · rcases i with i | i <;> rcases j with j | j
            · have hii : (i : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hj
              subst a
              exact congrArg (fun z => Sum.inr (Sum.inl z))
                (Subtype.ext (by omega))
            · simp [f] at hij
            · simp [f] at hij
            · have hii : (i : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hj
              subst a
              exact congrArg (fun z => Sum.inr (Sum.inr z))
                (Subtype.ext (by omega))
    _ = 2 := by simp

lemma flexibleLayerHallAnchor_single_fiber_cap
    {A D : Finset ℕ} {base copies a : ℕ} (_haA : a ∈ A)
    (ha0 : a ≠ base) (haD : a ∉ D) :
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
      fun i => flexibleLayerHallAnchor A D base copies i = a).card ≤ 1 := by
  classical
  let f : FlexibleLayerHallSlot A D base copies → Fin 1 := fun _ => 0
  calc
    ((Finset.univ : Finset (FlexibleLayerHallSlot A D base copies)).filter
        fun i => flexibleLayerHallAnchor A D base copies i = a).card ≤
        (Finset.univ : Finset (Fin 1)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj _
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi hj
        rcases i with i | i
        · exact False.elim (ha0 (by
            simpa [flexibleLayerHallAnchor] using hi.symm))
        · rcases j with j | j
          · exact False.elim (ha0 (by
              simpa [flexibleLayerHallAnchor] using hj.symm))
          · rcases i with i | i <;> rcases j with j | j
            · have hii : (i : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hi
              have hjj : (j : ℕ) = a := by
                simpa [flexibleLayerHallAnchor] using hj
              subst a
              exact congrArg (fun z => Sum.inr (Sum.inl z))
                (Subtype.ext (by omega))
            · exact False.elim (haD (by
                have : (j : ℕ) = a := by
                  simpa [flexibleLayerHallAnchor] using hj
                exact this ▸ j.2))
            · exact False.elim (haD (by
                have : (i : ℕ) = a := by
                  simpa [flexibleLayerHallAnchor] using hi
                exact this ▸ i.2))
            · exact False.elim (haD (by
                have : (i : ℕ) = a := by
                  simpa [flexibleLayerHallAnchor] using hi
                exact this ▸ i.2))
    _ = 1 := by simp

lemma sum_flexibleLayerHallAnchor
    {A D : Finset ℕ} {base copies : ℕ} (g : ℕ → ℕ) :
    ∑ i : FlexibleLayerHallSlot A D base copies,
        g (flexibleLayerHallAnchor A D base copies i) =
      copies * g base +
        ∑ a ∈ A.erase base, g a + ∑ a ∈ D, g a := by
  classical
  simp [FlexibleLayerHallSlot, flexibleLayerHallAnchor,
    Finset.sum_attach, add_assoc]

/-- Weighted lower bound from the variable-budget Hall construction. -/
theorem flexibleLayerHall_weighted_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {D : Finset ℕ} {base copies : ℕ}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ firstCoordinateSet X)
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : base ∉ D)
    (hCopiesPos : 1 ≤ copies)
    (hCopiesCard : copies ≤ (firstCoordinateSet X).card - 1)
    (hbudget : copies + D.card ≤
      (firstCoordinateSet X).max' hA + 1) :
    (copies - 1) * (coordinateFiber X base).card +
        ∑ a ∈ D, (coordinateFiber X a).card + X.card ≤
      (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let anchor : FlexibleLayerHallSlot A D base copies → ℕ :=
    flexibleLayerHallAnchor A D base copies
  have hanchor : ∀ i, anchor i ∈ A :=
    flexibleLayerHallAnchor_mem hbase hDA
  have hHall : ∀ J : Finset (FlexibleLayerHallSlot A D base copies),
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
    apply hall_condition_of_flexible_layer_multiplicity A D base copies anchor
      hA hAzero hAcard hgcd hbase hDA hDbase hCopiesPos hCopiesCard hbudget
      hanchor
    · simpa [anchor] using
        flexibleLayerHallAnchor_base_fiber_cap (A := A) hCopiesPos hDbase
    · intro a haD
      simpa [anchor] using
        flexibleLayerHallAnchor_double_fiber_cap (base := base)
          (copies := copies) hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using
        flexibleLayerHallAnchor_single_fiber_cap (base := base)
          (copies := copies) haA ha0 haD
  have hweighted := sum_card_coordinateFiber_le_add_of_hall X anchor hanchor hHall
  dsimp only [anchor] at hweighted
  have hanchorSum := sum_flexibleLayerHallAnchor
    (A := A) (D := D) (base := base) (copies := copies)
    (fun a ↦ (coordinateFiber X a).card)
  rw [hanchorSum] at hweighted
  have hXcard : X.card = ∑ a ∈ A, (coordinateFiber X a).card :=
    card_eq_sum_card_coordinateFiber X
  have hsplit : ∑ a ∈ A, (coordinateFiber X a).card =
      (coordinateFiber X base).card +
        ∑ a ∈ A.erase base, (coordinateFiber X a).card := by
    rw [add_comm]
    exact (Finset.sum_erase_add A
      (fun a ↦ (coordinateFiber X a).card) hbase).symm
  dsimp only [A] at hXcard hsplit hweighted ⊢
  rw [hXcard, hsplit]
  have hcoeff :
      (copies - 1) * (coordinateFiber X base).card +
          (coordinateFiber X base).card =
        copies * (coordinateFiber X base).card := by
    have hc : copies - 1 + 1 = copies := by omega
    calc
      (copies - 1) * (coordinateFiber X base).card +
          (coordinateFiber X base).card =
        (copies - 1 + 1) * (coordinateFiber X base).card := by ring
      _ = copies * (coordinateFiber X base).card := by rw [hc]
  calc
    (copies - 1) * (coordinateFiber X base).card +
          ∑ a ∈ D, (coordinateFiber X a).card +
          ((coordinateFiber X base).card +
            ∑ a ∈ (firstCoordinateSet X).erase base,
              (coordinateFiber X a).card) =
        ((copies - 1) * (coordinateFiber X base).card +
            (coordinateFiber X base).card) +
          ∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card +
          ∑ a ∈ D, (coordinateFiber X a).card := by omega
    _ = copies * (coordinateFiber X base).card +
          ∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card +
          ∑ a ∈ D, (coordinateFiber X a).card := by rw [hcoeff]
    _ ≤ (X + X).card := hweighted

lemma almost_surjective_weight_sum_le
    {A : Finset ℕ} (hA : A.Nonempty) (w : ℕ → ℕ) {L : ℕ}
    (hw : ∀ a ∈ A, w a ≤ L)
    (choice : Fin (A.card - 1) → ℕ)
    (hchoice : ∀ i, choice i ∈ A) (hinj : Function.Injective choice) :
    ∑ a ∈ A, w a ≤ (∑ i, w (choice i)) + L := by
  classical
  let I : Finset ℕ := Finset.univ.image choice
  have hIA : I ⊆ A := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hchoice i
  have hIcard : I.card = A.card - 1 := by
    dsimp [I]
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hdiffCard : (A \ I).card = 1 := by
    rw [Finset.card_sdiff_of_subset hIA, hIcard]
    exact Nat.sub_sub_self (Finset.card_pos.mpr hA)
  have hdiff : (∑ a ∈ A \ I, w a) ≤ L := by
    calc
      (∑ a ∈ A \ I, w a) ≤ ∑ _a ∈ A \ I, L := by
        apply Finset.sum_le_sum
        intro a ha
        exact hw a (Finset.mem_sdiff.mp ha).1
      _ = L := by simp [hdiffCard]
  have hsplit : (∑ a ∈ A \ I, w a) + ∑ a ∈ I, w a = ∑ a ∈ A, w a :=
    Finset.sum_sdiff hIA
  have hchoiceSum : (∑ i, w (choice i)) = ∑ a ∈ I, w a := by
    dsimp [I]
    rw [Finset.sum_image hinj.injOn]
  rw [hchoiceSum]
  omega

lemma bad_base_choice_fiber_sum_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {A E : Finset ℕ} {goodBase badBase : ℕ}
    {H : AddSubgroup (ZMod d)}
    (hA : A.Nonempty) (hAeq : A = firstCoordinateSet X)
    (hEA : E ⊆ A) (hgood : goodBase ∈ A \ E)
    (hbad : badBase ∈ E)
    (hmax : ∀ a ∈ A,
      (coordinateFiber X a).card ≤ (coordinateFiber X goodBase).card)
    (hGoodCos : ∀ a ∈ A \ E,
      ContainedInAddCoset H (coordinateFiber X a))
    (hBadNot : ¬ContainedInAddCoset H (coordinateFiber X badBase))
    (choice : Fin (A.card - 1) → ℕ)
    (hchoice : ∀ i, choice i ∈ A) (hinj : Function.Injective choice) :
    E.card * (coordinateFiber X badBase).card +
        2 * ∑ a ∈ (A \ E).erase goodBase,
          (coordinateFiber X a).card ≤
      ∑ i,
        (coordinateFiber X badBase + coordinateFiber X (choice i)).card := by
  classical
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let N := F badBase
  let M := F goodBase
  let w : ℕ → ℕ := fun a => if a ∈ E then N else 2 * F a
  have hbadA : badBase ∈ A := hEA hbad
  have hNleM : N ≤ M := hmax badBase hbadA
  have hw : ∀ a ∈ A, w a ≤ 2 * M := by
    intro a ha
    by_cases haE : a ∈ E
    · simp only [w, if_pos haE]
      omega
    · simp only [w, if_neg haE]
      exact Nat.mul_le_mul_left 2 (hmax a ha)
  have hall := almost_surjective_weight_sum_le hA w hw choice hchoice hinj
  have hpoint : ∀ i,
      w (choice i) ≤
        (coordinateFiber X badBase + coordinateFiber X (choice i)).card := by
    intro i
    have hciA := hchoice i
    have hcX : choice i ∈ firstCoordinateSet X := by simpa [← hAeq] using hciA
    by_cases hciE : choice i ∈ E
    · simp only [w, if_pos hciE, N, F]
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr hcX)
    · have hciGood : choice i ∈ A \ E :=
        Finset.mem_sdiff.mpr ⟨hciA, hciE⟩
      have hbadX : badBase ∈ firstCoordinateSet X := by
        simpa [← hAeq] using hbadA
      simp only [w, if_neg hciE, F]
      simpa [add_comm] using
        (two_mul_card_le_add_of_coset_and_not_coset
          (coordinateFiber_nonempty_iff.mpr hcX)
          (coordinateFiber_nonempty_iff.mpr hbadX)
          (hGoodCos (choice i) hciGood) hBadNot)
  have hchoiceLower : (∑ i, w (choice i)) ≤
      ∑ i,
        (coordinateFiber X badBase + coordinateFiber X (choice i)).card := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hsumE : (∑ a ∈ E, w a) = E.card * N := by
    calc
      (∑ a ∈ E, w a) = ∑ _a ∈ E, N := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w, ha]
      _ = E.card * N := by simp
  have hsumGood : (∑ a ∈ A \ E, w a) =
      2 * ∑ a ∈ A \ E, F a := by
    calc
      (∑ a ∈ A \ E, w a) = ∑ a ∈ A \ E, 2 * F a := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w, (Finset.mem_sdiff.mp ha).2]
      _ = 2 * ∑ a ∈ A \ E, F a := by rw [Finset.mul_sum]
  have hpartition : E ∪ (A \ E) = A := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro ha
      rcases ha with ha | ⟨ha, _⟩
      · exact hEA ha
      · exact ha
    · intro ha
      by_cases haE : a ∈ E
      · exact Or.inl haE
      · exact Or.inr ⟨ha, haE⟩
  have hdisj : Disjoint E (A \ E) := by
    rw [Finset.disjoint_left]
    intro a haE haDiff
    exact (Finset.mem_sdiff.mp haDiff).2 haE
  have hsumA : (∑ a ∈ A, w a) =
      E.card * N + 2 * ∑ a ∈ A \ E, F a := by
    calc
      (∑ a ∈ A, w a) = ∑ a ∈ E ∪ (A \ E), w a := by rw [hpartition]
      _ = (∑ a ∈ E, w a) + ∑ a ∈ A \ E, w a :=
        Finset.sum_union hdisj
      _ = E.card * N + 2 * ∑ a ∈ A \ E, F a := by
        rw [hsumE, hsumGood]
  have hgoodSplit : ∑ a ∈ A \ E, F a =
      M + ∑ a ∈ (A \ E).erase goodBase, F a := by
    rw [add_comm]
    exact (Finset.sum_erase_add (A \ E) F hgood).symm
  rw [hsumA, hgoodSplit] at hall
  dsimp only [F, M, N] at hall ⊢
  have htarget :
      E.card * (coordinateFiber X badBase).card +
          2 * ∑ a ∈ (A \ E).erase goodBase,
            (coordinateFiber X a).card ≤
        ∑ i, w (choice i) := by
    omega
  exact htarget.trans hchoiceLower

/-- The reordered Hall estimate in Balasubramanian--Pandey Lemma 4.  The
`s-1` copies of the bad base see every occupied layer except at most one;
the loss from that omitted partner is absorbed by the largest good fibre. -/
theorem reordered_layerHall_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {E D : Finset ℕ} {goodBase badBase : ℕ}
    {H : AddSubgroup (ZMod d)}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hgoodBase : goodBase ∈ firstCoordinateSet X)
    (hgoodNot : goodBase ∉ E)
    (hmax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X goodBase).card)
    (hEA : E ⊆ firstCoordinateSet X)
    (hGoodCos : ∀ a ∈ firstCoordinateSet X \ E,
      ContainedInAddCoset H (coordinateFiber X a))
    (hbadBase : badBase ∈ E)
    (hBadNot : ¬ContainedInAddCoset H (coordinateFiber X badBase))
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : badBase ∉ D)
    (hDcard : D.card ≤
      (firstCoordinateSet X).max' hA + 2 - (firstCoordinateSet X).card) :
    E.card * (coordinateFiber X badBase).card +
        2 * ∑ a ∈ (firstCoordinateSet X \ E).erase goodBase,
          (coordinateFiber X a).card +
        ∑ a ∈ (firstCoordinateSet X).erase badBase,
          (coordinateFiber X a).card +
        ∑ a ∈ D, (coordinateFiber X a).card ≤
      (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let anchor : LayerHallSlot A D badBase → ℕ :=
    layerHallAnchor A D badBase
  have hbadA : badBase ∈ A := hEA hbadBase
  have hgood : goodBase ∈ A \ E := by
    exact Finset.mem_sdiff.mpr ⟨hgoodBase, hgoodNot⟩
  have hanchor : ∀ i, anchor i ∈ A :=
    layerHallAnchor_mem hbadA hDA
  have hHall : ∀ J : Finset (LayerHallSlot A D badBase),
      J.card ≤ (J.biUnion fun i => A.image fun b => anchor i + b).card := by
    apply hall_condition_of_layer_multiplicity A D badBase anchor hA hAzero
      hAcard hgcd hbadA hDA hDbase hDcard hanchor
    · simpa [anchor] using layerHallAnchor_base_fiber_cap hAcard hDbase
    · intro a haD
      simpa [anchor] using layerHallAnchor_double_fiber_cap hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using layerHallAnchor_single_fiber_cap haA ha0 haD
  obtain ⟨choice, hchoice, hinj, htotal⟩ :=
    exists_choice_sum_card_coordinateFiber_add_le_of_hall
      X anchor hanchor hHall
  let baseChoice : Fin (A.card - 1) → ℕ :=
    fun i => choice (Sum.inl i)
  have hbaseChoice : ∀ i, baseChoice i ∈ A := by
    intro i
    exact hchoice (Sum.inl i)
  have hbaseChoiceInj : Function.Injective baseChoice := by
    intro i j hij
    have hsum : anchor (Sum.inl i) + choice (Sum.inl i) =
        anchor (Sum.inl j) + choice (Sum.inl j) := by
      simpa [anchor, layerHallAnchor, baseChoice] using congrArg (badBase + ·) hij
    exact Sum.inl.inj (hinj hsum)
  have hbaseLower :
      E.card * F badBase + 2 * ∑ a ∈ (A \ E).erase goodBase, F a ≤
        ∑ i : Fin (A.card - 1),
          (coordinateFiber X badBase +
            coordinateFiber X (baseChoice i)).card := by
    exact bad_base_choice_fiber_sum_lower X hA rfl hEA hgood hbadBase hmax
      hGoodCos hBadNot baseChoice hbaseChoice hbaseChoiceInj
  have heraseLower : (∑ a ∈ A.erase badBase, F a) ≤
      ∑ i : {a // a ∈ A.erase badBase},
        (coordinateFiber X (anchor (Sum.inr (Sum.inl i))) +
          coordinateFiber X (choice (Sum.inr (Sum.inl i)))).card := by
    have h : (∑ i : {a // a ∈ A.erase badBase}, F i.1) ≤
        ∑ i : {a // a ∈ A.erase badBase},
          (coordinateFiber X (anchor (Sum.inr (Sum.inl i))) +
            coordinateFiber X (choice (Sum.inr (Sum.inl i)))).card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inr (Sum.inl i))))
    simpa [Finset.sum_attach] using h
  have hdoubleLower : (∑ a ∈ D, F a) ≤
      ∑ i : {a // a ∈ D},
        (coordinateFiber X (anchor (Sum.inr (Sum.inr i))) +
          coordinateFiber X (choice (Sum.inr (Sum.inr i)))).card := by
    have h : (∑ i : {a // a ∈ D}, F i.1) ≤
        ∑ i : {a // a ∈ D},
          (coordinateFiber X (anchor (Sum.inr (Sum.inr i))) +
            coordinateFiber X (choice (Sum.inr (Sum.inr i)))).card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inr (Sum.inr i))))
    simpa [Finset.sum_attach] using h
  have hsumLower :
      E.card * F badBase + 2 * ∑ a ∈ (A \ E).erase goodBase, F a +
          ∑ a ∈ A.erase badBase, F a + ∑ a ∈ D, F a ≤
        ∑ i : LayerHallSlot A D badBase,
          (coordinateFiber X (anchor i) + coordinateFiber X (choice i)).card := by
    have hadded := Nat.add_le_add
      (Nat.add_le_add hbaseLower heraseLower) hdoubleLower
    simpa [LayerHallSlot, anchor, layerHallAnchor, baseChoice,
      add_assoc] using hadded
  dsimp only [A, F] at hsumLower ⊢
  exact hsumLower.trans htotal

/-- Division-free arithmetic endgame for the reordered Hall argument.  `B`
is the mass of the bad fibres other than the largest bad fibre, and `G` is
the mass of the good fibres other than the global largest fibre. -/
lemma reordered_hall_average_contradiction
    {s e k M N P Q G B Q₂ Z : ℕ}
    (hs : 6 ≤ s) (he : 1 ≤ e) (hk : 3 ≤ k) (hks : k ≤ s - 1)
    (hescape : 2 * (e + k) < s + 4)
    (hP : P ≤ (s - 1) * M)
    (havg : k * P ≤ (s - 1) * Q)
    (hX : M + P = M + G + N + B)
    (hN : N ≤ M)
    (hG : G ≤ (s - e - 1) * M)
    (hB : B ≤ (e - 1) * N)
    (havg₂ : k * (M + G + B) ≤ (s - 1) * Q₂)
    (hfirst : M + P + ((s + e - 2) * M + Q) ≤ Z)
    (hsecond : M + P + ((e - 1) * N + 2 * G + Q₂) ≤ Z)
    (hsmall : 2 * Z < 5 * (M + P)) : False := by
  have hspos : 0 < s - 1 := by omega
  have hse : e + 1 ≤ s := by omega
  have hX' : P = G + N + B := by omega
  have hsumSmall :
      (M + P + ((s + e - 2) * M + Q)) +
          (M + P + ((e - 1) * N + 2 * G + Q₂)) <
        5 * (M + P) := by
    have hsum := Nat.add_le_add hfirst hsecond
    have hle :
        (M + P + ((s + e - 2) * M + Q)) +
            (M + P + ((e - 1) * N + 2 * G + Q₂)) ≤ 2 * Z := by
      omega
    exact hle.trans_lt hsmall
  have hescZ : (2 : ℤ) * ((e : ℤ) + k) ≤ (s : ℤ) + 3 := by
    exact_mod_cast (show 2 * (e + k) ≤ s + 3 by omega)
  have hsZ : (6 : ℤ) ≤ s := by exact_mod_cast hs
  have heZ : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hNZ : (N : ℤ) ≤ M := by exact_mod_cast hN
  have hGZ0 : (G : ℤ) ≤ (((s - e - 1) * M : ℕ) : ℤ) := by
    exact_mod_cast hG
  have hseCast : (((s - e - 1 : ℕ) : ℤ)) = (s : ℤ) - e - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  have hGZ : (G : ℤ) ≤ ((s : ℤ) - e - 1) * M := by
    rw [Nat.cast_mul, hseCast] at hGZ0
    exact hGZ0
  have hBZ0 : (B : ℤ) ≤ (((e - 1) * N : ℕ) : ℤ) := by
    exact_mod_cast hB
  have heCast : (((e - 1 : ℕ) : ℤ)) = (e : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hBZ : (B : ℤ) ≤ ((e : ℤ) - 1) * N := by
    rw [Nat.cast_mul, heCast] at hBZ0
    exact hBZ0
  have hD : (0 : ℤ) ≤
      ((s : ℤ) - 1) *
          (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G -
            3 * (M + G + N + B)) +
        k * ((G + N + B) + (M + G + B)) := by
    by_cases he2 : 2 ≤ e
    · have he2Z : (2 : ℤ) ≤ e := by exact_mod_cast he2
      let cG : ℤ := 2 * k - s + 1
      let cB : ℤ := 2 * k - 3 * (s - 1)
      let cN : ℤ :=
        2 * e * k - 2 * e * s + 2 * e - k - s + 1
      have hcG : cG ≤ 0 := by
        dsimp only [cG]
        omega
      have hcB : cB ≤ 0 := by
        dsimp only [cB]
        omega
      have hsk : (0 : ℤ) ≤ (s : ℤ) - k - 1 := by omega
      have hemul : (0 : ℤ) ≤ 2 * (e : ℤ) * ((s : ℤ) - k - 1) := by
        positivity
      have hcN : cN ≤ 0 := by
        dsimp only [cN]
        nlinarith
      have hpG : (0 : ℤ) ≤
          cG * (G - (((s : ℤ) - e - 1) * M)) :=
        mul_nonneg_of_nonpos_of_nonpos hcG (by omega)
      have hpB : (0 : ℤ) ≤
          cB * (B - (((e : ℤ) - 1) * N)) :=
        mul_nonneg_of_nonpos_of_nonpos hcB (by omega)
      have hpN : (0 : ℤ) ≤ cN * (N - M) :=
        mul_nonneg_of_nonpos_of_nonpos hcN (by omega)
      have hfactor : (0 : ℤ) ≤
          (2 * (k : ℤ) - 5) * ((s : ℤ) - 1) * M := by
        exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by positivity)
      dsimp only [cG, cB, cN] at hpG hpB hpN
      rw [show
        ((s : ℤ) - 1) *
              (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G -
                3 * (M + G + N + B)) +
            k * ((G + N + B) + (M + G + B)) =
          (2 * k - s + 1) * (G - ((s - e - 1) * M)) +
            (2 * k - 3 * (s - 1)) * (B - ((e - 1) * N)) +
            (2 * e * k - 2 * e * s + 2 * e - k - s + 1) * (N - M) +
            (2 * k - 5) * (s - 1) * M by ring]
      positivity
    · have heEq : e = 1 := by omega
      subst e
      have hBzero : B = 0 := by simpa using hB
      subst B
      let cG : ℤ := 2 * k - s + 1
      let cN : ℤ := -3 * (s - 1) + k
      have hcN : cN ≤ 0 := by
        dsimp only [cN]
        omega
      have hpN : (0 : ℤ) ≤ cN * (N - M) :=
        mul_nonneg_of_nonpos_of_nonpos hcN (by omega)
      have hGZ' : (G : ℤ) ≤ ((s : ℤ) - 2) * M := by
        norm_num only [Nat.cast_one] at hGZ
        convert hGZ using 1 <;> ring
      by_cases hcG0 : cG ≤ 0
      · have hpG : (0 : ℤ) ≤
            cG * (G - (((s : ℤ) - 2) * M)) :=
          mul_nonneg_of_nonpos_of_nonpos hcG0 (by omega)
        have hfactor : (0 : ℤ) ≤
            (2 * (k : ℤ) - 5) * ((s : ℤ) - 1) * M := by
          exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by positivity)
        dsimp only [cG, cN] at hpG hpN
        norm_num only [Nat.cast_one, Nat.cast_zero]
        simp only [zero_mul, add_zero]
        rw [show (s : ℤ) + 1 - 2 = s - 1 by ring]
        change (0 : ℤ) ≤
          (s - 1) * ((s - 1) * M + 2 * G - 3 * (M + G + N)) +
            k * ((G + N) + (M + G))
        rw [show
          ((s : ℤ) - 1) * (((s : ℤ) - 1) * M + 2 * G -
              3 * (M + G + N)) + k * ((G + N) + (M + G)) =
            (2 * k - s + 1 : ℤ) * (G - (((s : ℤ) - 2) * M)) +
              (-3 * ((s : ℤ) - 1) + k) * (N - M) +
              (2 * k - 5 : ℤ) * ((s : ℤ) - 1) * M by ring]
        positivity
      · have hcGpos : (0 : ℤ) ≤ cG := by omega
        have hpG : (0 : ℤ) ≤ cG * G := mul_nonneg hcGpos (by positivity)
        have hres : (0 : ℤ) ≤
            (((s : ℤ) - 1) * ((s : ℤ) - 7) + 2 * k) * M := by
          by_cases hs6eq : s = 6
          · subst s
            exact mul_nonneg (by omega) (by positivity)
          · have hs7 : (7 : ℤ) ≤ s := by omega
            apply mul_nonneg
            · have : (0 : ℤ) ≤ ((s : ℤ) - 1) * ((s : ℤ) - 7) :=
                mul_nonneg (by omega) (by omega)
              omega
            · positivity
        dsimp only [cG, cN] at hpG hpN
        norm_num only [Nat.cast_one, Nat.cast_zero]
        simp only [zero_mul, add_zero]
        rw [show (s : ℤ) + 1 - 2 = s - 1 by ring]
        change (0 : ℤ) ≤
          (s - 1) * ((s - 1) * M + 2 * G - 3 * (M + G + N)) +
            k * ((G + N) + (M + G))
        rw [show
          ((s : ℤ) - 1) * (((s : ℤ) - 1) * M + 2 * G -
              3 * (M + G + N)) + k * ((G + N) + (M + G)) =
            (2 * k - s + 1 : ℤ) * G +
              (-3 * ((s : ℤ) - 1) + k) * (N - M) +
              (((s : ℤ) - 1) * ((s : ℤ) - 7) + 2 * k) * M by ring]
        positivity
  have havgZ : (k : ℤ) * P ≤ ((s : ℤ) - 1) * Q := by
    have h0 : ((k * P : ℕ) : ℤ) ≤ (((s - 1) * Q : ℕ) : ℤ) := by
      exact_mod_cast havg
    norm_num only [Nat.cast_mul] at h0
    have hsCast : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hsCast] at h0
    exact h0
  have havg₂Z : (k : ℤ) * (M + G + B) ≤
      ((s : ℤ) - 1) * Q₂ := by
    have h0 : ((k * (M + G + B) : ℕ) : ℤ) ≤
        (((s - 1) * Q₂ : ℕ) : ℤ) := by
      exact_mod_cast havg₂
    norm_num only [Nat.cast_mul, Nat.cast_add] at h0
    have hsCast : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hsCast] at h0
    exact h0
  have hPZ : (P : ℤ) = G + N + B := by exact_mod_cast hX'
  have hmulZ :
      ((s : ℤ) - 1) * (3 * (M + P)) ≤
        ((s : ℤ) - 1) *
          (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂) := by
    have havgSum : (k : ℤ) * (P + (M + G + B)) ≤
        ((s : ℤ) - 1) * (Q + Q₂) := by
      calc
        (k : ℤ) * (P + (M + G + B)) = k * P + k * (M + G + B) := by ring
        _ ≤ ((s : ℤ) - 1) * Q + ((s : ℤ) - 1) * Q₂ :=
          add_le_add havgZ havg₂Z
        _ = ((s : ℤ) - 1) * (Q + Q₂) := by ring
    have hD' : (0 : ℤ) ≤
        ((s : ℤ) - 1) *
            (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G -
              3 * (M + P)) +
          k * (P + (M + G + B)) := by
      rw [hPZ]
      simpa only [add_assoc] using hD
    calc
      ((s : ℤ) - 1) * (3 * (M + P)) ≤
          ((s : ℤ) - 1) *
              (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G) +
            k * (P + (M + G + B)) := by
        linarith
      _ ≤ ((s : ℤ) - 1) *
            (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G) +
          ((s : ℤ) - 1) * (Q + Q₂) :=
        by
          simpa only [add_comm, add_left_comm, add_assoc] using
            add_le_add_left havgSum
              (((s : ℤ) - 1) *
                (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G))
      _ = ((s : ℤ) - 1) *
          (((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂) := by
        ring
  have hsposZ : (0 : ℤ) < (s : ℤ) - 1 := by omega
  have hcoreZ : (3 : ℤ) * (M + P) ≤
      ((s : ℤ) + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂ := by
    exact le_of_mul_le_mul_left hmulZ hsposZ
  have hcore : 3 * (M + P) ≤
      (s + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂ := by
    by_contra hnot
    have hlt :
        (s + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂ <
          3 * (M + P) := Nat.lt_of_not_ge hnot
    have hltZ0 :
        ((((s + e - 2) * M + (e - 1) * N + 2 * G + Q + Q₂ : ℕ) : ℤ)) <
          (((3 * (M + P) : ℕ) : ℤ)) := by exact_mod_cast hlt
    have hse2Cast : (((s + e - 2 : ℕ) : ℤ)) = (s : ℤ) + e - 2 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add,
      Nat.cast_mul, hse2Cast, Nat.cast_mul, heCast, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_add] at hltZ0
    norm_num only [Nat.cast_ofNat] at hltZ0
    exact (not_lt_of_ge hcoreZ) hltZ0
  omega


/-- The averaged distinguished weight controls all but three maximal fibres. -/
lemma weighted_hall_core_bound
    {s k M P Q : ℕ} (hs : 4 ≤ s) (hk : 3 ≤ k) (hks : k ≤ s - 1)
    (hP : P ≤ (s - 1) * M) (havg : k * P ≤ (s - 1) * Q) :
    M + P ≤ (s - 3) * M + Q := by
  have hpos : 0 < s - 1 := by omega
  have hgap : s - 1 - k ≤ s - 4 := by omega
  have hgapP := Nat.mul_le_mul_left (s - 1 - k) hP
  have hsplit : (s - 1) * P = k * P + (s - 1 - k) * P := by
    have : k + (s - 1 - k) = s - 1 := by omega
    calc
      (s - 1) * P = (k + (s - 1 - k)) * P := by rw [this]
      _ = k * P + (s - 1 - k) * P := by ring
  have hmul : (s - 1) * P ≤ (s - 1) * ((s - 4) * M + Q) := by
    rw [hsplit]
    calc
      k * P + (s - 1 - k) * P ≤
          (s - 1) * Q + (s - 1 - k) * ((s - 1) * M) :=
        Nat.add_le_add havg hgapP
      _ ≤ (s - 1) * Q + (s - 4) * ((s - 1) * M) := by
        gcongr
      _ = (s - 1) * ((s - 4) * M + Q) := by ring
  have hcore : P ≤ (s - 4) * M + Q :=
    Nat.le_of_mul_le_mul_left hmul hpos
  have hscoeff : s - 3 = (s - 4) + 1 := by omega
  calc
    M + P ≤ M + ((s - 4) * M + Q) := Nat.add_le_add_left hcore M
    _ = (s - 3) * M + Q := by rw [hscoeff]; ring

theorem layerHall_escape_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {D E : Finset ℕ} {base : ℕ} {H : AddSubgroup (ZMod d)}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hEA : E ⊆ firstCoordinateSet X)
    (hEbad : ∀ a ∈ E, ¬ContainedInAddCoset H (coordinateFiber X a))
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : base ∉ D)
    (hDcard : D.card ≤
      (firstCoordinateSet X).max' hA + 2 - (firstCoordinateSet X).card) :
    E.card * (coordinateFiber X base).card +
        ((firstCoordinateSet X).card - 2) *
            (coordinateFiber X base).card +
        ∑ a ∈ D, (coordinateFiber X a).card + X.card ≤
      (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let M := F base
  let anchor : LayerHallSlot A D base → ℕ := layerHallAnchor A D base
  have hanchor : ∀ i, anchor i ∈ A :=
    layerHallAnchor_mem hbase hDA
  have hHall : ∀ J : Finset (LayerHallSlot A D base),
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
    apply hall_condition_of_layer_multiplicity A D base anchor hA hAzero
      hAcard hgcd hbase hDA hDbase hDcard hanchor
    · simpa [anchor] using layerHallAnchor_base_fiber_cap hAcard hDbase
    · intro a haD
      simpa [anchor] using layerHallAnchor_double_fiber_cap hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using layerHallAnchor_single_fiber_cap haA ha0 haD
  obtain ⟨choice, hchoice, hinj⟩ :=
    exists_injective_sum_representatives_of_hall A anchor hanchor hHall
  let pair : LayerHallSlot A D base → ℕ × ℕ :=
    fun i ↦ (anchor i, choice i)
  have hpair : Function.Injective pair := by
    intro i j hp
    apply hinj
    exact congrArg (fun p : ℕ × ℕ ↦ p.1 + p.2) hp
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  let sumCoord : ℕ × ℕ → ℕ := fun p ↦ p.1 + p.2
  have hPinj : Set.InjOn sumCoord P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := hinj hpq
    subst j
    rfl
  have hPmem : ∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hanchor i, hchoice i⟩
  let badSums : Finset ℕ := E.image fun a ↦ base + a
  let Pkeep : Finset (ℕ × ℕ) := P.filter fun p ↦ sumCoord p ∉ badSums
  let Q : Finset (ℕ × ℕ) := E.image fun a ↦ (base, a)
  let R : Finset (ℕ × ℕ) := Pkeep ∪ Q
  have hEbase : base ∉ E := by
    intro hbE
    exact hEbad base hbE hbaseCos
  have hQcard : Q.card = E.card := by
    dsimp [Q]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact congrArg Prod.snd hab
  have hbadCard : badSums.card = E.card := by
    dsimp [badSums]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  have hPkeepP : Pkeep ⊆ P := Finset.filter_subset _ _
  have hPQ : Disjoint Pkeep Q := by
    rw [Finset.disjoint_left]
    intro p hpP hpQ
    have hpNot : sumCoord p ∉ badSums := (Finset.mem_filter.mp hpP).2
    obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hpQ
    apply hpNot
    exact Finset.mem_image.mpr ⟨a, haE, rfl⟩
  have hRmem : ∀ p ∈ R, p.1 ∈ A ∧ p.2 ∈ A := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hPmem p (hPkeepP hp)
    · obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hbase, hEA haE⟩
  have hQinj : Set.InjOn sumCoord Q := by
    intro p hp q hq hpq
    obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hbE, rfl⟩ := Finset.mem_image.mp hq
    have hab : a = b := by
      dsimp [sumCoord] at hpq
      omega
    subst b
    rfl
  have hRinj : Set.InjOn sumCoord R := by
    intro p hp q hq hpq
    rcases Finset.mem_union.mp hp with hpP | hpQ <;>
      rcases Finset.mem_union.mp hq with hqP | hqQ
    · exact hPinj (hPkeepP hpP) (hPkeepP hqP) hpq
    · have hpNot : sumCoord p ∉ badSums := (Finset.mem_filter.mp hpP).2
      exfalso
      apply hpNot
      obtain ⟨a, haE, hqa⟩ := Finset.mem_image.mp hqQ
      apply Finset.mem_image.mpr
      refine ⟨a, haE, ?_⟩
      calc
        base + a = sumCoord q := by rw [← hqa]
        _ = sumCoord p := hpq.symm
    · have hqNot : sumCoord q ∉ badSums := (Finset.mem_filter.mp hqP).2
      exfalso
      apply hqNot
      obtain ⟨a, haE, hpa⟩ := Finset.mem_image.mp hpQ
      apply Finset.mem_image.mpr
      refine ⟨a, haE, ?_⟩
      calc
        base + a = sumCoord p := by rw [← hpa]
        _ = sumCoord q := hpq
    · exact hQinj hpQ hqQ hpq
  let Prem : Finset (ℕ × ℕ) := P \ Pkeep
  have hPremImage : Prem.image sumCoord ⊆ badSums := by
    intro z hz
    obtain ⟨p, hpRem, rfl⟩ := Finset.mem_image.mp hz
    have hpP : p ∈ P := (Finset.mem_sdiff.mp hpRem).1
    have hpNotKeep : p ∉ Pkeep := (Finset.mem_sdiff.mp hpRem).2
    by_contra hnot
    apply hpNotKeep
    exact Finset.mem_filter.mpr ⟨hpP, hnot⟩
  have hPremCard : Prem.card ≤ E.card := by
    calc
      Prem.card = (Prem.image sumCoord).card := by
        symm
        rw [Finset.card_image_iff.mpr]
        exact hPinj.mono (Finset.sdiff_subset.trans (by rfl))
      _ ≤ badSums.card := Finset.card_le_card hPremImage
      _ = E.card := hbadCard
  have hPremWeight : (∑ p ∈ Prem, F p.1) ≤ E.card * M := by
    calc
      (∑ p ∈ Prem, F p.1) ≤ ∑ _p ∈ Prem, M := by
        apply Finset.sum_le_sum
        intro p hp
        exact hbaseMax p.1 (hPmem p (Finset.mem_sdiff.mp hp).1).1
      _ = Prem.card * M := by simp
      _ ≤ E.card * M := Nat.mul_le_mul_right M hPremCard
  have hPsplit : (∑ p ∈ P, F p.1) =
      (∑ p ∈ Pkeep, F p.1) + ∑ p ∈ Prem, F p.1 := by
    have hk : Pkeep ⊆ P := hPkeepP
    rw [add_comm]
    exact (Finset.sum_sdiff hk).symm
  have hPweight : (∑ p ∈ P, F p.1) ≤
      (∑ p ∈ Pkeep, F p.1) + E.card * M := by
    rw [hPsplit]
    exact Nat.add_le_add_left hPremWeight _
  have hKeepLower : (∑ p ∈ Pkeep, F p.1) ≤
      ∑ p ∈ Pkeep,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    apply Finset.sum_le_sum
    intro p hp
    exact Finset.card_le_card_add_right
      (coordinateFiber_nonempty_iff.mpr (hPmem p (hPkeepP hp)).2)
  have hQLower : Q.card * (2 * M) ≤
      ∑ p ∈ Q,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    calc
      Q.card * (2 * M) = ∑ _p ∈ Q, 2 * M := by simp
      _ ≤ ∑ p ∈ Q,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hp
        simpa [M, F] using two_mul_card_le_add_of_coset_and_not_coset
          (coordinateFiber_nonempty_iff.mpr hbase)
          (coordinateFiber_nonempty_iff.mpr (hEA haE))
          hbaseCos (hEbad a haE)
  have hRsum : (∑ p ∈ R,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card := by
    exact sum_card_coordinateFiber_add_le_card_add_of_pairSelection
      X R hRmem hRinj
  have hmain : (∑ p ∈ P, F p.1) + E.card * M ≤
      (X + X).card := by
    calc
      (∑ p ∈ P, F p.1) + E.card * M ≤
          ((∑ p ∈ Pkeep, F p.1) + E.card * M) + E.card * M :=
        Nat.add_le_add_right hPweight _
      _ = (∑ p ∈ Pkeep, F p.1) + Q.card * (2 * M) := by
        rw [hQcard]
        ring
      _ ≤ (∑ p ∈ Pkeep,
            (coordinateFiber X p.1 + coordinateFiber X p.2).card) +
          ∑ p ∈ Q,
            (coordinateFiber X p.1 + coordinateFiber X p.2).card :=
        Nat.add_le_add hKeepLower hQLower
      _ = ∑ p ∈ R,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
        dsimp [R]
        rw [Finset.sum_union hPQ]
      _ ≤ (X + X).card := hRsum
  have hPanchor : (∑ p ∈ P, F p.1) =
      ∑ i : LayerHallSlot A D base, F (anchor i) := by
    dsimp [P]
    rw [Finset.sum_image hpair.injOn]
  have hanchorSum := sum_layerHallAnchor (A := A) (D := D)
    (base := base) F
  have hXcard : X.card = ∑ a ∈ A, F a := by
    simpa [A, F] using card_eq_sum_card_coordinateFiber X
  have hsplit : ∑ a ∈ A, F a = F base + ∑ a ∈ A.erase base, F a := by
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  rw [hPanchor, hanchorSum] at hmain
  dsimp only [A, F, M] at hmain ⊢
  have htargetEq :
      E.card * (coordinateFiber X base).card +
          ((firstCoordinateSet X).card - 2) *
              (coordinateFiber X base).card +
          ∑ a ∈ D, (coordinateFiber X a).card + X.card =
        (((firstCoordinateSet X).card - 1) *
            (coordinateFiber X base).card +
          ∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card +
          ∑ a ∈ D, (coordinateFiber X a).card) +
        E.card * (coordinateFiber X base).card := by
    rw [hXcard, hsplit]
    have hcoeff : (firstCoordinateSet X).card - 1 =
        ((firstCoordinateSet X).card - 2) + 1 := by omega
    rw [hcoeff]
    ring
  rw [htargetEq]
  simpa [add_assoc, add_comm, add_left_comm] using hmain

/-- Arithmetic consequence of the forced-pair Hall estimate.  Here `M` is
the largest fibre, `P` is the total mass of the other fibres, `Q` is the
mass of `k` largest distinguished fibres, and `e` is the number of fibres
escaping the chosen subgroup.  Small doubling forces the escaping layers
to be a strict minority, with the exact Hall correction `k`. -/
lemma escape_count_bound
    {s e k M P Q : ℕ}
    (hs : 3 ≤ s) (_hk : 1 ≤ k) (hks : k ≤ s - 1)
    (hP : P ≤ (s - 1) * M)
    (havg : k * P ≤ (s - 1) * Q)
    (hsmall : 2 * (e * M + (s - 2) * M + Q) < 3 * (M + P)) :
    2 * (e + k) < s + 4 := by
  by_contra hnot
  have hek : s + 4 ≤ 2 * (e + k) := Nat.le_of_not_gt hnot
  have hs1 : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hs2 : ((s - 2 : ℕ) : ℤ) = (s : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hcpos : 0 ≤ (3 : ℤ) * ((s : ℤ) - 1) - 2 * k := by
    omega
  have hPz0 : (P : ℤ) ≤ (((s - 1) * M : ℕ) : ℤ) := by
    exact_mod_cast hP
  have havgz0 : (((k * P : ℕ) : ℤ)) ≤
      ((((s - 1) * Q : ℕ) : ℤ)) := by
    exact_mod_cast havg
  have hPz : (P : ℤ) ≤ ((s : ℤ) - 1) * M := by
    simpa only [Nat.cast_mul, hs1] using hPz0
  have havgz : (k : ℤ) * P ≤ ((s : ℤ) - 1) * Q := by
    simpa only [Nat.cast_mul, hs1] using havgz0
  have hPmul := mul_le_mul_of_nonneg_left hPz hcpos
  have hMnonneg : (0 : ℤ) ≤ M := by positivity
  have hsmul : (0 : ℤ) ≤ (s : ℤ) - 1 := by omega
  have hEmul : ((s : ℤ) - 1) * ((s : ℤ) + 4) * M ≤
      ((s : ℤ) - 1) * (2 * ((e : ℤ) + k)) * M := by
    gcongr
    exact_mod_cast hek
  have htarget : (3 : ℤ) * ((s : ℤ) - 1) * (M + P) ≤
      2 * ((s : ℤ) - 1) *
        (e * M + ((s : ℤ) - 2) * M + Q) := by
    nlinarith
  have hsmallz0 :
      ((2 * (e * M + (s - 2) * M + Q) : ℕ) : ℤ) <
        ((3 * (M + P) : ℕ) : ℤ) := by
    exact_mod_cast hsmall
  have hsmallz' : (2 : ℤ) *
      (e * M + ((s : ℤ) - 2) * M + Q) < 3 * (M + P) := by
    norm_num only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, hs2]
      at hsmallz0 ⊢
    exact hsmallz0
  have hspos : (0 : ℤ) < (s : ℤ) - 1 := by omega
  nlinarith

/-- Set-theoretic form of `escape_count_bound`.  A maximal fibre contained
in an `H`-coset and a maximal-weight Hall set `D` force the number of fibres
escaping all `H`-cosets to satisfy the displayed strict bound. -/
theorem layerHall_escape_count_bound
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {D E : Finset ℕ} {base : ℕ} {H : AddSubgroup (ZMod d)}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 3 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hEA : E ⊆ firstCoordinateSet X)
    (hEbad : ∀ a ∈ E, ¬ContainedInAddCoset H (coordinateFiber X a))
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : base ∉ D)
    (hDcard : D.card ≤
      (firstCoordinateSet X).max' hA + 2 - (firstCoordinateSet X).card)
    (hDpos : 1 ≤ D.card)
    (havg : D.card *
        (∑ a ∈ (firstCoordinateSet X).erase base,
          (coordinateFiber X a).card) ≤
      ((firstCoordinateSet X).card - 1) *
        ∑ a ∈ D, (coordinateFiber X a).card)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    2 * (E.card + D.card) < (firstCoordinateSet X).card + 4 := by
  classical
  let A := firstCoordinateSet X
  let s := A.card
  let M := (coordinateFiber X base).card
  let P := ∑ a ∈ A.erase base, (coordinateFiber X a).card
  let Q := ∑ a ∈ D, (coordinateFiber X a).card
  have hDsubsetErase : D ⊆ A.erase base := by
    intro a ha
    exact Finset.mem_erase.mpr
      ⟨fun hab ↦ hDbase (hab ▸ ha), hDA ha⟩
  have hDle : D.card ≤ s - 1 := by
    calc
      D.card ≤ (A.erase base).card := Finset.card_le_card hDsubsetErase
      _ = s - 1 := by
        dsimp only [s]
        rw [Finset.card_erase_of_mem (show base ∈ A by exact hbase)]
  have hP : P ≤ (s - 1) * M := by
    dsimp only [P]
    calc
      ∑ a ∈ A.erase base, (coordinateFiber X a).card ≤
          ∑ _a ∈ A.erase base, M := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbaseMax a (Finset.mem_of_mem_erase ha)
      _ = (A.erase base).card * M := by simp
      _ = (s - 1) * M := by
        rw [Finset.card_erase_of_mem (show base ∈ A by exact hbase)]
  have hXcard : X.card = M + P := by
    rw [card_eq_sum_card_coordinateFiber X]
    dsimp only [A, M, P]
    rw [add_comm]
    exact (Finset.sum_erase_add (firstCoordinateSet X)
      (fun a ↦ (coordinateFiber X a).card) hbase).symm
  have hforced := layerHall_escape_fiber_lower X hA hAzero hAcard hgcd
    hbase hbaseMax hbaseCos hEA hEbad hDA hDbase hDcard
  have hextra : 2 * (E.card * M + (s - 2) * M + Q) <
      3 * (M + P) := by
    rw [hXcard] at hforced hsmall
    change E.card * M + (s - 2) * M + Q + (M + P) ≤
      (X + X).card at hforced
    change 2 * (X + X).card < 5 * (M + P) at hsmall
    omega
  exact escape_count_bound hAcard hDpos hDle hP
    (by simpa [A, s, P, Q] using havg) hextra


/-- Choose the `R-1` largest fibres away from a distinguished base layer in
the division-free averaged form needed by (SD1), where
`R = min (max A + 3 - |A|) |A|`. -/
theorem exists_weighted_distinguishedLayerSet
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    {base : ℕ} (hbase : base ∈ firstCoordinateSet X) :
    ∃ D : Finset ℕ,
      D ⊆ firstCoordinateSet X ∧ base ∉ D ∧
      D.card =
        min ((firstCoordinateSet X).max' hA + 3 -
          (firstCoordinateSet X).card) (firstCoordinateSet X).card - 1 ∧
      D.card ≤
        (firstCoordinateSet X).max' hA + 2 -
          (firstCoordinateSet X).card ∧
      (min ((firstCoordinateSet X).max' hA + 3 -
          (firstCoordinateSet X).card) (firstCoordinateSet X).card - 1) *
          (∑ a ∈ (firstCoordinateSet X).erase base,
            (coordinateFiber X a).card) ≤
        ((firstCoordinateSet X).card - 1) *
          ∑ a ∈ D, (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let R := min (A.max' hA + 3 - A.card) A.card
  let k := R - 1
  have hRle : R ≤ A.card := Nat.min_le_right _ _
  have hk : k ≤ (A.erase base).card := by
    rw [Finset.card_erase_of_mem hbase]
    dsimp only [k]
    exact Nat.sub_le_sub_right hRle 1
  obtain ⟨D, hDerase, hDcard, havg⟩ :=
    exists_subset_card_eq_mul_sum_le
      (fun a ↦ (coordinateFiber X a).card) hk
  have hDA : D ⊆ A := hDerase.trans (Finset.erase_subset base A)
  have hDbase : base ∉ D := by
    intro hbaseD
    exact (Finset.mem_erase.mp (hDerase hbaseD)).1 rfl
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.Icc 0 (A.max' hA) := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, A.le_max' a ha⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hDle : D.card ≤ A.max' hA + 2 - A.card := by
    rw [hDcard]
    have hRleft : R ≤ A.max' hA + 3 - A.card := Nat.min_le_left _ _
    omega
  refine ⟨D, ?_, hDbase, ?_, ?_, ?_⟩
  · simpa [A] using hDA
  · simpa [A, R, k] using hDcard
  · simpa [A] using hDle
  · simpa [A, R, k, Finset.card_erase_of_mem hbase] using havg

/-- The first conclusion of the Balasubramanian--Pandey fibre theorem,
anchored at any largest fibre.  If the doubling constant is below `5/2`,
then the integer span has `2 max(A) < 3 |A|`. -/
theorem fiber_span_lt_three_halves_of_small_doubling
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    {base : ℕ} (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    2 * (firstCoordinateSet X).max' hA <
      3 * (firstCoordinateSet X).card := by
  classical
  let A := firstCoordinateSet X
  let M := A.max' hA
  let s := A.card
  let F : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let R := min (M + 3 - s) s
  let k := R - 1
  obtain ⟨D, hDA, hDbase, hDcard, hDle, havg⟩ :=
    exists_weighted_distinguishedLayerSet X hA hbase
  have hweighted := layerHall_weighted_fiber_lower X hA hAzero
    (by omega) hgcd hbase hDA hDbase hDle
  have hXcard : X.card = ∑ a ∈ A, F a := by
    simpa [A, F] using card_eq_sum_card_coordinateFiber X
  have hsplit : ∑ a ∈ A, F a = F base + ∑ a ∈ A.erase base, F a := by
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  have hmaxsum : X.card ≤ s * F base := by
    rw [hXcard]
    calc
      ∑ a ∈ A, F a ≤ ∑ _a ∈ A, F base := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbaseMax a ha
      _ = s * F base := by simp [s]
  have hpossum : X.card = F base + ∑ a ∈ A.erase base, F a := by
    rw [hXcard, hsplit]
  by_contra hnot
  have hMlarge : 3 * s ≤ 2 * M := by
    have hnot' : ¬2 * M < 3 * s := by
      simpa [A, M, s] using hnot
    omega
  have hs6 : 6 ≤ s := by simpa [A, s] using hAcard
  have hklarge : s + 4 ≤ 2 * k := by
    have hfirst : s + 4 ≤ 2 * ((M + 3 - s) - 1) := by omega
    have hsecond : s + 4 ≤ 2 * (s - 1) := by omega
    by_cases h : M + 3 - s ≤ s
    · simpa [k, R, min_eq_left h] using hfirst
    · have hsx : s ≤ M + 3 - s := Nat.le_of_not_ge h
      simpa [k, R, min_eq_right hsx] using hsecond
  have hPbound : (∑ a ∈ A.erase base, F a) ≤ (s - 1) * F base := by
    have hspos : 0 < s := by dsimp only [s]; exact Finset.card_pos.mpr hA
    have hsmul : s * F base = F base + (s - 1) * F base := by
      have hsEq : s - 1 + 1 = s := by omega
      calc
        s * F base = (s - 1 + 1) * F base :=
          congrArg (fun q ↦ q * F base) hsEq.symm
        _ = F base + (s - 1) * F base := by ring
    rw [hpossum] at hmaxsum
    rw [hsmul] at hmaxsum
    omega
  have havg' : k * (∑ a ∈ A.erase base, F a) ≤
      (s - 1) * ∑ a ∈ D, F a := by
    simpa [A, M, s, F, R, k] using havg
  have hweighted' : (s - 2) * F base + (∑ a ∈ D, F a) + X.card ≤
      (X + X).card := by
    simpa [A, s, F] using hweighted
  have hkP := Nat.mul_le_mul_right (∑ a ∈ A.erase base, F a) hklarge
  have havg2 := Nat.mul_le_mul_left 2 havg'
  have hcoefP := Nat.mul_le_mul_left (2 * s - 7) hPbound
  have hPD : (s + 4) * (∑ a ∈ A.erase base, F a) ≤
      2 * (s - 1) * ∑ a ∈ D, F a := by
    calc
      (s + 4) * (∑ a ∈ A.erase base, F a) ≤
          2 * k * (∑ a ∈ A.erase base, F a) := hkP
      _ = 2 * (k * (∑ a ∈ A.erase base, F a)) := by ring
      _ ≤ 2 * ((s - 1) * ∑ a ∈ D, F a) := havg2
      _ = 2 * (s - 1) * ∑ a ∈ D, F a := by ring
  have hcore : 3 * X.card ≤
      2 * ((s - 2) * F base + ∑ a ∈ D, F a) := by
    have hs1 : 0 < s - 1 := by omega
    apply Nat.le_of_mul_le_mul_left (c := s - 1) (hc := hs1)
    rw [hpossum]
    have hsumCoeff : (s + 4) + (2 * s - 7) = 3 * (s - 1) := by omega
    have hbCoeff : 3 + (2 * s - 7) = 2 * (s - 2) := by omega
    have hsum := Nat.add_le_add hPD hcoefP
    have haug := Nat.add_le_add_left hsum (3 * (s - 1) * F base)
    calc
      (s - 1) * (3 * (F base + ∑ a ∈ A.erase base, F a)) =
          3 * (s - 1) * F base +
            ((s + 4) * (∑ a ∈ A.erase base, F a) +
              (2 * s - 7) * (∑ a ∈ A.erase base, F a)) := by
        calc
          (s - 1) * (3 * (F base + ∑ a ∈ A.erase base, F a)) =
              3 * (s - 1) * F base +
                3 * (s - 1) * (∑ a ∈ A.erase base, F a) := by ring
          _ = 3 * (s - 1) * F base +
                ((s + 4) * (∑ a ∈ A.erase base, F a) +
                  (2 * s - 7) * (∑ a ∈ A.erase base, F a)) := by
            rw [← add_mul, hsumCoeff]
      _ ≤ 3 * (s - 1) * F base +
            (2 * (s - 1) * (∑ a ∈ D, F a) +
              (2 * s - 7) * ((s - 1) * F base)) := haug
      _ = (s - 1) *
            (2 * ((s - 2) * F base + ∑ a ∈ D, F a)) := by
        calc
          3 * (s - 1) * F base +
                (2 * (s - 1) * (∑ a ∈ D, F a) +
                  (2 * s - 7) * ((s - 1) * F base)) =
              (3 + (2 * s - 7)) * ((s - 1) * F base) +
                2 * (s - 1) * (∑ a ∈ D, F a) := by ring
          _ = 2 * (s - 2) * ((s - 1) * F base) +
                2 * (s - 1) * (∑ a ∈ D, F a) := by rw [hbCoeff]
          _ = (s - 1) *
                (2 * ((s - 2) * F base + ∑ a ∈ D, F a)) := by ring
  have hdouble :
      2 * ((s - 2) * F base + ∑ a ∈ D, F a) + 2 * X.card ≤
        2 * (X + X).card := by
    nlinarith
  omega

/-- The span conclusion of the Balasubramanian--Pandey fibre theorem in its
intrinsic form: no ordering of the fibres is assumed.  A largest fibre exists
because the first-coordinate support is finite; using it as the Hall anchor
removes the harmless ordering convention in the paper's proof. -/
theorem fiber_span_lt_three_halves
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    2 * (firstCoordinateSet X).max' hA <
      3 * (firstCoordinateSet X).card := by
  obtain ⟨base, hbase, hbaseMax⟩ :=
    Finset.exists_max_image (firstCoordinateSet X)
      (fun a ↦ (coordinateFiber X a).card) hA
  exact fiber_span_lt_three_halves_of_small_doubling X hA hAzero hAcard
    hgcd hbase hbaseMax hsmall

/-! ### Ternary generation and affine Freiman labels

The affine-alignment step in the Deshouillers--Freiman fibre theorem has a
purely algebraic half which is useful independently of the cardinality
argument.  A set of integer layers is generated from two adjacent layers by
the operation `b + c - a` (while staying inside the layer set).  An
order-two Freiman labeling is then forced to be affine on every generated
layer.  The definition below packages generation by its universal property;
this avoids choosing a stopping time for an iterated finite closure.
-/

/-- The collision-preservation formulation of an order-two Freiman
homomorphism on a finite set of natural numbers.  No codomain finiteness is
needed for the affine-propagation argument. -/
def PreservesPairSums {G : Type*} [AddCommGroup G]
    (A : Finset ℕ) (x : ℕ → G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ z ∈ A,
    a + b = c + z → x a + x b = x c + x z

/-- A pair-sum-preserving labeling is affine on every layer ternary-generated
by two adjacent layers.  This is the algebraic propagation used after the
finite dense-layer argument in Balasubramanian--Pandey Theorem 7. -/
theorem affine_on_of_ternaryGenerates
    {G : Type*} [AddCommGroup G] {A : Finset ℕ} {p q : ℕ}
    {x : ℕ → G} (hgen : TernaryGenerates A p q) (hadj : q = p + 1)
    (hfreiman : PreservesPairSums A x) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  let u : G := x q - x p
  let v : G := x p - p • u
  let C : Set ℕ := {a | a ∈ A ∧ x a = a • u + v}
  have hpA : p ∈ A := hgen.1
  have hqA : q ∈ A := hgen.2.1
  have hpC : p ∈ C := by
    refine ⟨hpA, ?_⟩
    dsimp [u, v]
    abel
  have hqC : q ∈ C := by
    refine ⟨hqA, ?_⟩
    subst q
    dsimp [u, v]
    rw [add_nsmul]
    simp only [one_nsmul]
    abel
  have hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
      z + a = b + c → z ∈ C := by
    intro a ha b hb c hc z hz hrel
    refine ⟨hz, ?_⟩
    have hpair : x z + x a = x b + x c :=
      hfreiman z hz a ha.1 b hb.1 c hc.1 hrel
    have hnsmul : z • u + a • u = b • u + c • u := by
      have := congrArg (fun n : ℕ ↦ n • u) hrel
      simpa only [add_nsmul] using this
    rw [ha.2, hb.2, hc.2] at hpair
    calc
      x z = ((b • u + v) + (c • u + v)) - (a • u + v) := by
        rw [← hpair]
        abel
      _ = (b • u + c • u) - a • u + v := by abel
      _ = (z • u + a • u) - a • u + v := by rw [hnsmul]
      _ = z • u + v := by abel
  refine ⟨u, v, ?_⟩
  intro a ha
  exact (hgen.2.2 C (fun _ h ↦ h.1) hpC hqC hclosed ha).2

/-- Dense integer layers force every pair-sum-preserving label to be
affine.  This combines the fully formalized Balasubramanian--Pandey dense
structured-set proposition with the algebraic propagation theorem above. -/
theorem affine_on_of_dense_pairSums
    {G : Type*} [AddCommGroup G] {A : Finset ℕ} {N : ℕ}
    {x : ℕ → G} (hAN : A ⊆ Finset.range N)
    (hdense : 2 * N + 3 ≤ 3 * A.card)
    (hfreiman : PreservesPairSums A x) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  obtain ⟨p, hp⟩ := exists_adjacent_ternaryGenerates_of_dense hAN hdense
  exact affine_on_of_ternaryGenerates hp rfl hfreiman

/-- Deshouillers--Freiman affine alignment at doubling constant `5/2`.
The combinatorial content is supplied by the formal `3k - 4` induction in
`StructuredSmallDoubling`; gcd normalization turns its generating step into
an adjacent pair. -/
theorem affine_on_of_small_integer_doubling
    {G : Type*} [AddCommGroup G] {A : Finset ℕ} {x : ℕ → G}
    (hzero : 0 ∈ A) (hcard : 6 ≤ A.card)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (A + A).card < 5 * A.card)
    (hfreiman : PreservesPairSums A x) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  have hthree : (A + A).card ≤ 3 * A.card - 4 := by omega
  have hstruct : ProgressionTernaryGenerates A :=
    progressionTernaryGenerates_of_three_card_sub_four (by omega) hthree
  have hgcdNat : A.gcd (fun n : ℕ ↦ n) = 1 := by
    have hgcd' := hgcd
    rw [Erdos13Additive.nat_int_finset_gcd] at hgcd'
    exact_mod_cast hgcd'
  obtain ⟨p, hp⟩ := adjacent_of_progressionTernaryGenerates hzero hgcdNat hstruct
  exact affine_on_of_ternaryGenerates hp rfl hfreiman

/-! ### The canonical common subgroup of the product fibres

For a product set `X`, put into one subgroup every difference of two
second coordinates occurring above the same first coordinate of `X + X`.
Modulo this subgroup, every occupied fibre of `X` is a point and the points
form a Freiman homomorphism of the first-coordinate set.  This isolates the
purely algebraic part of the Deshouillers--Freiman common-coset argument
from the later cardinality estimate on the subgroup.
-/

/-- Differences occurring in one first-coordinate fibre of `X + X`. -/
def sameSumFiberDifferences {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) : Set (ZMod d) :=
  {z | ∃ s y y' : _, (s, y) ∈ X + X ∧ (s, y') ∈ X + X ∧ z = y - y'}

/-- The subgroup generated by all differences in the fibres of `X + X`. -/
def pairSumDifferenceSubgroup {d : ℕ} [NeZero d]
    (X : Finset (ℕ × ZMod d)) : AddSubgroup (ZMod d) :=
  AddSubgroup.closure (sameSumFiberDifferences X)

lemma same_sum_fiber_sub_mem_pairSumDifferenceSubgroup
    {d : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)}
    {s : ℕ} {y y' : ZMod d}
    (hy : (s, y) ∈ X + X) (hy' : (s, y') ∈ X + X) :
    y - y' ∈ pairSumDifferenceSubgroup X := by
  apply AddSubgroup.subset_closure
  exact ⟨s, y, y', hy, hy', rfl⟩

/-- Any two points in one fibre of `X` differ by the canonical subgroup,
provided `X` is nonempty. -/
lemma coordinateFiber_sub_mem_pairSumDifferenceSubgroup
    {d : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)}
    (hX : X.Nonempty) {a : ℕ} {y y' : ZMod d}
    (hy : y ∈ coordinateFiber X a) (hy' : y' ∈ coordinateFiber X a) :
    y - y' ∈ pairSumDifferenceSubgroup X := by
  obtain ⟨p, hp⟩ := hX
  have hsum : (a + p.1, y + p.2) ∈ X + X := by
    exact Finset.add_mem_add (mem_coordinateFiber.mp hy) hp
  have hsum' : (a + p.1, y' + p.2) ∈ X + X := by
    exact Finset.add_mem_add (mem_coordinateFiber.mp hy') hp
  have hmem := same_sum_fiber_sub_mem_pairSumDifferenceSubgroup hsum hsum'
  convert hmem using 1 <;> simp <;> abel

/-- A chosen point of an occupied coordinate fibre. -/
noncomputable def coordinateFiberRepresentative
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) (a : ℕ) : ZMod d := by
  classical
  exact if ha : a ∈ firstCoordinateSet X then
    (coordinateFiber_nonempty_iff.mpr ha).choose else 0

lemma coordinateFiberRepresentative_mem
    {d : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)} {a : ℕ}
    (ha : a ∈ firstCoordinateSet X) :
    coordinateFiberRepresentative X a ∈ coordinateFiber X a := by
  classical
  rw [coordinateFiberRepresentative, dif_pos ha]
  exact (coordinateFiber_nonempty_iff.mpr ha).choose_spec

/-- The chosen fibre representatives preserve all pair-sum collisions after
passing to the quotient by the canonical subgroup. -/
lemma coordinateFiberRepresentative_preservesPairSums_quotient
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) :
    PreservesPairSums (firstCoordinateSet X)
      (fun a ↦ QuotientAddGroup.mk' (pairSumDifferenceSubgroup X)
        (coordinateFiberRepresentative X a)) := by
  intro a ha b hb c hc z hz habcz
  let H := pairSumDifferenceSubgroup X
  have hab : (a + b,
      coordinateFiberRepresentative X a + coordinateFiberRepresentative X b)
      ∈ X + X := by
    exact Finset.add_mem_add
      (mem_coordinateFiber.mp (coordinateFiberRepresentative_mem ha))
      (mem_coordinateFiber.mp (coordinateFiberRepresentative_mem hb))
  have hcz : (a + b,
      coordinateFiberRepresentative X c + coordinateFiberRepresentative X z)
      ∈ X + X := by
    rw [habcz]
    exact Finset.add_mem_add
      (mem_coordinateFiber.mp (coordinateFiberRepresentative_mem hc))
      (mem_coordinateFiber.mp (coordinateFiberRepresentative_mem hz))
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  exact same_sum_fiber_sub_mem_pairSumDifferenceSubgroup hab hcz

/-- The canonical quotient argument gives a common affine coset for all
fibres.  The remaining, genuinely quantitative part of the fibre theorem is
to replace the canonical subgroup by a subgroup of controlled cardinality. -/
theorem exists_affine_commonFiberCosets
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hX : X.Nonempty)
    (hzero : 0 ∈ firstCoordinateSet X)
    (hcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (firstCoordinateSet X + firstCoordinateSet X).card <
      5 * (firstCoordinateSet X).card) :
    ∃ H : AddSubgroup (ZMod d), ∃ u v : ZMod d,
      H = pairSumDifferenceSubgroup X ∧
      ∀ a ∈ firstCoordinateSet X, ∀ y ∈ coordinateFiber X a,
        y - (a • u + v) ∈ H := by
  classical
  let H := pairSumDifferenceSubgroup X
  have hfreiman : PreservesPairSums (firstCoordinateSet X)
      (fun a ↦ QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)) := by
    simpa [H] using coordinateFiberRepresentative_preservesPairSums_quotient X
  obtain ⟨ubar, vbar, haff⟩ := affine_on_of_small_integer_doubling
    hzero hcard hgcd hsmall hfreiman
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk'_surjective H ubar
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective H vbar
  refine ⟨H, u, v, rfl, ?_⟩
  intro a ha y hy
  apply (QuotientAddGroup.eq_iff_sub_mem).1
  calc
    (y : ZMod d ⧸ H) =
        (coordinateFiberRepresentative X a : ZMod d ⧸ H) := by
      apply (QuotientAddGroup.eq_iff_sub_mem).2
      exact coordinateFiber_sub_mem_pairSumDifferenceSubgroup hX hy
        (coordinateFiberRepresentative_mem ha)
    _ = a • ubar + vbar := haff a ha
    _ = (a • u + v : ZMod d ⧸ H) := by
      rw [← hu, ← hv]
      simp

/-- Once the quotient--remainder fibres lie in common affine `H`-cosets,
their inverse image is the expected cyclic progression of cosets.  This is
the final algebraic bridge from the product fibre theorem to the cyclic
inverse theorem. -/
theorem commonFiberCosets_pullback_cyclicCosetProgression
    {m d L : ℕ} [NeZero d] [NeZero (m * d)]
    (B : Finset (ZMod (m * d)))
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hrange : firstCoordinateSet (zmodQuotRemImage m d B) ⊆ Finset.range L)
    (hcoset : ∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d B),
      ∀ y ∈ coordinateFiber (zmodQuotRemImage m d B) a,
        y - (a • u + v) ∈ H) :
    B ⊆ cyclicCosetProgression
      (H.map (zmodQuotientEmbedding m d))
      (zmodQuotientEmbedding m d v)
      ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) L := by
  apply zmodQuotRem_affineFiber_subset_cyclicCosetProgression
  intro z hz
  have hzX : zmodQuotRemLift m d z ∈ zmodQuotRemImage m d B :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have ha : z.val % m ∈ firstCoordinateSet (zmodQuotRemImage m d B) :=
    mem_firstCoordinateSet.mpr ⟨(z.val / m : ZMod d), hzX⟩
  refine ⟨Finset.mem_range.mp (hrange ha), ?_⟩
  exact hcoset (z.val % m) ha (z.val / m : ZMod d)
    (mem_coordinateFiber.mpr hzX)

/-! ### Finite Fourier identities for the partial lift -/

section CyclicFourier

open Finset AddChar ZMod
open scoped ComplexConjugate

/-- Orthogonality of the standard additive characters of a cyclic group. -/
lemma sum_stdAddChar_mul_eq {t : ℕ} [NeZero t] (x : ZMod t) :
    ∑ q : ZMod t, stdAddChar (q * x) =
      if x = 0 then (t : ℂ) else 0 := by
  simpa using AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar t)

/-- The unnormalized Fourier coefficient of the indicator of `B`. -/
noncomputable def cyclicFourierCoeff {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) (q : ZMod t) : ℂ :=
  ∑ x ∈ B, stdAddChar (q * x)

lemma cyclicFourierCoeff_zero {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) :
    cyclicFourierCoeff B 0 = B.card := by
  simp [cyclicFourierCoeff]

lemma cyclicFourierCoeff_conj {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) (q : ZMod t) :
    conj (cyclicFourierCoeff B q) = cyclicFourierCoeff B (-q) := by
  simp only [cyclicFourierCoeff, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← inv_apply_eq_conj, ← map_neg_eq_inv]
  congr 2
  ring

lemma cyclicFourierCoeff_mul_conj {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) (q : ZMod t) :
    cyclicFourierCoeff B q * conj (cyclicFourierCoeff B q) =
      ∑ a ∈ B, ∑ b ∈ B, stdAddChar (q * (b - a)) := by
  simp only [cyclicFourierCoeff, map_sum, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul]
  congr 2
  ring

lemma cyclicFourierCoeff_mul_conj' {t : ℕ} [NeZero t]
    (A C : Finset (ZMod t)) (q : ZMod t) :
    cyclicFourierCoeff A q * conj (cyclicFourierCoeff C q) =
      ∑ c ∈ C, ∑ a ∈ A, stdAddChar (q * (a - c)) := by
  simp only [cyclicFourierCoeff, map_sum, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro a ha
  rw [← inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul]
  congr 2
  ring

lemma cyclicFourierCoeff_sq_mul_conj {t : ℕ} [NeZero t]
    (B C : Finset (ZMod t)) (q : ZMod t) :
    cyclicFourierCoeff B q ^ 2 * conj (cyclicFourierCoeff C q) =
      ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ C,
        stdAddChar (q * (a + b - c)) := by
  rw [pow_two, mul_assoc, cyclicFourierCoeff_mul_conj']
  simp only [cyclicFourierCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [← map_add_eq_mul]
  congr 2
  ring

/-- Parseval's identity for an indicator, in its exact complex form. -/
lemma cyclicFourier_parseval {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) :
    ∑ q : ZMod t,
        cyclicFourierCoeff B q * conj (cyclicFourierCoeff B q) =
      (t * B.card : ℕ) := by
  simp_rw [cyclicFourierCoeff_mul_conj]
  calc
    (∑ q : ZMod t, ∑ a ∈ B, ∑ b ∈ B,
        stdAddChar (q * (b - a))) =
        ∑ a ∈ B, ∑ b ∈ B, ∑ q : ZMod t,
          stdAddChar (q * (b - a)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = (t * B.card : ℕ) := by
      simp only [sum_stdAddChar_mul_eq, sub_eq_zero]
      simp
      ring

/-- Real norm form of Parseval's identity. -/
lemma cyclicFourier_parseval_norm {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) :
    ∑ q : ZMod t, ‖cyclicFourierCoeff B q‖ ^ 2 =
      (t : ℝ) * B.card := by
  have h := congrArg Complex.re (cyclicFourier_parseval B)
  simp only [Complex.re_sum, Complex.mul_conj'] at h
  norm_cast at h
  simpa [Nat.cast_mul] using h

/-- Frequencies whose additive character has order below `R`. -/
noncomputable def lowOrderFrequencies (t R : ℕ) [NeZero t] :
    Finset (ZMod t) :=
  Finset.univ.filter fun q ↦ addOrderOf q < R

/-- A cyclic group has at most `R²` elements of additive order below `R`.
This is the finite counting estimate used to discard the low-order Fourier
frequencies. -/
lemma card_lowOrderFrequencies_le_sq {t R : ℕ} [NeZero t] :
    (lowOrderFrequencies t R).card ≤ R ^ 2 := by
  classical
  let K : ℕ → Finset (ZMod t) := fun r ↦
    Finset.univ.filter fun q ↦ r • q = 0
  have hsub : lowOrderFrequencies t R ⊆
      (Finset.Ico 1 R).biUnion K := by
    intro q hq
    have hord : addOrderOf q < R := (Finset.mem_filter.mp hq).2
    have hpos : 0 < addOrderOf q := addOrderOf_pos q
    apply Finset.mem_biUnion.mpr
    refine ⟨addOrderOf q, Finset.mem_Ico.mpr ⟨hpos, hord⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, addOrderOf_nsmul_eq_zero q⟩
  calc
    (lowOrderFrequencies t R).card ≤
        ((Finset.Ico 1 R).biUnion K).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.Ico 1 R, (K r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.Ico 1 R, R := by
      apply Finset.sum_le_sum
      intro r hr
      have hrpos : 0 < r := (Finset.mem_Ico.mp hr).1
      have hrlt : r < R := (Finset.mem_Ico.mp hr).2
      exact (IsAddCyclic.card_nsmul_eq_zero_le hrpos).trans hrlt.le
    _ ≤ R ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_right R (Nat.sub_le R 1)

/-- The exact cubic Fourier identity behind the large-coefficient step. -/
lemma cyclicFourier_triple_identity {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) :
    ∑ q : ZMod t, cyclicFourierCoeff B q ^ 2 *
        conj (cyclicFourierCoeff (B + B) q) =
      (t * B.card ^ 2 : ℕ) := by
  simp_rw [cyclicFourierCoeff_sq_mul_conj]
  calc
    (∑ q : ZMod t, ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B + B,
        stdAddChar (q * (a + b - c))) =
        ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B + B, ∑ q : ZMod t,
          stdAddChar (q * (a + b - c)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = (t * B.card ^ 2 : ℕ) := by
      simp only [sum_stdAddChar_mul_eq, sub_eq_zero]
      calc
        (∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B + B,
            if a + b = c then (t : ℂ) else 0) =
            ∑ a ∈ B, ∑ b ∈ B,
              if a + b ∈ B + B then (t : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_ite_eq]
        (∑ a ∈ B, ∑ b ∈ B,
            if a + b ∈ B + B then (t : ℂ) else 0) =
            ∑ a ∈ B, ∑ _b ∈ B, (t : ℂ) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [if_pos (Finset.add_mem_add ha hb)]
        _ = (t * B.card ^ 2 : ℕ) := by
          simp
          ring

/-- Every Fourier coefficient of an indicator is bounded by the cardinality
of its support. -/
lemma norm_cyclicFourierCoeff_le_card {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) (q : ZMod t) :
    ‖cyclicFourierCoeff B q‖ ≤ B.card := by
  rw [cyclicFourierCoeff]
  calc
    ‖∑ x ∈ B, stdAddChar (q * x)‖ ≤
        ∑ x ∈ B, ‖stdAddChar (q * x)‖ := norm_sum_le _ _
    _ = B.card := by simp

lemma norm_fourierCubicTerm {t : ℕ} [NeZero t]
    (B C : Finset (ZMod t)) (q : ZMod t) :
    ‖cyclicFourierCoeff B q ^ 2 * conj (cyclicFourierCoeff C q)‖ =
      ‖cyclicFourierCoeff B q‖ ^ 2 * ‖cyclicFourierCoeff C q‖ := by
  simp [norm_pow]

/-- A named cubic summand used when splitting the Fourier identity into low-
and high-order frequencies. -/
noncomputable def cyclicFourierCubicTerm {t : ℕ} [NeZero t]
    (B C : Finset (ZMod t)) (q : ZMod t) : ℂ :=
  cyclicFourierCoeff B q ^ 2 * conj (cyclicFourierCoeff C q)

lemma norm_sum_cyclicFourierCubicTerm_le
    {t : ℕ} [NeZero t] (S B C : Finset (ZMod t)) :
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
      S.card * (B.card : ℝ) ^ 2 * C.card := by
  calc
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
        ∑ q ∈ S, ‖cyclicFourierCubicTerm B C q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ S, (B.card : ℝ) ^ 2 * C.card := by
      apply Finset.sum_le_sum
      intro q hq
      rw [cyclicFourierCubicTerm, norm_fourierCubicTerm]
      have hB := norm_cyclicFourierCoeff_le_card B q
      have hC := norm_cyclicFourierCoeff_le_card C q
      gcongr
    _ = S.card * (B.card : ℝ) ^ 2 * C.card := by
      simp
      ring

/-- High-frequency cubic terms are controlled by a coefficient bound and
the two Parseval identities.  The elementary inequality
`2uv ≤ u² + v²` avoids introducing square roots. -/
lemma norm_sum_cyclicFourierCubicTerm_le_of_coeff_bound
    {t : ℕ} [NeZero t] (S B C : Finset (ZMod t)) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ S, ‖cyclicFourierCoeff B q‖ ≤ M) :
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
      M / 2 * ((t : ℝ) * B.card + (t : ℝ) * C.card) := by
  have hSB : (∑ q ∈ S, ‖cyclicFourierCoeff B q‖ ^ 2) ≤
      ∑ q : ZMod t, ‖cyclicFourierCoeff B q‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (by intro i hi hiS; positivity)
  have hSC : (∑ q ∈ S, ‖cyclicFourierCoeff C q‖ ^ 2) ≤
      ∑ q : ZMod t, ‖cyclicFourierCoeff C q‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (by intro i hi hiS; positivity)
  calc
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
        ∑ q ∈ S, ‖cyclicFourierCubicTerm B C q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, M / 2 *
        (‖cyclicFourierCoeff B q‖ ^ 2 +
          ‖cyclicFourierCoeff C q‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [cyclicFourierCubicTerm, norm_fourierCubicTerm]
      let u := ‖cyclicFourierCoeff B q‖
      let v := ‖cyclicFourierCoeff C q‖
      have hu : 0 ≤ u := norm_nonneg _
      have hv : 0 ≤ v := norm_nonneg _
      have huv : 0 ≤ u * v := mul_nonneg hu hv
      have h₁ : u * (u * v) ≤ M * (u * v) :=
        mul_le_mul_of_nonneg_right (hM q hq) huv
      have h₂ : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by
        nlinarith [sq_nonneg (u - v)]
      calc
        u ^ 2 * v = u * (u * v) := by ring
        _ ≤ M * (u * v) := h₁
        _ ≤ M * ((u ^ 2 + v ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h₂ hM0
        _ = M / 2 * (u ^ 2 + v ^ 2) := by ring
    _ = M / 2 * ((∑ q ∈ S, ‖cyclicFourierCoeff B q‖ ^ 2) +
        ∑ q ∈ S, ‖cyclicFourierCoeff C q‖ ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M / 2 * ((∑ q : ZMod t, ‖cyclicFourierCoeff B q‖ ^ 2) +
        ∑ q : ZMod t, ‖cyclicFourierCoeff C q‖ ^ 2) := by
      gcongr
    _ = M / 2 * ((t : ℝ) * B.card + (t : ℝ) * C.card) := by
      rw [cyclicFourier_parseval_norm, cyclicFourier_parseval_norm]

/-- The low-order part contributes at most one thousandth of the cubic
identity under the source's sparsity hypothesis. -/
lemma norm_lowOrder_cyclicFourierCubicTerm_le
    {t : ℕ} [NeZero t] (B C : Finset (ZMod t))
    (hsmall : 25 * C.card ≤ 51 * B.card)
    (hdense : 1000000000 * B.card ≤ t) :
    ‖∑ q ∈ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
      (1 / 1000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
  have hbase := norm_sum_cyclicFourierCubicTerm_le
    (lowOrderFrequencies t 240) B C
  have hcardNat : (lowOrderFrequencies t 240).card ≤ 240 ^ 2 :=
    card_lowOrderFrequencies_le_sq
  have hcard : ((lowOrderFrequencies t 240).card : ℝ) ≤ 240 ^ 2 := by
    exact_mod_cast hcardNat
  have hs : 25 * (C.card : ℝ) ≤ 51 * (B.card : ℝ) := by
    exact_mod_cast hsmall
  have hd : 1000000000 * (B.card : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hdense
  have hct : 1000 * (240 : ℝ) ^ 2 * C.card ≤ (t : ℝ) := by
    nlinarith
  calc
    ‖∑ q ∈ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
        (lowOrderFrequencies t 240).card * (B.card : ℝ) ^ 2 * C.card := hbase
    _ ≤ (240 : ℝ) ^ 2 * (B.card : ℝ) ^ 2 * C.card := by
      gcongr
    _ ≤ (1 / 1000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hct
        (sq_nonneg (B.card : ℝ))
      nlinarith

/-- Under a hypothetical `13/20` bound on all high-order coefficients, the
high-order part contributes at most `99/100` of the cubic identity. -/
lemma norm_highOrder_cyclicFourierCubicTerm_le
    {t : ℕ} [NeZero t] (B C : Finset (ZMod t))
    (hsmall : 25 * C.card ≤ 51 * B.card)
    (hcoeff : ∀ q ∈ Finset.univ \ lowOrderFrequencies t 240,
      ‖cyclicFourierCoeff B q‖ ≤ (13 / 20 : ℝ) * B.card) :
    ‖∑ q ∈ Finset.univ \ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
      (99 / 100 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
  let S := Finset.univ \ lowOrderFrequencies t 240
  let M : ℝ := (13 / 20 : ℝ) * B.card
  have hM0 : 0 ≤ M := by positivity
  have hbase := norm_sum_cyclicFourierCubicTerm_le_of_coeff_bound
    S B C M hM0 (by simpa [S, M] using hcoeff)
  have hs : 25 * (C.card : ℝ) ≤ 51 * (B.card : ℝ) := by
    exact_mod_cast hsmall
  have hbc : (B.card : ℝ) + C.card ≤
      (76 / 25 : ℝ) * B.card := by
    linarith
  have hprod : (t : ℝ) * B.card * ((B.card : ℝ) + C.card) ≤
      (t : ℝ) * B.card * ((76 / 25 : ℝ) * B.card) :=
    mul_le_mul_of_nonneg_left hbc (by positivity)
  calc
    ‖∑ q ∈ Finset.univ \ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
        M / 2 * ((t : ℝ) * B.card + (t : ℝ) * C.card) := by
      simpa [S] using hbase
    _ = (13 / 40 : ℝ) *
        ((t : ℝ) * B.card * ((B.card : ℝ) + C.card)) := by
      dsimp [M]
      ring
    _ ≤ (13 / 40 : ℝ) *
        ((t : ℝ) * B.card * ((76 / 25 : ℝ) * B.card)) := by
      gcongr
    _ ≤ (99 / 100 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (t : ℝ) * (B.card : ℝ) ^ 2 := by positivity
      nlinarith

/-- Sparse small-doubling sets have a genuinely large Fourier coefficient
whose character has order at least `240`.  The constants are deliberately
rationalized from the source: `13/20` yields a `33/40` semicircle core in the
next step. -/
theorem exists_large_order_fourierCoeff
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hdense : 1000000000 * B.card ≤ t) :
    ∃ q : ZMod t, 240 ≤ addOrderOf q ∧
      (13 / 20 : ℝ) * B.card < ‖cyclicFourierCoeff B q‖ := by
  by_contra hnone
  push Not at hnone
  let L := lowOrderFrequencies t 240
  let H := Finset.univ \ L
  let C := B + B
  let T : ℝ := (t : ℝ) * (B.card : ℝ) ^ 2
  have hcoeff : ∀ q ∈ H,
      ‖cyclicFourierCoeff B q‖ ≤ (13 / 20 : ℝ) * B.card := by
    intro q hq
    have hqnot : q ∉ L := (Finset.mem_sdiff.mp hq).2
    have hnotlt : ¬addOrderOf q < 240 := by
      intro hlt
      apply hqnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    exact hnone q (le_of_not_gt hnotlt)
  have hlow : ‖∑ q ∈ L, cyclicFourierCubicTerm B C q‖ ≤
      (1 / 1000 : ℝ) * T := by
    simpa [L, C, T, mul_assoc] using
      norm_lowOrder_cyclicFourierCubicTerm_le B (B + B) hsmall hdense
  have hhigh : ‖∑ q ∈ H, cyclicFourierCubicTerm B C q‖ ≤
      (99 / 100 : ℝ) * T := by
    simpa [H, L, C, T, mul_assoc] using
      norm_highOrder_cyclicFourierCubicTerm_le B (B + B) hsmall
        (by simpa [H, L] using hcoeff)
  have htotal : (∑ q : ZMod t, cyclicFourierCubicTerm B C q) =
      ((t * B.card ^ 2 : ℕ) : ℂ) := by
    simpa [cyclicFourierCubicTerm, C] using cyclicFourier_triple_identity B
  have htotalNorm : ‖∑ q : ZMod t, cyclicFourierCubicTerm B C q‖ = T := by
    rw [htotal]
    simp [T, Nat.cast_mul, Nat.cast_pow]
  have hsplit : (∑ q : ZMod t, cyclicFourierCubicTerm B C q) =
      (∑ q ∈ H, cyclicFourierCubicTerm B C q) +
        ∑ q ∈ L, cyclicFourierCubicTerm B C q := by
    dsimp [H]
    rw [Finset.sum_sdiff (Finset.subset_univ L)]
  have hTpos : 0 < T := by
    have ht : 0 < (t : ℝ) := by exact_mod_cast NeZero.pos t
    have hb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    positivity
  have hcontr : T ≤ (991 / 1000 : ℝ) * T := by
    calc
      T = ‖∑ q : ZMod t, cyclicFourierCubicTerm B C q‖ := htotalNorm.symm
      _ = ‖(∑ q ∈ H, cyclicFourierCubicTerm B C q) +
          ∑ q ∈ L, cyclicFourierCubicTerm B C q‖ := by rw [hsplit]
      _ ≤ ‖∑ q ∈ H, cyclicFourierCubicTerm B C q‖ +
          ‖∑ q ∈ L, cyclicFourierCubicTerm B C q‖ := norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) * T + (1 / 1000 : ℝ) * T :=
        add_le_add hhigh hlow
      _ = (991 / 1000 : ℝ) * T := by ring
  nlinarith

open MeasureTheory Set
open scoped Interval

/-- Membership in the half-open semicircle used in Freiman's averaging
argument, expressed in principal-argument coordinates. -/
abbrev freimanArcMember (α θ : ℝ) : Prop :=
  if 0 ≤ α then α - Real.pi / 2 < θ else θ ≤ α + Real.pi / 2

lemma intervalIntegral_cos_div_two (a b : ℝ) :
    (∫ θ in a..b, Real.cos θ / 2) =
      (Real.sin b - Real.sin a) / 2 := by
  rw [intervalIntegral.integral_div, integral_cos]

lemma integral_Ioi_cos_div_two {l a u : ℝ} (hla : l ≤ a) (hau : a ≤ u) :
    (∫ θ in l..u, if a < θ then Real.cos θ / 2 else 0) =
      ∫ θ in a..u, Real.cos θ / 2 := by
  let f : ℝ → ℝ := fun θ ↦ Real.cos θ / 2
  have hf : Continuous f := Real.continuous_cos.div_const 2
  have hfun : (fun θ ↦ if a < θ then f θ else 0) =
      fun θ ↦ f θ - Set.indicator (Set.Iic a) f θ := by
    funext θ
    by_cases hθ : a < θ
    · simp [hθ, Set.indicator, not_le.mpr hθ]
    · simp [hθ, Set.indicator, not_lt.mp hθ]
  have hfi : IntervalIntegrable (Set.indicator (Set.Iic a) f) volume l u := by
    constructor
    · exact ((hf.integrableOn_Icc (a := l) (b := u)).indicator measurableSet_Iic).mono_set
        Set.Ioc_subset_Icc_self
    · exact ((hf.integrableOn_Icc (a := u) (b := l)).indicator measurableSet_Iic).mono_set
        Set.Ioc_subset_Icc_self
  rw [hfun, intervalIntegral.integral_sub (hf.intervalIntegrable l u) hfi]
  have hi : (∫ x in l..u, Set.indicator (Set.Iic a) f x) =
      ∫ x in l..a, f x := by
    simpa only [Set.Iic] using
      (intervalIntegral.integral_indicator (f := f) (μ := volume) ⟨hla, hau⟩)
  rw [hi]
  linarith [intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := f)
    (hf.intervalIntegrable l a) (hf.intervalIntegrable a u)]

lemma integral_Iic_cos_div_two {l a u : ℝ} (hla : l ≤ a) (hau : a ≤ u) :
    (∫ θ in l..u, if θ ≤ a then Real.cos θ / 2 else 0) =
      ∫ θ in l..a, Real.cos θ / 2 := by
  let f : ℝ → ℝ := fun θ ↦ Real.cos θ / 2
  have hfun : (fun θ ↦ if θ ≤ a then f θ else 0) =
      Set.indicator (Set.Iic a) f := by
    funext θ
    by_cases hθ : θ ≤ a
    · simp [hθ, Set.indicator]
    · simp [hθ, Set.indicator]
  rw [hfun]
  simpa only [Set.Iic] using
    (intervalIntegral.integral_indicator (f := f) (μ := volume) ⟨hla, hau⟩)

lemma integral_freimanArcWeight (α : ℝ)
    (hαlo : -Real.pi < α) (hαhi : α ≤ Real.pi) :
    (∫ θ in -(Real.pi / 2)..Real.pi / 2,
      if freimanArcMember α θ then Real.cos θ / 2 else 0) =
        (1 + Real.cos α) / 2 := by
  by_cases hα : 0 ≤ α
  · have hlo : -(Real.pi / 2) ≤ α - Real.pi / 2 := by linarith
    have hhi : α - Real.pi / 2 ≤ Real.pi / 2 := by linarith
    have hfun : (fun θ ↦ if freimanArcMember α θ then Real.cos θ / 2 else 0) =
        fun θ ↦ if α - Real.pi / 2 < θ then Real.cos θ / 2 else 0 := by
      funext θ
      simp [freimanArcMember, hα]
    rw [hfun]
    rw [integral_Ioi_cos_div_two hlo hhi, intervalIntegral_cos_div_two]
    rw [Real.sin_pi_div_two, Real.sin_sub]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  · have hα' : α < 0 := lt_of_not_ge hα
    have hlo : -(Real.pi / 2) ≤ α + Real.pi / 2 := by linarith
    have hhi : α + Real.pi / 2 ≤ Real.pi / 2 := by linarith
    have hfun : (fun θ ↦ if freimanArcMember α θ then Real.cos θ / 2 else 0) =
        fun θ ↦ if θ ≤ α + Real.pi / 2 then Real.cos θ / 2 else 0 := by
      funext θ
      simp [freimanArcMember, hα]
    rw [hfun]
    rw [integral_Iic_cos_div_two hlo hhi, intervalIntegral_cos_div_two]
    rw [Real.sin_add, Real.sin_neg, Real.sin_pi_div_two]
    simp [Real.cos_pi_div_two]
    ring

lemma intervalIntegrable_freimanArcWeight (α : ℝ) :
    IntervalIntegrable
      (fun θ ↦ if freimanArcMember α θ then Real.cos θ / 2 else 0)
      volume (-(Real.pi / 2)) (Real.pi / 2) := by
  let f : ℝ → ℝ := fun θ ↦ Real.cos θ / 2
  have hf : Continuous f := Real.continuous_cos.div_const 2
  by_cases hα : 0 ≤ α
  · have hfun : (fun θ ↦ if freimanArcMember α θ then Real.cos θ / 2 else 0) =
        fun θ ↦ f θ - Set.indicator (Set.Iic (α - Real.pi / 2)) f θ := by
      funext θ
      by_cases hθ : α - Real.pi / 2 < θ
      · simp [freimanArcMember, hα, hθ, Set.indicator, not_le.mpr hθ, f]
      · simp [freimanArcMember, hα, hθ, Set.indicator, not_lt.mp hθ, f]
    rw [hfun]
    apply IntervalIntegrable.sub (hf.intervalIntegrable _ _)
    constructor
    · exact ((hf.integrableOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)).indicator
        measurableSet_Iic).mono_set Set.Ioc_subset_Icc_self
    · exact ((hf.integrableOn_Icc (a := Real.pi / 2) (b := -(Real.pi / 2))).indicator
        measurableSet_Iic).mono_set Set.Ioc_subset_Icc_self
  · have hfun : (fun θ ↦ if freimanArcMember α θ then Real.cos θ / 2 else 0) =
        Set.indicator (Set.Iic (α + Real.pi / 2)) f := by
      funext θ
      by_cases hθ : θ ≤ α + Real.pi / 2
      · simp [freimanArcMember, hα, hθ, Set.indicator, f]
      · simp [freimanArcMember, hα, hθ, Set.indicator, f]
    rw [hfun]
    constructor
    · exact ((hf.integrableOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)).indicator
        measurableSet_Iic).mono_set Set.Ioc_subset_Icc_self
    · exact ((hf.integrableOn_Icc (a := Real.pi / 2) (b := -(Real.pi / 2))).indicator
        measurableSet_Iic).mono_set Set.Ioc_subset_Icc_self

/-- Freiman's semicircle averaging lemma with the rational constants used in
the Erdős 360 partial lift. -/
lemma exists_dense_freimanArc {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ)
    (hα : ∀ x ∈ s, -Real.pi < α x ∧ α x ≤ Real.pi)
    (hcos : (13 / 20 : ℝ) * s.card < ∑ x ∈ s, Real.cos (α x)) :
    ∃ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2),
      33 * s.card ≤ 40 * (s.filter fun x ↦ freimanArcMember (α x) θ).card := by
  classical
  by_contra hnone
  push Not at hnone
  let F : ℝ → ℝ := fun θ ↦
    ∑ x ∈ s, if freimanArcMember (α x) θ then Real.cos θ / 2 else 0
  let G : ℝ → ℝ := fun θ ↦ (33 / 40 : ℝ) * s.card * (Real.cos θ / 2)
  have hFG : ∀ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2), F θ ≤ G θ := by
    intro θ hθ
    have hcos0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hθ.1 hθ.2
    have hcardNat : 40 * (s.filter fun x ↦ freimanArcMember (α x) θ).card <
        33 * s.card := hnone θ hθ
    have hcardCast : (40 : ℝ) *
        (s.filter fun x ↦ freimanArcMember (α x) θ).card <
          33 * (s.card : ℝ) := by
      exact_mod_cast hcardNat
    have hcard : ((s.filter fun x ↦ freimanArcMember (α x) θ).card : ℝ) <
        (33 / 40 : ℝ) * s.card := by
      linarith
    have hw : 0 ≤ Real.cos θ / 2 := by positivity
    dsimp [F, G]
    rw [show (∑ x ∈ s,
        if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
        (s.filter fun x ↦ freimanArcMember (α x) θ).card *
          (Real.cos θ / 2) by
      rw [← Finset.sum_filter]
      simp]
    exact (mul_le_mul_of_nonneg_right hcard.le hw)
  have hFint : IntervalIntegrable F volume (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [F]
    have hsum := IntervalIntegrable.sum s fun x hx ↦
      intervalIntegrable_freimanArcWeight (α x)
    have hfun : (fun θ ↦ ∑ x ∈ s,
        if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
        ∑ x ∈ s, (fun θ ↦
          if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) := by
      funext θ
      induction s using Finset.induction_on with
      | empty => simp
      | @insert x s hxs ih => simp [hxs]
    rw [hfun]
    exact hsum
  have hGint : IntervalIntegrable G volume (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [G]
    exact (continuous_const.mul (Real.continuous_cos.div_const 2)).intervalIntegrable _ _
  have hintle : (∫ θ in -(Real.pi / 2)..Real.pi / 2, F θ) ≤
      ∫ θ in -(Real.pi / 2)..Real.pi / 2, G θ :=
    intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hFint hGint hFG
  have hF : (∫ θ in -(Real.pi / 2)..Real.pi / 2, F θ) =
      (s.card + ∑ x ∈ s, Real.cos (α x)) / 2 := by
    dsimp [F]
    rw [intervalIntegral.integral_finsetSum (fun x hx ↦
      intervalIntegrable_freimanArcWeight (α x))]
    calc
      (∑ x ∈ s, ∫ θ in -(Real.pi / 2)..Real.pi / 2,
          if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
          ∑ x ∈ s, (1 + Real.cos (α x)) / 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact integral_freimanArcWeight (α x) (hα x hx).1 (hα x hx).2
      _ = (s.card + ∑ x ∈ s, Real.cos (α x)) / 2 := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib]
        simp only [one_div, sum_const, nsmul_eq_mul]
        rw [Finset.sum_div]
        ring
  have hG : (∫ θ in -(Real.pi / 2)..Real.pi / 2, G θ) =
      (33 / 40 : ℝ) * s.card := by
    dsimp [G]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_cos_div_two]
    rw [Real.sin_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
    ring
  rw [hF, hG] at hintle
  nlinarith

lemma sum_cos_arg_conj_mul_eq_norm {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ x ∈ s, ‖z x‖ = 1)
    (hS : (∑ x ∈ s, z x) ≠ 0) :
    (∑ x ∈ s, Real.cos (Complex.arg
      (conj (∑ y ∈ s, z y) * z x))) =
        ‖∑ x ∈ s, z x‖ := by
  let S : ℂ := ∑ x ∈ s, z x
  have hS0 : S ≠ 0 := by simpa [S] using hS
  have hSnorm : ‖S‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [S] using hS)
  have hterm : ∀ x ∈ s,
      Real.cos (Complex.arg (conj S * z x)) =
        (conj S * z x).re / ‖S‖ := by
    intro x hx
    rw [Complex.cos_arg]
    · rw [norm_mul]
      simp [hz x hx]
    · exact mul_ne_zero (by simpa using hS0)
        (norm_ne_zero_iff.mp (by simp [hz x hx]))
  simp only [S] at hterm ⊢
  calc
    (∑ x ∈ s, Real.cos (Complex.arg
        (conj (∑ y ∈ s, z y) * z x))) =
        ∑ x ∈ s, (conj (∑ y ∈ s, z y) * z x).re /
          ‖∑ y ∈ s, z y‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x hx
    _ = (∑ x ∈ s, (conj (∑ y ∈ s, z y) * z x).re) /
        ‖∑ y ∈ s, z y‖ := by rw [Finset.sum_div]
    _ = (conj (∑ y ∈ s, z y) * (∑ x ∈ s, z x)).re /
        ‖∑ y ∈ s, z y‖ := by rw [Finset.mul_sum, Complex.re_sum]
    _ = ‖∑ x ∈ s, z x‖ ^ 2 / ‖∑ y ∈ s, z y‖ := by
      rw [Complex.conj_mul']
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    _ = ‖∑ x ∈ s, z x‖ := by
      field_simp

lemma freimanArcMember_mem_Ico {α θ : ℝ}
    (hθ : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hmem : freimanArcMember α θ) :
    α ∈ Set.Ico (θ - Real.pi / 2) (θ + Real.pi / 2) := by
  rcases hθ with ⟨hθlo, hθhi⟩
  constructor
  · by_cases hα0 : 0 ≤ α
    · linarith [Real.pi_pos]
    · simp [freimanArcMember, hα0] at hmem
      linarith
  · by_cases hα0 : 0 ≤ α
    · simp [freimanArcMember, hα0] at hmem
      linarith
    · linarith [Real.pi_pos]

/-- A large cyclic Fourier coefficient has a `33/40`-dense core whose
phase-normalized character arguments lie in one half-open semicircle. -/
theorem exists_dense_cyclicFourierArc
    {t : ℕ} [NeZero t] (B : Finset (ZMod t)) (q : ZMod t)
    (hq : (13 / 20 : ℝ) * B.card < ‖cyclicFourierCoeff B q‖) :
    ∃ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2),
      33 * B.card ≤ 40 *
        (B.filter fun x ↦ freimanArcMember
          (Complex.arg (conj (cyclicFourierCoeff B q) *
            ZMod.stdAddChar (q * x))) θ).card := by
  classical
  let z : ZMod t → ℂ := fun x ↦ ZMod.stdAddChar (q * x)
  let α : ZMod t → ℝ := fun x ↦
    Complex.arg (conj (cyclicFourierCoeff B q) * z x)
  have hcoeff : (∑ x ∈ B, z x) = cyclicFourierCoeff B q := by
    simp [z, cyclicFourierCoeff]
  have hcoeff0 : cyclicFourierCoeff B q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hnonneg : 0 ≤ (13 / 20 : ℝ) * B.card := by positivity
    linarith
  have hz : ∀ x ∈ B, ‖z x‖ = 1 := by
    intro x hx
    simp [z]
  have hsum := sum_cos_arg_conj_mul_eq_norm B z hz (by simpa [hcoeff] using hcoeff0)
  have hcos : (13 / 20 : ℝ) * B.card < ∑ x ∈ B, Real.cos (α x) := by
    rw [show (∑ x ∈ B, Real.cos (α x)) = ‖cyclicFourierCoeff B q‖ by
      simpa [α, hcoeff] using hsum]
    exact hq
  obtain ⟨θ, hθ, hcard⟩ := exists_dense_freimanArc B α
    (fun x hx ↦ ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩) hcos
  refine ⟨θ, hθ, ?_⟩
  simpa [α, z] using hcard

lemma arg_div_eq_sub_arg_of_mem_Ioc {z w : ℂ}
    (hw : w ≠ 0) (hnorm : ‖z‖ = ‖w‖)
    (hsub : z.arg - w.arg ∈ Set.Ioc (-Real.pi) Real.pi) :
    (z / w).arg = z.arg - w.arg := by
  have hwNorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hzrep := Complex.norm_mul_exp_arg_mul_I z
  have hwrep := Complex.norm_mul_exp_arg_mul_I w
  have hquot : z / w =
      Complex.exp (((z.arg - w.arg : ℝ) : ℂ) * Complex.I) := by
    calc
      z / w = (‖z‖ * Complex.exp (z.arg * Complex.I)) /
          (‖w‖ * Complex.exp (w.arg * Complex.I)) := by rw [hzrep, hwrep]
      _ = Complex.exp (z.arg * Complex.I) /
          Complex.exp (w.arg * Complex.I) := by
        rw [hnorm]
        have hwNormC : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwNorm
        field_simp [hwNormC]
      _ = Complex.exp (((z.arg - w.arg : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_sub]
        congr 1
        push_cast
        ring
  rw [hquot, Complex.arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).mpr]
  simpa [two_mul] using hsub

lemma stdAddChar_eq_exp_val {m : ℕ} [NeZero m] (r : ZMod m) :
    ZMod.stdAddChar r =
      Complex.exp (((2 * Real.pi * r.val / m : ℝ) : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

lemma two_val_lt_of_stdAddChar_arg_mem_Ico {m : ℕ} [NeZero m]
    (r : ZMod m)
    (harg : (ZMod.stdAddChar r).arg ∈ Set.Ico 0 Real.pi) :
    2 * r.val < m := by
  let x : ℝ := 2 * Real.pi * r.val / m
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hv : (r.val : ℝ) < m := by exact_mod_cast ZMod.val_lt r
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 * Real.pi := by
    dsimp [x]
    apply (div_lt_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  rw [stdAddChar_eq_exp_val, Complex.arg_exp_mul_I] at harg
  change toIocMod Real.two_pi_pos (-Real.pi) x ∈ Set.Ico 0 Real.pi at harg
  by_contra hnot
  have hmx : (m : ℝ) ≤ 2 * r.val := by exact_mod_cast (not_lt.mp hnot)
  have hπx : Real.pi ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  by_cases heq : x = Real.pi
  · have hself : toIocMod Real.two_pi_pos (-Real.pi) x = x :=
      (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> nlinarith [Real.pi_pos])
    rw [hself, heq] at harg
    exact harg.2.false
  · have hπx' : Real.pi < x := lt_of_le_of_ne hπx (Ne.symm heq)
    have hy : x - 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have hself : toIocMod Real.two_pi_pos (-Real.pi) (x - 2 * Real.pi) =
        x - 2 * Real.pi := (toIocMod_eq_self Real.two_pi_pos).mpr (by
          simpa [two_mul] using hy)
    have hperiod : toIocMod Real.two_pi_pos (-Real.pi) (x - 2 * Real.pi) =
        toIocMod Real.two_pi_pos (-Real.pi) x := by
      simpa [two_nsmul] using
        (toIocMod_sub Real.two_pi_pos (-Real.pi) x)
    have hargneg : toIocMod Real.two_pi_pos (-Real.pi) x < 0 := by
      rw [← hperiod, hself]
      nlinarith [Real.pi_pos]
    exact (not_lt_of_ge harg.1) hargneg

/-- A half-open semicircle of character values becomes the standard
no-wrap half interval after translation by a point of the set. -/
lemma exists_translate_two_val_lt_of_arg_mem_halfArc
    {ι : Type*} [DecidableEq ι] {m : ℕ} [NeZero m]
    (C : Finset ι) (hC : C.Nonempty) (r : ι → ZMod m)
    (γ : ℂ) (hγ : γ ≠ 0) (l : ℝ)
    (harc : ∀ x ∈ C,
      (γ * ZMod.stdAddChar (r x)).arg ∈ Set.Ico l (l + Real.pi)) :
    ∃ x₀ ∈ C, ∀ x ∈ C, 2 * ((r x - r x₀).val) < m := by
  classical
  let α : ι → ℝ := fun x ↦ (γ * ZMod.stdAddChar (r x)).arg
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image C α hC
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  have hxarc := harc x hx
  have h0arc := harc x₀ hx₀
  have hdiff : α x - α x₀ ∈ Set.Ico 0 Real.pi := by
    constructor
    · linarith [hmin x hx]
    · linarith [hxarc.2, h0arc.1]
  have hargdiv :
      ((γ * ZMod.stdAddChar (r x)) /
        (γ * ZMod.stdAddChar (r x₀))).arg = α x - α x₀ := by
    apply arg_div_eq_sub_arg_of_mem_Ioc
    · exact mul_ne_zero hγ (norm_ne_zero_iff.mp (by simp))
    · simp
    · constructor
      · linarith [hdiff.1, Real.pi_pos]
      · exact hdiff.2.le
  have hquot :
      (γ * ZMod.stdAddChar (r x)) /
        (γ * ZMod.stdAddChar (r x₀)) =
          ZMod.stdAddChar (r x - r x₀) := by
    rw [AddChar.map_sub_eq_div]
    field_simp [hγ]
  apply two_val_lt_of_stdAddChar_arg_mem_Ico
  rw [← hquot, hargdiv]
  exact hdiff

end CyclicFourier

/-- The image of a cyclic finset under the affine map `x ↦ c + u*x`. -/
def zmodAffineImage {t : ℕ} [NeZero t]
    (c u : ZMod t) (B : Finset (ZMod t)) : Finset (ZMod t) :=
  B.image fun x ↦ c + u * x

/-- A unit-affine change of coordinates preserves cardinality. -/
lemma zmodAffineImage_card {t : ℕ} [NeZero t]
    {c u : ZMod t} (hu : IsUnit u) (B : Finset (ZMod t)) :
    (zmodAffineImage c u B).card = B.card := by
  rw [zmodAffineImage, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  apply hu.mul_left_cancel
  exact add_left_cancel hxy

/-- Doubling commutes with a unit-affine change of coordinates, with the
translation doubled.  The identity itself does not require the unit
hypothesis. -/
lemma zmodAffineImage_add {t : ℕ} [NeZero t]
    (c u : ZMod t) (B : Finset (ZMod t)) :
    zmodAffineImage c u B + zmodAffineImage c u B =
      zmodAffineImage (c + c) u (B + B) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
    ring
  · intro hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    rw [show c + c + u * (a + b) =
        (c + u * a) + (c + u * b) by ring]
    apply Finset.add_mem_add
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

/-- A unit-affine change of coordinates preserves the size of the double
sumset. -/
lemma zmodAffineImage_add_card {t : ℕ} [NeZero t]
    {c u : ZMod t} (hu : IsUnit u) (B : Finset (ZMod t)) :
    (zmodAffineImage c u B + zmodAffineImage c u B).card =
      (B + B).card := by
  rw [zmodAffineImage_add, zmodAffineImage_card hu]

/-- Multiplication by a unit is an additive equivalence of the cyclic
group.  We use this concrete equivalence to pull rectified progressions and
subgroup cosets back through a change of coordinates. -/
def unitMulAddEquiv {t : ℕ} [NeZero t] (w : (ZMod t)ˣ) :
    ZMod t ≃+ ZMod t where
  toFun x := (w : ZMod t) * x
  invFun x := (↑(w⁻¹) : ZMod t) * x
  left_inv x := by
    change (↑(w⁻¹) : ZMod t) * ((w : ZMod t) * x) = x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv x := by
    change (w : ZMod t) * ((↑(w⁻¹) : ZMod t) * x) = x
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  map_add' x y := by ring

@[simp] lemma unitMulAddEquiv_apply {t : ℕ} [NeZero t]
    (w : (ZMod t)ˣ) (x : ZMod t) :
    unitMulAddEquiv w x = (w : ZMod t) * x := rfl

@[simp] lemma unitMulAddEquiv_symm_apply {t : ℕ} [NeZero t]
    (w : (ZMod t)ˣ) (x : ZMod t) :
    (unitMulAddEquiv w).symm x = (↑(w⁻¹) : ZMod t) * x := rfl

/-- Pull a finite set back through the affine equivalence `x ↦ c + w*x`. -/
noncomputable def zmodAffinePreimage
    {t : ℕ} [NeZero t] (w : (ZMod t)ˣ) (c : ZMod t)
    (E : Finset (ZMod t)) : Finset (ZMod t) :=
  E.image fun y ↦ (unitMulAddEquiv w).symm (y - c)

/-- The inverse unit-affine image preserves cardinality. -/
lemma card_zmodAffinePreimage
    {t : ℕ} [NeZero t] (w : (ZMod t)ˣ) (c : ZMod t)
    (E : Finset (ZMod t)) :
    (zmodAffinePreimage w c E).card = E.card := by
  rw [zmodAffinePreimage, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  have h := congrArg (unitMulAddEquiv w) hxy
  simp only [AddEquiv.apply_symm_apply] at h
  exact sub_left_injective h

/-- Pulling back a subset of an affine image lands in the original set. -/
lemma zmodAffinePreimage_subset
    {t : ℕ} [NeZero t] (w : (ZMod t)ˣ) (c : ZMod t)
    {C E : Finset (ZMod t)}
    (hE : E ⊆ zmodAffineImage c (w : ZMod t) C) :
    zmodAffinePreimage w c E ⊆ C := by
  intro x hx
  obtain ⟨y, hyE, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z, hzC, hzy⟩ := Finset.mem_image.mp (hE hyE)
  have heq : (unitMulAddEquiv w).symm (y - c) = z := by
    apply (unitMulAddEquiv w).injective
    rw [AddEquiv.apply_symm_apply]
    rw [← hzy]
    simp [unitMulAddEquiv]
  rwa [heq]

/-- Inverse unit-affine images of subgroup cosets are subgroup cosets of
the same order. -/
lemma zmodAffinePreimage_coset
    {t : ℕ} [NeZero t] (w : (ZMod t)ˣ) (c : ZMod t)
    {E : Finset (ZMod t)} {K : AddSubgroup (ZMod t)}
    (hcos : ContainedInAddCoset K E) :
    ∃ K' : AddSubgroup (ZMod t),
      Nat.card K' = Nat.card K ∧
      ContainedInAddCoset K' (zmodAffinePreimage w c E) := by
  let e := unitMulAddEquiv w
  let K' : AddSubgroup (ZMod t) := K.comap e.toAddMonoidHom
  have hmap : K'.map e.toAddMonoidHom = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · change e (e.symm y) ∈ K
        simpa using hy
      · simp
  let ek : K' ≃+ K :=
    (e.addSubgroupMap K').trans (AddEquiv.addSubgroupCongr hmap)
  obtain ⟨a, ha⟩ := hcos
  refine ⟨K', Nat.card_congr ek.toEquiv, e.symm (a - c), ?_⟩
  intro x hx
  obtain ⟨y, hyE, rfl⟩ := Finset.mem_image.mp hx
  have hycos := ha hyE
  rw [Set.mem_vadd_set] at hycos ⊢
  obtain ⟨k, hk, hak⟩ := hycos
  refine ⟨e.symm k, ?_, ?_⟩
  · change e (e.symm k) ∈ K
    simpa using hk
  · simp only [vadd_eq_add]
    apply e.injective
    simp only [map_add, e.apply_symm_apply]
    have hak' : a + k = y := by simpa [vadd_eq_add] using hak
    rw [← hak']
    simp [e]
    abel

/-- Compatibility of the standard character with the factorization of a
cyclic frequency into its additive order and a complementary divisor. -/
lemma stdAddChar_mul_factor_eq_cast
    (m g : ℕ) [NeZero m] [NeZero (m * g)] (y : ZMod (m * g)) :
    ZMod.stdAddChar ((g : ZMod (m * g)) * y) =
      ZMod.stdAddChar (ZMod.cast y : ZMod m) := by
  rw [← ZMod.natCast_zmod_val y]
  rw [show (g : ZMod (m * g)) * (y.val : ZMod (m * g)) =
      ((g * y.val : ℕ) : ZMod (m * g)) by push_cast; ring]
  rw [show ZMod.cast (y.val : ZMod (m * g)) = (y.val : ZMod m) by simp]
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hg : (g : ℂ) ≠ 0 := by
    exact_mod_cast (fun hg0 ↦ NeZero.ne (m * g) (by simp [hg0]) : g ≠ 0)
  field_simp [hm, hg]

/-- Every cyclic frequency is a unit times the complementary divisor of its
additive order. -/
lemma exists_unit_divisor_factor
    {t : ℕ} [NeZero t] (q : ZMod t) :
    ∃ g : ℕ, ∃ w : (ZMod t)ˣ,
      t = addOrderOf q * g ∧ q = (w : ZMod t) * g := by
  obtain ⟨g, hgt, u, hu, hq⟩ := ZMod.eq_unit_mul_divisor q
  let w : (ZMod t)ˣ := hu.unit
  have hw : (w : ZMod t) = u := hu.unit_spec
  have hord : addOrderOf q = t / g := by
    rw [hq]
    have heq : (w : ZMod t) * (g : ZMod t) =
        unitMulAddEquiv w (g : ZMod t) := by simp [unitMulAddEquiv]
    rw [← hw, heq, AddEquiv.addOrderOf_eq]
    rw [ZMod.addOrderOf_coe g (NeZero.ne t)]
    rw [Nat.gcd_eq_right_iff_dvd.mpr hgt]
  refine ⟨g, w, ?_, ?_⟩
  · rw [hord]
    exact (Nat.div_mul_cancel hgt).symm
  · simpa [hw] using hq

lemma stdAddChar_mul_factor_eq_cast_of_eq
    {t m g : ℕ} [NeZero t] [NeZero m] (ht : t = m * g)
    (y : ZMod t) :
    ZMod.stdAddChar ((g : ZMod t) * y) =
      ZMod.stdAddChar (ZMod.cast y : ZMod m) := by
  subst t
  exact stdAddChar_mul_factor_eq_cast m g y

/-- The checked Fourier partial-lift core, before completing its fibers. -/
theorem exists_dense_cyclic_partialLiftCore
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ w : (ZMod t)ˣ, ∃ C : Finset (ZMod t), ∃ x₀ : ZMod t,
      t = m * g ∧ 240 ≤ m ∧ x₀ ∈ C ∧ C ⊆ B ∧
        33 * B.card ≤ 40 * C.card ∧
        ∀ x ∈ C,
          2 * ((ZMod.cast ((w : ZMod t) * x) : ZMod m) -
            ZMod.cast ((w : ZMod t) * x₀)).val < m := by
  classical
  obtain ⟨q, hqord, hqcoeff⟩ :=
    exists_large_order_fourierCoeff B hB hsmall hsparse
  obtain ⟨g, w, htg, hq⟩ := exists_unit_divisor_factor q
  let m := addOrderOf q
  have hmpos : 0 < m := by exact addOrderOf_pos q
  have hm : NeZero m := ⟨hmpos.ne'⟩
  let : NeZero m := hm
  obtain ⟨θ, hθ, hcard⟩ := exists_dense_cyclicFourierArc B q hqcoeff
  let C : Finset (ZMod t) := B.filter fun x ↦ freimanArcMember
    (Complex.arg (conj (cyclicFourierCoeff B q) *
      ZMod.stdAddChar (q * x))) θ
  have hCB : C ⊆ B := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hcard' : 33 * B.card ≤ 40 * C.card := by
    simpa [C] using hcard
  have hC : C.Nonempty := by
    apply Finset.card_pos.mp
    have hBcard : 0 < B.card := Finset.card_pos.mpr hB
    omega
  have hcoeff0 : conj (cyclicFourierCoeff B q) ≠ 0 := by
    have hnorm : 0 < ‖cyclicFourierCoeff B q‖ := by
      have hnonneg : 0 ≤ (13 / 20 : ℝ) * B.card := by positivity
      linarith
    intro hzero
    have horig : cyclicFourierCoeff B q = 0 := by
      have hc := congrArg conj hzero
      simpa using hc
    rw [horig, norm_zero] at hnorm
    exact lt_irrefl 0 hnorm
  have hchar : ∀ x : ZMod t,
      ZMod.stdAddChar (q * x) =
        ZMod.stdAddChar (ZMod.cast ((w : ZMod t) * x) : ZMod m) := by
    intro x
    calc
      ZMod.stdAddChar (q * x) =
          ZMod.stdAddChar ((g : ZMod t) * ((w : ZMod t) * x)) := by
            apply congrArg ZMod.stdAddChar
            rw [hq]
            ring
      _ = ZMod.stdAddChar
          (ZMod.cast ((w : ZMod t) * x) : ZMod m) :=
            stdAddChar_mul_factor_eq_cast_of_eq htg _
  have harc : ∀ x ∈ C,
      (conj (cyclicFourierCoeff B q) *
        ZMod.stdAddChar
          (ZMod.cast ((w : ZMod t) * x) : ZMod m)).arg ∈
        Set.Ico (θ - Real.pi / 2) (θ + Real.pi / 2) := by
    intro x hx
    have hxmem := (Finset.mem_filter.mp hx).2
    have hphase := freimanArcMember_mem_Ico hθ hxmem
    rw [← hchar x]
    exact hphase
  obtain ⟨x₀, hx₀, hhalf⟩ :=
    exists_translate_two_val_lt_of_arg_mem_halfArc C hC
      (fun x ↦ ZMod.cast ((w : ZMod t) * x))
      (conj (cyclicFourierCoeff B q)) hcoeff0
      (θ - Real.pi / 2) (by
        intro x hx
        convert harc x hx using 1 <;> ring_nf)
  refine ⟨m, g, w, C, x₀, ?_, ?_, hx₀, hCB, hcard', ?_⟩
  · simpa [m] using htg
  · simpa [m] using hqord
  · exact hhalf

lemma zmod_cast_val_eq_mod {t m : ℕ} [NeZero t] [NeZero m]
    (z : ZMod t) :
    (ZMod.cast z : ZMod m).val = z.val % m := by
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

/-- The Fourier core after the unit-affine cut has no carries in its first
quotient coordinate. -/
theorem exists_dense_cyclic_noCarryCore
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ w : (ZMod t)ˣ, ∃ c : ZMod t,
      ∃ C D : Finset (ZMod t),
      t = m * g ∧ 240 ≤ m ∧ C ⊆ B ∧
        33 * B.card ≤ 40 * C.card ∧ D = zmodAffineImage c (w : ZMod t) C ∧
        0 ∈ D ∧ D.card = C.card ∧ (D + D).card = (C + C).card ∧
        ∀ z ∈ D, 2 * (z.val % m) < m := by
  classical
  obtain ⟨m, g, w, C, x₀, htg, hm240, hx₀, hCB, hCcard, hhalf⟩ :=
    exists_dense_cyclic_partialLiftCore B hB hsmall hsparse
  have hmpos : 0 < m := by omega
  let : NeZero m := ⟨hmpos.ne'⟩
  let c : ZMod t := -((w : ZMod t) * x₀)
  let D := zmodAffineImage c (w : ZMod t) C
  have hDzero : 0 ∈ D := by
    apply Finset.mem_image.mpr
    refine ⟨x₀, hx₀, ?_⟩
    dsimp [c]
    abel
  have hDcard : D.card = C.card := zmodAffineImage_card w.isUnit C
  have hDsum : (D + D).card = (C + C).card :=
    zmodAffineImage_add_card w.isUnit C
  have hmt : m ∣ t := by
    rw [htg]
    exact dvd_mul_right m g
  have hDhalf : ∀ z ∈ D, 2 * (z.val % m) < m := by
    intro z hz
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hz
    have hcast :
        ZMod.cast (c + (w : ZMod t) * x) =
          (ZMod.cast ((w : ZMod t) * x) : ZMod m) -
            ZMod.cast ((w : ZMod t) * x₀) := by
      rw [show ZMod.cast (c + (w : ZMod t) * x) =
          ZMod.castHom hmt (ZMod m) (c + (w : ZMod t) * x) by
        simp [ZMod.castHom_apply]]
      rw [map_add]
      rw [show c = -((w : ZMod t) * x₀) by rfl, map_neg]
      simp only [ZMod.castHom_apply]
      ring
    rw [← zmod_cast_val_eq_mod]
    rw [hcast]
    exact hhalf x hxC
  refine ⟨m, g, w, c, C, D, htg, hm240, hCB, hCcard, rfl,
    hDzero, hDcard, hDsum, hDhalf⟩

/-- Package the Fourier core as an actual subset of
`ℕ × ZMod g`.  Besides the exact cardinality identities, this records the
strict `5/2` doubling threshold consumed by the fibre theorem. -/
theorem exists_dense_cyclic_smallProductCore
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ w : (ZMod t)ˣ, ∃ C : Finset (ZMod t),
      ∃ D : Finset (ZMod (m * g)), ∃ X : Finset (ℕ × ZMod g),
        t = m * g ∧ 240 ≤ m ∧ C ⊆ B ∧
        33 * B.card ≤ 40 * C.card ∧ 0 ∈ D ∧
        D.card = C.card ∧ X = zmodQuotRemImage m g D ∧
        X.card = D.card ∧ (X + X).card = (D + D).card ∧
        (0, 0) ∈ X ∧
        (∀ p ∈ X, p.1 < m) ∧
        2 * (X + X).card < 5 * X.card := by
  classical
  obtain ⟨m, g, w, c, C, D, htg, hm240, hCB, hCcard, hDaff,
      hDzero, hDcard, hDsum, hDhalf⟩ :=
    exists_dense_cyclic_noCarryCore B hB hsmall hsparse
  subst t
  have hm : 0 < m := by omega
  have hmg : 0 < m * g := NeZero.pos (m * g)
  have hg : 0 < g := Nat.pos_of_mul_pos_left hmg
  let : NeZero g := ⟨hg.ne'⟩
  let X := zmodQuotRemImage m g D
  have hnowrap : ∀ x ∈ D, ∀ y ∈ D,
      x.val % m + y.val % m < m := by
    intro x hx y hy
    have hxx := hDhalf x hx
    have hyy := hDhalf y hy
    omega
  have hXcard : X.card = D.card :=
    zmodQuotRemImage_card hm D
  have hXsum : (X + X).card = (D + D).card :=
    zmodQuotRemImage_add_card hm D hnowrap
  have hcoreSmall : 2 * (D + D).card < 5 * D.card := by
    have hCC : (C + C).card ≤ (B + B).card :=
      Finset.card_le_card (Finset.add_subset_add hCB hCB)
    have hsmall' : 25 * (C + C).card ≤ 51 * B.card :=
      (Nat.mul_le_mul_left 25 hCC).trans hsmall
    have h1 : 825 * (C + C).card ≤ 1683 * B.card := by
      nlinarith only [hsmall']
    have h2 : 1683 * B.card ≤ 2040 * C.card := by
      nlinarith only [hCcard]
    have hsumPos : 0 < (C + C).card := by
      have hCne : C.Nonempty := by
        apply Finset.card_pos.mp
        have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨0, hDzero⟩
        omega
      exact Finset.card_pos.mpr (hCne.add hCne)
    rw [hDsum, hDcard]
    by_contra hnot
    have h3 : 5 * C.card ≤ 2 * (C + C).card :=
      Nat.le_of_not_gt hnot
    have h4 : 2040 * C.card ≤ 816 * (C + C).card := by
      nlinarith only [h3]
    omega
  refine ⟨m, g, w, C, D, X, rfl, hm240, hCB, hCcard,
    hDzero, hDcard, rfl, hXcard, hXsum, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, hDzero, by simp [zmodQuotRemLift]⟩
  · intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mod_lt _ hm
  · rw [hXsum, hXcard]
    exact hcoreSmall

/-- Exact integral form of Ruzsa covering.  Keeping the product bound, rather
than rounding a real quotient, is important when the covering translates
are later multiplied by the order of a fibre subgroup. -/
lemma exists_ruzsa_covering_add_card_mul_le
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} (hB : B.Nonempty) :
    ∃ F ⊆ A, F.card * B.card ≤ (A + B).card ∧
      A ⊆ F + (B - B) := by
  classical
  have hBpos : (0 : ℝ) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hB
  let K : ℝ := (A + B).card / B.card
  have hK : ((A + B).card : ℝ) ≤ K * B.card := by
    dsimp [K]
    field_simp
    exact le_rfl
  obtain ⟨F, hFA, hFcard, hcover⟩ := Finset.ruzsa_covering_add hB hK
  refine ⟨F, hFA, ?_, hcover⟩
  have hmul : (F.card : ℝ) * B.card ≤
      ((A + B).card : ℝ) := by
    calc
      (F.card : ℝ) * B.card ≤ K * B.card :=
        mul_le_mul_of_nonneg_right hFcard hBpos.le
      _ = ((A + B).card : ℝ) := by
        dsimp [K]
        field_simp
  exact_mod_cast hmul

/-- A `33/40`-dense core of a set with doubling at most `51/25` controls
the whole set by at most two translates of its difference set.  This is the
Ruzsa-covering completion mechanism used after the Fourier partial lift. -/
lemma exists_two_translate_difference_cover
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {B C : Finset G} (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card) :
    ∃ F ⊆ B, F.card ≤ 2 ∧ B ⊆ F + (C - C) := by
  have hBC : B + C ⊆ B + B :=
    Finset.add_subset_add (Finset.Subset.rfl) hCB
  have hcardNat : 50 * (B + C).card ≤ 124 * C.card := by
    have hcard := Finset.card_le_card hBC
    have hsmall' : 25 * (B + C).card ≤ 51 * B.card :=
      (Nat.mul_le_mul_left 25 hcard).trans hsmall
    nlinarith
  have hcardReal : ((B + C).card : ℝ) ≤
      (5 / 2 : ℝ) * C.card := by
    have hcast : (50 : ℝ) * (B + C).card ≤ 124 * C.card := by
      exact_mod_cast hcardNat
    nlinarith
  obtain ⟨F, hFB, hFcard, hcover⟩ :=
    Finset.ruzsa_covering_add hC hcardReal
  refine ⟨F, hFB, ?_, hcover⟩
  have hFcard' : (F.card : ℝ) < 3 := hFcard.trans_lt (by norm_num)
  have hFcardNat : F.card < 3 := by exact_mod_cast hFcard'
  omega

/-- The difference set of a subset of a length-`L` cyclic coset progression
is contained in the corresponding length-`2L` difference progression.  The
extra endpoint in this convenient parameterization avoids a separate case
when `L = 0`. -/
lemma cyclicCosetProgression_sub_subset
    {t L : ℕ} [NeZero t] {H : AddSubgroup (ZMod t)}
    {a d : ZMod t} {C : Finset (ZMod t)}
    (hC : C ⊆ cyclicCosetProgression H a d L) :
    C - C ⊆ cyclicCosetProgression H (-(L • d)) d (2 * L) := by
  intro z hz
  obtain ⟨x, hxC, y, hyC, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp (hC hxC)
  obtain ⟨j, hj, hyj⟩ := mem_cyclicCosetProgression_iff.mp (hC hyC)
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i + (L - j), by omega, ?_⟩
  have hsub := H.sub_mem hxi hyj
  convert hsub using 1 <;>
    rw [add_nsmul, sub_nsmul d (by omega : j ≤ L)] <;> abel

/-- The trivial-subgroup specialization of
`cyclicCosetProgression_sub_subset`. -/
lemma cyclicCosetProgression_bot_sub_subset
    {t L : ℕ} [NeZero t] {a d : ZMod t} {C : Finset (ZMod t)}
    (hC : C ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L) :
    C - C ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod t))
      (-(L • d)) d (2 * L) := by
  intro z hz
  obtain ⟨x, hxC, y, hyC, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp (hC hxC)
  obtain ⟨j, hj, hyj⟩ := mem_cyclicCosetProgression_iff.mp (hC hyC)
  rw [AddSubgroup.mem_bot, sub_eq_zero] at hxi hyj
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i + (L - j), by omega, ?_⟩
  rw [AddSubgroup.mem_bot, sub_eq_zero]
  rw [hxi, hyj]
  simp only [add_sub_add_left_eq_sub]
  rw [add_nsmul, sub_nsmul d (by omega : j ≤ L)]
  abel

/-- Pull an ordinary cyclic progression back through a unit-affine change of
coordinates. -/
lemma zmodAffineImage_pullback_cyclic_bot
    {t L : ℕ} [NeZero t] (w : (ZMod t)ˣ)
    (c a d : ZMod t) (B : Finset (ZMod t))
    (hB : zmodAffineImage c (w : ZMod t) B ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L) :
    B ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod t))
      ((unitMulAddEquiv w).symm (a - c))
      ((unitMulAddEquiv w).symm d) L := by
  intro x hx
  have hxaff : c + (w : ZMod t) * x ∈
      zmodAffineImage c (w : ZMod t) B :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi, heq⟩ := mem_cyclicCosetProgression_iff.mp (hB hxaff)
  rw [AddSubgroup.mem_bot, sub_eq_zero] at heq
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i, hi, ?_⟩
  rw [AddSubgroup.mem_bot, sub_eq_zero]
  apply (unitMulAddEquiv w).injective
  simp only [map_add, map_nsmul]
  rw [unitMulAddEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  calc
    (w : ZMod t) * x = (c + (w : ZMod t) * x) - c := by ring
    _ = (a + i • d) - c := by rw [heq]
    _ = a - c + i • d := by ring

/-- Properness of an ordinary cyclic progression is invariant under a
unit-affine change of coordinates. -/
lemma zmodAffineImage_pullback_proper_cyclic_bot
    {t L : ℕ} [NeZero t] (w : (ZMod t)ˣ)
    (c a d : ZMod t)
    (hproper : IsProperCyclicCosetProgression
      (⊥ : AddSubgroup (ZMod t)) a d L) :
    IsProperCyclicCosetProgression (⊥ : AddSubgroup (ZMod t))
      ((unitMulAddEquiv w).symm (a - c))
      ((unitMulAddEquiv w).symm d) L := by
  intro i hi j hj hij
  apply hproper i hi j hj
  rw [AddSubgroup.mem_bot] at hij ⊢
  have h := congrArg (unitMulAddEquiv w) hij
  simp only [map_sub, map_add, map_nsmul, AddEquiv.apply_symm_apply,
    map_zero] at h
  convert h using 1 <;> abel

/-- Pull containment in a proper subgroup coset back through a unit-affine
change of coordinates. -/
lemma zmodAffineImage_pullback_properCoset
    {t : ℕ} [NeZero t] (w : (ZMod t)ˣ)
    (c a : ZMod t) (B : Finset (ZMod t))
    (K : AddSubgroup (ZMod t)) (hK : K ≠ ⊤)
    (hB : (zmodAffineImage c (w : ZMod t) B : Set (ZMod t)) ⊆
      a +ᵥ (K : Set (ZMod t))) :
    ∃ K' : AddSubgroup (ZMod t), K' ≠ ⊤ ∧ ∃ a' : ZMod t,
      (B : Set (ZMod t)) ⊆ a' +ᵥ (K' : Set (ZMod t)) := by
  let e := unitMulAddEquiv w
  let K' : AddSubgroup (ZMod t) := K.comap e.toAddMonoidHom
  have hK' : K' ≠ ⊤ := by
    intro htop
    apply hK
    apply top_unique
    intro y hy
    have hmem : e.symm y ∈ K' := by
      rw [htop]
      trivial
    change e (e.symm y) ∈ K at hmem
    simpa using hmem
  refine ⟨K', hK', e.symm (a - c), ?_⟩
  intro x hx
  have hxaff : c + (w : ZMod t) * x ∈
      zmodAffineImage c (w : ZMod t) B :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨k, hk, heq⟩ := Set.mem_vadd_set.mp (hB hxaff)
  rw [Set.mem_vadd_set]
  refine ⟨x - e.symm (a - c), ?_, ?_⟩
  · change e (x - e.symm (a - c)) ∈ K
    rw [map_sub, e.apply_symm_apply]
    have hdiff : c + (w : ZMod t) * x - a ∈ K := by
      have heq' : c + (w : ZMod t) * x = a + k := by
        simpa [vadd_eq_add] using heq.symm
      rw [heq']
      simpa using hk
    convert hdiff using 1 <;> simp [e, unitMulAddEquiv] <;> ring
  · simp [vadd_eq_add]

/-- A cyclic set which becomes no-wrap after a unit-affine coordinate change
satisfies the rectified progression/proper-subgroup dichotomy.  This is the
formal interface needed by the partial-lift step of the cyclic inverse
theorem. -/
lemma unitAffineRectified_progression_or_properSubgroup
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hBne : B.Nonempty) (w : (ZMod t)ˣ) (c : ZMod t)
    (hnowrap : ∀ x ∈ zmodAffineImage c (w : ZMod t) B,
      2 * x.val < t)
    (hcard : 30 ≤ B.card)
    (hsmall : 10 * (B + B).card ≤ 21 * B.card)
    (hsparse : 6 * B.card < 5 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧ ∃ a : ZMod t,
      (B : Set (ZMod t)) ⊆ a +ᵥ (K : Set (ZMod t))) ∨
    (∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L ∧
      IsProperCyclicCosetProgression (⊥ : AddSubgroup (ZMod t)) a d L ∧
      10 * L ≤ 11 * B.card + 10) := by
  let C := zmodAffineImage c (w : ZMod t) B
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hBne
    exact ⟨c + (w : ZMod t) * x,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hCcard : C.card = B.card :=
    zmodAffineImage_card w.isUnit B
  have hCsum : (C + C).card = (B + B).card :=
    zmodAffineImage_add_card w.isUnit B
  have hmodel : HasNatFreimanModel C :=
    hasNatFreimanModel_of_double_val_lt hCne hnowrap
  have hdich := natFreimanModel_progression_or_properSubgroup
    hmodel (by simpa [hCcard] using hcard)
    (by simpa [hCsum, hCcard] using hsmall)
    (by simpa [hCcard] using hsparse)
  rcases hdich with ⟨K, hK, a, hCK⟩ | ⟨a, d, L, hCP, hproper, hL⟩
  · exact Or.inl (zmodAffineImage_pullback_properCoset
      w c a B K hK hCK)
  · right
    refine ⟨(unitMulAddEquiv w).symm (a - c),
      (unitMulAddEquiv w).symm d, L,
      zmodAffineImage_pullback_cyclic_bot w c a d B hCP,
      zmodAffineImage_pullback_proper_cyclic_bot w c a d hproper, ?_⟩
    simpa [hCcard] using hL

lemma mem_subgroup_iff_val_dvd_of_generator_modulus
    {b q : ℕ} [NeZero b] (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H) (x : ZMod b) :
    x ∈ H ↔ q ∣ x.val := by
  constructor
  · exact hHdiv x
  · rintro ⟨i, hi⟩
    have hx : x = (i * q : ℕ) := by
      rw [← ZMod.natCast_zmod_val x, hi]
      simp [mul_comm]
    rw [hx]
    simpa using hmult i

/-- Membership in a cyclic subgroup coset is equality of the corresponding
least nonnegative residues modulo the subgroup generator. -/
lemma sub_mem_subgroup_iff_val_mod_eq
    {b q : ℕ} [NeZero b] (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (x c : ZMod b) :
    x - c ∈ H ↔ x.val % q = c.val % q := by
  rw [mem_subgroup_iff_val_dvd_of_generator_modulus H hHdiv hmult]
  constructor
  · intro hdiv
    have hzero : ZMod.castHom hqb (ZMod q) (x - c) = 0 := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val,
        ZMod.natCast_eq_zero_iff]
      exact hdiv
    rw [map_sub, sub_eq_zero] at hzero
    have heq : (x.val : ZMod q) = (c.val : ZMod q) := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hzero
    exact (ZMod.natCast_eq_natCast_iff' x.val c.val q).mp heq
  · intro hmod
    have heq : (x.val : ZMod q) = (c.val : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff' x.val c.val q).mpr hmod
    have hzero : ZMod.castHom hqb (ZMod q) (x - c) = 0 := by
      rw [map_sub, sub_eq_zero]
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using heq
    rw [ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.natCast_eq_zero_iff] at hzero
    exact hzero

/-- Least representatives of one coset of the subgroup generated by `q`
lie in a `q`-step progression of exactly `b/q` terms. -/
lemma coset_values_subset_natProgression
    {b q : ℕ} [NeZero b] (hq : 0 < q) (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (c : ZMod b) :
    zmodValues ((subgroupFinset H).image fun h ↦ c + h) ⊆
      natProgression (c.val % q) q (b / q) := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := mem_zmodValues_iff.mp hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hr
  have hsub : (c + h) - c ∈ H := by simpa using hh
  have hmod : (c + h).val % q = c.val % q :=
    (sub_mem_subgroup_iff_val_mod_eq hqb H hHdiv hmult _ _).mp hsub
  rw [mem_natProgression_iff]
  refine ⟨(c + h).val / q, ?_, ?_⟩
  · have hlt : (c + h).val < b := ZMod.val_lt _
    exact (Nat.div_lt_iff_lt_mul hq).mpr (by
      rw [Nat.div_mul_cancel hqb]
      exact hlt)
  · calc
      x = (c + h).val := hrx.symm
      _ = (c + h).val % q + q * ((c + h).val / q) := by
        symm
        simpa [mul_comm] using Nat.mod_add_div (c + h).val q
      _ = c.val % q + q * ((c + h).val / q) := by rw [hmod]

/-- The ordinary progression lifting the `i`th coset of a cyclic coset
progression. -/
def cyclicCosetLiftPiece {b : ℕ} [NeZero b]
    (a d : ZMod b) (q : ℕ) (length : ℕ) (i : Fin length) :
    Finset ℕ :=
  natProgression ((a + i.1 • d).val % q) q (b / q)

lemma cyclicCosetLiftPiece_card {b q length : ℕ} [NeZero b]
    (hq : 0 < q) (a d : ZMod b) (i : Fin length) :
    (cyclicCosetLiftPiece a d q length i).card = b / q := by
  exact card_natProgression hq

/-- The family of ordinary progressions obtained by lifting each constituent
coset covers every least representative of the cyclic coset progression. -/
lemma cyclicCosetLiftCover_covers
    {b q length : ℕ} [NeZero b] (hq : 0 < q) (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) :
    ∀ x ∈ zmodValues (cyclicCosetProgression H a d length),
      ∃ i : Fin length, x ∈ cyclicCosetLiftPiece a d q length i := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := mem_zmodValues_iff.mp hx
  obtain ⟨i, hi, hri⟩ := mem_cyclicCosetProgression_iff.mp hr
  let c := a + i • d
  have hrmem : r ∈ (subgroupFinset H).image fun h ↦ c + h := by
    apply Finset.mem_image.mpr
    refine ⟨r - c, mem_subgroupFinset.mpr hri, ?_⟩
    abel
  have hxmem : x ∈ zmodValues
      ((subgroupFinset H).image fun h ↦ c + h) := by
    exact mem_zmodValues_iff.mpr ⟨r, hrmem, hrx⟩
  refine ⟨⟨i, hi⟩, ?_⟩
  exact coset_values_subset_natProgression hq hqb H hHdiv hmult c hxmem

lemma cyclicCosetLiftCover_total_card
    {b q length : ℕ} [NeZero b] (hq : 0 < q)
    (a d : ZMod b) :
    ∑ i : Fin length, (cyclicCosetLiftPiece a d q length i).card =
      length * (b / q) := by
  simp [cyclicCosetLiftPiece_card hq]

lemma cyclicCosetLiftCover_total_card_eq
    {b q length : ℕ} [NeZero b] (hb : 0 < b) (hq : 0 < q)
    (hqb : q ∣ b) (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) :
    ∑ i : Fin length, (cyclicCosetLiftPiece a d q length i).card =
      length * Nat.card H := by
  rw [cyclicCosetLiftCover_total_card hq,
    natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]

/-- Data for an ordinary finite progression.  Positivity of the step makes
its parameterization injective, so its carrier has exactly `length` terms. -/
structure NatProgressionSpec where
  start : ℕ
  step : ℕ
  length : ℕ
  step_pos : 0 < step

def NatProgressionSpec.carrier (P : NatProgressionSpec) : Finset ℕ :=
  natProgression P.start P.step P.length

@[simp] lemma NatProgressionSpec.card_carrier (P : NatProgressionSpec) :
    P.carrier.card = P.length := card_natProgression P.step_pos

/-- `X` has a progression cover of total parameter mass at most `mass`, and
every constituent progression is long enough that its cubed length dominates
`|X|`.  This integral formulation avoids rounding a real cube root. -/
def HasLongProgressionCover (X : Finset ℕ) (mass : ℕ) : Prop :=
  ∃ m : ℕ, ∃ P : Fin m → NatProgressionSpec,
    (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) ∧
    (∑ i, (P i).length) ≤ mass ∧
    ∀ i, X.card ≤ (P i).length ^ 3

lemma HasLongProgressionCover.mono_set
    {X Y : Finset ℕ} {mass : ℕ} (hXY : X ⊆ Y)
    (h : HasLongProgressionCover Y mass) :
    HasLongProgressionCover X mass := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  refine ⟨m, P, ?_, hmass, ?_⟩
  · intro x hx
    exact hcover x (hXY hx)
  · intro i
    exact (Finset.card_le_card hXY).trans (hlong i)

/-- Extend a progression without changing its start or step. -/
def NatProgressionSpec.extendLength (k : ℕ) (P : NatProgressionSpec) :
    NatProgressionSpec where
  start := P.start
  step := P.step
  length := k * P.length
  step_pos := P.step_pos

lemma NatProgressionSpec.carrier_subset_extendLength
    (P : NatProgressionSpec) {k : ℕ} (hk : 1 ≤ k) :
    P.carrier ⊆ (P.extendLength k).carrier := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_natProgression_iff.mp hx
  apply mem_natProgression_iff.mpr
  refine ⟨i, ?_, rfl⟩
  change i < k * P.length
  exact hi.trans_le (by
    simpa using Nat.mul_le_mul_right P.length hk)

/-- Multiplying every progression length by `k ≥ 1` preserves a long cover
and multiplies its total mass by at most `k`. -/
lemma HasLongProgressionCover.extendLength
    {X : Finset ℕ} {mass k : ℕ} (h : HasLongProgressionCover X mass)
    (hk : 1 ≤ k) :
    HasLongProgressionCover X (k * mass) := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  let Q : Fin m → NatProgressionSpec := fun i ↦ (P i).extendLength k
  refine ⟨m, Q, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, (P i).carrier_subset_extendLength hk hi⟩
  · change (∑ i, k * (P i).length) ≤ k * mass
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left k hmass
  · intro i
    change X.card ≤ (k * (P i).length) ^ 3
    exact (hlong i).trans (Nat.pow_le_pow_left
      (Nat.le_mul_of_pos_left (P i).length (by omega : 0 < k)) 3)

lemma sum_append_progression_lengths {m n : ℕ}
    (P : Fin m → NatProgressionSpec) (R : Fin n → NatProgressionSpec) :
    (∑ i, ((Fin.append P R) i).length) =
      (∑ i, (P i).length) + ∑ j, (R j).length := by
  rw [← (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).sum_comp
    (fun i => ((Fin.append P R) i).length)]
  rw [Fintype.sum_sum_type]
  simp

/-- Combine two covers of equicardinal sets.  Doubling all constituent
lengths makes every piece long relative to the union, even if the two sets
overlap unevenly. -/
lemma HasLongProgressionCover.union_equal_card
    {X Y : Finset ℕ} {massX massY : ℕ}
    (hX : HasLongProgressionCover X massX)
    (hY : HasLongProgressionCover Y massY)
    (hcard : X.card = Y.card) :
    HasLongProgressionCover (X ∪ Y) (2 * (massX + massY)) := by
  obtain ⟨m, P, hcoverP, hmassP, hlongP⟩ := hX
  obtain ⟨n, R, hcoverR, hmassR, hlongR⟩ := hY
  let P' : Fin m → NatProgressionSpec := fun i ↦ (P i).extendLength 2
  let R' : Fin n → NatProgressionSpec := fun i ↦ (R i).extendLength 2
  let Q := Fin.append P' R'
  refine ⟨m + n, Q, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := hcoverP x hx
      refine ⟨Fin.castAdd n i, ?_⟩
      simpa [Q, P'] using
        (P i).carrier_subset_extendLength (by omega : 1 ≤ 2) hi
    · obtain ⟨i, hi⟩ := hcoverR x hx
      refine ⟨Fin.natAdd m i, ?_⟩
      simpa [Q, R'] using
        (R i).carrier_subset_extendLength (by omega : 1 ≤ 2) hi
  · rw [show (∑ i, (Q i).length) =
        (∑ i, (P' i).length) + ∑ j, (R' j).length by
      exact sum_append_progression_lengths P' R']
    change (∑ i, 2 * (P i).length) + (∑ j, 2 * (R j).length) ≤
      2 * (massX + massY)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith
  · intro i
    have hunion : (X ∪ Y).card ≤ 2 * X.card := by
      calc
        (X ∪ Y).card ≤ X.card + Y.card := Finset.card_union_le X Y
        _ = 2 * X.card := by omega
    by_cases hi : i.1 < m
    · let j : Fin m := ⟨i.1, hi⟩
      have hij : i = Fin.castAdd n j := by apply Fin.ext; rfl
      rw [hij]
      simp only [Q, Fin.append_left, P', NatProgressionSpec.extendLength]
      have hj := hlongP j
      nlinarith [hunion]
    · have him : m ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin n := ⟨i.1 - m, by omega⟩
      have hij : i = Fin.natAdd m j := by apply Fin.ext; simp [j, him]
      rw [hij]
      simp only [Q, Fin.append_right, R', NatProgressionSpec.extendLength]
      have hj := hlongR j
      rw [hcard] at hunion
      nlinarith [hunion]

/-- The easy case of CFP Lemma 5.10: when the subgroup itself is at least
the cube-root scale, lifting the constituent cosets already gives the desired
long progression cover, with no loss in total mass. -/
lemma large_subgroup_longProgressionCover
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) (hproper : IsProperCyclicCosetProgression H a d length)
    (hlarge : (cyclicCosetProgression H a d length).card ≤
      (Nat.card H) ^ 3) :
    HasLongProgressionCover
      (zmodValues (cyclicCosetProgression H a d length))
      (cyclicCosetProgression H a d length).card := by
  let P : Fin length → NatProgressionSpec := fun i ↦
    { start := (a + i.1 • d).val % q
      step := q
      length := b / q
      step_pos := hq }
  refine ⟨length, P, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ :=
      cyclicCosetLiftCover_covers hq hqb H hHdiv hmult a d x hx
    exact ⟨i, hi⟩
  · rw [show (∑ i, (P i).length) = length * (b / q) by simp [P]]
    rw [cyclicCosetProgression_card_eq_of_proper H a d hproper,
      natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
  · intro i
    change (zmodValues (cyclicCosetProgression H a d length)).card ≤
      (b / q) ^ 3
    rw [card_zmodValues]
    have hcardH :=
      natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult
    rw [hcardH] at hlarge
    exact hlarge

def coprimePart (X : Finset ℕ) (M : ℕ) : Finset ℕ :=
  X.filter fun x ↦ Nat.Coprime M x

lemma progression_coprimePart_card
    (P : NatProgressionSpec) (M : ℕ) :
    (coprimePart P.carrier M).card =
      (progressionCoprimeIndices P.start P.step P.length M).card := by
  let g : ℕ → ℕ := fun i ↦ P.start + P.step * i
  have hinj : Set.InjOn g (Finset.range P.length) := by
    intro i hi j hj hij
    apply mul_left_cancel₀ P.step_pos.ne'
    exact Nat.add_left_cancel hij
  have heq : coprimePart P.carrier M =
      (progressionCoprimeIndices P.start P.step P.length M).image g := by
    ext x
    simp only [coprimePart, NatProgressionSpec.carrier, natProgression,
      Finset.mem_filter, Finset.mem_image, progressionCoprimeIndices,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hcop⟩
      exact ⟨i, ⟨hi, hcop⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hcop⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hcop⟩
  rw [heq, Finset.card_image_iff.mpr]
  exact hinj.mono (Finset.filter_subset _ _)

/-- A progression cover gives an occurrence-counting upper bound after any
coprimality sieve, even when its pieces overlap. -/
lemma card_coprimePart_le_sum_cover
    {X : Finset ℕ} {m : ℕ} (P : Fin m → NatProgressionSpec)
    (hcover : ∀ x ∈ X, ∃ i, x ∈ (P i).carrier) (M : ℕ) :
    (coprimePart X M).card ≤
      ∑ i, (progressionCoprimeIndices
        (P i).start (P i).step (P i).length M).card := by
  let U := Finset.univ.biUnion fun i : Fin m ↦ coprimePart (P i).carrier M
  have hsub : coprimePart X M ⊆ U := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
    have hxcop : Nat.Coprime M x := (Finset.mem_filter.mp hx).2
    obtain ⟨i, hi⟩ := hcover x hxX
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hi, hxcop⟩⟩
  calc
    (coprimePart X M).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.univ, (coprimePart (P i).carrier M).card :=
      Finset.card_biUnion_le
    _ = ∑ i, (progressionCoprimeIndices
          (P i).start (P i).step (P i).length M).card := by
      simp_rw [progression_coprimePart_card]

lemma HasLongProgressionCover.card_coprimePart_le_sum
    {X : Finset ℕ} {mass M : ℕ}
    (h : HasLongProgressionCover X mass) :
    ∃ m : ℕ, ∃ P : Fin m → NatProgressionSpec,
      (coprimePart X M).card ≤
        ∑ i, (progressionCoprimeIndices
          (P i).start (P i).step (P i).length M).card ∧
      (∑ i, (P i).length) ≤ mass ∧
      ∀ i, X.card ≤ (P i).length ^ 3 := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  exact ⟨m, P, card_coprimePart_le_sum_cover P hcover M, hmass, hlong⟩

/-- The progression beta sieve summed over an overlapping progression cover.
The main term depends only on total cover mass; one square-error term is paid
per progression. -/
theorem exists_progressionCover_coprimePart_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n y S mass m : ℕ, ∀ P : Fin m → NatProgressionSpec,
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        (∀ i, Nat.Coprime (P i).step (missingPrimeProduct n y)) →
        (∑ i, (P i).length) ≤ mass →
        ∀ X : Finset ℕ,
          (∀ x ∈ X, ∃ i, x ∈ (P i).carrier) →
          let V := missingEulerProduct n y
          let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
          let D := y ^ S
          ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
            (mass : ℝ) * ((1 + eta) * V) +
              (m : ℝ) * (D : ℝ) ^ 2 := by
  obtain ⟨A, hA, hsieve⟩ := exists_progressionCoprimeIndices_card_bound
  refine ⟨A, hA, ?_⟩
  intro n y S mass m P hy hS hlog hcop hmass X hcover
  dsimp only
  let K := (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    missingEulerProduct n y
  let D := y ^ S
  have hpiece (i : Fin m) :
      ((progressionCoprimeIndices (P i).start (P i).step (P i).length
        (missingPrimeProduct n y)).card : ℝ) ≤
        ((P i).length : ℝ) * K + (D : ℝ) ^ 2 := by
    simpa [K, D] using hsieve n (P i).start (P i).step (P i).length
      y S hy hS hlog (hcop i)
  have hcount := card_coprimePart_le_sum_cover P hcover
    (missingPrimeProduct n y)
  have hcountR :
      ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) := by
    exact_mod_cast hcount
  have hmassR : ((∑ i, (P i).length : ℕ) : ℝ) ≤ mass := by
    exact_mod_cast hmass
  have hK : 0 ≤ K := by
    dsimp [K]
    have hV := (missingEulerProduct_pos n y).le
    positivity
  calc
    ((coprimePart X (missingPrimeProduct n y)).card : ℝ) ≤
        ∑ i, ((progressionCoprimeIndices
          (P i).start (P i).step (P i).length
          (missingPrimeProduct n y)).card : ℝ) := hcountR
    _ ≤ ∑ i, (((P i).length : ℝ) * K + (D : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun i hi ↦ hpiece i
    _ = ((∑ i, (P i).length : ℕ) : ℝ) * K +
          (m : ℝ) * (D : ℝ) ^ 2 := by
      push_cast
      simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (mass : ℝ) * K + (m : ℝ) * (D : ℝ) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_right hmassR hK) le_rfl
    _ = _ := rfl

/-- Integral Dirichlet approximation in the exact form needed to unwrap a
cyclic progression in square-root-sized blocks. -/
lemma exists_small_modular_multiple
    {q u length : ℕ} (hq : 0 < q) (hlength : 0 < length) :
    ∃ s : ℕ, 0 < s ∧ s ≤ Nat.sqrt length ∧
      ∃ w : ℤ,
        (w - (s * u : ℕ) : ℤ) % q = 0 ∧
        w.natAbs * (Nat.sqrt length + 1) ≤ q := by
  let n := Nat.sqrt length
  have hn : 0 < n := Nat.sqrt_pos.2 hlength
  obtain ⟨j, k, hkpos, hkn, happ⟩ :=
    Real.exists_int_int_abs_mul_sub_le ((u : ℝ) / q) hn
  let s := k.toNat
  have hks : (s : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  have hspos : 0 < s := by
    have : (0 : ℤ) < (s : ℤ) := by simpa [hks] using hkpos
    exact_mod_cast this
  have hsn : s ≤ n := by
    have : (s : ℤ) ≤ (n : ℤ) := by simpa [hks] using hkn
    exact_mod_cast this
  let w : ℤ := k * u - j * q
  refine ⟨s, hspos, hsn, w, ?_, ?_⟩
  · dsimp [w]
    rw [hks]
    push_cast
    rw [show k * (u : ℤ) - j * (q : ℤ) - k * (u : ℤ) =
        -(j * (q : ℤ)) by ring]
    exact Int.emod_eq_zero_of_dvd ⟨-j, by ring⟩
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnR : (0 : ℝ) < n + 1 := by positivity
    have hwEq : ((w : ℤ) : ℝ) =
        (q : ℝ) * ((k : ℝ) * ((u : ℝ) / q) - j) := by
      dsimp [w]
      push_cast
      field_simp [hqR.ne']
    have habsEq : |((w : ℤ) : ℝ)| =
        (q : ℝ) * |(k : ℝ) * ((u : ℝ) / q) - j| := by
      rw [hwEq, abs_mul, abs_of_pos hqR]
    have hboundR : |((w : ℤ) : ℝ)| * (n + 1 : ℕ) ≤ q := by
      rw [habsEq]
      have hm := mul_le_mul_of_nonneg_left happ hqR.le
      have hnR' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      rw [div_eq_mul_inv] at hm
      calc
        (q : ℝ) * |(k : ℝ) * ((u : ℝ) / q) - j| *
            (n + 1 : ℕ) ≤
            ((q : ℝ) * (1 / ((n : ℝ) + 1))) *
              (n + 1 : ℕ) := by
          exact mul_le_mul_of_nonneg_right hm hnR'.le
        _ = q := by
          push_cast
          field_simp
    have hcastAbs : ((w.natAbs : ℕ) : ℝ) =
        |((w : ℤ) : ℝ)| := by simp
    rw [← hcastAbs] at hboundR
    exact_mod_cast hboundR

def positiveBlockPiece (q z v m : ℕ) (side : Fin 2) :
    NatProgressionSpec :=
  if hv : v = 0 then
    { start := q + z
      step := 1
      length := m
      step_pos := by omega }
  else
    { start := if side.1 = 0 then q + z else z
      step := v
      length := m
      step_pos := Nat.pos_of_ne_zero hv }

lemma positiveBlockPiece_length (q z v m : ℕ) (side : Fin 2) :
    (positiveBlockPiece q z v m side).length = m := by
  by_cases hv : v = 0 <;> simp [positiveBlockPiece, hv]

lemma positive_modular_block_cover
    {q z v m : ℕ} (hq : 0 < q) (hz : z < q)
    (hvm : v * m ≤ q) :
    ∀ t < m, ∃ side : Fin 2,
      q + ((z + v * t) % q) ∈
        (positiveBlockPiece q z v m side).carrier := by
  intro t ht
  by_cases hv : v = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [NatProgressionSpec.carrier, positiveBlockPiece, dif_pos hv,
      mem_natProgression_iff]
    refine ⟨0, Nat.zero_lt_of_lt ht, ?_⟩
    simp [hv, Nat.mod_eq_of_lt hz]
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    have htv : v * t ≤ v * m := Nat.mul_le_mul_left v ht.le
    have htvq : v * t ≤ q := htv.trans hvm
    have hraw : z + v * t < 2 * q := by omega
    by_cases hlt : z + v * t < q
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [NatProgressionSpec.carrier, positiveBlockPiece, dif_neg hv,
        mem_natProgression_iff]
      refine ⟨t, ht, ?_⟩
      change q + ((z + v * t) % q) = q + z + v * t
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [NatProgressionSpec.carrier, positiveBlockPiece, dif_neg hv,
        mem_natProgression_iff]
      refine ⟨t, ht, ?_⟩
      change q + ((z + v * t) % q) = z + v * t
      have hqle : q ≤ z + v * t := le_of_not_gt hlt
      have hsub : z + v * t = q + (z + v * t - q) := by omega
      have hsublt : z + v * t - q < q := by omega
      have hmod : (z + v * t) % q = z + v * t - q := by
        calc
          (z + v * t) % q = (q + (z + v * t - q)) % q :=
            congrArg (fun x ↦ x % q) hsub
          _ = (z + v * t - q) % q := by simp
          _ = z + v * t - q := Nat.mod_eq_of_lt hsublt
      rw [hmod]
      omega

def negativeBlockPiece (q z v m : ℕ) (side : Fin 2) :
    NatProgressionSpec :=
  if hv : v = 0 then
    { start := q + z
      step := 1
      length := m
      step_pos := by omega }
  else
    { start := if side.1 = 0 then q + z - (m - 1) * v
        else 2 * q + z - (m - 1) * v
      step := v
      length := m
      step_pos := Nat.pos_of_ne_zero hv }

lemma negativeBlockPiece_length (q z v m : ℕ) (side : Fin 2) :
    (negativeBlockPiece q z v m side).length = m := by
  by_cases hv : v = 0 <;> simp [negativeBlockPiece, hv]

lemma negative_modular_block_cover
    {q z v m : ℕ} (hq : 0 < q) (hz : z < q)
    (hvm : v * m ≤ q) :
    ∀ t < m, ∃ side : Fin 2,
      q + ((z + q - v * t) % q) ∈
        (negativeBlockPiece q z v m side).carrier := by
  intro t ht
  by_cases hv : v = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [NatProgressionSpec.carrier, negativeBlockPiece, dif_pos hv,
      mem_natProgression_iff]
    refine ⟨0, Nat.zero_lt_of_lt ht, ?_⟩
    simp [hv, Nat.mod_eq_of_lt hz]
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    have htv : v * t ≤ v * m := Nat.mul_le_mul_left v ht.le
    have htvq : v * t ≤ q := htv.trans hvm
    let j := m - 1 - t
    have hmpos : 0 < m := Nat.zero_lt_of_lt ht
    have hjlt : j < m := by dsimp [j]; omega
    have hjt : j + t = m - 1 := by dsimp [j]; omega
    have hdecomp : (m - 1) * v = j * v + t * v := by
      rw [← Nat.add_mul, hjt]
    have hdecomp' : (m - 1) * v = v * j + v * t := by
      simpa [mul_comm] using hdecomp
    have hmv : (m - 1) * v ≤ q := by
      calc
        (m - 1) * v ≤ m * v := Nat.mul_le_mul_right v (by omega)
        _ = v * m := by ring
        _ ≤ q := hvm
    by_cases htz : v * t ≤ z
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [NatProgressionSpec.carrier, negativeBlockPiece, dif_neg hv,
        mem_natProgression_iff]
      refine ⟨j, hjlt, ?_⟩
      change q + ((z + q - v * t) % q) =
        (q + z - (m - 1) * v) + v * j
      have hy : z + q - v * t = q + (z - v * t) := by omega
      have hzsub : z - v * t < q := by omega
      have hmod : (z + q - v * t) % q = z - v * t := by
        calc
          (z + q - v * t) % q = (q + (z - v * t)) % q :=
            congrArg (fun x ↦ x % q) hy
          _ = (z - v * t) % q := by simp
          _ = z - v * t := Nat.mod_eq_of_lt hzsub
      rw [hmod]
      have hstart : (m - 1) * v ≤ q + z := hmv.trans (Nat.le_add_right q z)
      have hrestore : q + z - (m - 1) * v + (m - 1) * v = q + z :=
        Nat.sub_add_cancel hstart
      omega
    · have hzt : z < v * t := lt_of_not_ge htz
      refine ⟨⟨1, by omega⟩, ?_⟩
      rw [NatProgressionSpec.carrier, negativeBlockPiece, dif_neg hv,
        mem_natProgression_iff]
      refine ⟨j, hjlt, ?_⟩
      change q + ((z + q - v * t) % q) =
        (2 * q + z - (m - 1) * v) + v * j
      have hylt : z + q - v * t < q := by omega
      rw [Nat.mod_eq_of_lt hylt]
      have hstart : (m - 1) * v ≤ 2 * q + z :=
        hmv.trans (by omega)
      have hrestore : 2 * q + z - (m - 1) * v + (m - 1) * v =
          2 * q + z := Nat.sub_add_cancel hstart
      omega

lemma cyclic_anchor_val_mod
    {b q : ℕ} [NeZero b] (hq : 0 < q) (hqb : q ∣ b)
    (a d : ZMod b) (i : ℕ) :
    (a + i • d).val % q = (a.val + i * d.val) % q := by
  let : NeZero q := ⟨hq.ne'⟩
  have heq : ((a + i • d).val : ZMod q) =
      ((a.val + i * d.val : ℕ) : ZMod q) := by
    calc
      ((a + i • d).val : ZMod q) =
          ZMod.castHom hqb (ZMod q) (a + i • d) := by
        rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      _ = ZMod.castHom hqb (ZMod q) a +
          i • ZMod.castHom hqb (ZMod q) d := by
        rw [map_add, map_nsmul]
      _ = (a.val : ZMod q) + i • (d.val : ZMod q) := by
        simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
      _ = ((a.val + i * d.val : ℕ) : ZMod q) := by
        push_cast
        simp [nsmul_eq_mul]
  exact (ZMod.natCast_eq_natCast_iff'
    (a + i • d).val (a.val + i * d.val) q).mp heq

lemma intModEq_of_sub_emod_eq_zero {q : ℕ} {w : ℤ} {v : ℕ}
    (h : (w - v) % q = 0) : w ≡ v [ZMOD q] := by
  rw [Int.modEq_iff_dvd]
  have hd : (q : ℤ) ∣ w - v := Int.dvd_iff_emod_eq_zero.mpr h
  obtain ⟨c, hc⟩ := hd
  refine ⟨-c, ?_⟩
  calc
    (v : ℤ) - w = -(w - v) := by ring
    _ = -((q : ℤ) * c) := by rw [hc]
    _ = (q : ℤ) * -c := by ring

lemma positive_cyclic_block_relation
    {b q i₀ s v : ℕ} [NeZero b] (hq : 0 < q) (hqb : q ∣ b)
    (a d : ZMod b)
    (hstep : ((v : ℕ) : ℤ) ≡ (s * d.val : ℕ) [ZMOD q]) :
    ∀ t : ℕ,
      (a + (i₀ + s * t) • d).val % q =
        (((a + i₀ • d).val % q) + v * t) % q := by
  have hstepNat : v ≡ s * d.val [MOD q] :=
    Int.natCast_modEq_iff.mp hstep
  intro t
  have hbase : (a + i₀ • d).val % q ≡
      a.val + i₀ * d.val [MOD q] := by
    rw [Nat.ModEq]
    simp only [Nat.mod_mod]
    rw [cyclic_anchor_val_mod hq hqb]
  have hsum := hbase.add (hstepNat.mul_left t)
  have htarget : (a + i₀ • d).val % q + v * t ≡
      a.val + (i₀ + s * t) * d.val [MOD q] := by
    convert hsum using 1 <;> ring
  rw [cyclic_anchor_val_mod hq hqb]
  exact htarget.symm

lemma negative_step_natModEq
    {q s u v : ℕ} (hvq : v ≤ q)
    (hstep : (-((v : ℕ) : ℤ)) ≡ (s * u : ℕ) [ZMOD q]) :
    q - v ≡ s * u [MOD q] := by
  apply Int.natCast_modEq_iff.mp
  have hcast : (((q - v : ℕ) : ℤ)) = (q : ℤ) - v := by
    rw [Int.natCast_sub hvq]
  have hshift : (q : ℤ) - v ≡ -((v : ℕ) : ℤ) [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  rw [hcast]
  exact hshift.trans hstep

lemma negative_cyclic_block_relation
    {b q i₀ s v m : ℕ} [NeZero b] (hq : 0 < q) (hqb : q ∣ b)
    (a d : ZMod b) (hvm : v * m ≤ q)
    (hstep : (-((v : ℕ) : ℤ)) ≡ (s * d.val : ℕ) [ZMOD q]) :
    ∀ t < m,
      (a + (i₀ + s * t) • d).val % q =
        (((a + i₀ • d).val % q) + q - v * t) % q := by
  intro t ht
  have hmpos : 0 < m := Nat.zero_lt_of_lt ht
  have hvq : v ≤ q := by
    calc
      v ≤ v * m := by
        apply Nat.le_mul_of_pos_right
        exact hmpos
      _ ≤ q := hvm
  have hstepNat : q - v ≡ s * d.val [MOD q] :=
    negative_step_natModEq hvq hstep
  have htv : v * t ≤ q :=
    (Nat.mul_le_mul_left v ht.le).trans hvm
  have hbase : (a + i₀ • d).val % q ≡
      a.val + i₀ * d.val [MOD q] := by
    rw [Nat.ModEq]
    simp only [Nat.mod_mod]
    rw [cyclic_anchor_val_mod hq hqb]
  have hsum := hbase.add (hstepNat.mul_left t)
  have htarget : (a + i₀ • d).val % q + t * (q - v) ≡
      a.val + (i₀ + s * t) * d.val [MOD q] := by
    convert hsum using 1 <;> ring
  have hleft : (a + i₀ • d).val % q + q - v * t ≡
      (a + i₀ • d).val % q + t * (q - v) [MOD q] := by
    let : NeZero q := ⟨hq.ne'⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_sub (htv.trans (Nat.le_add_left q _))]
    push_cast
    rw [Nat.cast_sub hvq]
    push_cast
    simp
    ring
  rw [cyclic_anchor_val_mod hq hqb]
  exact (hleft.trans htarget).symm

def shiftedZmodValues {b : ℕ} [NeZero b]
    (R : Finset (ZMod b)) : Finset ℕ :=
  R.image fun x ↦ b + x.val

lemma mem_shiftedZmodValues_iff {b : ℕ} [NeZero b]
    {R : Finset (ZMod b)} {x : ℕ} :
    x ∈ shiftedZmodValues R ↔ ∃ r ∈ R, b + r.val = x := by
  simp [shiftedZmodValues]

lemma card_shiftedZmodValues {b : ℕ} [NeZero b]
    (R : Finset (ZMod b)) :
    (shiftedZmodValues R).card = R.card := by
  rw [shiftedZmodValues, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  apply ZMod.val_injective b
  exact Nat.add_left_cancel hxy

def NatProgressionSpec.translate (c : ℕ) (P : NatProgressionSpec) :
    NatProgressionSpec where
  start := c + P.start
  step := P.step
  length := P.length
  step_pos := P.step_pos

@[simp] lemma NatProgressionSpec.translate_length
    (c : ℕ) (P : NatProgressionSpec) : (P.translate c).length = P.length := rfl

lemma NatProgressionSpec.add_mem_translate
    {x c : ℕ} {P : NatProgressionSpec} (hx : x ∈ P.carrier) :
    c + x ∈ (P.translate c).carrier := by
  rw [NatProgressionSpec.carrier, mem_natProgression_iff] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, hi, by simp [NatProgressionSpec.translate, add_assoc]⟩

/-- If a residue set lies in a union of translates of `H` and is no larger
than `|H|³`, lift every translate to one ordinary progression.  Each lifted
progression has exactly `|H|` terms, so it is long relative to the set being
covered and the total parameter mass is exactly the number of displayed
translates times `|H|`. -/
lemma subgroup_translates_shifted_longProgressionCover
    {b : ℕ} [NeZero b]
    (H : AddSubgroup (ZMod b)) (B F : Finset (ZMod b))
    (hBF : B ⊆ F + subgroupFinset H)
    (hlong : B.card ≤ (Nat.card H) ^ 3) :
    HasLongProgressionCover (shiftedZmodValues B)
      (F.card * Nat.card H) := by
  classical
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  obtain ⟨q, hq, hqb, hHdiv, hmult⟩ := exists_generator_modulus hb H
  let P : Fin F.card → NatProgressionSpec := fun i ↦
    { start := ((F.equivFin).symm i).1.val % q
      step := q
      length := b / q
      step_pos := hq }
  let Q : Fin F.card → NatProgressionSpec := fun i ↦ (P i).translate b
  refine ⟨F.card, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxB, hxy⟩ := mem_shiftedZmodValues_iff.mp hy
    obtain ⟨f, hfF, h, hhH, hfh⟩ := Finset.mem_add.mp (hBF hxB)
    let i : Fin F.card := F.equivFin ⟨f, hfF⟩
    have hxcos : x ∈ (subgroupFinset H).image (fun z ↦ f + z) := by
      exact Finset.mem_image.mpr ⟨h, hhH, hfh⟩
    have hxval : x.val ∈ zmodValues
        ((subgroupFinset H).image (fun z ↦ f + z)) :=
      mem_zmodValues_iff.mpr ⟨x, hxcos, rfl⟩
    have hxp := coset_values_subset_natProgression
      hq hqb H hHdiv hmult f hxval
    have hPi : (P i).carrier =
        natProgression (f.val % q) q (b / q) := by
      simp [P, i, NatProgressionSpec.carrier]
    have hxPi : x.val ∈ (P i).carrier := by rwa [hPi]
    refine ⟨i, ?_⟩
    have htrans := NatProgressionSpec.add_mem_translate (c := b) hxPi
    rwa [hxy] at htrans
  · change (∑ _i : Fin F.card, b / q) ≤ F.card * Nat.card H
    rw [show (∑ _i : Fin F.card, b / q) = F.card * (b / q) by simp]
    rw [natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
  · intro i
    rw [card_shiftedZmodValues]
    change B.card ≤ (b / q) ^ 3
    rw [← natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
    exact hlong

/-- Large-subgroup completion of the dense-fibre branch.  A fibre occupying
more than two thirds of an `H`-coset has difference set `H`.  Ruzsa covering
then covers `B` by `H`-cosets whose total lifted progression mass is strictly
less than `3|B+B|/2`. -/
lemma dense_coset_large_subgroup_cover
    {b : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    {B C : Finset (ZMod b)}
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hcos : ContainedInAddCoset H C)
    (hdense : 2 * Nat.card H < 3 * C.card)
    (hlong : B.card ≤ (Nat.card H) ^ 3) :
    ∃ mass : ℕ, 2 * mass < 3 * (B + B).card ∧
      HasLongProgressionCover (shiftedZmodValues B) mass := by
  classical
  obtain ⟨F, _hFB, hFcard, hcover⟩ :=
    exists_ruzsa_covering_add_card_mul_le (A := B) (B := C) hC
  have hCC : C - C = subgroupFinset H :=
    dense_coset_sub_eq_subgroup hcos (by omega)
  rw [hCC] at hcover
  have hB : B.Nonempty := hC.mono hCB
  have hF : F.Nonempty := by
    obtain ⟨x, hxB⟩ := hB
    obtain ⟨f, hf, h, hh, _⟩ := Finset.mem_add.mp (hcover hxB)
    exact ⟨f, hf⟩
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  have hmuldense : F.card * (2 * Nat.card H) <
      F.card * (3 * C.card) :=
    (Nat.mul_lt_mul_left hFpos).mpr hdense
  have hmasslt : 2 * (F.card * Nat.card H) <
      3 * (F.card * C.card) := by
    nlinarith only [hmuldense]
  have hBC : (B + C).card ≤ (B + B).card :=
    Finset.card_le_card (Finset.add_subset_add Finset.Subset.rfl hCB)
  have hFC : F.card * C.card ≤ (B + B).card := hFcard.trans hBC
  refine ⟨F.card * Nat.card H, ?_,
    subgroup_translates_shifted_longProgressionCover H B F hcover hlong⟩
  exact hmasslt.trans_le (Nat.mul_le_mul_left 3 hFC)

lemma exists_square_block_decomposition
    {i length s m : ℕ} (hi : i < length)
    (hs : 0 < s) (hm : 0 < m) :
    ∃ r < length / (s * m) + 1, ∃ h < s, ∃ t < m,
      i = r * (s * m) + h + s * t := by
  let h := i % s
  let t := (i / s) % m
  let r := (i / s) / m
  have hh : h < s := Nat.mod_lt i hs
  have ht : t < m := Nat.mod_lt (i / s) hm
  have hir : i / s = t + m * r := by
    dsimp [t, r]
    simpa [mul_comm] using (Nat.mod_add_div (i / s) m).symm
  have hidecomp : i = h + s * (i / s) := by
    dsimp [h]
    simpa [mul_comm] using (Nat.mod_add_div i s).symm
  have heq : i = r * (s * m) + h + s * t := by
    rw [hidecomp, hir]
    ring
  have hrle : r ≤ length / (s * m) := by
    have hdiv : r = i / (s * m) := by
      dsimp [r]
      rw [Nat.div_div_eq_div_mul]
    rw [hdiv]
    exact Nat.div_le_div_right hi.le
  exact ⟨r, by omega, h, hh, t, ht, heq⟩

def encodeFourFin {B s Hn : ℕ}
    (r : Fin B) (h : Fin s) (side : Fin 2) (k : Fin Hn) :
    Fin (((B * s) * 2) * Hn) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (r, h), side), k)

lemma decode_encodeFourFin {B s Hn : ℕ}
    (r : Fin B) (h : Fin s) (side : Fin 2) (k : Fin Hn) :
    let p3 : Fin ((B * s) * 2) × Fin Hn :=
      finProdFinEquiv.symm (encodeFourFin r h side k)
    let p2 : Fin (B * s) × Fin 2 := finProdFinEquiv.symm p3.1
    let p1 : Fin B × Fin s := finProdFinEquiv.symm p2.1
    p1 = (r, h) ∧ p2.2 = side ∧ p3.2 = k := by
  simp [encodeFourFin]

lemma square_block_cover_mass_bound
    {length s Hn : ℕ} (hlength : 0 < length)
    (hs : 0 < s) (hsn : s ≤ Nat.sqrt length) :
    let m := Nat.sqrt length + 1
    let B := length / (s * m) + 1
    (((B * s) * 2) * Hn) * m ≤ 6 * (length * Hn) := by
  dsimp only
  let n := Nat.sqrt length
  have hn : 0 < n := Nat.sqrt_pos.2 hlength
  have hm : 0 < n + 1 := by omega
  have hsqrt : n ^ 2 ≤ length := Nat.sqrt_le' length
  have hsm : s * (n + 1) ≤ 2 * length := by
    calc
      s * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) hsn
      _ ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ 2 * length := Nat.mul_le_mul_left 2 hsqrt
  have hdiv := Nat.div_mul_le_self length (s * (n + 1))
  have hblock : (length / (s * (n + 1)) + 1) * (s * (n + 1)) ≤
      3 * length := by
    nlinarith
  calc
    ((((length / (s * (n + 1)) + 1) * s) * 2) * Hn) * (n + 1) =
        2 * ((length / (s * (n + 1)) + 1) * (s * (n + 1))) * Hn := by
          ring
    _ ≤ 2 * (3 * length) * Hn :=
      Nat.mul_le_mul_right Hn (Nat.mul_le_mul_left 2 hblock)
    _ = 6 * (length * Hn) := by ring

lemma small_subgroup_piece_is_long
    {length Hn : ℕ} (hlength : 0 < length) (hHn : 0 < Hn)
    (hsmall : Hn ^ 3 < length * Hn) :
    length * Hn < (Nat.sqrt length + 1) ^ 3 := by
  let n := Nat.sqrt length
  have hsqrt : n ^ 2 ≤ length := Nat.sqrt_le' length
  have hlengthlt : length < (n + 1) ^ 2 := by
    simpa [n] using Nat.lt_succ_sqrt' length
  have hHsq : Hn ^ 2 < length := by
    rw [show Hn ^ 3 = Hn ^ 2 * Hn by ring] at hsmall
    exact (Nat.mul_lt_mul_right hHn).mp hsmall
  have hHlt : Hn < n + 1 := by
    by_contra hnot
    have hge : n + 1 ≤ Hn := Nat.le_of_not_gt hnot
    have : (n + 1) ^ 2 ≤ Hn ^ 2 := by nlinarith
    omega
  calc
    length * Hn < (n + 1) ^ 2 * (n + 1) :=
      mul_lt_mul hlengthlt hHlt.le hHn (by positivity)
    _ = (Nat.sqrt length + 1) ^ 3 := by simp [n]; ring

def signedBlockPiece (q z m : ℕ) (w : ℤ) (side : Fin 2) :
    NatProgressionSpec :=
  if 0 ≤ w then positiveBlockPiece q z w.natAbs m side
  else negativeBlockPiece q z w.natAbs m side

@[simp] lemma signedBlockPiece_length
    (q z m : ℕ) (w : ℤ) (side : Fin 2) :
    (signedBlockPiece q z m w side).length = m := by
  by_cases hw : 0 ≤ w <;>
    simp [signedBlockPiece, hw, positiveBlockPiece_length,
      negativeBlockPiece_length]

lemma small_subgroup_shifted_longProgressionCover
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b) (hlength : 0 < length)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b)
    (hsmall : (Nat.card H) ^ 3 <
      (cyclicCosetProgression H a d length).card) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (6 * (length * Nat.card H)) := by
  let Hn := b / q
  let n := Nat.sqrt length
  let m := n + 1
  have hHn : 0 < Hn := by
    exact Nat.div_pos (Nat.le_of_dvd hb hqb) hq
  have hn : 0 < n := by simpa [n] using Nat.sqrt_pos.2 hlength
  have hm : 0 < m := by dsimp [m]; omega
  have hcardH : Nat.card H = Hn := by
    exact natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult
  have hRcard : (cyclicCosetProgression H a d length).card ≤ length * Hn := by
    rw [← hcardH]
    exact cyclicCosetProgression_card_le H a d length
  have hsmall' : Hn ^ 3 < length * Hn := by
    have hs : Hn ^ 3 <
        (cyclicCosetProgression H a d length).card := by
      rw [← hcardH]
      exact hsmall
    exact hs.trans_le hRcard
  have hlong : length * Hn < m ^ 3 := by
    simpa [m, n] using
      small_subgroup_piece_is_long hlength hHn hsmall'
  obtain ⟨s, hs, hsn, w, hstepZero, hwbound⟩ :=
    exists_small_modular_multiple hq hlength (u := d.val)
  let B := length / (s * m) + 1
  let total := ((B * s) * 2) * Hn
  let Q : Fin total → NatProgressionSpec := fun idx ↦
    let p3 : Fin ((B * s) * 2) × Fin Hn := finProdFinEquiv.symm idx
    let p2 : Fin (B * s) × Fin 2 := finProdFinEquiv.symm p3.1
    let p1 : Fin B × Fin s := finProdFinEquiv.symm p2.1
    let i₀ := p1.1.1 * (s * m) + p1.2.1
    (signedBlockPiece q ((a + i₀ • d).val % q) m w p2.2).translate
      (q * (Hn - 1 + p3.2.1))
  refine ⟨total, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxR, hxy⟩ := mem_shiftedZmodValues_iff.mp hy
    obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp hxR
    obtain ⟨r, hr, h, hh, t, ht, hidecomp⟩ :=
      exists_square_block_decomposition hi hs hm
    let rr : Fin B := ⟨r, by simpa [B] using hr⟩
    let hhv : Fin s := ⟨h, hh⟩
    let i₀ := r * (s * m) + h
    have hzlt : (a + i₀ • d).val % q < q := Nat.mod_lt _ hq
    have hxmod : x.val % q = (a + i • d).val % q :=
      (sub_mem_subgroup_iff_val_mod_eq hqb H hHdiv hmult _ _).mp hxi
    have hstepW : w ≡ (s * d.val : ℕ) [ZMOD q] :=
      intModEq_of_sub_emod_eq_zero hstepZero
    have hbase : ∃ side : Fin 2,
        q + x.val % q ∈
          (signedBlockPiece q ((a + i₀ • d).val % q) m w side).carrier := by
      by_cases hwpos : 0 ≤ w
      · have hwEq : ((w.natAbs : ℕ) : ℤ) = w := Int.natAbs_of_nonneg hwpos
        have hstep : ((w.natAbs : ℕ) : ℤ) ≡
            (s * d.val : ℕ) [ZMOD q] := by simpa [hwEq] using hstepW
        have hrel := positive_cyclic_block_relation hq hqb a d hstep
          (i₀ := i₀) t
        rw [show i₀ + s * t = i by simpa [i₀] using hidecomp.symm] at hrel
        obtain ⟨side, hside⟩ :=
          positive_modular_block_cover hq hzlt hwbound t ht
        refine ⟨side, ?_⟩
        have hxseq : x.val % q =
            ((a + i₀ • d).val % q + w.natAbs * t) % q :=
          hxmod.trans hrel
        simpa [signedBlockPiece, hwpos, hxseq] using hside
      · have hwEq : w = -((w.natAbs : ℕ) : ℤ) :=
          Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hwpos)
        have hstep : (-((w.natAbs : ℕ) : ℤ)) ≡
            (s * d.val : ℕ) [ZMOD q] := by
          simpa only [hwEq.symm] using hstepW
        have hrel := negative_cyclic_block_relation hq hqb a d hwbound hstep
          (i₀ := i₀) t ht
        rw [show i₀ + s * t = i by simpa [i₀] using hidecomp.symm] at hrel
        obtain ⟨side, hside⟩ :=
          negative_modular_block_cover hq hzlt hwbound t ht
        refine ⟨side, ?_⟩
        have hxseq : x.val % q =
            ((a + i₀ • d).val % q + q - w.natAbs * t) % q :=
          hxmod.trans hrel
        simpa [signedBlockPiece, hwpos, hxseq] using hside
    obtain ⟨side, hside⟩ := hbase
    have hjlt : x.val / q < Hn := by
      dsimp [Hn]
      exact (Nat.div_lt_iff_lt_mul hq).mpr (by
        rw [Nat.div_mul_cancel hqb]
        exact ZMod.val_lt x)
    let k : Fin Hn := ⟨x.val / q, hjlt⟩
    have hbq : q * Hn = b := by
      simpa [Hn, mul_comm] using Nat.div_mul_cancel hqb
    have hxsplit : x.val % q + q * (x.val / q) = x.val :=
      Nat.mod_add_div x.val q
    have htranslate :
        q * (Hn - 1 + x.val / q) + (q + x.val % q) = b + x.val := by
      have hHsub : Hn - 1 + 1 = Hn := by omega
      nlinarith
    have htranslated := NatProgressionSpec.add_mem_translate
      (c := q * (Hn - 1 + x.val / q)) hside
    rw [htranslate, hxy] at htranslated
    refine ⟨encodeFourFin rr hhv side k, ?_⟩
    have hQ : Q (encodeFourFin rr hhv side k) =
        (signedBlockPiece q ((a + i₀ • d).val % q) m w side).translate
          (q * (Hn - 1 + x.val / q)) := by
      dsimp only [Q]
      simp only [encodeFourFin, Equiv.symm_apply_apply]
      rfl
    rwa [hQ]
  · have hmass := square_block_cover_mass_bound hlength hs hsn (Hn := Hn)
    have hsum : (∑ idx, (Q idx).length) = total * m := by
      simp [Q, total]
    rw [hsum]
    calc
      total * m ≤ 6 * (length * Hn) := by simpa [total, B, m, n] using hmass
      _ = 6 * (length * Nat.card H) := by rw [hcardH]
  · intro idx
    rw [card_shiftedZmodValues]
    have hQlen : (Q idx).length = m := by simp [Q]
    rw [hQlen]
    exact hRcard.trans hlong.le


lemma HasLongProgressionCover.mono_mass
    {X : Finset ℕ} {mass mass' : ℕ}
    (h : HasLongProgressionCover X mass) (hmm : mass ≤ mass') :
    HasLongProgressionCover X mass' := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  exact ⟨m, P, hcover, hmass.trans hmm, hlong⟩

lemma large_subgroup_shifted_longProgressionCover
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) (hproper : IsProperCyclicCosetProgression H a d length)
    (hlarge : (cyclicCosetProgression H a d length).card ≤
      (Nat.card H) ^ 3) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (cyclicCosetProgression H a d length).card := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ :=
    large_subgroup_longProgressionCover hb hq hqb H hHdiv hmult
      a d hproper hlarge
  let Q : Fin m → NatProgressionSpec := fun i ↦ (P i).translate b
  refine ⟨m, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxR, hxy⟩ := mem_shiftedZmodValues_iff.mp hy
    have hxVal : x.val ∈ zmodValues (cyclicCosetProgression H a d length) :=
      mem_zmodValues_iff.mpr ⟨x, hxR, rfl⟩
    obtain ⟨i, hi⟩ := hcover x.val hxVal
    refine ⟨i, ?_⟩
    have := NatProgressionSpec.add_mem_translate (c := b) hi
    rwa [hxy] at this
  · simpa [Q] using hmass
  · intro i
    rw [card_shiftedZmodValues]
    have hi := hlong i
    rw [card_zmodValues] at hi
    simpa [Q] using hi

/-- Parameter-mass version of the large-subgroup lift.  It does not require
the displayed cosets to be distinct. -/
lemma large_subgroup_shifted_longProgressionCover_parametric
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b)
    (hlarge : (cyclicCosetProgression H a d length).card ≤
      (Nat.card H) ^ 3) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (length * Nat.card H) := by
  let P : Fin length → NatProgressionSpec := fun i ↦
    { start := (a + i.1 • d).val % q
      step := q
      length := b / q
      step_pos := hq }
  let Q : Fin length → NatProgressionSpec := fun i ↦ (P i).translate b
  refine ⟨length, Q, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxR, hxy⟩ := mem_shiftedZmodValues_iff.mp hy
    have hxVal : x.val ∈
        zmodValues (cyclicCosetProgression H a d length) :=
      mem_zmodValues_iff.mpr ⟨x, hxR, rfl⟩
    obtain ⟨i, hi⟩ :=
      cyclicCosetLiftCover_covers hq hqb H hHdiv hmult a d x.val hxVal
    refine ⟨i, ?_⟩
    have hiP : x.val ∈ (P i).carrier := by
      simpa [P, NatProgressionSpec.carrier, cyclicCosetLiftPiece] using hi
    have := NatProgressionSpec.add_mem_translate (c := b) hiP
    rwa [hxy] at this
  · change (∑ _i : Fin length, b / q) ≤ length * Nat.card H
    rw [show (∑ _i : Fin length, b / q) = length * (b / q) by simp]
    rw [natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
  · intro i
    rw [card_shiftedZmodValues]
    change (cyclicCosetProgression H a d length).card ≤ (b / q) ^ 3
    rw [← natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult]
    exact hlarge

/-- CFP's lifting lemma in parameter-mass form.  Repeated cosets are harmless:
the cover has total mass at most six times the number of displayed coset
positions times the subgroup size. -/
lemma cyclicCosetProgression_shifted_longProgressionCover_parametric
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b) (hlength : 0 < length)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (6 * (length * Nat.card H)) := by
  by_cases hlarge : (cyclicCosetProgression H a d length).card ≤
      (Nat.card H) ^ 3
  · apply (large_subgroup_shifted_longProgressionCover_parametric
      hb hq hqb H hHdiv hmult a d hlarge).mono_mass
    omega
  · exact small_subgroup_shifted_longProgressionCover hb hq hqb hlength
      H hHdiv hmult a d (Nat.lt_of_not_ge hlarge)

lemma cyclicCosetProgression_shifted_longProgressionCover
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b) (hlength : 0 < length)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) (hproper : IsProperCyclicCosetProgression H a d length) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (6 * (cyclicCosetProgression H a d length).card) := by
  by_cases hlarge : (cyclicCosetProgression H a d length).card ≤
      (Nat.card H) ^ 3
  · apply (large_subgroup_shifted_longProgressionCover hb hq hqb H
      hHdiv hmult a d hproper hlarge).mono_mass
    omega
  · have hcover := small_subgroup_shifted_longProgressionCover hb hq hqb hlength
      H hHdiv hmult a d (Nat.lt_of_not_ge hlarge)
    simpa [cyclicCosetProgression_card_eq_of_proper H a d hproper] using hcover

lemma shiftedZmodValues_mono
    {b : ℕ} [NeZero b] {R S : Finset (ZMod b)} (hRS : R ⊆ S) :
    shiftedZmodValues R ⊆ shiftedZmodValues S := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
  exact mem_shiftedZmodValues_iff.mpr ⟨r, hRS hr, rfl⟩

/-- A cyclic progression modulo the trivial subgroup either is proper, or
is already contained in the single coset of the subgroup generated by its
step. -/
lemma cyclicCosetProgression_bot_subset_zmultiples_one
    {b L : ℕ} [NeZero b] (a d : ZMod b) :
    cyclicCosetProgression (⊥ : AddSubgroup (ZMod b)) a d L ⊆
      cyclicCosetProgression (AddSubgroup.zmultiples d) a d 1 := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp hx
  rw [AddSubgroup.mem_bot, sub_eq_zero] at hxi
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨0, by omega, ?_⟩
  rw [hxi]
  simpa using
    ((AddSubgroup.zmultiples d).nsmul_mem
      (AddSubgroup.mem_zmultiples d) i)

lemma isProperCyclicCosetProgression_zmultiples_one
    {b : ℕ} [NeZero b] (a d : ZMod b) :
    IsProperCyclicCosetProgression (AddSubgroup.zmultiples d) a d 1 := by
  intro i hi j hj _
  omega

/-- Every nonempty ordinary cyclic progression has a long ordinary-integer
progression cover of linear total mass.  In the wrapping case it is first
normalized to one proper coset of the subgroup generated by the step. -/
lemma cyclicCosetProgression_bot_shifted_longProgressionCover
    {b L : ℕ} [NeZero b] (a d : ZMod b) (hL : 0 < L) :
    HasLongProgressionCover
      (shiftedZmodValues
        (cyclicCosetProgression (⊥ : AddSubgroup (ZMod b)) a d L))
      (6 * L) := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  by_cases hproperLength : L ≤ addOrderOf d
  · have hproper := isProperCyclicCosetProgression_bot_of_le_addOrderOf
      a d hproperLength
    obtain ⟨q, hq, hqb, hHdiv, hmult⟩ :=
      exists_generator_modulus hb (⊥ : AddSubgroup (ZMod b))
    have hcover := cyclicCosetProgression_shifted_longProgressionCover
      hb hq hqb hL (⊥ : AddSubgroup (ZMod b)) hHdiv hmult a d hproper
    apply hcover.mono_mass
    have hcard := cyclicCosetProgression_card_le
      (⊥ : AddSubgroup (ZMod b)) a d L
    simpa using Nat.mul_le_mul_left 6 hcard
  · let H : AddSubgroup (ZMod b) := AddSubgroup.zmultiples d
    let R := cyclicCosetProgression H a d 1
    have hsub : cyclicCosetProgression (⊥ : AddSubgroup (ZMod b)) a d L ⊆ R :=
      cyclicCosetProgression_bot_subset_zmultiples_one a d
    have hproper : IsProperCyclicCosetProgression H a d 1 :=
      isProperCyclicCosetProgression_zmultiples_one a d
    obtain ⟨q, hq, hqb, hHdiv, hmult⟩ := exists_generator_modulus hb H
    have hcoverR := cyclicCosetProgression_shifted_longProgressionCover
      hb hq hqb (by omega : 0 < 1) H hHdiv hmult a d hproper
    have hcover := hcoverR.mono_set (shiftedZmodValues_mono hsub)
    apply hcover.mono_mass
    have hRcard : R.card = addOrderOf d := by
      dsimp [R, H]
      rw [cyclicCosetProgression_card_eq_of_proper
        (AddSubgroup.zmultiples d) a d
        (isProperCyclicCosetProgression_zmultiples_one a d)]
      simpa only [one_mul] using Nat.card_zmultiples d
    have horder : addOrderOf d ≤ L := le_of_not_ge hproperLength
    rw [hRcard]
    exact Nat.mul_le_mul_left 6 horder

lemma cyclicCosetProgression_add_start
    {b L : ℕ} [NeZero b] (H : AddSubgroup (ZMod b))
    (f a d : ZMod b) :
    cyclicCosetProgression H (f + a) d L =
      Erdos587.addTranslate f (cyclicCosetProgression H a d L) := by
  ext x
  rw [Erdos587.mem_addTranslate]
  simp only [mem_cyclicCosetProgression_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    convert hx using 1 <;> abel
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    convert hx using 1 <;> abel

lemma card_cyclicCosetProgression_add_start
    {b L : ℕ} [NeZero b] (H : AddSubgroup (ZMod b))
    (f a d : ZMod b) :
    (cyclicCosetProgression H (f + a) d L).card =
      (cyclicCosetProgression H a d L).card := by
  rw [cyclicCosetProgression_add_start]
  exact Erdos587.card_addTranslate _ _

/-- Completion after rectification: if the dense Fourier core lies in one
ordinary cyclic progression, Ruzsa covering puts the original set in two
translates of its difference progression.  Lifting those two translates
gives a long integer-progression cover with total mass `48L`. -/
lemma dense_core_progression_longProgressionCover
    {b L : ℕ} [NeZero b] {a d : ZMod b} {B C : Finset (ZMod b)}
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hCprog : C ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod b)) a d L)
    (hL : 0 < L) :
    HasLongProgressionCover (shiftedZmodValues B) (48 * L) := by
  classical
  obtain ⟨F, hFB, hFcard, hBF⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hsmall
  let R := cyclicCosetProgression (⊥ : AddSubgroup (ZMod b))
    (-(L • d)) d (2 * L)
  have hCR : C - C ⊆ R := cyclicCosetProgression_bot_sub_subset hCprog
  have hBR : B ⊆ F + R :=
    hBF.trans (Finset.add_subset_add Finset.Subset.rfl hCR)
  have hB : B.Nonempty := hC.mono hCB
  have hF : F.Nonempty := by
    obtain ⟨x, hxB⟩ := hB
    obtain ⟨f, hfF, r, hrR, hfr⟩ := Finset.mem_add.mp (hBR hxB)
    exact ⟨f, hfF⟩
  let f₀ := hF.choose
  have hf₀ : f₀ ∈ F := hF.choose_spec
  let E := F.erase f₀
  have hEcard : E.card ≤ 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hf₀]
    omega
  let f₁ := if hE : E.Nonempty then hE.choose else f₀
  have hf_cases : ∀ f ∈ F, f = f₀ ∨ f = f₁ := by
    intro f hf
    by_cases hff₀ : f = f₀
    · exact Or.inl hff₀
    · right
      have hfE : f ∈ E := by simpa [E, hff₀] using hf
      by_cases hE : E.Nonempty
      · have hf₁E : f₁ ∈ E := by simpa [f₁, hE] using hE.choose_spec
        exact Finset.card_le_one.mp hEcard f hfE f₁ hf₁E
      · exact False.elim (hE ⟨f, hfE⟩)
  let P₀ := cyclicCosetProgression (⊥ : AddSubgroup (ZMod b))
    (f₀ + (-(L • d))) d (2 * L)
  let P₁ := cyclicCosetProgression (⊥ : AddSubgroup (ZMod b))
    (f₁ + (-(L • d))) d (2 * L)
  have hBsub : shiftedZmodValues B ⊆
      shiftedZmodValues P₀ ∪ shiftedZmodValues P₁ := by
    intro y hy
    obtain ⟨x, hxB, rfl⟩ := mem_shiftedZmodValues_iff.mp hy
    obtain ⟨f, hfF, r, hrR, hfr⟩ := Finset.mem_add.mp (hBR hxB)
    rcases hf_cases f hfF with rfl | rfl
    · apply Finset.mem_union_left
      apply mem_shiftedZmodValues_iff.mpr
      refine ⟨x, ?_, rfl⟩
      dsimp [P₀]
      rw [cyclicCosetProgression_add_start]
      apply Erdos587.mem_addTranslate.mpr
      rw [← hfr]
      simpa [R] using hrR
    · apply Finset.mem_union_right
      apply mem_shiftedZmodValues_iff.mpr
      refine ⟨x, ?_, rfl⟩
      dsimp [P₁]
      rw [cyclicCosetProgression_add_start]
      apply Erdos587.mem_addTranslate.mpr
      rw [← hfr]
      simpa [R] using hrR
  have h2L : 0 < 2 * L := by omega
  have hcover₀ : HasLongProgressionCover (shiftedZmodValues P₀) (12 * L) := by
    change HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression
        (⊥ : AddSubgroup (ZMod b)) (f₀ + (-(L • d))) d (2 * L)))
      (12 * L)
    convert cyclicCosetProgression_bot_shifted_longProgressionCover
      (f₀ + (-(L • d))) d h2L using 1 <;> omega
  have hcover₁ : HasLongProgressionCover (shiftedZmodValues P₁) (12 * L) := by
    change HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression
        (⊥ : AddSubgroup (ZMod b)) (f₁ + (-(L • d))) d (2 * L)))
      (12 * L)
    convert cyclicCosetProgression_bot_shifted_longProgressionCover
      (f₁ + (-(L • d))) d h2L using 1 <;> omega
  have hcardP : (shiftedZmodValues P₀).card =
      (shiftedZmodValues P₁).card := by
    rw [card_shiftedZmodValues, card_shiftedZmodValues]
    dsimp [P₀, P₁, R]
    rw [card_cyclicCosetProgression_add_start,
      card_cyclicCosetProgression_add_start]
  have hunion := hcover₀.union_equal_card hcover₁ hcardP
  convert hunion.mono_set hBsub using 1 <;> omega

/-- Completion after rectification for a general cyclic coset progression.
The parameter mass is the number `L` of displayed cosets times the subgroup
size; no properness assumption is needed. -/
lemma dense_core_cosetProgression_longProgressionCover
    {b L : ℕ} [NeZero b] {H : AddSubgroup (ZMod b)}
    {a d : ZMod b} {B C : Finset (ZMod b)}
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hCprog : C ⊆ cyclicCosetProgression H a d L)
    (hL : 0 < L) :
    HasLongProgressionCover (shiftedZmodValues B)
      (48 * (L * Nat.card H)) := by
  classical
  obtain ⟨F, hFB, hFcard, hBF⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hsmall
  let R := cyclicCosetProgression H (-(L • d)) d (2 * L)
  have hCR : C - C ⊆ R := cyclicCosetProgression_sub_subset hCprog
  have hBR : B ⊆ F + R :=
    hBF.trans (Finset.add_subset_add Finset.Subset.rfl hCR)
  have hB : B.Nonempty := hC.mono hCB
  have hF : F.Nonempty := by
    obtain ⟨x, hxB⟩ := hB
    obtain ⟨f, hfF, r, hrR, _⟩ := Finset.mem_add.mp (hBR hxB)
    exact ⟨f, hfF⟩
  let f₀ := hF.choose
  have hf₀ : f₀ ∈ F := hF.choose_spec
  let E := F.erase f₀
  have hEcard : E.card ≤ 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hf₀]
    omega
  let f₁ := if hE : E.Nonempty then hE.choose else f₀
  have hf_cases : ∀ f ∈ F, f = f₀ ∨ f = f₁ := by
    intro f hf
    by_cases hff₀ : f = f₀
    · exact Or.inl hff₀
    · right
      have hfE : f ∈ E := by simpa [E, hff₀] using hf
      by_cases hE : E.Nonempty
      · have hf₁E : f₁ ∈ E := by simpa [f₁, hE] using hE.choose_spec
        exact Finset.card_le_one.mp hEcard f hfE f₁ hf₁E
      · exact False.elim (hE ⟨f, hfE⟩)
  let P₀ := cyclicCosetProgression H
    (f₀ + (-(L • d))) d (2 * L)
  let P₁ := cyclicCosetProgression H
    (f₁ + (-(L • d))) d (2 * L)
  have hBsub : shiftedZmodValues B ⊆
      shiftedZmodValues P₀ ∪ shiftedZmodValues P₁ := by
    intro y hy
    obtain ⟨x, hxB, rfl⟩ := mem_shiftedZmodValues_iff.mp hy
    obtain ⟨f, hfF, r, hrR, hfr⟩ := Finset.mem_add.mp (hBR hxB)
    rcases hf_cases f hfF with rfl | rfl
    · apply Finset.mem_union_left
      apply mem_shiftedZmodValues_iff.mpr
      refine ⟨x, ?_, rfl⟩
      dsimp [P₀]
      rw [cyclicCosetProgression_add_start]
      apply Erdos587.mem_addTranslate.mpr
      rw [← hfr]
      simpa [R] using hrR
    · apply Finset.mem_union_right
      apply mem_shiftedZmodValues_iff.mpr
      refine ⟨x, ?_, rfl⟩
      dsimp [P₁]
      rw [cyclicCosetProgression_add_start]
      apply Erdos587.mem_addTranslate.mpr
      rw [← hfr]
      simpa [R] using hrR
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  obtain ⟨q, hq, hqb, hHdiv, hmult⟩ := exists_generator_modulus hb H
  have h2L : 0 < 2 * L := by omega
  have hcover₀ : HasLongProgressionCover (shiftedZmodValues P₀)
      (12 * (L * Nat.card H)) := by
    change HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H
        (f₀ + (-(L • d))) d (2 * L)))
      (12 * (L * Nat.card H))
    convert cyclicCosetProgression_shifted_longProgressionCover_parametric
      hb hq hqb h2L H hHdiv hmult (f₀ + (-(L • d))) d using 1 <;> ring
  have hcover₁ : HasLongProgressionCover (shiftedZmodValues P₁)
      (12 * (L * Nat.card H)) := by
    change HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H
        (f₁ + (-(L • d))) d (2 * L)))
      (12 * (L * Nat.card H))
    convert cyclicCosetProgression_shifted_longProgressionCover_parametric
      hb hq hqb h2L H hHdiv hmult (f₁ + (-(L • d))) d using 1 <;> ring
  have hcardP : (shiftedZmodValues P₀).card =
      (shiftedZmodValues P₁).card := by
    rw [card_shiftedZmodValues, card_shiftedZmodValues]
    dsimp [P₀, P₁, R]
    rw [card_cyclicCosetProgression_add_start,
      card_cyclicCosetProgression_add_start]
  have hunion := hcover₀.union_equal_card hcover₁ hcardP
  convert hunion.mono_set hBsub using 1 <;> ring

lemma coprime_add_of_dvd_left {M b x : ℕ} (hMb : M ∣ b) :
    Nat.Coprime M (b + x) ↔ Nat.Coprime M x := by
  obtain ⟨k, rfl⟩ := hMb
  simpa [add_comm, mul_comm] using Nat.coprime_add_mul_left_right M x k

lemma card_coprimePart_shiftedZmodValues
    {b M : ℕ} [NeZero b] (hMb : M ∣ b) (R : Finset (ZMod b)) :
    (coprimePart (shiftedZmodValues R) M).card =
      (coprimePart (zmodValues R) M).card := by
  let e : ℕ → ℕ := fun x ↦ b + x
  have heq : coprimePart (shiftedZmodValues R) M =
      (coprimePart (zmodValues R) M).image e := by
    ext y
    simp only [coprimePart, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hy, hycop⟩
      obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hy
      refine ⟨r.val, ⟨mem_zmodValues_iff.mpr ⟨r, hr, rfl⟩, ?_⟩, rfl⟩
      exact (coprime_add_of_dvd_left hMb).mp hycop
    · rintro ⟨x, ⟨hx, hxcop⟩, rfl⟩
      obtain ⟨r, hr, rfl⟩ := mem_zmodValues_iff.mp hx
      exact ⟨mem_shiftedZmodValues_iff.mpr ⟨r, hr, rfl⟩,
        (coprime_add_of_dvd_left hMb).mpr hxcop⟩
  rw [heq, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact Nat.add_left_cancel hxy

/-! ### Divisor-sensitive modular completeness -/

/-- A homomorphism sends list subset sums onto the subset sums of the
mapped list. -/
lemma image_listSubsetSums_map {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
    (f : G →+ H) (A : List G) :
    (Erdos587.listSubsetSums A).image f =
      Erdos587.listSubsetSums (A.map f) := by
  have image_addTranslate (a : G) (S : Finset G) :
      (Erdos587.addTranslate a S).image f =
        Erdos587.addTranslate (f a) (S.image f) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      rw [Erdos587.mem_addTranslate] at hx ⊢
      apply Finset.mem_image.mpr
      refine ⟨-a + x, hx, ?_⟩
      rw [map_add, map_neg, hxy]
    · intro hy
      rw [Erdos587.mem_addTranslate] at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨a + x, ?_, ?_⟩
      · rw [Erdos587.mem_addTranslate]
        simpa
      · rw [map_add, hxy]
        abel
  induction A with
  | nil => simp [Erdos587.listSubsetSums]
  | cons a A ih =>
      simp only [Erdos587.listSubsetSums_cons, List.map_cons,
        Finset.image_union, ih]
      rw [image_addTranslate, ih]

lemma zmod_castHom_eq_zero_iff_val_dvd {q d : ℕ} [NeZero q]
    (hdq : d ∣ q) (x : ZMod q) :
    ZMod.castHom hdq (ZMod d) x = 0 ↔ d ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- If a surjective quotient has exactly the translation stabilizer of `S`
as its kernel, the image of `S` is aperiodic. -/
lemma image_stabilizer_eq_bot {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (S : Finset G)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    Erdos587.finsetAddStabilizer (S.image f) = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hy' : Erdos587.addTranslate (f x) (S.image f) = S.image f := hy
  have hxsub : Erdos587.addTranslate x S ⊆ S := by
    intro z hz
    have hs : -x + z ∈ S := Erdos587.mem_addTranslate.mp hz
    have hfs : f (-x + z) ∈ S.image f :=
      Finset.mem_image.mpr ⟨_, hs, rfl⟩
    have hfztrans : f z ∈ Erdos587.addTranslate (f x) (S.image f) := by
      apply Finset.mem_image.mpr
      refine ⟨f (-x + z), hfs, ?_⟩
      simp only [map_add, map_neg]
      abel
    rw [hy'] at hfztrans
    obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfztrans
    have hzero : f (z - t) = 0 := by
      rw [map_sub, hft]
      simp
    have hstab : z - t ∈ Erdos587.finsetAddStabilizer S :=
      (hker _).mp hzero
    have hmem : (z - t) + t ∈ Erdos587.addTranslate (z - t) S := by
      apply Finset.mem_image.mpr
      exact ⟨t, ht, rfl⟩
    rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
    simpa using hmem
  have hxstab : Erdos587.addTranslate x S = S := by
    exact Finset.eq_of_subset_of_card_le hxsub (by
      rw [Erdos587.card_addTranslate])
  have hxker : f x = 0 := (hker x).mpr hxstab
  simpa [hxker]

/-- Under the same kernel hypothesis, a proper set has proper image. -/
lemma image_ne_univ_of_stabilizer_kernel {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (S : Finset G) (hSproper : S ≠ Finset.univ)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    S.image f ≠ Finset.univ := by
  intro himage
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hfx : f x ∈ S.image f := by rw [himage]; simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfx
  have hzero : f (x - t) = 0 := by rw [map_sub, hft]; simp
  have hstab : x - t ∈ Erdos587.finsetAddStabilizer S :=
    (hker _).mp hzero
  have hmem : (x - t) + t ∈ Erdos587.addTranslate (x - t) S := by
    apply Finset.mem_image.mpr
    exact ⟨t, ht, rfl⟩
  rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
  simpa using hmem

/-- If list subset sums are proper and have trivial stabilizer, fewer than
`|G|-1` occurrences can be nonzero. -/
lemma nonzero_length_add_one_lt_card_of_stabilizer_bot
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : List G)
    (hproper : Erdos587.listSubsetSums A ≠ Finset.univ)
    (hstab : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums A) = ⊥) :
    (A.filter fun a => a ≠ 0).length + 1 < Fintype.card G := by
  have hstable :
      (Erdos587.subsetSumStableTerms A).filter (fun a => a ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have haStab : a ∈ Erdos587.finsetAddStabilizer
        (Erdos587.listSubsetSums A) :=
      Erdos587.mem_stable_stabilizes_listSubsetSums ha
    rw [hstab] at haStab
    simpa using haStab
  have hperm :=
    (Erdos587.stable_append_growth_perm A).filter (fun a => a ≠ 0)
  have hlen :
      (A.filter fun a => a ≠ 0).length ≤
        (Erdos587.subsetSumGrowthTerms A).length := by
    rw [← hperm.length_eq, List.filter_append, hstable]
    exact List.length_filter_le _ _
  have hcardlt : (Erdos587.listSubsetSums A).card < Fintype.card G := by
    have hss : Erdos587.listSubsetSums A ⊂ (Finset.univ : Finset G) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩
    exact Finset.card_lt_card hss
  have hgrowth := Erdos587.growth_length_add_one_le_card_listSubsetSums A
  omega

lemma length_filter_zmod_castHom_ne_zero
    {q d : ℕ} [NeZero q] [NeZero d] (hdq : d ∣ q) (A : List ℕ) :
    ((A.map fun a : ℕ => ZMod.castHom hdq (ZMod d) (a : ZMod q)).filter
      fun x => x ≠ 0).length =
      (A.filter fun a => ¬ d ∣ a).length := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.map_cons, map_natCast]
      have ih' :
          ((A.map fun a : ℕ => (a : ZMod d)).filter fun x => x ≠ 0).length =
            (A.filter fun a => ¬ d ∣ a).length := by
        simpa only [map_natCast] using ih
      by_cases ha : d ∣ a
      · have ha0 : (a : ZMod d) = 0 :=
          (ZMod.natCast_eq_zero_iff a d).mpr ha
        rw [List.filter_cons_of_neg (by simpa using ha0),
          List.filter_cons_of_neg (by simpa using ha)]
        exact ih'
      · have ha0 : (a : ZMod d) ≠ 0 :=
          fun h => ha ((ZMod.natCast_eq_zero_iff a d).mp h)
        rw [List.filter_cons_of_pos (by simp [ha0]),
          List.filter_cons_of_pos (by simp [ha]),
          List.length_cons, List.length_cons, ih']

/-- CFP's divisor-sensitive modular completeness criterion. -/
theorem listSubsetSums_mod_eq_univ_of_divisor_diverse
    {q : ℕ} [NeZero q] (hq : 0 < q) (A : List ℕ)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ (A.filter fun a => ¬ d ∣ a).length) :
    Erdos587.listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) =
      Finset.univ := by
  let M : List (ZMod q) := A.map fun a : ℕ => (a : ZMod q)
  let S : Finset (ZMod q) := Erdos587.listSubsetSums M
  by_contra hproper
  have hproperS : S ≠ Finset.univ := by simpa [S, M] using hproper
  let K : AddSubgroup (ZMod q) := Erdos587.finsetAddStabilizer S
  have hKproper : K ≠ ⊤ :=
    Erdos587.finsetAddStabilizer_ne_top
      (by simpa [S] using Erdos587.zero_mem_listSubsetSums M) hproperS
  obtain ⟨d, hdpos, hdq, hKdiv, hmultK⟩ := exists_generator_modulus hq K
  have hdgt : 1 < d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    apply hKproper
    apply top_unique
    intro x _
    rw [← ZMod.natCast_zmod_val x]
    simpa [hd1] using hmultK x.val
  let : NeZero d := ⟨hdpos.ne'⟩
  let f : ZMod q →+ ZMod d :=
    (ZMod.castHom hdq (ZMod d)).toAddMonoidHom
  have hfsurj : Function.Surjective f := by
    intro y
    refine ⟨(y.val : ZMod q), ?_⟩
    have hdqle : d ≤ q := Nat.le_of_dvd hq hdq
    have hyq : y.val < q := y.val_lt.trans_le hdqle
    dsimp [f]
    rw [ZMod.cast_eq_val, ZMod.val_natCast, Nat.mod_eq_of_lt hyq]
    exact ZMod.natCast_zmod_val y
  have hker : ∀ x : ZMod q,
      f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S := by
    intro x
    constructor
    · intro hx
      have hdval : d ∣ x.val :=
        (zmod_castHom_eq_zero_iff_val_dvd hdq x).mp (by
          simpa [f] using hx)
      obtain ⟨i, hi⟩ := hdval
      have hxrepr : x = (i * d : ℕ) := by
        calc
          x = (x.val : ZMod q) := (ZMod.natCast_zmod_val x).symm
          _ = (d * i : ℕ) := by rw [hi]
          _ = (i * d : ℕ) := by rw [mul_comm]
      rw [hxrepr]
      change ((i * d : ℕ) : ZMod q) ∈ K
      simpa only [Nat.cast_mul] using hmultK i
    · intro hx
      apply (zmod_castHom_eq_zero_iff_val_dvd hdq x).mpr
      exact hKdiv x hx
  let B : List (ZMod d) := M.map f
  have himage : S.image f = Erdos587.listSubsetSums B := by
    simpa [S, B] using image_listSubsetSums_map f M
  have hproperB : Erdos587.listSubsetSums B ≠ Finset.univ := by
    intro hall
    have himageProper := image_ne_univ_of_stabilizer_kernel
      f S hproperS hker
    apply himageProper
    rw [himage, hall]
  have hstabB : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums B) = ⊥ := by
    have hstab := image_stabilizer_eq_bot f hfsurj S hker
    rwa [himage] at hstab
  have hfew := nonzero_length_add_one_lt_card_of_stabilizer_bot
    B hproperB hstabB
  have hfew' : (B.filter fun a => a ≠ 0).length + 1 < d := by
    simpa [ZMod.card] using hfew
  have hfilter :
      (B.filter fun a => a ≠ 0).length =
        (A.filter fun a => ¬ d ∣ a).length := by
    simpa [B, M, f, List.map_map, Function.comp_def] using
      length_filter_zmod_castHom_ne_zero hdq A
  rw [hfilter] at hfew'
  have hlower := hdiverse d hdgt hdq
  omega

/-- Adjoining a new group element replaces the finite subset-sum set by
its union with the translate by that element. -/
lemma subsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (a : G) (haA : a ∉ A) :
    (insert a A).subsetSum =
      A.subsetSum ∪ Erdos587.addTranslate a A.subsetSum := by
  ext x
  simp only [Finset.mem_subsetSum_iff, Finset.mem_union]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases ha : a ∈ B
    · right
      rw [Erdos587.mem_addTranslate, Finset.mem_subsetSum_iff]
      refine ⟨B.erase a, ?_, ?_⟩
      · intro y hy
        have hy' := Finset.mem_erase.mp hy
        exact (Finset.mem_insert.mp (hB hy'.2)).resolve_left
          (fun h => hy'.1 h)
      · have he := Finset.sum_erase_add B id ha
        simp only [id_eq] at he
        rw [← he]
        abel
    · left
      exact ⟨B, fun y hy => (Finset.mem_insert.mp (hB hy)).resolve_left
        (fun h => ha (h ▸ hy)), rfl⟩
  · rintro (⟨B, hB, rfl⟩ | hx)
    · exact ⟨B, hB.trans (Finset.subset_insert a A), rfl⟩
    · rw [Erdos587.mem_addTranslate] at hx
      obtain ⟨B, hB, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
      have ha : a ∉ B := fun haB => haA (hB haB)
      refine ⟨insert a B, Finset.insert_subset_insert a hB, ?_⟩
      rw [Finset.sum_insert ha, hsum]
      abel

lemma listSubsetSums_eq_of_perm
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : List G} (h : A.Perm B) :
    Erdos587.listSubsetSums A = Erdos587.listSubsetSums B := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Erdos587.listSubsetSums_cons, ih]
  | swap a b l =>
      simp only [Erdos587.listSubsetSums_cons,
        Erdos587.addTranslate_union, Erdos587.addTranslate_add]
      rw [add_comm a b]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Finset subset sums agree with the duplicate-free list recursion. -/
lemma listSubsetSums_toList_eq_subsetSum
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    Erdos587.listSubsetSums A.toList = A.subsetSum := by
  induction A using Finset.induction with
  | empty =>
      simp [Erdos587.listSubsetSums_nil, Finset.subsetSum]
  | @insert a A ha ih =>
      rw [listSubsetSums_eq_of_perm (Finset.toList_insert ha)]
      simp only [Erdos587.listSubsetSums_cons, ih]
      symm
      exact subsetSum_insert_eq A a ha

/-! ### Subgroup coset fibres of subset-sum sets -/

/-- A coset fibre of `S`, translated back into its subgroup. -/
noncomputable def normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  exact Finset.univ.filter fun h ↦ u + h.1 ∈ S

@[simp] lemma mem_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {S : Finset G} {u : G} {h : H} :
    h ∈ normalizedCosetFiber H S u ↔ u + h.1 ∈ S := by
  let : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  simp [normalizedCosetFiber]

/-- The elements of a finite ambient set which lie in a subgroup, lifted to
the subgroup subtype. -/
noncomputable def elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  exact Finset.univ.filter fun h ↦ h.1 ∈ A

@[simp] lemma mem_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {h : H} :
    h ∈ elementsInSubgroup H A ↔ h.1 ∈ A := by
  let : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  simp [elementsInSubgroup]

/-! ### The cyclic modulus attached to a residue set -/

/-- The positive divisor `q ∣ b` for which the subgroup generated by `R`
is the subgroup of multiples of `q`. -/
noncomputable def closureModulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : ℕ :=
  Classical.choose (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_spec {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    0 < closureModulus hb R ∧ closureModulus hb R ∣ b ∧
      (∀ x : ZMod b, x ∈ AddSubgroup.closure (R : Set (ZMod b)) →
        closureModulus hb R ∣ x.val) ∧
      (∀ i : ℕ, (i * closureModulus hb R : ZMod b) ∈
        AddSubgroup.closure (R : Set (ZMod b))) :=
  Classical.choose_spec (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_pos {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : 0 < closureModulus hb R :=
  (closureModulus_spec hb R).1

lemma closureModulus_dvd {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R ∣ b :=
  (closureModulus_spec hb R).2.1

lemma closure_eq_zmultiples_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.zmultiples (closureModulus hb R : ZMod b) :=
  subgroup_eq_zmultiples_of_generator_modulus _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma mem_closure_iff_modulus_dvd_val {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) (x : ZMod b) :
    x ∈ AddSubgroup.closure (R : Set (ZMod b)) ↔
      closureModulus hb R ∣ x.val := by
  constructor
  · exact (closureModulus_spec hb R).2.2.1 x
  · rintro ⟨i, hi⟩
    have hmultiple := (closureModulus_spec hb R).2.2.2 i
    have hx : x = (i * closureModulus hb R : ℕ) := by
      calc
        x = (x.val : ZMod b) := (ZMod.natCast_zmod_val x).symm
        _ = (closureModulus hb R * i : ℕ) := by rw [hi]
        _ = (i * closureModulus hb R : ℕ) := by rw [mul_comm]
    rw [hx]
    simpa only [Nat.cast_mul] using hmultiple

lemma ncard_closure_eq_div_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard =
      b / closureModulus hb R :=
  ncard_subgroup_of_generator_modulus hb (closureModulus_pos hb R)
    (closureModulus_dvd hb R) _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma card_elementsInSubgroup_of_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (hAH : (A : Set G) ⊆ H) :
    (elementsInSubgroup H A).card = A.card := by
  classical
  let : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  have himage : (elementsInSubgroup H A).image (fun h : H ↦ h.1) = A := by
    ext x
    simp only [Finset.mem_image, mem_elementsInSubgroup]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hx
      exact ⟨⟨x, hAH hx⟩, hx, rfl⟩
  calc
    (elementsInSubgroup H A).card =
        ((elementsInSubgroup H A).image (fun h : H ↦ h.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := by rw [himage]

/-- The residue set injects into its closure, so its defining modulus times
its cardinality is at most the ambient modulus. -/
lemma closureModulus_mul_card_le {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R * R.card ≤ b := by
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  have hRcard : R.card ≤ Fintype.card H := by
    rw [← card_elementsInSubgroup_of_subset H R
      (fun _ hx => AddSubgroup.subset_closure hx)]
    exact Finset.card_le_univ _
  have hHcard : Fintype.card H = b / closureModulus hb R := by
    rw [show Fintype.card H = (H : Set (ZMod b)).ncard by
      exact Set.fintypeCard_eq_ncard (H : Set (ZMod b))]
    exact ncard_closure_eq_div_modulus hb R
  rw [hHcard] at hRcard
  calc
    closureModulus hb R * R.card ≤
        closureModulus hb R * (b / closureModulus hb R) :=
      Nat.mul_le_mul_left _ hRcard
    _ = b := Nat.mul_div_cancel' (closureModulus_dvd hb R)

/-- Shrinking a residue set can only enlarge its cyclic modulus. -/
lemma closureModulus_dvd_of_subset {b : ℕ} [NeZero b] (hb : 0 < b)
    {R T : Finset (ZMod b)} (hTR : T ⊆ R) :
    closureModulus hb R ∣ closureModulus hb T := by
  let q := closureModulus hb R
  let r := closureModulus hb T
  have hrb : r ∣ b := closureModulus_dvd hb T
  have hrle : r ≤ b := Nat.le_of_dvd hb hrb
  by_cases hrEq : r = b
  · change q ∣ r
    rw [hrEq]
    exact closureModulus_dvd hb R
  · have hrlt : r < b := lt_of_le_of_ne hrle hrEq
    have hmemT : (r : ZMod b) ∈ AddSubgroup.closure (T : Set (ZMod b)) := by
      have := (closureModulus_spec hb T).2.2.2 1
      simpa [r] using this
    have hmemR : (r : ZMod b) ∈ AddSubgroup.closure (R : Set (ZMod b)) := by
      apply AddSubgroup.closure_mono (by exact_mod_cast hTR)
      exact hmemT
    have hqval := (closureModulus_spec hb R).2.2.1 (r : ZMod b) hmemR
    simpa [q, r, ZMod.val_natCast, Nat.mod_eq_of_lt hrlt] using hqval

/-- Divisor diversity in an original residue set implies that the already
used elements represent every coset of the subgroup generated by the
remaining set. -/
lemma normalizedCosetFiber_nonempty_of_diverse_used
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    ∀ u : ZMod b,
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).Nonempty := by
  classical
  let q := closureModulus hb R
  have hq : 0 < q := closureModulus_pos hb R
  let : NeZero q := ⟨hq.ne'⟩
  let U := R₀ \ R
  let f : ZMod b →+ ZMod q :=
    (ZMod.castHom (closureModulus_dvd hb R) (ZMod q)).toAddMonoidHom
  have hUdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length := by
    intro d hd hdq
    have hnonmult : R₀.filter (fun x => ¬d ∣ x.val) ⊆
        U.filter (fun x => ¬d ∣ x.val) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      refine ⟨?_, hx.2⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hx.1, ?_⟩
      intro hxR
      have hqval : q ∣ x.val :=
        (closureModulus_spec hb R).2.2.1 x
          (AddSubgroup.subset_closure hxR)
      exact hx.2 (hdq.trans hqval)
    have hcard := Finset.card_le_card hnonmult
    have hlen : ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length =
        (U.filter fun x => ¬d ∣ x.val).card := by
      rw [List.filter_map]
      rw [List.length_map]
      rw [← List.toFinset_card_of_nodup (U.nodup_toList.filter _)]
      rw [List.toFinset_filter]
      simp [Function.comp_def]
    rw [hlen]
    exact (hdiverse d hd (by simpa [q] using hdq)).trans hcard
  have hallVal : Erdos587.listSubsetSums
      ((U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q)) = Finset.univ :=
    listSubsetSums_mod_eq_univ_of_divisor_diverse hq _ hUdiverse
  have hmap : U.toList.map f =
      (U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp [f, ZMod.castHom_apply]
  have hall : U.subsetSum.image f = Finset.univ := by
    rw [← listSubsetSums_toList_eq_subsetSum]
    rw [image_listSubsetSums_map, hmap, hallVal]
  intro u
  obtain ⟨e, he⟩ := hE
  have htarget : f (u - e) ∈ U.subsetSum.image f := by
    rw [hall]
    simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp htarget
  let H := AddSubgroup.closure (R : Set (ZMod b))
  have hker : e + t - u ∈ H := by
    apply (mem_closure_iff_modulus_dvd_val hb R (e + t - u)).2
    apply (zmod_castHom_eq_zero_iff_val_dvd
      (closureModulus_dvd hb R) (e + t - u)).mp
    change f (e + t - u) = 0
    rw [map_sub, map_add, hft]
    simp [map_sub]
  refine ⟨⟨e + t - u, hker⟩, ?_⟩
  rw [mem_normalizedCosetFiber]
  rw [Finset.mem_add]
  refine ⟨e, he, t, ht, ?_⟩
  simp [sub_eq_add_neg]

/-- If every coset fibre contains at least one quarter of its subgroup,
then the entire set occupies at least one quarter of the ambient group. -/
lemma card_le_four_mul_card_of_all_coset_fibers_large
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G)
    (hlarge : ∀ u : G,
      (H : Set G).ncard ≤ 4 * (normalizedCosetFiber H S u).card) :
    Fintype.card G ≤ 4 * S.card := by
  classical
  let : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let I : Finset (Σ _u : G, H) :=
    (Finset.univ : Finset G).sigma fun u => normalizedCosetFiber H S u
  let J : Finset (G × H) := S ×ˢ (Finset.univ : Finset H)
  have hIJ : I.card = J.card := by
    apply Finset.card_bij'
        (fun p _ => (p.1 + p.2.1, p.2))
        (fun p _ => ⟨p.1 - p.2.1, p.2⟩)
    · rintro ⟨u, h⟩ hp
      simp [sub_eq_add_neg]
    · rintro ⟨s, h⟩ hp
      simp [sub_eq_add_neg]
    · intro p hp
      dsimp only [J]
      rw [Finset.mem_product]
      dsimp only [I] at hp
      have hpFiber := (Finset.mem_sigma.mp hp).2
      exact ⟨mem_normalizedCosetFiber.mp hpFiber, Finset.mem_univ _⟩
    · intro p hp
      dsimp only [I]
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_normalizedCosetFiber]
      dsimp only [J] at hp
      rw [Finset.mem_product] at hp
      simpa [sub_eq_add_neg] using hp.1
  have hsum : Fintype.card G * (H : Set G).ncard ≤ 4 * I.card := by
    calc
      Fintype.card G * (H : Set G).ncard =
          ∑ _u : G, (H : Set G).ncard := by simp
      _ ≤ ∑ u : G, 4 * (normalizedCosetFiber H S u).card := by
        exact Finset.sum_le_sum fun u _ => hlarge u
      _ = 4 * I.card := by
        simp only [I, Finset.card_sigma]
        simp [Finset.mul_sum]
  have hHcard : (H : Set G).ncard = Fintype.card H := by
    exact (Set.fintypeCard_eq_ncard (H : Set G)).symm
  have hHpos : 0 < (H : Set G).ncard := by
    rw [hHcard]
    exact Fintype.card_pos
  have hIcard : I.card = S.card * (H : Set G).ncard := by
    simp only [hIJ, J, Finset.card_product, Finset.card_univ, hHcard]
  rw [hIcard] at hsum
  have hmul : Fintype.card G * (H : Set G).ncard ≤
      (4 * S.card) * (H : Set G).ncard := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hmul hHpos

/-- The seeded subset-sum set after adjoining one unused element is the
old set together with one translate. -/
lemma seededSubsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (E A : Finset G) (x : G) (hx : x ∉ A) :
    E + (insert x A).subsetSum =
      (E + A.subsetSum) ∪
        Erdos587.addTranslate x (E + A.subsetSum) := by
  rw [subsetSum_insert_eq A x hx, Finset.add_union]
  congr 1
  ext z
  constructor
  · intro hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    rw [Erdos587.mem_addTranslate]
    apply Finset.mem_add.mpr
    refine ⟨e, he, -x + t, ?_, ?_⟩
    · exact Erdos587.mem_addTranslate.mp ht
    · calc
        e + (-x + t) = -x + (e + t) := by abel
        _ = -x + z := by rw [hzt]
  · intro hz
    rw [Erdos587.mem_addTranslate] at hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    apply Finset.mem_add.mpr
    refine ⟨e, he, x + t, ?_, ?_⟩
    · rw [Erdos587.mem_addTranslate]
      simpa using ht
    · calc
        e + (x + t) = x + (e + t) := by abel
        _ = x + (-x + z) := by rw [hzt]
        _ = z := by abel

lemma sdiff_erase_eq_insert_sdiff
    {α : Type*} [DecidableEq α] {R₀ R : Finset α} {x : α}
    (hxR : x ∈ R) (hR : R ⊆ R₀) :
    R₀ \ R.erase x = insert x (R₀ \ R) := by
  ext y
  by_cases hyx : y = x
  · subst y
    simp [hxR, hR hxR]
  · simp [hyx]

lemma exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {t : H}
    (ht : t ∈ (elementsInSubgroup H A).subsetSum) :
    ∃ U : Finset G, U ⊆ A ∧ (∀ x ∈ U, x ∈ H) ∧
      ∑ x ∈ U, x = t.1 := by
  rw [Finset.mem_subsetSum_iff] at ht
  obtain ⟨T, hT, hsum⟩ := ht
  let U : Finset G := T.image fun h : H ↦ h.1
  have hU : U ⊆ A := by
    intro x hx
    obtain ⟨h, hhT, rfl⟩ := Finset.mem_image.mp hx
    exact mem_elementsInSubgroup.mp (hT hhT)
  refine ⟨U, hU, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
    exact h.2
  · change ∑ x ∈ T.image (fun h : H ↦ h.1), x = t.1
    rw [Finset.sum_image (fun _ _ _ _ h ↦ Subtype.ext h)]
    have he := congrArg Subtype.val hsum
    simpa using he

/-- CFP Lemma 5.11: every occupied subgroup coset of a subset-sum set
contains at least as many points as the subset sums made only from elements
of that subgroup. -/
lemma subsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H A.subsetSum u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H A.subsetSum u).card := by
  classical
  let : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hy : u + h₀.1 ∈ A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_subsetSum_iff] at hy
  obtain ⟨B, hBA, hBsum⟩ := hy
  let B₀ := B.filter fun x ↦ x ∉ H
  let B₁ := B.filter fun x ↦ x ∈ H
  let y := ∑ x ∈ B₀, x
  have hBsplit : B₀ ∪ B₁ = B := by
    ext x
    by_cases hx : x ∈ H <;> simp [B₀, B₁, hx]
  have hBdisj : Disjoint B₀ B₁ := by
    rw [Finset.disjoint_left]
    intro x hx₀ hx₁
    exact (Finset.mem_filter.mp hx₀).2 (Finset.mem_filter.mp hx₁).2
  have hysum : y + ∑ x ∈ B₁, x = u + h₀.1 := by
    rw [← Finset.sum_union hBdisj, hBsplit, hBsum]
  have hB₁H : ∑ x ∈ B₁, x ∈ H := by
    apply H.sum_mem
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hycoset : -u + y ∈ H := by
    have heq : -u + y = h₀.1 - ∑ x ∈ B₁, x := by
      calc
        -u + y = (-u + (y + ∑ x ∈ B₁, x)) - ∑ x ∈ B₁, x := by abel
        _ = (-u + (u + h₀.1)) - ∑ x ∈ B₁, x := by rw [hysum]
        _ = h₀.1 - ∑ x ∈ B₁, x := by abel
    rw [heq]
    exact H.sub_mem h₀.2 hB₁H
  let base : H := ⟨-u + y, hycoset⟩
  let f : H → H := fun t ↦ base + t
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    rw [Finset.mem_coe, mem_normalizedCosetFiber]
    obtain ⟨T, hTA, hTH, hTsum⟩ :=
      exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup ht
    rw [Finset.mem_subsetSum_iff]
    have hBT : Disjoint B₀ T := by
      rw [Finset.disjoint_left]
      intro x hxB hxT
      exact (Finset.mem_filter.mp hxB).2 (hTH x hxT)
    refine ⟨B₀ ∪ T, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx
      exact hx.elim
        (fun h ↦ hBA (Finset.filter_subset _ _ h))
        (fun h ↦ hTA h)
    · rw [Finset.sum_union hBT, hTsum]
      change y + t.1 = u + (base + t).1
      dsimp [base]
      abel
  · intro a _ b _ hab
    exact add_left_cancel hab

/-- Seeded form of CFP Lemma 5.11.  A fixed first summand does not change
the lower bound in any occupied subgroup fibre. -/
lemma seededSubsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (E A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H (E + A.subsetSum) u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H (E + A.subsetSum) u).card := by
  classical
  let : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hsum : u + h₀.1 ∈ E + A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_add] at hsum
  obtain ⟨e, he, x, hx, hex⟩ := hsum
  have hxcoset : -(u - e) + x ∈ H := by
    have heq : -(u - e) + x = h₀.1 := by
      calc
        -(u - e) + x = -u + (e + x) := by abel
        _ = -u + (u + h₀.1) := by rw [hex]
        _ = h₀.1 := by abel
    rw [heq]
    exact h₀.2
  let hxH : H := ⟨-(u - e) + x, hxcoset⟩
  have hxEq : (u - e) + hxH.1 = x := by
    dsimp [hxH]
    abel
  have hfiberA :
      (normalizedCosetFiber H A.subsetSum (u - e)).Nonempty := by
    refine ⟨hxH, ?_⟩
    rw [mem_normalizedCosetFiber, hxEq]
    exact hx
  have hcard := subsetSum_fiber_lower H A (u - e) hfiberA
  exact hcard.trans (Finset.card_le_card (by
    intro h hh
    rw [mem_normalizedCosetFiber] at hh ⊢
    rw [Finset.mem_add]
    refine ⟨e, he, (u - e) + h.1, hh, ?_⟩
    abel))

/-- The remaining translations, regarded inside the subgroup they generate. -/
noncomputable def liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    Finset (AddSubgroup.closure (X : Set G)) := by
  classical
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) ↦ x.1)
      Subtype.val_injective
  exact Finset.univ.filter fun x ↦ x.1 ∈ X

@[simp] lemma mem_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {X : Finset G} {x : AddSubgroup.closure (X : Set G)} :
    x ∈ liftFinsetToClosure X ↔ x.1 ∈ X := by
  let : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) ↦ x.1)
      Subtype.val_injective
  simp [liftFinsetToClosure]

lemma card_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : (liftFinsetToClosure X).card = X.card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  let : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  have himage : (liftFinsetToClosure X).image (fun x : H ↦ x.1) = X := by
    ext x
    simp only [Finset.mem_image, mem_liftFinsetToClosure]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_liftFinsetToClosure.mp hy
    · intro hx
      exact ⟨⟨x, AddSubgroup.subset_closure hx⟩,
        mem_liftFinsetToClosure.mpr hx, rfl⟩
  calc
    (liftFinsetToClosure X).card =
        ((liftFinsetToClosure X).image (fun x : H ↦ x.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = X.card := by rw [himage]

lemma closure_liftFinsetToClosure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) :
    AddSubgroup.closure ((liftFinsetToClosure X :
      Finset (AddSubgroup.closure (X : Set G))) :
        Set (AddSubgroup.closure (X : Set G))) = ⊤ := by
  let H := AddSubgroup.closure (X : Set G)
  let : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  have hset : ((liftFinsetToClosure X : Finset H) : Set H) =
      H.subtype ⁻¹' (X : Set G) := by
    ext x
    simp [H]
  rw [hset]
  exact AddSubgroup.closure_preimage_eq_top (X : Set G)

lemma card_translationNew_normalizedCosetFiber_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) (x : H) :
    (translationNew (normalizedCosetFiber H S u) x).card ≤
      (translationNew S x.1).card := by
  classical
  let f : H → G := fun h ↦ u + h.1
  apply Finset.card_le_card_of_injOn f
  · intro h hh
    rw [Finset.mem_coe, translationNew, Finset.mem_sdiff] at hh
    rw [Finset.mem_coe, translationNew, Finset.mem_sdiff]
    constructor
    · rw [Erdos587.mem_addTranslate] at hh ⊢
      simpa [f, add_assoc, add_left_comm, add_comm] using hh.1
    · simpa [f] using hh.2
  · intro a _ b _ hab
    apply Subtype.ext
    exact add_left_cancel hab

/-- Unsaturated growth in one coset implies the same quantitative growth of
the entire modular subset-sum set. -/
lemma exists_translationNew_large_of_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S X : Finset G} {u : G}
    (hU : (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).Nonempty)
    (hX : X.Nonempty)
    (hXU : X.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card)
    (hUG : 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card <
        (AddSubgroup.closure (X : Set G) : Set G).ncard) :
    ∃ x ∈ X, X.card ≤ 16 * (translationNew S x).card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  let : Fintype H :=
    Fintype.ofInjective (fun x : H ↦ x.1) Subtype.val_injective
  let XH : Finset H := liftFinsetToClosure X
  let U : Finset H := normalizedCosetFiber H S u
  have hXH : XH.Nonempty := by
    apply Finset.card_pos.mp
    rw [show XH.card = X.card by exact card_liftFinsetToClosure X]
    exact Finset.card_pos.mpr hX
  have hXcard : XH.card = X.card := card_liftFinsetToClosure X
  have hUG' : 4 * U.card < Fintype.card H := by
    have hcardH : Fintype.card H = (H : Set G).ncard := by
      exact Set.fintypeCard_eq_ncard (H : Set G)
    rw [hcardH]
    simpa [U, H] using hUG
  obtain ⟨x, hxXH, hxlarge⟩ :=
    exists_translationNew_large_of_closure_eq_top hU hXH
      (by simpa [U, hXcard] using hXU)
      hUG'
      (closure_liftFinsetToClosure_eq_top X)
  refine ⟨x.1, (mem_liftFinsetToClosure.mp hxXH), ?_⟩
  have hle := card_translationNew_normalizedCosetFiber_le H S u x
  rw [← hXcard]
  exact hxlarge.trans (Nat.mul_le_mul_left 16 hle)

/-- If the current internal subset-sum set has fewer than half as many
points as the remaining set, one remaining shift grows it by at least
the factor `3/2`. -/
lemma exists_three_halves_growth
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T X : Finset G} (hT : T.Nonempty) (_hX : X.Nonempty)
    (hsmall : 2 * T.card < X.card) :
    ∃ x ∈ X,
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  let e := T.card / 2
  let P := almostPeriods T e
  have hTpos : 0 < T.card := Finset.card_pos.mpr hT
  have hden : T.card ≤ 2 * (T.card - e) := by
    dsimp [e]
    omega
  have hAPbound := card_sub_mul_card_almostPeriods_le_sq T e
  have hPcard : P.card ≤ 2 * T.card := by
    have hmul : T.card * P.card ≤ T.card * (2 * T.card) := by
      calc
        T.card * P.card ≤ 2 * ((T.card - e) * P.card) := by nlinarith
        _ ≤ 2 * T.card ^ 2 := by
          exact Nat.mul_le_mul_left 2 (by simpa [P] using hAPbound)
        _ = T.card * (2 * T.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hTpos
  have hnot : ¬ X ⊆ P := by
    intro hXP
    have := (Finset.card_le_card hXP).trans hPcard
    omega
  obtain ⟨x, hxX, hxP⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hxX, ?_⟩
  have hnew : e < (translationNew T x).card := by
    contrapose! hxP
    exact mem_almostPeriods_iff_card_translationNew_le.mpr hxP
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  have hunion : (T ∪ Erdos587.addTranslate x T).card =
      T.card + (translationNew T x).card := by
    dsimp [translationNew] at hsdiff ⊢
    rw [Finset.union_comm] at hsdiff
    omega
  rw [hunion]
  dsimp [e] at hnew
  omega

/-- A growth phase is witnessed by a coset fibre no larger than one quarter
of the remaining residue set. -/
def IsModularGrowthPhase {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) : Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card ≤ R.card

/-- An unsaturated fibre has less than one quarter of its subgroup. -/
def HasUnsaturatedFiber {b : ℕ} [NeZero b] (R₀ R E : Finset (ZMod b)) :
    Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card <
        (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard

lemma exists_internal_growth_of_modularGrowthPhase
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hgrowth : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    ∃ x : H, x.1 ∈ R ∧
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X := liftFinsetToClosure R
  obtain ⟨u, huSmall⟩ := hgrowth
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hTle : T.card ≤ (normalizedCosetFiber H
      (E + (R₀ \ R).subsetSum) u).card := by
    exact seededSubsetSum_fiber_lower H E (R₀ \ R) u huNe
  have hTne : T.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp only [T]
    rw [Finset.mem_subsetSum_iff]
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  have hXne : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hRne
  have hsmall : 2 * T.card < X.card := by
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    have : 4 * T.card ≤ R.card :=
      (Nat.mul_le_mul_left 4 hTle).trans huSmall
    omega
  obtain ⟨x, hx, hxGrowth⟩ := exists_three_halves_growth hTne hXne hsmall
  exact ⟨x, mem_liftFinsetToClosure.mp hx, hxGrowth⟩

lemma exists_large_step_of_unsaturatedFiber
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hnotGrowth : ¬IsModularGrowthPhase hb R₀ R E)
    (hunsat : HasUnsaturatedFiber R₀ R E) :
    ∃ x ∈ R, R.card ≤ 16 *
      (Erdos360.translationNew (E + (R₀ \ R).subsetSum) x).card := by
  classical
  obtain ⟨u, huSmall⟩ := hunsat
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hlarge : R.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).card := by
    by_contra hnot
    apply hnotGrowth
    exact ⟨u, by omega⟩
  exact exists_translationNew_large_of_normalizedCosetFiber
    huNe hRne hlarge huSmall

lemma saturated_modularPhase_card
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hsaturated : ¬HasUnsaturatedFiber R₀ R E) :
    b ≤ 4 * (E + (R₀ \ R).subsetSum).card := by
  have hlarge : ∀ u : ZMod b,
      (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard ≤
        4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
          (E + (R₀ \ R).subsetSum) u).card := by
    intro u
    have huNe := normalizedCosetFiber_nonempty_of_diverse_used
      hb R₀ R E hE hdiverse u
    by_contra hnot
    apply hsaturated
    exact ⟨u, by omega⟩
  simpa [ZMod.card] using
    (card_le_four_mul_card_of_all_coset_fibers_large
      (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) hlarge)

/-! ### The deterministic modular phase recursion -/

/-- Diversity only where it can be used by a phase whose remainder still
contains at least half of the original residues. -/
def PhaseDiverse {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ : Finset (ZMod b)) : Prop :=
  ∀ R : Finset (ZMod b), R ⊆ R₀ → R₀.card ≤ 2 * R.card →
    ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card

lemma phaseDiverse_of_bounded
    {b : ℕ} [NeZero b] (hb : 0 < b) (R₀ : Finset (ZMod b))
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d * R₀.card ≤ 2 * b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    PhaseDiverse hb R₀ := by
  intro R _hR hwide d hd hdq
  apply hdiverse d hd (hdq.trans (closureModulus_dvd hb R))
  have hdle : d ≤ closureModulus hb R :=
    Nat.le_of_dvd (closureModulus_pos hb R) hdq
  have hclosure := closureModulus_mul_card_le hb R
  nlinarith

/-- A canonical choice for the next phase.  In a growth phase it uses the
internal multiplicative-growth witness; in an unsaturated phase it uses the
large-translation witness; otherwise it removes an arbitrary remaining
element. -/
noncomputable def modularPhasePick
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · by_cases hsub : R ⊆ R₀
    · by_cases hwide : R₀.card ≤ 2 * R.card
      · by_cases hg : IsModularGrowthPhase hb R₀ R E
        · exact (Classical.choose
            (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
              (hdiverse R hsub hwide) hg)).1
        · by_cases hu : HasUnsaturatedFiber R₀ R E
          · exact Classical.choose
              (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
                (hdiverse R hsub hwide) hg hu)
          · exact hR.choose
      · exact hR.choose
    · exact hR.choose
  · exact 0

lemma modularPhasePick_mem
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty) :
    modularPhasePick hb R₀ E hE hdiverse R ∈ R := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR]
  by_cases hsub : R ⊆ R₀
  · rw [dif_pos hsub]
    by_cases hwide : R₀.card ≤ 2 * R.card
    · rw [dif_pos hwide]
      by_cases hg : IsModularGrowthPhase hb R₀ R E
      · rw [dif_pos hg]
        exact (Classical.choose_spec
            (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
              (hdiverse R hsub hwide) hg)).1
      · rw [dif_neg hg]
        by_cases hu : HasUnsaturatedFiber R₀ R E
        · rw [dif_pos hu]
          exact (Classical.choose_spec
            (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
              (hdiverse R hsub hwide) hg hu)).1
        · rw [dif_neg hu]
          exact hR.choose_spec
    · rw [dif_neg hwide]
      exact hR.choose_spec
  · rw [dif_neg hsub]
    exact hR.choose_spec

lemma modularPhasePick_internal_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hsub : R ⊆ R₀)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    3 * T.card ≤ 2 *
      (T ∪ Erdos587.addTranslate
        (⟨modularPhasePick hb R₀ E hE hdiverse R,
          AddSubgroup.subset_closure
            (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ : H) T).card := by
  classical
  dsimp only
  let hex := exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
    (hdiverse R hsub hwide) hg
  let x := Classical.choose hex
  have hxSpec := (Classical.choose_spec hex).2
  have hpick : modularPhasePick hb R₀ E hE hdiverse R = x.1 := by
    simp only [modularPhasePick, dif_pos hR, dif_pos hsub, dif_pos hwide,
      dif_pos hg, hex, x]
  have hsubtype :
      (⟨modularPhasePick hb R₀ E hE hdiverse R,
        AddSubgroup.subset_closure
          (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ :
          AddSubgroup.closure (R : Set (ZMod b))) = x := by
    exact Subtype.ext hpick
  rw [hsubtype]
  exact hxSpec

lemma modularPhasePick_unsaturated_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hsub : R ⊆ R₀)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : ¬IsModularGrowthPhase hb R₀ R E)
    (hu : HasUnsaturatedFiber R₀ R E) :
    R.card ≤ 16 * (Erdos360.translationNew
      (E + (R₀ \ R).subsetSum)
      (modularPhasePick hb R₀ E hE hdiverse R)).card := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR, dif_pos hsub, dif_pos hwide, dif_neg hg, dif_pos hu]
  exact (Classical.choose_spec
    (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
      (hdiverse R hsub hwide) hg hu)).2

noncomputable def modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ℕ → Finset (ZMod b)
  | 0 => R₀
  | i + 1 =>
      let R := modularRemainder hb R₀ E hE hdiverse i
      if R.Nonempty then
        R.erase (modularPhasePick hb R₀ E hE hdiverse R)
      else R

noncomputable def modularPhaseSums
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Finset (ZMod b) :=
  E + (R₀ \ modularRemainder hb R₀ E hE hdiverse i).subsetSum

@[simp] lemma modularRemainder_zero
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    modularRemainder hb R₀ E hE hdiverse 0 = R₀ := rfl

lemma modularRemainder_succ_of_nonempty
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) (hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) =
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i)) := by
  change (if (modularRemainder hb R₀ E hE hdiverse i).Nonempty then
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i))
    else modularRemainder hb R₀ E hE hdiverse i) = _
  rw [if_pos hne]

lemma modularRemainder_succ_subset
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  change (if R.Nonempty then
      R.erase (modularPhasePick hb R₀ E hE hdiverse R) else R) ⊆ R
  split_ifs
  · exact Finset.erase_subset _ _
  · exact fun _ hx => hx

lemma modularRemainder_subset_initial
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ∀ i : ℕ, modularRemainder hb R₀ E hE hdiverse i ⊆ R₀ := by
  intro i
  induction i with
  | zero => exact fun _ hx => hx
  | succ i ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse i).trans ih

lemma card_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (modularRemainder hb R₀ E hE hdiverse i).card = R₀.card - i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ R₀.card := by omega
      have hcard := ih hi'
      have hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcard]
        omega
      rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hne]
      rw [Finset.card_erase_of_mem
        (modularPhasePick_mem hb R₀ E hE hdiverse _ hne)]
      omega

lemma card_used_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (R₀ \ modularRemainder hb R₀ E hE hdiverse i).card = i := by
  rw [Finset.card_sdiff_of_subset
    (modularRemainder_subset_initial hb R₀ E hE hdiverse i)]
  rw [card_modularRemainder hb R₀ E hE hdiverse hi]
  omega

lemma modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse (i + 1) =
      modularPhaseSums hb R₀ E hE hdiverse i ∪
        Erdos587.addTranslate
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))
          (modularPhaseSums hb R₀ E hE hdiverse i) := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  have hcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hRsub : R ⊆ R₀ :=
    modularRemainder_subset_initial hb R₀ E hE hdiverse i
  have hxR := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxNot : modularPhasePick hb R₀ E hE hdiverse R ∉ R₀ \ R := by
    simp only [Finset.mem_sdiff]
    exact fun h => h.2 hxR
  rw [modularPhaseSums, modularPhaseSums]
  rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne]
  rw [sdiff_erase_eq_insert_sdiff hxR hRsub]
  exact seededSubsetSum_insert_eq E (R₀ \ R)
    (modularPhasePick hb R₀ E hE hdiverse R) hxNot

/-- The numerical size of the subset sums made from already-used elements
which lie in the subgroup generated by the current remainder. -/
noncomputable def modularInternalCard
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) : ℕ :=
  let H := AddSubgroup.closure (R : Set (ZMod b))
  (elementsInSubgroup H (R₀ \ R)).subsetSum.card

lemma elementsInSubgroup_mono
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) {A B : Finset G} (hAB : A ⊆ B) :
    elementsInSubgroup H A ⊆ elementsInSubgroup H B := by
  intro x hx
  rw [mem_elementsInSubgroup] at hx ⊢
  exact hAB hx

lemma modularInternalCard_mono_of_subset_of_closure_eq
    {b : ℕ} [NeZero b] (R₀ : Finset (ZMod b))
    {R T : Finset (ZMod b)} (hTR : T ⊆ R)
    (hclosure : AddSubgroup.closure (T : Set (ZMod b)) =
      AddSubgroup.closure (R : Set (ZMod b))) :
    modularInternalCard R₀ R ≤ modularInternalCard R₀ T := by
  classical
  let HR := AddSubgroup.closure (R : Set (ZMod b))
  let HT := AddSubgroup.closure (T : Set (ZMod b))
  have hused : R₀ \ R ⊆ R₀ \ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxT => hx.2 (hTR hxT)⟩
  have hsub : elementsInSubgroup HR (R₀ \ R) ⊆
      elementsInSubgroup HR (R₀ \ T) :=
    elementsInSubgroup_mono HR hused
  have hsums := Finset.subsetSum_mono hsub
  have hcard := Finset.card_le_card hsums
  dsimp only [modularInternalCard]
  rw [hclosure]
  exact hcard

lemma closure_eq_of_closureModulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b) {R T : Finset (ZMod b)}
    (hmod : closureModulus hb R = closureModulus hb T) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.closure (T : Set (ZMod b)) := by
  rw [closure_eq_zmultiples_modulus hb R,
    closure_eq_zmultiples_modulus hb T, hmod]

lemma modularRemainder_antitone
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularRemainder hb R₀ E hE hdiverse j ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse (i + k)).trans
        (ih (by omega))

lemma modularInternalCard_mono_of_modulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse j) := by
  apply modularInternalCard_mono_of_subset_of_closure_eq R₀
    (modularRemainder_antitone hb R₀ E hE hdiverse hij)
  exact (closure_eq_of_closureModulus_eq hb hmod).symm

lemma elementsInSubgroup_insert
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (x : H) (hx : x.1 ∉ A) :
    elementsInSubgroup H (insert x.1 A) =
      insert x (elementsInSubgroup H A) := by
  ext y
  simp only [mem_elementsInSubgroup, Finset.mem_insert, Subtype.coe_inj]

lemma modularInternalCard_growth_step
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card)
    (hwide : R₀.card ≤ 2 *
      (modularRemainder hb R₀ E hE hdiverse i).card)
    (hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse (i + 1))) :
    3 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      2 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
  classical
  let R := modularRemainder hb R₀ E hE hdiverse i
  let T := modularRemainder hb R₀ E hE hdiverse (i + 1)
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := R₀ \ R
  let x := modularPhasePick hb R₀ E hE hdiverse R
  have hRcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hxR : x ∈ R := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxU : x ∉ U := by
    simp only [U, Finset.mem_sdiff]
    exact fun h => h.2 hxR
  have hT : T = R.erase x := by
    exact modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne
  have hRsub : R ⊆ R₀ :=
    modularRemainder_subset_initial hb R₀ E hE hdiverse i
  have hused : R₀ \ T = insert x U := by
    rw [hT]
    exact sdiff_erase_eq_insert_sdiff hxR
      (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hgrowth := modularPhasePick_internal_growth
    hb R₀ E hE hdiverse R hRne hRsub hwide hg
  have hclosure : AddSubgroup.closure (T : Set (ZMod b)) = H := by
    exact (closure_eq_of_closureModulus_eq hb hmod).symm
  have hnext : elementsInSubgroup H (R₀ \ T) =
      insert xH (elementsInSubgroup H U) := by
    rw [hused]
    exact elementsInSubgroup_insert H U xH hxU
  have hsumNext : (elementsInSubgroup H (R₀ \ T)).subsetSum =
      (elementsInSubgroup H U).subsetSum ∪
        Erdos587.addTranslate xH (elementsInSubgroup H U).subsetSum := by
    rw [hnext]
    exact subsetSum_insert_eq _ _ (by
      rw [mem_elementsInSubgroup]
      exact hxU)
  dsimp only [modularInternalCard]
  rw [show AddSubgroup.closure (T : Set (ZMod b)) = H by exact hclosure]
  rw [hsumNext]
  exact hgrowth

lemma log_two_lt_of_double_le {a c : ℕ} (ha : 0 < a)
    (hac : 2 * a ≤ c) : Nat.log 2 a < Nat.log 2 c := by
  have hstep : Nat.log 2 a < Nat.log 2 (a * 2) := by
    rw [Nat.log_mul_base (by omega) ha.ne']
    omega
  exact hstep.trans_le (Nat.log_mono_right (by simpa [mul_comm] using hac))

lemma eq_of_dvd_of_log_two_eq {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ∣ c) (hlog : Nat.log 2 a = Nat.log 2 c) : a = c := by
  obtain ⟨r, rfl⟩ := hac
  have hr : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    simp at hc
  by_contra hne
  have hrne : r ≠ 1 := by
    intro hrone
    subst r
    simp at hne
  have hr2 : 2 ≤ r := by
    omega
  have hdouble : 2 * a ≤ a * r := by
    nlinarith
  exact (Nat.ne_of_lt (log_two_lt_of_double_le ha hdouble)) hlog

lemma modularInternalCard_pos
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    0 < modularInternalCard R₀ R := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨0, Finset.zero_mem_subsetSum⟩

lemma modularInternalCard_le
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    modularInternalCard R₀ R ≤ b := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  calc
    modularInternalCard R₀ R =
        (elementsInSubgroup H (R₀ \ R)).subsetSum.card := rfl
    _ ≤ Fintype.card H := Finset.card_le_univ _
    _ ≤ Fintype.card (ZMod b) :=
      Fintype.card_le_of_injective (fun h : H => h.1) Subtype.val_injective
    _ = b := ZMod.card b

lemma closureModulus_eq_between
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i t j : ℕ} (hit : i ≤ t) (htj : t ≤ j)
    (hij : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse t) := by
  apply Nat.dvd_antisymm
  · exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hit)
  · rw [hij]
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse htj)

/-- The phase indices at which the selector invokes the internal
multiplicative-growth alternative. -/
noncomputable def modularGrowthIndices
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i =>
    IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E

/-- Binary logarithms of the current subgroup modulus and its internal
subset-sum cardinality.  Both coordinates lie between zero and `log₂ b`. -/
noncomputable def modularGrowthCode
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1) :=
  (⟨Nat.log 2 (closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse i)), by
      have hle : closureModulus hb
          (modularRemainder hb R₀ E hE hdiverse i) ≤ b :=
        Nat.le_of_dvd hb (closureModulus_dvd hb _)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hle)⟩,
   ⟨Nat.log 2 (modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse i)), by
      exact Nat.lt_succ_of_le (Nat.log_mono_right
        (modularInternalCard_le R₀ _))⟩)

lemma exists_three_ordered_of_two_lt_card {S : Finset ℕ}
    (hS : 2 < S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i < j ∧ j < k := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hS
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨a, ha, b, hb, c, hc, hab', hbc'⟩
      · exact ⟨a, ha, c, hc, b, hb, hac', hcb'⟩
    · exact ⟨c, hc, a, ha, b, hb, hca', hab'⟩
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · exact ⟨b, hb, a, ha, c, hc, hba', hac'⟩
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨b, hb, c, hc, a, ha, hbc', hca'⟩
      · exact ⟨c, hc, b, hb, a, ha, hcb', hba'⟩

lemma modularGrowthCode_not_three
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : 2 * (k + 1) ≤ R₀.card)
    (hgi : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hgj : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse j) E)
    (hcodeIJ : modularGrowthCode hb R₀ E hE hdiverse i =
      modularGrowthCode hb R₀ E hE hdiverse j)
    (hcodeJK : modularGrowthCode hb R₀ E hE hdiverse j =
      modularGrowthCode hb R₀ E hE hdiverse k) : False := by
  let Ri := modularRemainder hb R₀ E hE hdiverse i
  let Rj := modularRemainder hb R₀ E hE hdiverse j
  let Rk := modularRemainder hb R₀ E hE hdiverse k
  let qi := closureModulus hb Ri
  let qj := closureModulus hb Rj
  let qk := closureModulus hb Rk
  let ci := modularInternalCard R₀ Ri
  let cj := modularInternalCard R₀ Rj
  let ck := modularInternalCard R₀ Rk
  have hqLogIJ : Nat.log 2 qi = Nat.log 2 qj :=
    congrArg (fun z => z.1.val) hcodeIJ
  have hqLogJK : Nat.log 2 qj = Nat.log 2 qk :=
    congrArg (fun z => z.1.val) hcodeJK
  have hcLogIJ : Nat.log 2 ci = Nat.log 2 cj :=
    congrArg (fun z => z.2.val) hcodeIJ
  have hcLogJK : Nat.log 2 cj = Nat.log 2 ck :=
    congrArg (fun z => z.2.val) hcodeJK
  have hqDivIJ : qi ∣ qj := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hij.le)
  have hqDivJK : qj ∣ qk := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hjk.le)
  have hqEqIJ : qi = qj :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Ri)
      (closureModulus_pos hb Rj) hqDivIJ hqLogIJ
  have hqEqJK : qj = qk :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Rj)
      (closureModulus_pos hb Rk) hqDivJK hqLogJK
  have hqiSucc : closureModulus hb Ri = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqIJ
  have hqjSucc : closureModulus hb Rj = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqJK
  have hgrowI : 3 * ci ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgi hqiSucc
  have hmonoIJ : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) ≤ cj := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqiSucc.symm.trans hqEqIJ
  have hgrowJ : 3 * cj ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgj hqjSucc
  have hmonoJK : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) ≤ ck := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqjSucc.symm.trans hqEqJK
  have hthreeI : 3 * ci ≤ 2 * cj := hgrowI.trans (Nat.mul_le_mul_left 2 hmonoIJ)
  have hthreeJ : 3 * cj ≤ 2 * ck := hgrowJ.trans (Nat.mul_le_mul_left 2 hmonoJK)
  have hdouble : 2 * ci ≤ ck := by
    have hcipos : 0 < ci := modularInternalCard_pos R₀ Ri
    omega
  have hloglt : Nat.log 2 ci < Nat.log 2 ck :=
    log_two_lt_of_double_le (modularInternalCard_pos R₀ Ri) hdouble
  exact (Nat.ne_of_lt hloglt) (hcLogIJ.trans hcLogJK)

theorem card_modularGrowthIndices_le
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    (modularGrowthIndices hb R₀ E hE hdiverse k).card ≤
      2 * (Nat.log 2 b + 1) ^ 2 := by
  classical
  let G := modularGrowthIndices hb R₀ E hE hdiverse k
  let C := Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1)
  let f : ℕ → C := modularGrowthCode hb R₀ E hE hdiverse
  by_contra hnot
  have hlarge : (Finset.univ : Finset C).card * 2 < G.card := by
    simp only [Finset.card_univ, C, Fintype.card_prod, Fintype.card_fin]
    dsimp only [G] at hnot ⊢
    have hgt : 2 * (Nat.log 2 b + 1) ^ 2 <
        (modularGrowthIndices hb R₀ E hE hdiverse k).card :=
      Nat.lt_of_not_ge hnot
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hgt
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := Finset.univ) (f := f)
      (n := 2) (fun _ _ => Finset.mem_univ _) hlarge
  let S := G.filter fun i => f i = y
  have hScard : 2 < S.card := by
    simpa only [S] using hy
  obtain ⟨i, hiS, j, hjS, q, hqS, hij, hjq⟩ :=
    exists_three_ordered_of_two_lt_card hScard
  have hiG : i ∈ G := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ G := (Finset.mem_filter.mp hjS).1
  have hqG : q ∈ G := (Finset.mem_filter.mp hqS).1
  have hfi : f i = y := (Finset.mem_filter.mp hiS).2
  have hfj : f j = y := (Finset.mem_filter.mp hjS).2
  have hfq : f q = y := (Finset.mem_filter.mp hqS).2
  have hiData := Finset.mem_filter.mp hiG
  have hjData := Finset.mem_filter.mp hjG
  have hqData := Finset.mem_filter.mp hqG
  exact modularGrowthCode_not_three hb R₀ E hE hdiverse hij hjq
    (by
      have hqk : q < k := Finset.mem_range.mp hqData.1
      omega)
    hiData.2 hjData.2 (hfi.trans hfj.symm) (hfj.trans hfq.symm)

lemma card_union_addTranslate_eq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x : G) :
    (S ∪ Erdos587.addTranslate x S).card =
      S.card + (Erdos360.translationNew S x).card := by
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x S) S
  dsimp only [Erdos360.translationNew] at hsdiff ⊢
  rw [Finset.union_comm] at hsdiff
  omega

lemma card_modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card =
      (modularPhaseSums hb R₀ E hE hdiverse i).card +
        (Erdos360.translationNew
          (modularPhaseSums hb R₀ E hE hdiverse i)
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))).card := by
  rw [modularPhaseSums_succ hb R₀ E hE hdiverse hi]
  exact card_union_addTranslate_eq _ _

lemma card_modularGrowthIndices_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse (i + 1)).card =
      if IsModularGrowthPhase hb R₀
          (modularRemainder hb R₀ E hE hdiverse i) E then
        (modularGrowthIndices hb R₀ E hE hdiverse i).card + 1
      else (modularGrowthIndices hb R₀ E hE hdiverse i).card := by
  classical
  by_cases hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E <;>
    simp [modularGrowthIndices, Finset.range_add_one, Finset.filter_insert, hg]

lemma card_modularGrowthIndices_le_index
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse i).card ≤ i := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range i)

lemma mul_pred_potential_le (u r : ℕ) (hr : 0 < r) :
    (u + 1) * (r - 1) ≤ u * r + r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [Nat.succ_sub_one]
  nlinarith

/-- If no saturated phase occurs, every nongrowth phase contributes a
linear number of genuinely new residues.  This potential packages all those
increments while allowing the remainder to shrink. -/
theorem unsaturated_modularPhase_potential
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card)
    (hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E) :
    (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
        (R₀.card - k) ≤
      16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < R₀.card := by omega
      have hkprev : k ≤ R₀.card := hklt.le
      have hhalfPrev : 2 * k ≤ R₀.card := by omega
      have huPrev : ∀ i < k, HasUnsaturatedFiber R₀
          (modularRemainder hb R₀ E hE hdiverse i) E := by
        intro i hi
        exact hu i (by omega)
      have hIH := ih hhalfPrev huPrev
      let R := modularRemainder hb R₀ E hE hdiverse k
      let S := modularPhaseSums hb R₀ E hE hdiverse k
      let x := modularPhasePick hb R₀ E hE hdiverse R
      let D := Erdos360.translationNew S x
      have hRcard : R.card = R₀.card - k :=
        card_modularRemainder hb R₀ E hE hdiverse hkprev
      have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
      have hwide : R₀.card ≤ 2 * R.card := by rw [hRcard]; omega
      have huK : HasUnsaturatedFiber R₀ R E := hu k (by omega)
      have hScard :
          (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card =
            S.card + D.card := by
        exact card_modularPhaseSums_succ hb R₀ E hE hdiverse hklt
      by_cases hg : IsModularGrowthPhase hb R₀ R E
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_pos hg] at hGcard
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hrem : R₀.card - (k + 1) ≤ R₀.card - k := by omega
        have hleft :
            (k + 1 - ((modularGrowthIndices hb R₀ E hE hdiverse k).card + 1)) *
                (R₀.card - (k + 1)) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) := by
          apply Nat.mul_le_mul
          · omega
          · exact hrem
        exact hleft.trans (hIH.trans (Nat.mul_le_mul_left 16
          (Nat.le_add_right S.card D.card)))
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_neg hg] at hGcard
        have hnew : R.card ≤ 16 * D.card := by
          exact modularPhasePick_unsaturated_growth
            hb R₀ E hE hdiverse R hRne
              (modularRemainder_subset_initial hb R₀ E hE hdiverse k)
              hwide hg huK
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hremSucc : R₀.card - (k + 1) = (R₀.card - k) - 1 := by
          omega
        have hphaseSucc :
            k + 1 - (modularGrowthIndices hb R₀ E hE hdiverse k).card =
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1 := by
          omega
        rw [hremSucc, hphaseSucc]
        calc
          ((k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1) *
                ((R₀.card - k) - 1) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) + R.card := by
            rw [hRcard]
            exact mul_pred_potential_le _ _ (by omega)
          _ ≤ 16 * S.card + 16 * D.card := Nat.add_le_add hIH hnew
          _ = 16 * (S.card + D.card) := by ring

lemma modularPhaseSums_mono
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆
      modularPhaseSums hb R₀ E hE hdiverse j := by
  rw [modularPhaseSums, modularPhaseSums]
  apply Finset.add_subset_add_left
  apply Finset.subsetSum_mono
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro hxj
  exact hx.2 (modularRemainder_antitone hb R₀ E hE hdiverse hij hxj)

/-- Exact output of the deterministic modular phase machine: either one
phase has already filled a quarter of the cyclic group, or the accumulated
unsaturated phases satisfy the quantitative potential bound. -/
theorem modularPhase_dichotomy
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
          (R₀.card - k) ≤
        16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  classical
  by_cases hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E
  · exact Or.inr (unsaturated_modularPhase_potential
      hb R₀ E hE hdiverse hhalf hu)
  · push Not at hu
    obtain ⟨i, hi, hsat⟩ := hu
    left
    have hiCard : i ≤ R₀.card := by omega
    have hwide : R₀.card ≤ 2 *
        (modularRemainder hb R₀ E hE hdiverse i).card := by
      rw [card_modularRemainder hb R₀ E hE hdiverse hiCard]
      omega
    have hquarter := saturated_modularPhase_card hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E hE
      (hdiverse _
        (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
        hwide) hsat
    exact hquarter.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card
      (modularPhaseSums_mono hb R₀ E hE hdiverse hi.le)))

/-- Bounded modular subset-sum growth with explicit, deliberately coarse
constants.  Once the number of exposed phases dominates the logarithmic
growth count and no more than half the residues have been used, either a
quarter of the group is filled or the sumset has quadratic-size growth. -/
theorem bounded_modular_subsetSum_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hlog : 4 * (Nat.log 2 b + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      k * R₀.card ≤
        64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  have hk : k ≤ R₀.card := by omega
  rcases modularPhase_dichotomy hb R₀ E hE hdiverse hhalf with hfill | hpot
  · exact Or.inl hfill
  · right
    let g := (modularGrowthIndices hb R₀ E hE hdiverse k).card
    have hg := card_modularGrowthIndices_le hb R₀ E hE hdiverse hhalf
    have hgk : 2 * g ≤ k := by
      dsimp only [g]
      nlinarith
    have hg_le : g ≤ k := by omega
    have hkleft : k ≤ 2 * (k - g) := by omega
    have hmright : R₀.card ≤ 2 * (R₀.card - k) := by omega
    have hprod : k * R₀.card ≤
        4 * ((k - g) * (R₀.card - k)) := by
      calc
        k * R₀.card ≤ (2 * (k - g)) * (2 * (R₀.card - k)) :=
          Nat.mul_le_mul hkleft hmright
        _ = 4 * ((k - g) * (R₀.card - k)) := by ring
    calc
      k * R₀.card ≤ 4 * ((k - g) * (R₀.card - k)) := hprod
      _ ≤ 4 * (16 * (modularPhaseSums hb R₀ E hE hdiverse k).card) :=
        Nat.mul_le_mul_left 4 hpot
      _ = 64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by ring
/-! ### Common-divisor extraction -/

noncomputable def divideMultiples (Y : Finset ℕ) (e : ℕ) : Finset ℕ :=
  (Y.filter fun y => e ∣ y).image fun y => y / e

lemma mem_divideMultiples_iff {Y : Finset ℕ} {e y : ℕ} (he : 0 < e) :
    y ∈ divideMultiples Y e ↔ e * y ∈ Y := by
  classical
  rw [divideMultiples, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    simpa [Nat.mul_div_cancel' hx.2] using hx.1
  · intro hy
    refine ⟨e * y, Finset.mem_filter.mpr ⟨hy, dvd_mul_right e y⟩, ?_⟩
    exact Nat.mul_div_right y he

lemma card_divideMultiples {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    (divideMultiples Y e).card = (Y.filter fun y => e ∣ y).card := by
  classical
  rw [divideMultiples, Finset.card_image_iff]
  intro x hx y hy hxy
  have hx' : x ∈ Y ∧ e ∣ x := Finset.mem_filter.mp hx
  have hy' : y ∈ Y ∧ e ∣ y := Finset.mem_filter.mp hy
  have hxmul : e * (x / e) = x := by
    simpa [mul_comm] using Nat.mul_div_cancel' hx'.2
  have hymul : e * (y / e) = y := by
    simpa [mul_comm] using Nat.mul_div_cancel' hy'.2
  change x / e = y / e at hxy
  rw [← hxmul, ← hymul]
  exact congrArg (fun z => e * z) hxy

lemma card_sub_card_divideMultiples {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    Y.card - (divideMultiples Y e).card =
      (Y.filter fun y => ¬e ∣ y).card := by
  rw [card_divideMultiples he]
  have hpartition : (Y.filter fun y => e ∣ y) ∪
      (Y.filter fun y => ¬e ∣ y) = Y := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (Y.filter fun y => e ∣ y)
      (Y.filter fun y => ¬e ∣ y) := by
    rw [Finset.disjoint_left]
    intro y hy hny
    simp only [Finset.mem_filter] at hy hny
    exact hny.2 hy.2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hpartition] at hcard
  omega

lemma divideMultiples_subset_Icc {Y : Finset ℕ} {e n : ℕ} (he : 0 < e)
    (hY : Y ⊆ Finset.Icc 1 n) :
    divideMultiples Y e ⊆ Finset.Icc 1 (n / e) := by
  intro y hy
  rw [mem_divideMultiples_iff he] at hy
  have hmem := Finset.mem_Icc.mp (hY hy)
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    have : y = 0 := Nat.eq_zero_of_not_pos h
    subst y
    simp at hmem
  · exact (Nat.le_div_iff_mul_le he).2 (by simpa [mul_comm] using hmem.2)

lemma divideMultiples_scaled_subset {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    ∀ y ∈ divideMultiples Y e, e * y ∈ Y := by
  intro y hy
  exact (mem_divideMultiples_iff he).mp hy

/-- Finite descent which repeatedly discards the exceptional nonmultiples
and divides by their common divisor.  The returned list records every
division, making the total loss auditable. -/
theorem exists_divisorExtractionAux
    (B L K d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧
      (∀ z ∈ Z, q * z ∈ Y) ∧
      Y.card - Z.card ≤ L * factors.length + K * factors.sum ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ (Z.filter fun z => ¬e ∣ z).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (Y.filter fun y => ¬e ∣ y).card < L + K * e
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := divideMultiples Y e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, factors, hq, hqprod, hfactors, hdqB,
            hscale, hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' rfl
        refine ⟨e * q, Z, e :: factors, Nat.mul_pos hepos hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun h => h ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · intro z hz
          have hzY' : q * z ∈ Y' := hscale z hz
          have := divideMultiples_scaled_subset hepos (q * z) hzY'
          simpa [mul_assoc] using this
        · have hY'le : Y'.card ≤ Y.card := by
            dsimp only [Y']
            rw [card_divideMultiples hepos]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have hZle : Z.card ≤ Y'.card := by
            apply Finset.card_le_card_of_injOn (fun z => q * z)
            · intro z hz
              exact hscale z hz
            · intro x hx y hy hxy
              exact Nat.eq_of_mul_eq_mul_left hq hxy
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          rw [hsplit]
          have hfirst : Y.card - Y'.card ≤ L + K * e := by
            dsimp only [Y']
            rw [card_sub_card_divideMultiples hepos]
            exact hsmall.le
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e) +
                  (L * factors.length + K * factors.sum) :=
              Nat.add_le_add hfirst hloss
            _ = L * (e :: factors).length + K * (e :: factors).sum := by
              simp only [List.length_cons, List.sum_cons]
              ring
        · intro a ha hbound
          convert hdiverse a ha (by simpa [mul_assoc] using hbound) using 1 <;>
            simp [mul_assoc]
      · refine ⟨1, Y, [], by omega, by simp, by simp, ?_, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using (Nat.lt_of_not_ge hnot)

lemma prod_pos_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → 0 < factors.prod
  | [], _ => by simp
  | e :: factors, h => by
      simp only [List.prod_cons]
      exact Nat.mul_pos (by have := h e (by simp); omega)
        (prod_pos_of_one_lt factors (by
          intro a ha
          exact h a (by simp [ha])))

lemma sum_le_prod_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → factors.sum ≤ factors.prod
  | [], _ => by simp
  | [e], h => by simp
  | e :: f :: factors, h => by
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ f :: factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      have hfprod : 2 ≤ (f :: factors).prod := by
        have hf : 2 ≤ f := htail f (by simp)
        simp only [List.prod_cons]
        exact hf.trans (Nat.le_mul_of_pos_right f
          (prod_pos_of_one_lt factors (by
            intro a ha
            exact htail a (by simp [ha]))))
      have ih := sum_le_prod_of_one_lt (f :: factors) htail
      simp only [List.sum_cons, List.prod_cons]
      calc
        e + (f :: factors).sum ≤ e + (f :: factors).prod :=
          Nat.add_le_add_left ih e
        _ ≤ e * (f :: factors).prod := by nlinarith

lemma length_le_log_prod_of_one_lt (factors : List ℕ)
    (h : ∀ e ∈ factors, 1 < e) :
    factors.length ≤ Nat.log 2 factors.prod := by
  apply Nat.le_log_of_pow_le (by omega)
  induction factors with
  | nil => simp
  | cons e factors ih =>
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      simp only [List.length_cons, List.prod_cons, pow_succ]
      simpa [mul_comm] using Nat.mul_le_mul (ih htail) he

/-- Usable corollary of the descent: the output is diverse up to the global
divisor budget and loses only a logarithmic term plus a term linear in that
budget. -/
theorem exists_divisorExtraction
    (B L K : ℕ) (hB : 0 < B) (Y : Finset ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun z => ¬e ∣ z).card := by
  obtain ⟨d, Z, factors, hd, hdprod, hfactors, hdB,
      hscale, hloss, hdiverse⟩ :=
    exists_divisorExtractionAux B L K 1 (by omega) hB Y
  refine ⟨d, Z, hd, by simpa using hdB, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤ L * factors.length + K * factors.sum := hloss
      _ ≤ L * Nat.log 2 B + K * B := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left
          exact (length_le_log_prod_of_one_lt factors hfactors).trans
            (Nat.log_mono_right (by simpa [hdprod] using hdB))
        · apply Nat.mul_le_mul_left
          exact (sum_le_prod_of_one_lt factors hfactors).trans
            (by simpa [hdprod] using hdB)
  · intro e he hde
    exact hdiverse e he (by simpa using hde)

/-! The finite completion needs a lower pool whose elements are all smaller
than a reserved pivot pool.  The reserve required after division by `d` is
only `P / d`; charging that geometrically decreasing quantity during the
divisor descent avoids an erroneous extra logarithmic factor. -/

noncomputable def lowerPart (Y : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (Y.card - r)).attach.image fun i ↦
    Y.orderEmbOfFin rfl ⟨i.1, by
      have hi := Finset.mem_range.mp i.2
      omega⟩

lemma card_lowerPart (Y : Finset ℕ) (r : ℕ) :
    (lowerPart Y r).card = Y.card - r := by
  classical
  rw [lowerPart, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Subtype.ext
    have hij' :
        (⟨i.1, by
          have hi := Finset.mem_range.mp i.2
          omega⟩ : Fin Y.card) =
        ⟨j.1, by
          have hj := Finset.mem_range.mp j.2
          omega⟩ :=
      (Y.orderEmbOfFin rfl).injective hij
    exact congrArg Fin.val hij'

lemma lowerPart_subset (Y : Finset ℕ) (r : ℕ) : lowerPart Y r ⊆ Y := by
  classical
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  exact Y.orderEmbOfFin_mem rfl _

lemma card_sdiff_lowerPart (Y : Finset ℕ) (r : ℕ) :
    (Y \ lowerPart Y r).card = min r Y.card := by
  rw [Finset.card_sdiff_of_subset (lowerPart_subset Y r), card_lowerPart]
  omega

lemma card_sdiff_lowerPart_le (Y : Finset ℕ) (r : ℕ) :
    (Y \ lowerPart Y r).card ≤ r := by
  rw [card_sdiff_lowerPart]
  exact min_le_left _ _

lemma lowerPart_lt_sdiff {Y : Finset ℕ} {r x y : ℕ}
    (hx : x ∈ lowerPart Y r) (hy : y ∈ Y \ lowerPart Y r) : x < y := by
  classical
  obtain ⟨i, hiRange, hix⟩ := Finset.mem_image.mp hx
  have hi : i.1 < Y.card - r := Finset.mem_range.mp i.2
  have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
  let jy : Fin Y.card := (Y.orderIsoOfFin rfl).symm ⟨y, hyY⟩
  have hjLarge : Y.card - r ≤ jy.val := by
    by_contra hnot
    have hj : jy.val ∈ Finset.range (Y.card - r) := by
      rw [Finset.mem_range]
      omega
    apply (Finset.mem_sdiff.mp hy).2
    apply Finset.mem_image.mpr
    refine ⟨⟨jy.val, hj⟩, by simp, ?_⟩
    have hinv := (Y.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyY⟩
    exact congrArg Subtype.val hinv
  have hfin : (⟨i.1, by omega⟩ : Fin Y.card) < jy := by
    exact Fin.mk_lt_mk.mpr (hi.trans_le hjLarge)
  have hlt := (Y.orderEmbOfFin rfl).strictMono hfin
  have hinv := (Y.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyY⟩
  have hjy : Y.orderEmbOfFin rfl jy = y := congrArg Subtype.val hinv
  rw [hix, hjy] at hlt
  exact hlt

lemma card_filter_le_lowerPart_add (Y : Finset ℕ) (r : ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    (Y.filter P).card ≤ ((lowerPart Y r).filter P).card + r := by
  classical
  let L := lowerPart Y r
  let U := Y \ L
  have hsub : Y.filter P ⊆ L.filter P ∪ U := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_cases hyL : y ∈ L
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyL, hy.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy.1, hyL⟩)
  calc
    (Y.filter P).card ≤ (L.filter P ∪ U).card := Finset.card_le_card hsub
    _ ≤ (L.filter P).card + U.card := Finset.card_union_le _ _
    _ ≤ (L.filter P).card + r :=
      Nat.add_le_add_left (card_sdiff_lowerPart_le Y r) _

lemma two_mul_div_le_self {x e : ℕ} (he : 2 ≤ e) : 2 * (x / e) ≤ x := by
  calc
    2 * (x / e) ≤ e * (x / e) := Nat.mul_le_mul_right (x / e) he
    _ = (x / e) * e := by ring
    _ ≤ x := Nat.div_mul_le_self _ _

/-- Divisor descent with a geometrically shrinking ordered reserve.  At scale
`d`, the largest `P / d` labels may be reserved as future pivots; diversity is
required only in the remaining lower pool. -/
theorem exists_orderedDivisorExtractionAux
    (B L K P S d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧
      (∀ z ∈ Z, q * z ∈ Y) ∧
      Y.card - Z.card ≤
        (L + S) * factors.length + K * factors.sum + 2 * (P / d) ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ ((lowerPart Z (P / (d * q) + S)).filter
          fun z => ¬e ∣ z).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (((lowerPart Y (P / d + S)).filter fun y => ¬e ∣ y).card <
            L + K * e)
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := divideMultiples Y e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, factors, hq, hqprod, hfactors, hdqB,
            hscale, hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' rfl
        refine ⟨e * q, Z, e :: factors, Nat.mul_pos hepos hq,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun h => h ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · intro z hz
          have hzY' : q * z ∈ Y' := hscale z hz
          have hzY := divideMultiples_scaled_subset hepos (q * z) hzY'
          simpa [mul_assoc] using hzY
        · have hY'le : Y'.card ≤ Y.card := by
            dsimp only [Y']
            rw [card_divideMultiples hepos]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have hZle : Z.card ≤ Y'.card := by
            apply Finset.card_le_card_of_injOn (fun z => q * z)
            · intro z hz
              exact hscale z hz
            · intro x hx y hy hxy
              exact Nat.eq_of_mul_eq_mul_left hq hxy
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          rw [hsplit]
          have hfirst : Y.card - Y'.card ≤ L + K * e + (P / d + S) := by
            dsimp only [Y']
            rw [card_sub_card_divideMultiples hepos]
            calc
              (Y.filter fun y => ¬e ∣ y).card ≤
                  (((lowerPart Y (P / d + S)).filter fun y => ¬e ∣ y).card) +
                    (P / d + S) :=
                card_filter_le_lowerPart_add Y (P / d + S) (fun y => ¬e ∣ y)
              _ ≤ L + K * e + (P / d + S) :=
                Nat.add_le_add_right hsmall.le _
          have hassoc : P / (d * e) = (P / d) / e := by
            exact (Nat.div_div_eq_div_mul P d e).symm
          have hgeom : P / d + 2 * (P / (d * e)) ≤ 2 * (P / d) := by
            rw [hassoc]
            have hhalf := two_mul_div_le_self (x := P / d) (e := e) (by omega)
            omega
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e + (P / d + S)) +
                  ((L + S) * factors.length + K * factors.sum +
                    2 * (P / (d * e))) := Nat.add_le_add hfirst hloss
            _ ≤ (L + S) * (e :: factors).length + K * (e :: factors).sum +
                  2 * (P / d) := by
              simp only [List.length_cons, List.sum_cons]
              nlinarith
        · intro a ha hbound
          have hdv := hdiverse a ha (by simpa only [mul_assoc] using hbound)
          simpa only [mul_assoc] using hdv
      · refine ⟨1, Y, [], by omega, by simp, by simp, ?_, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using (Nat.lt_of_not_ge hnot)

/-- Ordered common-divisor extraction.  The terminal lower part is diverse,
the complementary upper part has at most `P / d` elements, and the whole
descent loses only `2P` in addition to the logarithmic and divisor charges. -/
theorem exists_orderedDivisorExtraction
    (B L K P S : ℕ) (hB : 0 < B) (Y : Finset ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      Y.card - Z.card ≤ (L + S) * Nat.log 2 B + K * B + 2 * P ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ ((lowerPart Z (P / d + S)).filter
          fun z => ¬e ∣ z).card := by
  obtain ⟨d, Z, factors, hd, hdprod, hfactors, hdB,
      hscale, hloss, hdiverse⟩ :=
    exists_orderedDivisorExtractionAux B L K P S 1 (by omega) hB Y
  refine ⟨d, Z, hd, by simpa using hdB, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤
          (L + S) * factors.length + K * factors.sum + 2 * (P / 1) := hloss
      _ ≤ (L + S) * Nat.log 2 B + K * B + 2 * P := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.mul_le_mul_left
            exact (length_le_log_prod_of_one_lt factors hfactors).trans
              (Nat.log_mono_right (by simpa [hdprod] using hdB))
          · apply Nat.mul_le_mul_left
            exact (sum_le_prod_of_one_lt factors hfactors).trans
              (by simpa [hdprod] using hdB)
        · simp
  · intro e he hde
    simpa [mul_assoc] using hdiverse e he (by simpa [mul_assoc] using hde)

/-! ### A finite simultaneous-balancing lemma -/

open Erdos697.Bernoulli in

lemma sum_le_bound_add_sum_subset_card_sub_one
    {A C : Finset ℕ} {g : ℕ → ℕ} {M : ℕ}
    (hCA : C ⊆ A) (hcard : C.card = A.card - 1)
    (hA : A.Nonempty) (hmax : ∀ a ∈ A, g a ≤ M) :
    ∑ a ∈ A, g a ≤ M + ∑ a ∈ C, g a := by
  classical
  have hdiffcard : (A \ C).card = 1 := by
    rw [Finset.card_sdiff_of_subset hCA, hcard]
    have hpos : 1 ≤ A.card := Finset.one_le_card.mpr hA
    omega
  have hdiff : ∑ a ∈ A \ C, g a ≤ M := by
    calc
      ∑ a ∈ A \ C, g a ≤ ∑ _a ∈ A \ C, M := by
        apply Finset.sum_le_sum
        intro a ha
        exact hmax a (Finset.mem_sdiff.mp ha).1
      _ = M := by simp [hdiffcard]
  have hsplit : ∑ a ∈ A, g a =
      (∑ a ∈ C, g a) + ∑ a ∈ A \ C, g a := by
    rw [add_comm]
    exact (Finset.sum_sdiff hCA).symm
  rw [hsplit]
  omega

theorem layerHall_uniform_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {D : Finset ℕ} {base : ℕ}
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 5 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hDA : D ⊆ firstCoordinateSet X) (hDbase : base ∉ D)
    (hDcard : D.card ≤
      (firstCoordinateSet X).max' hA + 2 - (firstCoordinateSet X).card)
    (hno : ¬ ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card) :
    ((firstCoordinateSet X).card - 5) * (coordinateFiber X base).card +
        4 * X.card + 2 * ∑ a ∈ D, (coordinateFiber X a).card ≤
      2 * (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let anchor : LayerHallSlot A D base → ℕ := layerHallAnchor A D base
  have hAcard' : 5 ≤ A.card := by simpa [A] using hAcard
  have hanchor : ∀ i, anchor i ∈ A :=
    layerHallAnchor_mem hbase hDA
  have hHall : ∀ J : Finset (LayerHallSlot A D base),
      J.card ≤ (J.biUnion fun i ↦ A.image fun b ↦ anchor i + b).card := by
    apply hall_condition_of_layer_multiplicity A D base anchor hA hAzero
      (by omega) hgcd hbase hDA hDbase hDcard hanchor
    · simpa [anchor] using layerHallAnchor_base_fiber_cap (by omega) hDbase
    · intro a haD
      simpa [anchor] using layerHallAnchor_double_fiber_cap hDbase haD
    · intro a haA ha0 haD
      simpa [anchor] using layerHallAnchor_single_fiber_cap haA ha0 haD
  obtain ⟨choice, hchoice, hinj, hsum⟩ :=
    exists_choice_sum_card_coordinateFiber_add_le_of_hall
      X anchor hanchor hHall
  let baseChoice : Fin (A.card - 1) → ℕ :=
    fun i ↦ choice (Sum.inl i)
  have hbaseChoice : ∀ i, baseChoice i ∈ A := by
    intro i
    exact hchoice (Sum.inl i)
  have hbaseChoiceInj : Function.Injective baseChoice := by
    intro i j hij
    apply Sum.inl.inj
    apply hinj
    simpa [anchor, layerHallAnchor, baseChoice, hij]
  let C : Finset ℕ := Finset.univ.image baseChoice
  have hCA : C ⊆ A := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hbaseChoice i
  have hCcard : C.card = A.card - 1 := by
    dsimp [C]
    rw [Finset.card_image_iff.mpr hbaseChoiceInj.injOn]
    simp
  have hXcard : X.card = ∑ a ∈ A, F a := by
    simpa [A, F] using card_eq_sum_card_coordinateFiber X
  have hchoiceSum : X.card ≤ F base + ∑ i, F (baseChoice i) := by
    have hsub := sum_le_bound_add_sum_subset_card_sub_one hCA hCcard hA
      (fun a ha ↦ hbaseMax a ha)
    have hsumC : ∑ a ∈ C, F a = ∑ i, F (baseChoice i) := by
      dsimp [C]
      rw [Finset.sum_image]
      exact hbaseChoiceInj.injOn
    rw [hXcard]
    simpa [F, hsumC] using hsub
  have hbaseTerms :
      (A.card - 1) * F base + 2 * ∑ i, F (baseChoice i) ≤
        2 * ∑ i : Fin (A.card - 1),
          (coordinateFiber X base +
            coordinateFiber X (baseChoice i)).card := by
    have hpoint : ∀ i : Fin (A.card - 1),
        F base + 2 * F (baseChoice i) ≤
          2 * (coordinateFiber X base +
            coordinateFiber X (baseChoice i)).card := by
      intro i
      have hFbase : (coordinateFiber X base).Nonempty :=
        coordinateFiber_nonempty_iff.mpr hbase
      have hFchoice : (coordinateFiber X (baseChoice i)).Nonempty :=
        coordinateFiber_nonempty_iff.mpr (hbaseChoice i)
      have hle : (coordinateFiber X (baseChoice i)).card ≤
          (coordinateFiber X base).card :=
        hbaseMax _ (hbaseChoice i)
      rcases small_coset_or_uniform_pair_sum_lower hFbase hFchoice hle with
        hbad | hgood
      · exact False.elim (hno hbad)
      · simpa [F] using hgood
    have h :
        (∑ i : Fin (A.card - 1), (F base + 2 * F (baseChoice i))) ≤
          (∑ i : Fin (A.card - 1),
            2 * (coordinateFiber X base +
              coordinateFiber X (baseChoice i)).card) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i
    simpa [Finset.sum_add_distrib, Finset.mul_sum, F] using h
  have hbaseLower :
      (A.card - 3) * F base + 2 * X.card ≤
        2 * ∑ i : Fin (A.card - 1),
          (coordinateFiber X base +
            coordinateFiber X (baseChoice i)).card := by
    calc
      (A.card - 3) * F base + 2 * X.card ≤
          (A.card - 3) * F base +
            2 * (F base + ∑ i, F (baseChoice i)) := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hchoiceSum) _
      _ = (A.card - 1) * F base +
            2 * ∑ i, F (baseChoice i) := by
        have hs : A.card - 1 = (A.card - 3) + 2 := by omega
        have hcoeff : (A.card - 1) * F base =
            (A.card - 3) * F base + 2 * F base := by
          rw [hs]
          ring
        rw [hcoeff]
        ring
      _ ≤ _ := hbaseTerms
  have hotherLower :
      (∑ a ∈ A.erase base, F a) + ∑ a ∈ D, F a ≤
        ∑ i : ({a // a ∈ A.erase base} ⊕ {a // a ∈ D}),
          (coordinateFiber X (anchor (Sum.inr i)) +
            coordinateFiber X (choice (Sum.inr i))).card := by
    have hpoint : ∀ i : ({a // a ∈ A.erase base} ⊕ {a // a ∈ D}),
        F (anchor (Sum.inr i)) ≤
          (coordinateFiber X (anchor (Sum.inr i)) +
            coordinateFiber X (choice (Sum.inr i))).card := by
      intro i
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inr i)))
    have h :
        (∑ i : ({a // a ∈ A.erase base} ⊕ {a // a ∈ D}),
          F (anchor (Sum.inr i))) ≤
        (∑ i : ({a // a ∈ A.erase base} ⊕ {a // a ∈ D}),
          (coordinateFiber X (anchor (Sum.inr i)) +
            coordinateFiber X (choice (Sum.inr i))).card) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i
    simp only [Fintype.sum_sum_type, anchor, layerHallAnchor] at h ⊢
    rw [Finset.sum_subtype (p := fun x ↦ x ∈ A.erase base)
        (s := A.erase base) (by simp) F,
      Finset.sum_subtype (p := fun x ↦ x ∈ D)
        (s := D) (by simp) F]
    simpa only [F] using h
  have hsplit : X.card = F base + ∑ a ∈ A.erase base, F a := by
    rw [hXcard]
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  have hsum' :
      (∑ i : Fin (A.card - 1),
          (coordinateFiber X base +
            coordinateFiber X (baseChoice i)).card) +
        (∑ i : ({a // a ∈ A.erase base} ⊕ {a // a ∈ D}),
          (coordinateFiber X (anchor (Sum.inr i)) +
            coordinateFiber X (choice (Sum.inr i))).card) ≤
        (X + X).card := by
    simpa [LayerHallSlot, anchor, layerHallAnchor, baseChoice,
      Fintype.sum_sum_type] using hsum
  dsimp only [A, F] at hbaseLower hotherLower hsplit ⊢
  have hscoeff : (firstCoordinateSet X).card - 3 =
      ((firstCoordinateSet X).card - 5) + 2 := by omega
  have hcombine := Nat.add_le_add hbaseLower
    (Nat.mul_le_mul_left 2 hotherLower)
  have htargetEq :
      ((firstCoordinateSet X).card - 5) * (coordinateFiber X base).card +
          4 * X.card + 2 * ∑ a ∈ D, (coordinateFiber X a).card =
        (((firstCoordinateSet X).card - 3) *
            (coordinateFiber X base).card + 2 * X.card) +
          2 * ((∑ a ∈ (firstCoordinateSet X).erase base,
              (coordinateFiber X a).card) +
            ∑ a ∈ D, (coordinateFiber X a).card) := by
    rw [hscoeff]
    rw [hsplit]
    ring
  rw [htargetEq]
  exact hcombine.trans (by
    calc
      2 * ∑ i, (coordinateFiber X base +
              coordinateFiber X (baseChoice i)).card +
          2 * ∑ i, (coordinateFiber X (anchor (Sum.inr i)) +
              coordinateFiber X (choice (Sum.inr i))).card =
          2 * ((∑ i, (coordinateFiber X base +
              coordinateFiber X (baseChoice i)).card) +
            ∑ i, (coordinateFiber X (anchor (Sum.inr i)) +
              coordinateFiber X (choice (Sum.inr i))).card) := by ring
      _ ≤ 2 * (X + X).card := Nat.mul_le_mul_left 2 hsum')

theorem exists_small_largestFiber_coset_of_four_le_R
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    {base : ℕ} (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hR4 : 4 ≤ min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  let s := A.card
  let M := F base
  let R := min (A.max' hA + 3 - A.card) A.card
  let k := R - 1
  obtain ⟨D, hDA, hDbase, hDcard, hDle, havg⟩ :=
    exists_weighted_distinguishedLayerSet X hA hbase
  by_contra hno
  have huniform := layerHall_uniform_fiber_lower X hA hAzero (by omega) hgcd
    hbase hbaseMax hDA hDbase hDle hno
  have hstrict : (s - 5) * M + 2 * ∑ a ∈ D, F a < X.card := by
    dsimp only [A, F, s, M] at huniform ⊢
    omega
  have hXcard : X.card = ∑ a ∈ A, F a := by
    simpa [A, F] using card_eq_sum_card_coordinateFiber X
  have hsplit : X.card = M + ∑ a ∈ A.erase base, F a := by
    rw [hXcard]
    dsimp only [M]
    rw [add_comm]
    exact (Finset.sum_erase_add A F hbase).symm
  let P := ∑ a ∈ A.erase base, F a
  let Q := ∑ a ∈ D, F a
  have hs6 : 6 ≤ s := by simpa [s, A] using hAcard
  have hR4' : 4 ≤ R := by simpa [R, A] using hR4
  have hk3 : 3 ≤ k := by dsimp only [k]; omega
  have hPbound : P ≤ (s - 1) * M := by
    dsimp only [P]
    have herase : (A.erase base).card = s - 1 := by
      rw [Finset.card_erase_of_mem hbase]
    calc
      ∑ a ∈ A.erase base, F a ≤
          ∑ _a ∈ A.erase base, M := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbaseMax a (Finset.mem_of_mem_erase ha)
      _ = (A.erase base).card * M := by simp
      _ = (s - 1) * M := by rw [herase]
  have havg' : k * P ≤ (s - 1) * Q := by
    simpa [A, F, s, R, k, P, Q] using havg
  have hcoreMul : (s - 1) * P ≤
      (s - 1) * ((s - 6) * M + 2 * Q) := by
    by_cases hkbig : s - 1 ≤ 2 * k
    · have hkp := Nat.mul_le_mul_right P hkbig
      have havg2 := Nat.mul_le_mul_left 2 havg'
      calc
        (s - 1) * P ≤ 2 * k * P := by simpa [mul_assoc] using hkp
        _ = 2 * (k * P) := by ring
        _ ≤ 2 * ((s - 1) * Q) := havg2
        _ ≤ (s - 1) * ((s - 6) * M + 2 * Q) := by
          ring_nf
          omega
    · have hklt : 2 * k < s - 1 := Nat.lt_of_not_ge hkbig
      have hgap : s - 1 - 2 * k ≤ s - 6 := by omega
      have hgapP := Nat.mul_le_mul_right P hgap
      have hgapM := Nat.mul_le_mul_left (s - 1 - 2 * k) hPbound
      have hgapBound : (s - 1 - 2 * k) * P ≤
          (s - 1) * ((s - 6) * M) := by
        calc
          (s - 1 - 2 * k) * P ≤
              (s - 1 - 2 * k) * ((s - 1) * M) := hgapM
          _ = (s - 1) * ((s - 1 - 2 * k) * M) := by ring
          _ ≤ (s - 1) * ((s - 6) * M) := by
            gcongr
      have havg2 := Nat.mul_le_mul_left 2 havg'
      have hdecomp : (s - 1) * P =
          (s - 1 - 2 * k) * P + 2 * k * P := by
        have hsdecomp : s - 1 = (s - 1 - 2 * k) + 2 * k := by omega
        calc
          (s - 1) * P = ((s - 1 - 2 * k) + 2 * k) * P := by
            exact congrArg (fun q ↦ q * P) hsdecomp
          _ = (s - 1 - 2 * k) * P + 2 * k * P := by ring
      rw [hdecomp]
      calc
        (s - 1 - 2 * k) * P + 2 * k * P ≤
            (s - 1) * ((s - 6) * M) +
              2 * ((s - 1) * Q) := by
          exact Nat.add_le_add hgapBound (by
            simpa [mul_assoc] using havg2)
        _ = (s - 1) * ((s - 6) * M + 2 * Q) := by ring
  have hspos : 0 < s - 1 := by omega
  have hcore : P ≤ (s - 6) * M + 2 * Q :=
    Nat.le_of_mul_le_mul_left hcoreMul hspos
  dsimp only [P, Q] at hcore
  rw [hsplit] at hstrict
  have hscoeff : s - 5 = (s - 6) + 1 := by omega
  rw [hscoeff] at hstrict
  ring_nf at hstrict
  omega

/-- In the comparable-size regime, failure of the `3|A|/2` sumset bound
puts the larger summand in a coset of a subgroup smaller than `3|A|/2`. -/
lemma small_coset_or_comparable_pair_sum_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) (hbalance : 3 * A.card ≤ 4 * B.card) :
    (∃ H : AddSubgroup G,
      ContainedInAddCoset H A ∧ 2 * Nat.card H < 3 * A.card) ∨
      3 * A.card ≤ 2 * (A + B).card := by
  by_cases hlower : 3 * A.card ≤ 2 * (A + B).card
  · exact Or.inr hlower
  · left
    have hleft : 2 * (A + B).card < 3 * A.card := by omega
    have hright : (A + B).card < 2 * B.card := by omega
    obtain ⟨H, c, hcoset, hHcard⟩ :=
      small_sumset_stabilizer_coset hA hB hleft hright
    have hsum :=
      summands_subset_cosets_of_sumset_subset_coset hA hB hcoset
    exact ⟨H, hsum.1, by omega⟩

/-- In the imbalanced-size regime, failure of the `2|B|` sumset bound
puts the larger summand in a coset of a subgroup smaller than `3|A|/2`. -/
lemma small_coset_or_imbalanced_pair_sum_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) (hbalance : 4 * B.card < 3 * A.card) :
    (∃ H : AddSubgroup G,
      ContainedInAddCoset H A ∧ 2 * Nat.card H < 3 * A.card) ∨
      2 * B.card ≤ (A + B).card := by
  by_cases hlower : 2 * B.card ≤ (A + B).card
  · exact Or.inr hlower
  · left
    obtain ⟨H, c, hcoset, hHcard⟩ :=
      deshouillersFreiman_kneser_corollary_two hA hB
        (by omega) hbalance
    have hsum :=
      summands_subset_cosets_of_sumset_subset_coset hA hB hcoset
    exact ⟨H, hsum.1, by omega⟩

/-- The doubled contribution forced by a pair with a largest fibre. -/
def largestPairWeight (M b : ℕ) : ℕ :=
  if 3 * M ≤ 4 * b then 3 * M else max (2 * M) (4 * b)

lemma small_coset_or_largestPairWeight_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) :
    (∃ H : AddSubgroup G,
      ContainedInAddCoset H A ∧ 2 * Nat.card H < 3 * A.card) ∨
      largestPairWeight A.card B.card ≤ 2 * (A + B).card := by
  by_cases hbalance : 3 * A.card ≤ 4 * B.card
  · rcases small_coset_or_comparable_pair_sum_lower hA hB hBA hbalance with
      hbad | hgood
    · exact Or.inl hbad
    · exact Or.inr (by simpa [largestPairWeight, hbalance] using hgood)
  · rcases small_coset_or_imbalanced_pair_sum_lower hA hB hBA
      (Nat.lt_of_not_ge hbalance) with hbad | hgood
    · exact Or.inl hbad
    · right
      have hlarge : 2 * A.card ≤ 2 * (A + B).card := by
        exact Nat.mul_le_mul_left 2 (Finset.card_le_card_add_right hB)
      have hsmall : 4 * B.card ≤ 2 * (A + B).card := by omega
      simp only [largestPairWeight, if_neg hbalance]
      exact max_le hlarge hsmall

/-- Symmetric version of the sharp doubled pair contribution. -/
def pairWeight (a b : ℕ) : ℕ :=
  largestPairWeight (max a b) (min a b)

lemma pairWeight_comm (a b : ℕ) : pairWeight a b = pairWeight b a := by
  simp [pairWeight, max_comm, min_comm]

@[simp] lemma pairWeight_self (a : ℕ) : pairWeight a a = 3 * a := by
  by_cases ha : a = 0
  · subst a
    simp [pairWeight, largestPairWeight]
  · simp only [pairWeight, max_self, min_self, largestPairWeight]
    rw [if_pos (by omega)]

lemma two_mul_left_le_pairWeight (a b : ℕ) :
    2 * a ≤ pairWeight a b := by
  simp only [pairWeight, largestPairWeight]
  split_ifs <;> simp only [max_def, min_def] <;>
    split_ifs <;> omega

lemma two_mul_right_le_pairWeight (a b : ℕ) :
    2 * b ≤ pairWeight a b := by
  rw [pairWeight_comm]
  exact two_mul_left_le_pairWeight b a

lemma add_add_min_le_pairWeight (a b : ℕ) :
    a + b + min a b ≤ pairWeight a b := by
  simp only [pairWeight, largestPairWeight]
  simp only [max_def, min_def]
  split_ifs <;> omega

lemma max_add_two_min_le_pairWeight (a b : ℕ) :
    max a b + 2 * min a b ≤ pairWeight a b := by
  simp only [pairWeight, largestPairWeight]
  simp only [max_def, min_def]
  split_ifs <;> omega

lemma larger_add_two_smaller_le_pairWeight {a b : ℕ} (hab : a ≤ b) :
    b + 2 * a ≤ pairWeight a b := by
  simpa [max_eq_right hab, min_eq_left hab] using
    max_add_two_min_le_pairWeight a b

private lemma ordered_pair_middle_bound {b c : ℕ} (hbc : b ≤ c) :
    4 * b + 2 * c ≤ pairWeight b c + max (2 * c) (3 * b) := by
  simp only [pairWeight, max_eq_right hbc, min_eq_left hbc,
    largestPairWeight]
  split_ifs <;> simp only [max_def] <;> split_ifs <;> omega

private lemma three_weight_endpoint_bound_of_le {a b c : ℕ} (hac : a ≤ c) :
    5 * (a + b + c) ≤
      pairWeight a a + pairWeight a b +
        max (pairWeight a c) (pairWeight b b) +
        pairWeight b c + pairWeight c c := by
  rcases le_total b a with hba | hab
  · have hbc : b ≤ c := hba.trans hac
    have habw := larger_add_two_smaller_le_pairWeight hba
    rw [pairWeight_comm b a] at habw
    have hbcw := larger_add_two_smaller_le_pairWeight hbc
    have hacw := add_add_min_le_pairWeight a c
    have hcenter : pairWeight a c ≤
        max (pairWeight a c) (pairWeight b b) := le_max_left _ _
    rw [pairWeight_self a, pairWeight_self c]
    omega
  · rcases le_total b c with hbc | hcb
    · have habw := larger_add_two_smaller_le_pairWeight hab
      have hbcw := ordered_pair_middle_bound hbc
      have hcenterC : 2 * c ≤
          max (pairWeight a c) (pairWeight b b) :=
        (two_mul_right_le_pairWeight a c).trans (le_max_left _ _)
      have hcenterB : 3 * b ≤
          max (pairWeight a c) (pairWeight b b) := by
        rw [← pairWeight_self b]
        exact le_max_right _ _
      have hcenter : max (2 * c) (3 * b) ≤
          max (pairWeight a c) (pairWeight b b) :=
        max_le hcenterC hcenterB
      rw [pairWeight_self a, pairWeight_self c]
      omega
    · have hab' : a ≤ b := hac.trans hcb
      have habw := larger_add_two_smaller_le_pairWeight hab'
      have hbcw := larger_add_two_smaller_le_pairWeight hcb
      rw [pairWeight_comm c b] at hbcw
      have hcenter : 3 * b ≤
          max (pairWeight a c) (pairWeight b b) := by
        rw [← pairWeight_self b]
        exact le_max_right _ _
      rw [pairWeight_self a, pairWeight_self c]
      omega

/-- The three-layer endpoint-recursion base case.  The maximum in the
middle antidiagonal chooses between `(0,2)` and `(1,1)`. -/
lemma three_weight_endpoint_bound (a b c : ℕ) :
    5 * (a + b + c) ≤
      pairWeight a a + pairWeight a b +
        max (pairWeight a c) (pairWeight b b) +
        pairWeight b c + pairWeight c c := by
  rcases le_total a c with hac | hca
  · exact three_weight_endpoint_bound_of_le hac
  · have h := three_weight_endpoint_bound_of_le (a := c) (b := b) (c := a) hca
    rw [pairWeight_comm c b, pairWeight_comm c a,
      pairWeight_comm b a] at h
    simpa [add_comm, add_left_comm, add_assoc] using h

/-- A sharp-weight pair selection, one pair on each antidiagonal of an
initial interval. -/
def IsWeightedIntervalPairSelection (n : ℕ) (w : ℕ → ℕ)
    (P : Finset (ℕ × ℕ)) : Prop :=
  P.card = 2 * n - 1 ∧
  (∀ p ∈ P, p.1 < n ∧ p.2 < n) ∧
  Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
  5 * ∑ i ∈ Finset.range n, w i ≤
    ∑ p ∈ P, pairWeight (w p.1) (w p.2)

theorem exists_weighted_intervalPairSelection
    (w : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    ∃ P : Finset (ℕ × ℕ), IsWeightedIntervalPairSelection n w P := by
  induction n, hn using Nat.le_induction with
  | base =>
      by_cases hmid : pairWeight (w 1) (w 1) ≤ pairWeight (w 0) (w 2)
      · let P : Finset (ℕ × ℕ) :=
          {(0, 0), (0, 1), (0, 2), (1, 2), (2, 2)}
        refine ⟨P, ?_⟩
        have hbase := three_weight_endpoint_bound (w 0) (w 1) (w 2)
        have hmax : max (pairWeight (w 0) (w 2))
            (pairWeight (w 1) (w 1)) = pairWeight (w 0) (w 2) :=
          max_eq_left hmid
        dsimp [IsWeightedIntervalPairSelection, P]
        refine ⟨by decide, ?_, by decide, ?_⟩
        · intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl <;> omega
        · rw [hmax] at hbase
          simp only [pairWeight_self] at hbase
          simp [P, Finset.sum_range_succ]
          omega
      · have hmid' : pairWeight (w 0) (w 2) < pairWeight (w 1) (w 1) :=
          Nat.lt_of_not_ge hmid
        let P : Finset (ℕ × ℕ) :=
          {(0, 0), (0, 1), (1, 1), (1, 2), (2, 2)}
        refine ⟨P, ?_⟩
        have hbase := three_weight_endpoint_bound (w 0) (w 1) (w 2)
        have hmax : max (pairWeight (w 0) (w 2))
            (pairWeight (w 1) (w 1)) = pairWeight (w 1) (w 1) :=
          max_eq_right hmid'.le
        dsimp [IsWeightedIntervalPairSelection, P]
        refine ⟨by decide, ?_, by decide, ?_⟩
        · intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl <;> omega
        · rw [hmax] at hbase
          simp only [pairWeight_self] at hbase
          simp [P, Finset.sum_range_succ]
          omega
  | succ n hn ih =>
      obtain ⟨P, hPcard, hPbound, hPinj, hPweight⟩ := ih
      let u : ℕ × ℕ := (n - 1, n)
      let v : ℕ × ℕ := (n, n)
      let Q : Finset (ℕ × ℕ) := insert u (insert v P)
      have hnpos : 0 < n := by omega
      have huP : u ∉ P := by
        intro hu
        have hub := hPbound u hu
        dsimp [u] at hub
        omega
      have hvP : v ∉ P := by
        intro hv
        have hvb := hPbound v hv
        dsimp [v] at hvb
        omega
      have huv : u ≠ v := by
        intro huv
        have := congrArg Prod.fst huv
        dsimp [u, v] at this
        omega
      refine ⟨Q, ?_, ?_, ?_, ?_⟩
      · dsimp [Q]
        rw [Finset.card_insert_of_notMem (by simp [huv, huP]),
          Finset.card_insert_of_notMem hvP, hPcard]
        omega
      · intro p hp
        change p ∈ insert u (insert v P) at hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | rfl | hp
        · dsimp [u]
          omega
        · dsimp [v]
          omega
        · have := hPbound p hp
          omega
      · intro p hp q hq hpq
        change p ∈ insert u (insert v P) at hp
        change q ∈ insert u (insert v P) at hq
        simp only [Finset.mem_insert] at hp hq
        rcases hp with rfl | rfl | hp <;>
          rcases hq with rfl | rfl | hq
        · rfl
        · dsimp [u, v] at hpq
          omega
        · have hqb := hPbound q hq
          dsimp [u] at hpq
          have hqsum : q.1 + q.2 ≤ 2 * n - 2 := by omega
          omega
        · dsimp [u, v] at hpq
          omega
        · rfl
        · have hqb := hPbound q hq
          dsimp [v] at hpq
          have hqsum : q.1 + q.2 ≤ 2 * n - 2 := by omega
          omega
        · have hpb := hPbound p hp
          dsimp [u] at hpq
          have hpsum : p.1 + p.2 ≤ 2 * n - 2 := by omega
          omega
        · have hpb := hPbound p hp
          dsimp [v] at hpq
          have hpsum : p.1 + p.2 ≤ 2 * n - 2 := by omega
          omega
        · exact hPinj hp hq hpq
      · have huWeight := two_mul_right_le_pairWeight (w (n - 1)) (w n)
        have hvWeight := pairWeight_self (w n)
        dsimp [Q]
        rw [Finset.sum_insert (by simp [huv, huP]),
          Finset.sum_insert hvP, Finset.sum_range_succ]
        dsimp [u, v]
        omega

lemma dense_coset_or_pairWeight_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    (∃ H : AddSubgroup G,
        (ContainedInAddCoset H A ∧ 2 * Nat.card H < 3 * A.card) ∨
        (ContainedInAddCoset H B ∧ 2 * Nat.card H < 3 * B.card)) ∨
      pairWeight A.card B.card ≤ 2 * (A + B).card := by
  rcases le_total B.card A.card with hBA | hAB
  · rcases small_coset_or_largestPairWeight_le hA hB hBA with hbad | hgood
    · exact Or.inl ⟨hbad.choose, Or.inl hbad.choose_spec⟩
    · right
      simpa [pairWeight, max_eq_left hBA, min_eq_right hBA] using hgood
  · rcases small_coset_or_largestPairWeight_le hB hA hAB with hbad | hgood
    · exact Or.inl ⟨hbad.choose, Or.inr hbad.choose_spec⟩
    · right
      simpa [pairWeight, max_eq_right hAB, min_eq_left hAB,
        add_comm] using hgood

abbrev IntervalFullHallSlot (s base : ℕ) : Type :=
  Fin s ⊕ {a // a ∈ (Finset.range s).erase base}

def intervalFullHallAnchor (s base : ℕ) :
    IntervalFullHallSlot s base → ℕ
  | Sum.inl _ => base
  | Sum.inr a => a.1

def intervalFullHallChoice (s base : ℕ) :
    IntervalFullHallSlot s base → ℕ
  | Sum.inl i => i.1
  | Sum.inr a => if a.1 < base then 0 else s - 1

lemma intervalFullHallChoice_mem {s base : ℕ} (hs : 0 < s) :
    ∀ i : IntervalFullHallSlot s base,
      intervalFullHallChoice s base i ∈ Finset.range s := by
  intro i
  rcases i with i | a
  · exact Finset.mem_range.mpr i.2
  · simp only [intervalFullHallChoice]
    split_ifs <;> simp only [Finset.mem_range] <;> omega

lemma intervalFullHallAnchor_mem {s base : ℕ} (hbase : base < s) :
    ∀ i : IntervalFullHallSlot s base,
      intervalFullHallAnchor s base i ∈ Finset.range s := by
  intro i
  rcases i with i | a
  · exact Finset.mem_range.mpr hbase
  · exact Finset.mem_of_mem_erase a.2

lemma intervalFullHall_sum_injective {s base : ℕ} (hbase : base < s) :
    Function.Injective (fun i : IntervalFullHallSlot s base =>
      intervalFullHallAnchor s base i + intervalFullHallChoice s base i) := by
  intro i j hij
  rcases i with i | a <;> rcases j with j | b
  · apply congrArg Sum.inl
    apply Fin.ext
    simp only [intervalFullHallAnchor, intervalFullHallChoice] at hij
    omega
  · simp only [intervalFullHallAnchor, intervalFullHallChoice] at hij
    have hbmem := Finset.mem_erase.mp b.2
    split_ifs at hij with hb
    · omega
    · have hblt : base < b.1 := by
        have : b.1 < s := Finset.mem_range.mp hbmem.2
        omega
      omega
  · simp only [intervalFullHallAnchor, intervalFullHallChoice] at hij
    have hamem := Finset.mem_erase.mp a.2
    split_ifs at hij with ha
    · omega
    · have halt : base < a.1 := by
        have : a.1 < s := Finset.mem_range.mp hamem.2
        omega
      omega
  · simp only [intervalFullHallAnchor, intervalFullHallChoice] at hij
    have hamem := Finset.mem_erase.mp a.2
    have hbmem := Finset.mem_erase.mp b.2
    split_ifs at hij with ha hb
    · apply congrArg Sum.inr
      apply Subtype.ext
      omega
    · have hblt : base < b.1 := by
        have : b.1 < s := Finset.mem_range.mp hbmem.2
        omega
      omega
    · have halt : base < a.1 := by
        have : a.1 < s := Finset.mem_range.mp hamem.2
        omega
      omega
    · apply congrArg Sum.inr
      apply Subtype.ext
      omega

lemma intervalFullHall_condition {s base : ℕ} (hbase : base < s) :
    ∀ J : Finset (IntervalFullHallSlot s base),
      J.card ≤ (J.biUnion fun i => (Finset.range s).image fun b =>
        intervalFullHallAnchor s base i + b).card := by
  classical
  intro J
  let f : IntervalFullHallSlot s base → ℕ := fun i =>
    intervalFullHallAnchor s base i + intervalFullHallChoice s base i
  have hfsub : J.image f ⊆
      J.biUnion fun i => (Finset.range s).image fun b =>
        intervalFullHallAnchor s base i + b := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_image.mpr ⟨intervalFullHallChoice s base i,
      intervalFullHallChoice_mem (by omega) i, rfl⟩⟩
  calc
    J.card = (J.image f).card := by
      symm
      rw [Finset.card_image_iff.mpr]
      exact (intervalFullHall_sum_injective hbase).injOn
    _ ≤ _ := Finset.card_le_card hfsub

theorem interval_full_partner_fiber_lower
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    {s base : ℕ} {E : Finset ℕ} {H : AddSubgroup (ZMod d)}
    (hs : 0 < s)
    (hsupport : firstCoordinateSet X = Finset.range s)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hEA : E ⊆ firstCoordinateSet X)
    (hEbad : ∀ a ∈ E,
      ¬ContainedInAddCoset H (coordinateFiber X a)) :
    X.card + (s + E.card - 1) * (coordinateFiber X base).card ≤
      (X + X).card := by
  classical
  let A := Finset.range s
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let anchor : IntervalFullHallSlot s base → ℕ :=
    intervalFullHallAnchor s base
  let choice : IntervalFullHallSlot s base → ℕ :=
    intervalFullHallChoice s base
  let pair : IntervalFullHallSlot s base → ℕ × ℕ :=
    fun i => (anchor i, choice i)
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hbaseLt : base < s := by
    rw [hsupport] at hbase
    exact Finset.mem_range.mp hbase
  have hanchor : ∀ i, anchor i ∈ firstCoordinateSet X := by
    intro i
    rw [hsupport]
    exact intervalFullHallAnchor_mem hbaseLt i
  have hchoice : ∀ i, choice i ∈ firstCoordinateSet X := by
    intro i
    rw [hsupport]
    exact intervalFullHallChoice_mem hs i
  have hsumInj : Function.Injective (fun i => anchor i + choice i) := by
    simpa [anchor, choice] using intervalFullHall_sum_injective hbaseLt
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply hsumInj
    exact congrArg (fun p : ℕ × ℕ => p.1 + p.2) hij
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hanchor i, hchoice i⟩
  have hPinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := hsumInj hpq
    subst j
    rfl
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  let bonus : IntervalFullHallSlot s base → ℕ
    | Sum.inl i => if i.1 ∈ E then F base else 0
    | Sum.inr _ => 0
  have hpoint : ∀ i : IntervalFullHallSlot s base,
      F (anchor i) + bonus i ≤
        (coordinateFiber X (anchor i) + coordinateFiber X (choice i)).card := by
    intro i
    rcases i with i | a
    · simp only [anchor, intervalFullHallAnchor, bonus]
      by_cases hiE : i.1 ∈ E
      · rw [if_pos hiE]
        have hbad := hEbad i.1 hiE
        have hne : (coordinateFiber X (choice (Sum.inl i))).Nonempty :=
          coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inl i))
        have htwo := two_mul_card_le_add_of_coset_and_not_coset
          (coordinateFiber_nonempty_iff.mpr hbase) hne hbaseCos
          (by simpa [choice, intervalFullHallChoice] using hbad)
        simpa [F, choice, intervalFullHallChoice, two_mul] using htwo
      · rw [if_neg hiE, add_zero]
        exact Finset.card_le_card_add_right
          (coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inl i)))
    · simp only [anchor, intervalFullHallAnchor, bonus, add_zero]
      exact Finset.card_le_card_add_right
        (coordinateFiber_nonempty_iff.mpr (hchoice (Sum.inr a)))
  have hslotSum : (∑ i : IntervalFullHallSlot s base,
        (F (anchor i) + bonus i)) ≤
      ∑ i : IntervalFullHallSlot s base,
        (coordinateFiber X (anchor i) + coordinateFiber X (choice i)).card := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hslotToP : (∑ i : IntervalFullHallSlot s base,
        (coordinateFiber X (anchor i) + coordinateFiber X (choice i)).card) =
      ∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hEsubset : E ⊆ Finset.range s := by
    simpa [hsupport] using hEA
  have hfilter : (Finset.range s).filter (fun i => i ∈ E) = E := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hi
      exact ⟨hEsubset hi, hi⟩
  have hbonus : (∑ i : IntervalFullHallSlot s base, bonus i) =
      E.card * F base := by
    simp only [Fintype.sum_sum_type, bonus, Finset.sum_const_zero, add_zero]
    let T := (Finset.univ : Finset (Fin s)).filter fun i => i.1 ∈ E
    have hTimage : T.image (fun i : Fin s => i.1) = E := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
        have hiE : i.1 ∈ E := (Finset.mem_filter.mp hi).2
        simpa [hia] using hiE
      · intro ha
        have has : a < s := Finset.mem_range.mp (hEsubset ha)
        apply Finset.mem_image.mpr
        refine ⟨⟨a, has⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hTcard : T.card = E.card := by
      calc
        T.card = (T.image (fun i : Fin s => i.1)).card := by
          symm
          rw [Finset.card_image_iff.mpr Fin.val_injective.injOn]
        _ = E.card := by rw [hTimage]
    change (∑ i ∈ (Finset.univ : Finset (Fin s)),
      if i.1 ∈ E then F base else 0) = E.card * F base
    rw [← Finset.sum_filter]
    change (∑ _i ∈ T, F base) = E.card * F base
    simp [hTcard]
  have hanchorSum : (∑ i : IntervalFullHallSlot s base, F (anchor i)) =
      s * F base + ∑ a ∈ (Finset.range s).erase base, F a := by
    simp only [Fintype.sum_sum_type, anchor, intervalFullHallAnchor]
    have hleft : (∑ _i : Fin s, F base) = s * F base := by simp
    rw [hleft]
    rw [Finset.sum_subtype (p := fun a => a ∈ (Finset.range s).erase base)
      (s := (Finset.range s).erase base) (by simp) F]
  have hXcard : X.card = F base +
      ∑ a ∈ (Finset.range s).erase base, F a := by
    rw [card_eq_sum_card_coordinateFiber X, hsupport]
    rw [add_comm]
    exact (Finset.sum_erase_add (Finset.range s) F
      (Finset.mem_range.mpr hbaseLt)).symm
  calc
    X.card + (s + E.card - 1) * (coordinateFiber X base).card =
        (∑ i : IntervalFullHallSlot s base,
          (F (anchor i) + bonus i)) := by
      rw [Finset.sum_add_distrib, hanchorSum, hbonus, hXcard]
      dsimp only [F]
      have hsE : s + E.card - 1 = (s - 1) + E.card := by omega
      have hs' : s = (s - 1) + 1 := by omega
      rw [hsE]
      nlinarith
    _ ≤ ∑ i : IntervalFullHallSlot s base,
        (coordinateFiber X (anchor i) + coordinateFiber X (choice i)).card :=
      hslotSum
    _ = ∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := hslotToP
    _ ≤ (X + X).card := hPsum


/-- Complete exceptional `R = 2` subgroup-existence branch.  When the
integer support is an interval, one of its fibres occupies more than two
thirds of a subgroup coset. -/
theorem exists_dense_fiber_coset_of_interval_support
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {n : ℕ}
    (hn : 3 ≤ n)
    (hsupport : firstCoordinateSet X = Finset.range n)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let w : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  obtain ⟨P, hPcard, hPbound, hPinj, hPweight⟩ :=
    exists_weighted_intervalPairSelection w hn
  by_contra hno
  push Not at hno
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    have hb := hPbound p hp
    rw [hsupport]
    exact ⟨Finset.mem_range.mpr hb.1, Finset.mem_range.mpr hb.2⟩
  have hpoint : ∀ p ∈ P,
      pairWeight (w p.1) (w p.2) ≤
        2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    intro p hp
    have hpM := hPmem p hp
    have hleft : (coordinateFiber X p.1).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.1
    have hright : (coordinateFiber X p.2).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.2
    rcases dense_coset_or_pairWeight_le hleft hright with hbad | hgood
    · obtain ⟨H, hbad | hbad⟩ := hbad
      · have hnot := hno p.1 hpM.1 H hbad.1
        omega
      · have hnot := hno p.2 hpM.2 H hbad.1
        omega
    · simpa [w] using hgood
  have hweightSum :
      (∑ p ∈ P, pairWeight (w p.1) (w p.2)) ≤
        2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    calc
      (∑ p ∈ P, pairWeight (w p.1) (w p.2)) ≤
          ∑ p ∈ P,
            2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card :=
        Finset.sum_le_sum hpoint
      _ = 2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
        rw [Finset.mul_sum]
  have hpairSum :
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hXcard : X.card = ∑ i ∈ Finset.range n, w i := by
    rw [card_eq_sum_card_coordinateFiber X, hsupport]
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hPweight.trans (hweightSum.trans
      (Nat.mul_le_mul_left 2 hpairSum))
  omega

theorem exists_dense_fiber_coset_of_R_eq_two
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hR2 : min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card = 2)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let s := A.card
  let M := A.max' hA
  have hs : 6 ≤ s := by simpa [s, A] using hAcard
  have hAmax : s ≤ M + 1 := by
    have hsub : A ⊆ Finset.range (M + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    simpa [s, M] using Finset.card_le_card hsub
  have htwoLeft : 2 ≤ M + 3 - s := by
    have hmin := Nat.min_le_left (M + 3 - s) s
    simpa [A, M, s, hR2] using hmin
  have hleftTwo : M + 3 - s ≤ 2 := by
    by_contra hnot
    have htwoS : 2 < s := by omega
    have htwoL : 2 < M + 3 - s := Nat.lt_of_not_ge hnot
    have := lt_min htwoL htwoS
    rw [show min (M + 3 - s) s = 2 by simpa [A, M, s] using hR2] at this
    omega
  have hMs : M + 1 = s := by omega
  have hsupport : A = Finset.range s := by
    have hsub : A ⊆ Finset.range s := by
      intro a ha
      rw [← hMs]
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    apply Finset.eq_of_subset_of_card_le hsub
    simp [s]
  apply exists_dense_fiber_coset_of_interval_support X (n := s) (by omega)
  · simpa [A] using hsupport
  · exact hsmall

def shiftPair (k : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + k, p.2 + k)

lemma shiftPair_injective (k : ℕ) : Function.Injective (shiftPair k) := by
  intro p q hpq
  apply Prod.ext <;> have := congrArg (fun z => z.1) hpq <;>
    have := congrArg (fun z => z.2) hpq <;>
    simp only [shiftPair] at * <;> omega

/-- Translation of the weighted interval selection to an arbitrary interval
of indices. -/
theorem exists_shifted_weighted_intervalPairSelection
    (w : ℕ → ℕ) (k : ℕ) {n : ℕ} (hn : 3 ≤ n) :
    ∃ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, k ≤ p.1 ∧ p.1 < k + n ∧
        k ≤ p.2 ∧ p.2 < k + n) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
      5 * ∑ i ∈ Finset.range n, w (i + k) ≤
        ∑ p ∈ P, pairWeight (w p.1) (w p.2) := by
  let wk : ℕ → ℕ := fun i ↦ w (i + k)
  obtain ⟨P, _hPcard, hPbound, hPinj, hPweight⟩ :=
    exists_weighted_intervalPairSelection wk hn
  let Q := P.image (shiftPair k)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hb := hPbound p hp
    dsimp [shiftPair]
    omega
  · intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    change (a.1 + k) + (a.2 + k) = (b.1 + k) + (b.2 + k) at hpq
    have habSum : a.1 + a.2 = b.1 + b.2 := by omega
    have hab : a = b := hPinj ha hb habSum
    subst b
    rfl
  · calc
      5 * ∑ i ∈ Finset.range n, w (i + k) =
          5 * ∑ i ∈ Finset.range n, wk i := by rfl
      _ ≤ ∑ p ∈ P, pairWeight (wk p.1) (wk p.2) := hPweight
      _ = ∑ q ∈ Q, pairWeight (w q.1) (w q.2) := by
        dsimp [Q]
        rw [Finset.sum_image]
        · rfl
        · exact (shiftPair_injective k).injOn

/-- Two occupied intervals separated by one missing index admit compatible
sharp-weight selections: their antidiagonal-sum ranges are disjoint. -/
theorem exists_weighted_twoIntervalsPairSelection
    (w : ℕ → ℕ) {h r : ℕ} (hh : 3 ≤ h) (hr : 3 ≤ r) :
    ∃ P : Finset (ℕ × ℕ),
      (∀ p ∈ P,
        (p.1 < h ∧ p.2 < h) ∨
        (h + 1 ≤ p.1 ∧ p.1 < h + 1 + r ∧
          h + 1 ≤ p.2 ∧ p.2 < h + 1 + r)) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
      5 * ((∑ i ∈ Finset.range h, w i) +
        ∑ i ∈ Finset.range r, w (i + (h + 1))) ≤
        ∑ p ∈ P, pairWeight (w p.1) (w p.2) := by
  obtain ⟨L, hLbound, hLinj, hLweight⟩ :=
    exists_shifted_weighted_intervalPairSelection w 0 hh
  obtain ⟨R, hRbound, hRinj, hRweight⟩ :=
    exists_shifted_weighted_intervalPairSelection w (h + 1) hr
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p hpL hpR
    have hlb := hLbound p hpL
    have hrb := hRbound p hpR
    omega
  refine ⟨L ∪ R, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hpL | hpR
    · left
      have hb := hLbound p hpL
      omega
    · right
      exact hRbound p hpR
  · intro p hp q hq hpq
    rcases Finset.mem_union.mp hp with hpL | hpR <;>
      rcases Finset.mem_union.mp hq with hqL | hqR
    · exact hLinj hpL hqL hpq
    · have hpb := hLbound p hpL
      have hqb := hRbound q hqR
      have hlt : p.1 + p.2 < q.1 + q.2 := by omega
      exact False.elim ((Nat.ne_of_lt hlt) hpq)
    · have hpb := hRbound p hpR
      have hqb := hLbound q hqL
      have hlt : q.1 + q.2 < p.1 + p.2 := by omega
      exact False.elim ((Nat.ne_of_lt hlt) hpq.symm)
    · exact hRinj hpR hqR hpq
  · rw [Finset.sum_union hdisj]
    have hadd := Nat.add_le_add hLweight hRweight
    simpa [Nat.mul_add, add_assoc] using hadd

/-- Sharp-weight selection for `[0,s]` with one internal index omitted. -/
theorem exists_weighted_oneHolePairSelection
    (w : ℕ → ℕ) {s h : ℕ} (hs : 5 ≤ s) (hhpos : 0 < h) (hhs : h < s) :
    ∃ P : Finset (ℕ × ℕ),
      (∀ p ∈ P,
        p.1 ≤ s ∧ p.1 ≠ h ∧ p.2 ≤ s ∧ p.2 ≠ h) ∧
      Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) P ∧
      5 * ((∑ i ∈ Finset.range h, w i) +
        ∑ i ∈ Finset.range (s - h), w (i + (h + 1))) ≤
        ∑ p ∈ P, pairWeight (w p.1) (w p.2) := by
  classical
  by_cases hh1 : h = 1
  · subst h
    have hr : 3 ≤ s - 1 := by omega
    obtain ⟨R, hRbound, hRinj, hRweight⟩ :=
      exists_shifted_weighted_intervalPairSelection w 2 hr
    let u : ℕ × ℕ := (0, 0)
    let v : ℕ × ℕ := (0, 2)
    let P : Finset (ℕ × ℕ) := insert u (insert v R)
    have huR : u ∉ R := by
      intro hu
      have hb := hRbound u hu
      dsimp [u] at hb
      omega
    have hvR : v ∉ R := by
      intro hv
      have hb := hRbound v hv
      dsimp [v] at hb
      omega
    have huv : u ≠ v := by decide
    refine ⟨P, ?_, ?_, ?_⟩
    · intro p hp
      change p ∈ insert u (insert v R) at hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · dsimp [u]
        omega
      · dsimp [v]
        omega
      · have hb := hRbound p hp
        omega
    · intro p hp q hq hpq
      change p ∈ insert u (insert v R) at hp
      change q ∈ insert u (insert v R) at hq
      simp only [Finset.mem_insert] at hp hq
      rcases hp with rfl | rfl | hp <;>
        rcases hq with rfl | rfl | hq
      · rfl
      · dsimp [u, v] at hpq
        omega
      · have hqb := hRbound q hq
        dsimp [u] at hpq
        omega
      · dsimp [u, v] at hpq
        omega
      · rfl
      · have hqb := hRbound q hq
        dsimp [v] at hpq
        omega
      · have hpb := hRbound p hp
        dsimp [u] at hpq
        omega
      · have hpb := hRbound p hp
        dsimp [v] at hpq
        omega
      · exact hRinj hp hq hpq
    · have huWeight := pairWeight_self (w 0)
      have hvWeight := two_mul_left_le_pairWeight (w 0) (w 2)
      have hboundary : 5 * w 0 ≤
          pairWeight (w 0) (w 0) + pairWeight (w 0) (w 2) := by omega
      have hadd := Nat.add_le_add hboundary hRweight
      dsimp [P]
      rw [Finset.sum_insert (by simp [huv, huR]),
        Finset.sum_insert hvR]
      dsimp [u, v]
      simpa [Finset.sum_range_succ, Nat.mul_add, add_assoc] using hadd
  · by_cases hh2 : h = 2
    · subst h
      have hr : 3 ≤ s - 2 := by omega
      obtain ⟨R, hRbound, hRinj, hRweight⟩ :=
        exists_shifted_weighted_intervalPairSelection w 3 hr
      let B : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (1, 1), (1, 3)}
      have hBR : Disjoint B R := by
        rw [Finset.disjoint_left]
        intro p hpB hpR
        have hrb := hRbound p hpR
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hpB
        rcases hpB with rfl | rfl | rfl | rfl <;> omega
      have hBinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) B := by
        decide
      have hBweight : 5 * (w 0 + w 1) ≤
          ∑ p ∈ B, pairWeight (w p.1) (w p.2) := by
        have h00 := pairWeight_self (w 0)
        have h11 := pairWeight_self (w 1)
        have h01 := two_mul_left_le_pairWeight (w 0) (w 1)
        have h13 := two_mul_left_le_pairWeight (w 1) (w 3)
        simp [B]
        omega
      refine ⟨B ∪ R, ?_, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_union.mp hp with hpB | hpR
        · simp only [B, Finset.mem_insert, Finset.mem_singleton] at hpB
          rcases hpB with rfl | rfl | rfl | rfl <;> omega
        · have hb := hRbound p hpR
          omega
      · intro p hp q hq hpq
        rcases Finset.mem_union.mp hp with hpB | hpR <;>
          rcases Finset.mem_union.mp hq with hqB | hqR
        · exact hBinj hpB hqB hpq
        · have hpb : p.1 + p.2 ≤ 4 := by
            simp only [B, Finset.mem_insert, Finset.mem_singleton] at hpB
            rcases hpB with rfl | rfl | rfl | rfl <;> omega
          have hqb := hRbound q hqR
          have hlt : p.1 + p.2 < q.1 + q.2 := by omega
          exact False.elim ((Nat.ne_of_lt hlt) hpq)
        · have hqb : q.1 + q.2 ≤ 4 := by
            simp only [B, Finset.mem_insert, Finset.mem_singleton] at hqB
            rcases hqB with rfl | rfl | rfl | rfl <;> omega
          have hpb := hRbound p hpR
          have hlt : q.1 + q.2 < p.1 + p.2 := by omega
          exact False.elim ((Nat.ne_of_lt hlt) hpq.symm)
        · exact hRinj hpR hqR hpq
      · rw [Finset.sum_union hBR]
        have hRweight' : 5 * ∑ i ∈ Finset.range (s - 2), w (i + 3) ≤
            ∑ p ∈ R, pairWeight (w p.1) (w p.2) := by
          simpa using hRweight
        have hadd := Nat.add_le_add hBweight hRweight'
        simpa [Finset.sum_range_succ, Nat.mul_add, add_assoc] using hadd
    · have hh3 : 3 ≤ h := by omega
      by_cases hr1 : s - h = 1
      · have hEq : h = s - 1 := by omega
        obtain ⟨L, hLbound, hLinj, hLweight⟩ :=
          exists_shifted_weighted_intervalPairSelection w 0 hh3
        let u : ℕ × ℕ := (s, s)
        let v : ℕ × ℕ := (s - 2, s)
        let P : Finset (ℕ × ℕ) := insert u (insert v L)
        have huL : u ∉ L := by
          intro hu
          have hb := hLbound u hu
          dsimp [u] at hb
          omega
        have hvL : v ∉ L := by
          intro hv
          have hb := hLbound v hv
          dsimp [v] at hb
          omega
        have huv : u ≠ v := by
          intro huv
          have := congrArg Prod.fst huv
          dsimp [u, v] at this
          omega
        refine ⟨P, ?_, ?_, ?_⟩
        · intro p hp
          change p ∈ insert u (insert v L) at hp
          simp only [Finset.mem_insert] at hp
          rcases hp with rfl | rfl | hp
          · dsimp [u]
            omega
          · dsimp [v]
            omega
          · have hb := hLbound p hp
            omega
        · intro p hp q hq hpq
          change p ∈ insert u (insert v L) at hp
          change q ∈ insert u (insert v L) at hq
          simp only [Finset.mem_insert] at hp hq
          rcases hp with rfl | rfl | hp <;>
            rcases hq with rfl | rfl | hq
          · rfl
          · dsimp [u, v] at hpq
            omega
          · have hqb := hLbound q hq
            dsimp [u] at hpq
            omega
          · dsimp [u, v] at hpq
            omega
          · rfl
          · have hqb := hLbound q hq
            dsimp [v] at hpq
            omega
          · have hpb := hLbound p hp
            dsimp [u] at hpq
            omega
          · have hpb := hLbound p hp
            dsimp [v] at hpq
            omega
          · exact hLinj hp hq hpq
        · have huWeight := pairWeight_self (w s)
          have hvWeight := two_mul_right_le_pairWeight (w (s - 2)) (w s)
          have hboundary : 5 * w s ≤
              pairWeight (w s) (w s) +
                pairWeight (w (s - 2)) (w s) := by omega
          have hLweight' : 5 * ∑ i ∈ Finset.range h, w i ≤
              ∑ p ∈ L, pairWeight (w p.1) (w p.2) := by
            simpa using hLweight
          have hadd := Nat.add_le_add hLweight' hboundary
          dsimp [P]
          rw [Finset.sum_insert (by simp [huv, huL]),
            Finset.sum_insert hvL]
          dsimp [u, v]
          rw [hr1]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          have hsIndex : h + 1 = s := by omega
          simp only [hsIndex]
          simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hadd
      · by_cases hr2 : s - h = 2
        · have hEq : h = s - 2 := by omega
          obtain ⟨L, hLbound, hLinj, hLweight⟩ :=
            exists_shifted_weighted_intervalPairSelection w 0 hh3
          let bpair : Fin 4 → ℕ × ℕ := ![
            (s - 1, s - 1), (s - 1, s), (s, s), (s - 3, s - 1)]
          let B : Finset (ℕ × ℕ) := Finset.univ.image bpair
          have hbpair : Function.Injective bpair := by
            intro i j hij
            fin_cases i <;> fin_cases j <;>
              simp [bpair] at hij ⊢ <;> omega
          have hBL : Disjoint B L := by
            rw [Finset.disjoint_left]
            intro p hpB hpL
            have hlb := hLbound p hpL
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hpB
            fin_cases i <;>
              simp [bpair] at hlb ⊢ <;> omega
          have hBinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) B := by
            intro p hp q hq hpq
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
            fin_cases i <;> fin_cases j <;>
              simp [bpair] at hpq ⊢ <;> omega
          have hBweight : 5 * (w (s - 1) + w s) ≤
              ∑ p ∈ B, pairWeight (w p.1) (w p.2) := by
            have haa := pairWeight_self (w (s - 1))
            have hbb := pairWeight_self (w s)
            have hab := two_mul_right_le_pairWeight (w (s - 1)) (w s)
            have hca := two_mul_right_le_pairWeight (w (s - 3)) (w (s - 1))
            dsimp [B]
            rw [Finset.sum_image hbpair.injOn]
            simp [Fin.sum_univ_succ, bpair]
            omega
          refine ⟨B ∪ L, ?_, ?_, ?_⟩
          · intro p hp
            rcases Finset.mem_union.mp hp with hpB | hpL
            · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hpB
              fin_cases i <;>
                simp [bpair] <;> omega
            · have hb := hLbound p hpL
              omega
          · intro p hp q hq hpq
            rcases Finset.mem_union.mp hp with hpB | hpL <;>
              rcases Finset.mem_union.mp hq with hqB | hqL
            · exact hBinj hpB hqB hpq
            · have hpsum : 2 * s - 4 ≤ p.1 + p.2 := by
                obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hpB
                fin_cases i <;>
                  simp [bpair] <;> omega
              have hqb := hLbound q hqL
              have hlt : q.1 + q.2 < p.1 + p.2 := by omega
              exact False.elim ((Nat.ne_of_lt hlt) hpq.symm)
            · have hqsum : 2 * s - 4 ≤ q.1 + q.2 := by
                obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hqB
                fin_cases i <;>
                  simp [bpair] <;> omega
              have hpb := hLbound p hpL
              have hlt : p.1 + p.2 < q.1 + q.2 := by omega
              exact False.elim ((Nat.ne_of_lt hlt) hpq)
            · exact hLinj hpL hqL hpq
          · rw [Finset.sum_union hBL]
            have hLweight' : 5 * ∑ i ∈ Finset.range h, w i ≤
                ∑ p ∈ L, pairWeight (w p.1) (w p.2) := by
              simpa using hLweight
            have hadd := Nat.add_le_add hLweight' hBweight
            rw [hr2]
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
            have hfirst : h + 1 = s - 1 := by omega
            simp only [hfirst]
            have hsecond : 1 + (s - 1) = s := by omega
            simp only [hsecond]
            simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hadd
        · have hr3 : 3 ≤ s - h := by omega
          obtain ⟨P, hPbound, hPinj, hPweight⟩ :=
            exists_weighted_twoIntervalsPairSelection w hh3 hr3
          refine ⟨P, ?_, hPinj, hPweight⟩
          intro p hp
          rcases hPbound p hp with hpL | hpR
          · omega
          · omega

/-- Complete exceptional subgroup-existence argument when the integer
support is `[0,s]` with one internal point deleted. -/
theorem exists_dense_fiber_coset_of_oneHole_support
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {s h : ℕ}
    (hs : 5 ≤ s) (hhpos : 0 < h) (hhs : h < s)
    (hsupport : firstCoordinateSet X = (Finset.range (s + 1)).erase h)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let w : ℕ → ℕ := fun a ↦ (coordinateFiber X a).card
  obtain ⟨P, hPbound, hPinj, hPweight⟩ :=
    exists_weighted_oneHolePairSelection w hs hhpos hhs
  by_contra hno
  push Not at hno
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    have hb := hPbound p hp
    rw [hsupport]
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hpoint : ∀ p ∈ P,
      pairWeight (w p.1) (w p.2) ≤
        2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    intro p hp
    have hpM := hPmem p hp
    have hleft : (coordinateFiber X p.1).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.1
    have hright : (coordinateFiber X p.2).Nonempty :=
      coordinateFiber_nonempty_iff.mpr hpM.2
    rcases dense_coset_or_pairWeight_le hleft hright with hbad | hgood
    · obtain ⟨H, hbad | hbad⟩ := hbad
      · have hnot := hno p.1 hpM.1 H hbad.1
        omega
      · have hnot := hno p.2 hpM.2 H hbad.1
        omega
    · simpa [w] using hgood
  have hweightSum :
      (∑ p ∈ P, pairWeight (w p.1) (w p.2)) ≤
        2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    calc
      (∑ p ∈ P, pairWeight (w p.1) (w p.2)) ≤
          ∑ p ∈ P,
            2 * (coordinateFiber X p.1 + coordinateFiber X p.2).card :=
        Finset.sum_le_sum hpoint
      _ = 2 * ∑ p ∈ P,
          (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
        rw [Finset.mul_sum]
  have hpairSum :
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card ≤
        (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hsumSupport :
      ∑ i ∈ (Finset.range (s + 1)).erase h, w i =
        (∑ i ∈ Finset.range h, w i) +
          ∑ i ∈ Finset.range (s - h), w (i + (h + 1)) := by
    have hhmem : h ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
    have herase := Finset.sum_erase_add (Finset.range (s + 1)) w hhmem
    have htotal :
        ∑ i ∈ Finset.range (s + 1), w i =
          ((∑ i ∈ Finset.range h, w i) + w h) +
            ∑ i ∈ Finset.range (s - h), w (i + (h + 1)) := by
      calc
        ∑ i ∈ Finset.range (s + 1), w i =
            ∑ i ∈ Finset.range ((h + 1) + (s - h)), w i := by
          congr 2 <;> omega
        _ = (∑ i ∈ Finset.range (h + 1), w i) +
              ∑ i ∈ Finset.range (s - h), w ((h + 1) + i) :=
          Finset.sum_range_add w (h + 1) (s - h)
        _ = ((∑ i ∈ Finset.range h, w i) + w h) +
              ∑ i ∈ Finset.range (s - h), w (i + (h + 1)) := by
          rw [Finset.sum_range_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [add_comm]
    omega
  have hXcard : X.card =
      (∑ i ∈ Finset.range h, w i) +
        ∑ i ∈ Finset.range (s - h), w (i + (h + 1)) := by
    rw [card_eq_sum_card_coordinateFiber X, hsupport, hsumSupport]
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hPweight.trans (hweightSum.trans
      (Nat.mul_le_mul_left 2 hpairSum))
  omega

/-- Complete exceptional `R = 3` subgroup-existence branch.  The occupied
integer support has size `s`, maximum `s`, contains zero, and hence is
`[0,s]` with one nonzero, nonterminal point deleted. -/
theorem exists_dense_fiber_coset_of_R_eq_three
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hR3 : min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card = 3)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let s := A.card
  let M := A.max' hA
  have hs : 6 ≤ s := by simpa [s, A] using hAcard
  have hAmax : s ≤ M + 1 := by
    have hsub : A ⊆ Finset.range (M + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    simpa [s, M] using Finset.card_le_card hsub
  have hthreeLeft : 3 ≤ M + 3 - s := by
    have hmin := Nat.min_le_left (M + 3 - s) s
    rw [show min (M + 3 - s) s = 3 by simpa [A, M, s] using hR3] at hmin
    exact hmin
  have hleftThree : M + 3 - s ≤ 3 := by
    by_contra hnot
    have hthreeS : 3 < s := by omega
    have hthreeL : 3 < M + 3 - s := Nat.lt_of_not_ge hnot
    have := lt_min hthreeL hthreeS
    rw [show min (M + 3 - s) s = 3 by simpa [A, M, s] using hR3] at this
    omega
  have hMs : M = s := by omega
  have hsub : A ⊆ Finset.range (s + 1) := by
    intro a ha
    exact Finset.mem_range.mpr (by
      have := A.le_max' a ha
      omega)
  have hdiffcard : (Finset.range (s + 1) \ A).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    simp only [Finset.card_range]
    simp only [s]
    omega
  obtain ⟨h, hdiff⟩ := Finset.card_eq_one.mp hdiffcard
  have hhdiff : h ∈ Finset.range (s + 1) \ A := by
    rw [hdiff]
    simp
  have hhRange : h ∈ Finset.range (s + 1) :=
    (Finset.mem_sdiff.mp hhdiff).1
  have hhnotA : h ∉ A := (Finset.mem_sdiff.mp hhdiff).2
  have hsupport : A = (Finset.range (s + 1)).erase h := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_erase]
      refine ⟨?_, hsub hx⟩
      intro hxh
      subst x
      exact hhnotA hx
    · intro hx
      rw [Finset.mem_erase] at hx
      by_contra hxA
      have hxin : x ∈ Finset.range (s + 1) \ A :=
        Finset.mem_sdiff.mpr ⟨hx.2, hxA⟩
      rw [hdiff] at hxin
      have : x = h := by simpa using hxin
      exact hx.1 this
  have hhpos : 0 < h := by
    by_contra hnot
    have hh0 : h = 0 := Nat.eq_zero_of_not_pos hnot
    apply hhnotA
    simpa [A, hh0] using hAzero
  have hhs : h < s := by
    have hhLe : h ≤ s := by
      simpa [Finset.mem_range] using hhRange
    have hMmem : M ∈ A := A.max'_mem hA
    have hsA : s ∈ A := by simpa [hMs] using hMmem
    have hhne : h ≠ s := by
      intro heq
      apply hhnotA
      simpa [heq] using hsA
    omega
  apply exists_dense_fiber_coset_of_oneHole_support X (by omega) hhpos hhs
  · simpa [A] using hsupport
  · exact hsmall

/-- The complete subgroup-existence half of the finite fibre theorem,
including the interval (`R = 2`), one-hole (`R = 3`), and Hall-weighted
(`R ≥ 4`) regimes. -/
theorem exists_dense_fiber_coset_of_small_doubling
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ a ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X a) ∧
        2 * Nat.card H < 3 * (coordinateFiber X a).card := by
  classical
  let A := firstCoordinateSet X
  let R := min (A.max' hA + 3 - A.card) A.card
  have hAmax : A.card ≤ A.max' hA + 1 := by
    have hsub : A ⊆ Finset.range (A.max' hA + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (by
        have := A.le_max' a ha
        omega)
    simpa using Finset.card_le_card hsub
  have hRge : 2 ≤ R := by
    apply Nat.le_min.mpr
    constructor
    · omega
    · have : 6 ≤ A.card := by simpa [A] using hAcard
      omega
  by_cases hR2 : R = 2
  · apply exists_dense_fiber_coset_of_R_eq_two X hA hAcard
    · simpa [R, A] using hR2
    · exact hsmall
  by_cases hR3 : R = 3
  · apply exists_dense_fiber_coset_of_R_eq_three X hA hAzero hAcard
    · simpa [R, A] using hR3
    · exact hsmall
  have hR4 : 4 ≤ R := by omega
  obtain ⟨base, hbase, hbaseMax⟩ :=
    Finset.exists_max_image A (fun a ↦ (coordinateFiber X a).card) hA
  obtain ⟨H, hHcoset, hHcard⟩ :=
    exists_small_largestFiber_coset_of_four_le_R X hA hAzero hAcard hgcd
      hbase hbaseMax (by simpa [R, A] using hR4) hsmall
  exact ⟨base, by simpa [A] using hbase, H, hHcoset, hHcard⟩

theorem all_fibers_contained_of_four_le_R
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card)
    {base : ℕ} (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hR4 : 4 ≤ min ((firstCoordinateSet X).max' hA + 3 -
      (firstCoordinateSet X).card) (firstCoordinateSet X).card) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let s := A.card
  let M := F base
  let R := min (A.max' hA + 3 - A.card) A.card
  let k := R - 1
  let E := A.filter fun a => ¬ContainedInAddCoset H (coordinateFiber X a)
  have hEA : E ⊆ A := Finset.filter_subset _ _
  have hEbad : ∀ a ∈ E,
      ¬ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hbaseNot : base ∉ E := by
    intro hb
    exact hEbad base hb hbaseCos
  have hGoodCos : ∀ a ∈ A \ E,
      ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha
    by_contra hnot
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hnot⟩)
  intro a haA
  by_contra haBad
  have haE : a ∈ E := Finset.mem_filter.mpr ⟨haA, haBad⟩
  have hEne : E.Nonempty := ⟨a, haE⟩
  obtain ⟨badBase, hbadBase, hbadMax⟩ :=
    Finset.exists_max_image E F hEne
  obtain ⟨D, hDA, hDbase, hDcard, hDle, havg⟩ :=
    exists_weighted_distinguishedLayerSet X hA hbase
  obtain ⟨D₂, hD₂A, hD₂base, hD₂card, hD₂le, havg₂⟩ :=
    exists_weighted_distinguishedLayerSet X hA (hEA hbadBase)
  have hR4' : 4 ≤ R := by simpa [R, A] using hR4
  have hk3 : 3 ≤ k := by dsimp only [k]; omega
  have hDpos : 1 ≤ D.card := by
    rw [hDcard]
    change 1 ≤ R - 1
    omega
  have havgForEscape : D.card *
        (∑ a ∈ (firstCoordinateSet X).erase base,
          (coordinateFiber X a).card) ≤
      ((firstCoordinateSet X).card - 1) *
        ∑ a ∈ D, (coordinateFiber X a).card := by
    rw [hDcard]
    exact havg
  have hescape : 2 * (E.card + D.card) < A.card + 4 :=
    layerHall_escape_count_bound X hA hAzero (by omega) hgcd hbase
      hbaseMax hbaseCos hEA hEbad hDA hDbase hDle hDpos havgForEscape hsmall
  have hfirstRaw := layerHall_escape_fiber_lower X hA hAzero (by omega)
    hgcd hbase hbaseMax hbaseCos hEA hEbad hDA hDbase hDle
  have hsecondRaw := reordered_layerHall_fiber_lower X hA hAzero (by omega)
    hgcd hbase hbaseNot hbaseMax hEA hGoodCos hbadBase
    (hEbad badBase hbadBase) hD₂A hD₂base hD₂le
  let N := F badBase
  let P := ∑ a ∈ A.erase base, F a
  let Q := ∑ a ∈ D, F a
  let G := ∑ a ∈ (A \ E).erase base, F a
  let B := ∑ a ∈ E.erase badBase, F a
  let Q₂ := ∑ a ∈ D₂, F a
  let Z := (X + X).card
  have hXcard : X.card = M + P := by
    rw [card_eq_sum_card_coordinateFiber X]
    dsimp only [A, F, M, P]
    rw [add_comm]
    exact (Finset.sum_erase_add (firstCoordinateSet X)
      (fun a => (coordinateFiber X a).card) hbase).symm
  have hgoodBase : base ∈ A \ E := Finset.mem_sdiff.mpr ⟨hbase, hbaseNot⟩
  have hgoodSplit : ∑ a ∈ A \ E, F a = M + G := by
    dsimp only [M, G]
    rw [add_comm]
    exact (Finset.sum_erase_add (A \ E) F hgoodBase).symm
  have hbadSplit : ∑ a ∈ E, F a = N + B := by
    dsimp only [N, B]
    rw [add_comm]
    exact (Finset.sum_erase_add E F hbadBase).symm
  have hpartition : (A \ E) ∪ E = A := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hz
      rcases hz with ⟨hz, _⟩ | hz
      · exact hz
      · exact hEA hz
    · intro hz
      by_cases hzE : z ∈ E
      · exact Or.inr hzE
      · exact Or.inl ⟨hz, hzE⟩
  have hdisj : Disjoint (A \ E) E := by
    rw [Finset.disjoint_left]
    intro z hzG hzE
    exact (Finset.mem_sdiff.mp hzG).2 hzE
  have hXcard₂ : X.card = M + G + N + B := by
    rw [card_eq_sum_card_coordinateFiber X]
    have hsum : ∑ z ∈ A, F z =
        (∑ z ∈ A \ E, F z) + ∑ z ∈ E, F z := by
      calc
        ∑ z ∈ A, F z = ∑ z ∈ (A \ E) ∪ E, F z := by rw [hpartition]
        _ = (∑ z ∈ A \ E, F z) + ∑ z ∈ E, F z :=
          Finset.sum_union hdisj
    rw [hsum, hgoodSplit, hbadSplit]
    omega
  have hX : M + P = M + G + N + B := by omega
  have hN : N ≤ M := hbaseMax badBase (hEA hbadBase)
  have hGoodCard : ((A \ E).erase base).card = s - E.card - 1 := by
    rw [Finset.card_erase_of_mem hgoodBase,
      Finset.card_sdiff_of_subset hEA]
  have hG : G ≤ (s - E.card - 1) * M := by
    dsimp only [G]
    calc
      ∑ z ∈ (A \ E).erase base, F z ≤
          ∑ _z ∈ (A \ E).erase base, M := by
        apply Finset.sum_le_sum
        intro z hz
        exact hbaseMax z (Finset.mem_sdiff.mp
          (Finset.mem_of_mem_erase hz)).1
      _ = ((A \ E).erase base).card * M := by simp
      _ = (s - E.card - 1) * M := by rw [hGoodCard]
  have hBadCard : (E.erase badBase).card = E.card - 1 :=
    Finset.card_erase_of_mem hbadBase
  have hB : B ≤ (E.card - 1) * N := by
    dsimp only [B]
    calc
      ∑ z ∈ E.erase badBase, F z ≤ ∑ _z ∈ E.erase badBase, N := by
        apply Finset.sum_le_sum
        intro z hz
        exact hbadMax z (Finset.mem_of_mem_erase hz)
      _ = (E.erase badBase).card * N := by simp
      _ = (E.card - 1) * N := by rw [hBadCard]
  have hP : P ≤ (s - 1) * M := by
    dsimp only [P]
    calc
      ∑ z ∈ A.erase base, F z ≤ ∑ _z ∈ A.erase base, M := by
        apply Finset.sum_le_sum
        intro z hz
        exact hbaseMax z (Finset.mem_of_mem_erase hz)
      _ = (A.erase base).card * M := by simp
      _ = (s - 1) * M := by
        rw [Finset.card_erase_of_mem hbase]
  have havg' : k * P ≤ (s - 1) * Q := by
    simpa [A, F, s, R, k, P, Q] using havg
  have havg₂' : k * (M + G + B) ≤ (s - 1) * Q₂ := by
    have hrest : ∑ z ∈ A.erase badBase, F z = M + G + B := by
      have hbadX : X.card = N + ∑ z ∈ A.erase badBase, F z := by
        rw [card_eq_sum_card_coordinateFiber X]
        rw [add_comm]
        exact (Finset.sum_erase_add A F (hEA hbadBase)).symm
      omega
    have havg₂'' : k * (∑ z ∈ A.erase badBase, F z) ≤
        (s - 1) * ∑ z ∈ D₂, F z := by
      simpa [A, F, s, R, k, Finset.card_erase_of_mem (hEA hbadBase)] using
        havg₂
    simpa [hrest, Q₂] using havg₂''
  have hfirst : M + P + ((s + E.card - 2) * M + Q) ≤ Z := by
    dsimp only [A, F, s, M, P, Q, Z] at hfirstRaw ⊢
    have hcoeff : (firstCoordinateSet X).card + E.card - 2 =
        E.card + ((firstCoordinateSet X).card - 2) := by omega
    calc
      (coordinateFiber X base).card +
            (∑ a ∈ (firstCoordinateSet X).erase base,
              (coordinateFiber X a).card) +
          (((firstCoordinateSet X).card + E.card - 2) *
              (coordinateFiber X base).card +
            ∑ a ∈ D, (coordinateFiber X a).card) =
        E.card * (coordinateFiber X base).card +
            ((firstCoordinateSet X).card - 2) *
              (coordinateFiber X base).card +
            ∑ a ∈ D, (coordinateFiber X a).card + X.card := by
          rw [hcoeff, hXcard]
          ring
      _ ≤ (X + X).card := hfirstRaw
  have hsecond : M + P + ((E.card - 1) * N + 2 * G + Q₂) ≤ Z := by
    dsimp only [A, F, M, N, P, G, Q₂, Z] at hsecondRaw ⊢
    have hbadX : X.card = (coordinateFiber X badBase).card +
        ∑ z ∈ (firstCoordinateSet X).erase badBase,
          (coordinateFiber X z).card := by
      rw [card_eq_sum_card_coordinateFiber X]
      rw [add_comm]
      exact (Finset.sum_erase_add (firstCoordinateSet X)
        (fun z => (coordinateFiber X z).card) (hEA hbadBase)).symm
    have hecoeff : E.card = (E.card - 1) + 1 := by
      have := Finset.card_pos.mpr hEne
      omega
    calc
      (coordinateFiber X base).card +
            (∑ a ∈ (firstCoordinateSet X).erase base,
              (coordinateFiber X a).card) +
          ((E.card - 1) * (coordinateFiber X badBase).card +
            2 * ∑ a ∈ (firstCoordinateSet X \ E).erase base,
                (coordinateFiber X a).card +
            ∑ a ∈ D₂, (coordinateFiber X a).card) =
        E.card * (coordinateFiber X badBase).card +
            2 * ∑ a ∈ (firstCoordinateSet X \ E).erase base,
              (coordinateFiber X a).card +
            ∑ a ∈ (firstCoordinateSet X).erase badBase,
              (coordinateFiber X a).card +
            ∑ a ∈ D₂, (coordinateFiber X a).card := by
          rw [← hXcard, hbadX, hecoeff]
          have hcoeff' : E.card - 1 + 1 - 1 = E.card - 1 := by omega
          have hcoeff'' : E.card - 1 + 1 = E.card := by omega
          rw [hcoeff', hcoeff'']
          have hmul : (coordinateFiber X badBase).card +
                (coordinateFiber X badBase).card * (E.card - 1) =
              (coordinateFiber X badBase).card * E.card := by
            calc
              (coordinateFiber X badBase).card +
                    (coordinateFiber X badBase).card * (E.card - 1) =
                  (coordinateFiber X badBase).card *
                    ((E.card - 1) + 1) := by ring
              _ = (coordinateFiber X badBase).card * E.card := by
                rw [hcoeff'']
          rw [Nat.mul_comm (E.card - 1) (coordinateFiber X badBase).card,
            Nat.mul_comm E.card (coordinateFiber X badBase).card]
          omega
      _ ≤ (X + X).card := hsecondRaw
  have hks : k ≤ s - 1 := by
    have hRle : R ≤ s := by
      dsimp only [R, s, A]
      exact Nat.min_le_right _ _
    dsimp only [k]
    omega
  have hsmall' : 2 * Z < 5 * (M + P) := by
    dsimp only [Z]
    rw [← hXcard]
    exact hsmall
  exact False.elim (reordered_hall_average_contradiction
    (s := s) (e := E.card) (k := k) (M := M) (N := N)
    (P := P) (Q := Q) (G := G) (B := B) (Q₂ := Q₂) (Z := Z)
    (by simpa [s, A] using hAcard) (Finset.card_pos.mpr hEne) hk3 hks
    (by rw [hDcard] at hescape; simpa [A, R, k] using hescape)
    hP havg' hX hN hG hB havg₂' hfirst hsecond hsmall')


/-! ## A coprime tuning prime

Five disjoint Bertrand intervals suffice to find a prime not dividing `n`
once their common lower scale has fifth power larger than `n`.  This replaces
the short-interval prime-number-theorem step in the paper by a coarser but
constant-factor construction. -/

lemma exists_bertrandPrime_not_dvd {a n : ℕ} (ha : 1 ≤ a)
    (hn : 0 < n) (hnsmall : n < a ^ 5) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ 32 * a ∧ ¬p ∣ n := by
  obtain ⟨p₁, hp₁, hp₁lo, hp₁hi⟩ := Nat.bertrand a (by omega)
  obtain ⟨p₂, hp₂, hp₂lo, hp₂hi⟩ := Nat.bertrand (2 * a) (by omega)
  obtain ⟨p₃, hp₃, hp₃lo, hp₃hi⟩ := Nat.bertrand (4 * a) (by omega)
  obtain ⟨p₄, hp₄, hp₄lo, hp₄hi⟩ := Nat.bertrand (8 * a) (by omega)
  obtain ⟨p₅, hp₅, hp₅lo, hp₅hi⟩ := Nat.bertrand (16 * a) (by omega)
  by_contra hnone
  push Not at hnone
  have h₁ := hnone p₁ hp₁ (by omega) (by omega)
  have h₂ := hnone p₂ hp₂ (by omega) (by omega)
  have h₃ := hnone p₃ hp₃ (by omega) (by omega)
  have h₄ := hnone p₄ hp₄ (by omega) (by omega)
  have h₅ := hnone p₅ hp₅ (by omega) (by omega)
  have hc₁₂ : Nat.Coprime p₁ p₂ :=
    (Nat.coprime_primes hp₁ hp₂).mpr (by omega)
  have hd₁₂ : p₁ * p₂ ∣ n := hc₁₂.mul_dvd_of_dvd_of_dvd h₁ h₂
  have hc₁₂₃ : Nat.Coprime (p₁ * p₂) p₃ :=
    (Nat.coprime_primes hp₁ hp₃).mpr (by omega) |>.mul_left
      ((Nat.coprime_primes hp₂ hp₃).mpr (by omega))
  have hd₁₂₃ : p₁ * p₂ * p₃ ∣ n :=
    hc₁₂₃.mul_dvd_of_dvd_of_dvd hd₁₂ h₃
  have hc₁₂₃₄ : Nat.Coprime (p₁ * p₂ * p₃) p₄ :=
    ((Nat.coprime_primes hp₁ hp₄).mpr (by omega) |>.mul_left
      ((Nat.coprime_primes hp₂ hp₄).mpr (by omega))).mul_left
        ((Nat.coprime_primes hp₃ hp₄).mpr (by omega))
  have hd₁₂₃₄ : p₁ * p₂ * p₃ * p₄ ∣ n :=
    hc₁₂₃₄.mul_dvd_of_dvd_of_dvd hd₁₂₃ h₄
  have hc₁₂₃₄₅ : Nat.Coprime (p₁ * p₂ * p₃ * p₄) p₅ :=
    (((Nat.coprime_primes hp₁ hp₅).mpr (by omega) |>.mul_left
      ((Nat.coprime_primes hp₂ hp₅).mpr (by omega))).mul_left
        ((Nat.coprime_primes hp₃ hp₅).mpr (by omega))).mul_left
          ((Nat.coprime_primes hp₄ hp₅).mpr (by omega))
  have hd : p₁ * p₂ * p₃ * p₄ * p₅ ∣ n :=
    hc₁₂₃₄₅.mul_dvd_of_dvd_of_dvd hd₁₂₃₄ h₅
  have hprodle : p₁ * p₂ * p₃ * p₄ * p₅ ≤ n := Nat.le_of_dvd hn hd
  have hprodgt : a ^ 5 < p₁ * p₂ * p₃ * p₄ * p₅ := by
    simp only [pow_succ, pow_zero]
    gcongr <;> omega
  omega

/-- The integral tuning scale used to enlarge the filtered small-prime
product. -/
def tuningBase (n h y : ℕ) : ℕ :=
  h / (missingPrimeProduct n y).totient + 1

/-- Finite modulus selector for the upper bound.  The modulus is the product
of the filtered prime product and one Bertrand prime.  It is coprime to the
target, lies within a fixed factor of `M * (h / φ(M) + 1)`, and has totient
at most a fixed multiple of `h`. -/
lemma exists_tuned_modulus {n h y : ℕ}
    (hn : 0 < n) (hh : 0 < h)
    (hphi : (missingPrimeProduct n y).totient ≤ h)
    (hy : y < tuningBase n h y)
    (hpow : n < tuningBase n h y ^ 5) :
    ∃ d : ℕ, 1 < d ∧ Nat.Coprime n d ∧
      missingPrimeProduct n y * tuningBase n h y < d ∧
      d ≤ 32 * missingPrimeProduct n y * tuningBase n h y ∧
      d.primeFactors.card ≤ y + 2 ∧
      d.totient ≤ 64 * h := by
  let M := missingPrimeProduct n y
  let a := tuningBase n h y
  have hM : 0 < M := by simpa [M] using missingPrimeProduct_pos n y
  have hphiM : 0 < M.totient := Nat.totient_pos.mpr hM
  have hphiM_le : M.totient ≤ h := by simpa [M] using hphi
  have ha : 1 ≤ a := by simp [a, tuningBase]
  obtain ⟨q, hqprime, haq, hqa, hqn⟩ :=
    exists_bertrandPrime_not_dvd ha hn hpow
  have hqM : ¬q ∣ M := by
    intro hqM
    have hqmem : q ∈ M.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hqM, hM.ne'⟩
    have hqmissing : q ∈ missingPrimesUpTo n y := by
      rw [show M.primeFactors = missingPrimesUpTo n y by
        simpa [M] using primeFactors_missingPrimeProduct n y] at hqmem
      exact hqmem
    have hqy : q ≤ y := (mem_missingPrimesUpTo.mp hqmissing).2.1
    omega
  have hcopMq : Nat.Coprime M q :=
    Nat.Coprime.symm (hqprime.coprime_iff_not_dvd.mpr hqM)
  have hcopMn : Nat.Coprime M n := by
    simpa [M] using missingPrimeProduct_coprime_target n y
  have hcopqn : Nat.Coprime q n := hqprime.coprime_iff_not_dvd.mpr hqn
  refine ⟨M * q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hq2 : 2 ≤ q := hqprime.two_le
    nlinarith
  · exact (hcopMn.mul_left hcopqn).symm
  · exact Nat.mul_lt_mul_of_pos_left haq hM
  · calc
      M * q ≤ M * (32 * a) := Nat.mul_le_mul_left M hqa
      _ = 32 * M * a := by ring
  · rw [Nat.primeFactors_mul hM.ne' hqprime.ne_zero,
      primeFactors_missingPrimeProduct]
    calc
      (missingPrimesUpTo n y ∪ q.primeFactors).card ≤
          (missingPrimesUpTo n y).card + q.primeFactors.card :=
        Finset.card_union_le _ _
      _ ≤ y + 2 := by
        have hmissing : missingPrimesUpTo n y ⊆ Finset.range (y + 1) := by
          intro p hp
          exact Finset.mem_range.mpr (by
            have := (mem_missingPrimesUpTo.mp hp).2.1
            omega)
        have hcard : (missingPrimesUpTo n y).card ≤ y + 1 := by
          simpa using Finset.card_le_card hmissing
        have hqcard : q.primeFactors.card = 1 := by
          rw [hqprime.primeFactors]
          simp
        rw [hqcard]
        omega
  · rw [Nat.totient_mul hcopMq, Nat.totient_prime hqprime]
    have hphia : M.totient * a ≤ 2 * h := by
      calc
        M.totient * a = M.totient * (h / M.totient + 1) := by
          simp [a, tuningBase, M]
        _ = M.totient * (h / M.totient) + M.totient := by ring
        _ ≤ h + M.totient :=
          Nat.add_le_add_right (Nat.mul_div_le h M.totient) _
        _ ≤ 2 * h := by omega
    have hqm1 : q - 1 ≤ 32 * a := (Nat.sub_le q 1).trans hqa
    calc
      M.totient * (q - 1) ≤ M.totient * (32 * a) :=
        Nat.mul_le_mul_left _ hqm1
      _ = 32 * (M.totient * a) := by ring
      _ ≤ 64 * h := by omega

/-- A tuned modulus is large enough that its reciprocal is controlled by
the missing-prime Euler product divided by the band parameter.  This is the
second copy of the Euler product in the analytic upper bound. -/
lemma tuned_modulus_inv_le {n h z d : ℕ} (hh : 0 < h)
    (hd : missingPrimeProduct n z * tuningBase n h z < d) :
    (d : ℝ)⁻¹ ≤ missingEulerProduct n z / h := by
  let M := missingPrimeProduct n z
  have hM : 0 < M := by simpa [M] using missingPrimeProduct_pos n z
  have hphi : 0 < M.totient := Nat.totient_pos.mpr hM
  have hha : h < M.totient * tuningBase n h z := by
    simpa [tuningBase, M] using Nat.lt_mul_div_succ h hphi
  have hMd : M * h < M.totient * d := by
    calc
      M * h < M * (M.totient * tuningBase n h z) :=
        Nat.mul_lt_mul_of_pos_left hha hM
      _ = M.totient * (M * tuningBase n h z) := by ring
      _ < M.totient * d := Nat.mul_lt_mul_of_pos_left hd hphi
  have hdpos : (0 : ℝ) < d := by
    have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd
    exact_mod_cast this
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  rw [← totient_missingPrimeProduct_div_self]
  rw [inv_eq_one_div]
  rw [div_div]
  exact (div_le_div_iff₀ hdpos (mul_pos hMR hhR)).mpr (by
    have hcast : (M : ℝ) * h < (M.totient : ℝ) * d := by
      exact_mod_cast hMd
    nlinarith)

lemma resolutionScale_mainTerm_identity {n : ℕ} (hn : 0 < n)
    (hL : 0 < Real.log (n : ℝ))
    (hLL : 0 < Real.log (Real.log (n : ℝ))) :
    (n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3 /
        (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 *
          resolutionScale n ^ 2) = resolutionScale n := by
  let N : ℝ := n
  let L := Real.log N
  let LL := Real.log L
  let R : ℝ := N / Nat.totient n
  have hN : 0 < N := by
    change (0 : ℝ) < (n : ℝ)
    exact_mod_cast hn
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hR : 0 < R := div_pos hN hphi
  have hL' : 0 < L := by simpa [L, N] using hL
  have hLL' : 0 < LL := by simpa [LL, L, N] using hLL
  have hLcube : (Real.rpow L (1 / 3 : ℝ)) ^ 3 = L := by
    calc
      (Real.rpow L (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow L (1 / 3 : ℝ)) (3 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 3
      _ = Real.rpow L ((1 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hL'.le _ _).symm
      _ = L := by norm_num
  have hLLcube : (Real.rpow LL (2 / 3 : ℝ)) ^ 3 = LL ^ 2 := by
    calc
      (Real.rpow LL (2 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow LL (2 / 3 : ℝ)) (3 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 3
      _ = Real.rpow LL ((2 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hLL'.le _ _).symm
      _ = LL ^ 2 := by norm_num
  change N * R ^ 3 / (L * LL ^ 2 * resolutionScale n ^ 2) =
    resolutionScale n
  rw [resolutionScale]
  change N * R ^ 3 /
      (L * LL ^ 2 *
        (Real.rpow N (1 / 3 : ℝ) * R /
          (Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ))) ^ 2) =
    Real.rpow N (1 / 3 : ℝ) * R /
      (Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ))
  have hNcube : (Real.rpow N (1 / 3 : ℝ)) ^ 3 = N := by
    calc
      (Real.rpow N (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow N (1 / 3 : ℝ)) (3 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 3
      _ = Real.rpow N ((1 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hN.le _ _).symm
      _ = N := by norm_num
  field_simp [hN.ne', hL'.ne', hLL'.ne', hR.ne',
    (Real.rpow_pos_of_pos hN _).ne', (Real.rpow_pos_of_pos hL' _).ne',
    (Real.rpow_pos_of_pos hLL' _).ne']
  rw [hNcube, hLcube, hLLcube]
  ring

/-- A coarse polynomial lower bound for the resolution scale.  Its purpose is
to absorb all logarithmic and finite-error terms in the eventual estimates. -/
lemma resolutionScale_ge_rpow_three_tenths {n : ℕ} (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) :
    (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) ≤
      resolutionScale n := by
  let N : ℝ := n
  let L : ℝ := Real.log N
  let LL : ℝ := Real.log L
  have hNpos : 0 < N := by
    change (0 : ℝ) < (n : ℝ)
    exact_mod_cast hn
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hLLpos : 0 < LL := lt_of_lt_of_le zero_lt_one hloglog
  have hLLleL : LL ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    change Real.log L ≤ L
    linarith
  have hdenpos :
      0 < Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hLpos _)
      (Real.rpow_pos_of_pos hLLpos _)
  have hdenle :
      Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ) ≤ L := by
    calc
      Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ) ≤
          Real.rpow L (1 / 3 : ℝ) * Real.rpow L (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hLLpos.le hLLleL (by norm_num))
          (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow L ((1 / 3 : ℝ) + (2 / 3 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = L := by norm_num
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hratio : (1 : ℝ) ≤ N / Nat.totient n := by
    rw [le_div_iff₀ hphi]
    have hcast : (n.totient : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.totient_le n
    simpa [N] using hcast
  have hraw :=
    Real.log_le_rpow_div hNpos.le (show (0 : ℝ) < 1 / 30 by norm_num)
  have hLupper : L ≤ 30 * Real.rpow N (1 / 30 : ℝ) := by
    simpa [L, div_eq_mul_inv, mul_comm] using hraw
  have hNpow : 0 ≤ Real.rpow N (1 / 3 : ℝ) :=
    Real.rpow_nonneg hNpos.le _
  have hrsub :
      Real.rpow N (1 / 3 - 1 / 30 : ℝ) =
        Real.rpow N (1 / 3 : ℝ) / Real.rpow N (1 / 30 : ℝ) := by
    exact Real.rpow_sub hNpos (1 / 3 : ℝ) (1 / 30 : ℝ)
  calc
    (1 / 30 : ℝ) * Real.rpow N (3 / 10 : ℝ) =
        Real.rpow N (1 / 3 : ℝ) /
          (30 * Real.rpow N (1 / 30 : ℝ)) := by
      rw [show (3 / 10 : ℝ) = 1 / 3 - 1 / 30 by norm_num, hrsub]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hNpos (1 / 30 : ℝ))]
    _ ≤ Real.rpow N (1 / 3 : ℝ) / L := by
      exact div_le_div_of_nonneg_left hNpow hLpos hLupper
    _ ≤ Real.rpow N (1 / 3 : ℝ) /
          (Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ)) := by
      exact div_le_div_of_nonneg_left hNpow hdenpos hdenle
    _ ≤ Real.rpow N (1 / 3 : ℝ) * (N / Nat.totient n) /
          (Real.rpow L (1 / 3 : ℝ) * Real.rpow LL (2 / 3 : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      nlinarith [hNpow]
    _ = resolutionScale n := by rfl

lemma resolutionScale_tendsto_atTop :
    Tendsto resolutionScale atTop atTop := by
  have hlog :=
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog :=
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hlower : ∀ᶠ n : ℕ in atTop,
      (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) ≤
        resolutionScale n := by
    filter_upwards [hlog, hloglog, hpos] with n hnlog hnloglog hn
    exact resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  have hrpow : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (3 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ ↦
      (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ)) atTop atTop :=
    hrpow.const_mul_atTop (by norm_num)
  exact tendsto_atTop_mono' atTop hlower hmul

lemma eventually_rpow_one_fifth_le_resolutionScale :
    ∀ᶠ n : ℕ in atTop,
      Real.rpow (n : ℝ) (1 / 5 : ℝ) ≤ resolutionScale n := by
  have hlog :=
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog := tendsto_log_log_coe_at_top.eventually
    (eventually_ge_atTop (1 : ℝ))
  have hlarge :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (30 : ℝ))
  filter_upwards [eventually_gt_atTop 0, hlog, hloglog, hlarge] with
      n hn hnlog hnloglog hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.rpow (n : ℝ) (3 / 10 : ℝ) =
      Real.rpow (n : ℝ) (1 / 5 : ℝ) *
        Real.rpow (n : ℝ) (1 / 10 : ℝ) := by
    have hadd := Real.rpow_add hnR (1 / 5 : ℝ) (1 / 10 : ℝ)
    convert hadd using 1 <;> norm_num
  have hscale :=
    resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  calc
    Real.rpow (n : ℝ) (1 / 5 : ℝ) =
        (1 / 30 : ℝ) * (30 * Real.rpow (n : ℝ) (1 / 5 : ℝ)) := by ring
    _ ≤ (1 / 30 : ℝ) *
        (Real.rpow (n : ℝ) (1 / 10 : ℝ) *
          Real.rpow (n : ℝ) (1 / 5 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnlarge
          (Real.rpow_nonneg hnR.le _)) (by norm_num)
    _ = (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
      rw [hsplit]
      ring
    _ ≤ resolutionScale n := hscale

/-- Rounded number of size bands used in the eventual upper construction. -/
noncomputable def upperBandCount (K : ℝ) (n : ℕ) : ℕ :=
  ⌈K * resolutionScale n⌉₊

/-- Polynomial cutoff for the filtered beta sieve.  The exponent is chosen
so that the square of the depth error is a fixed sub-cubic power of `n`. -/
noncomputable def upperSieveCutoff (S n : ℕ) : ℕ :=
  ⌊Real.rpow (n : ℝ) (1 / (10 * S : ℝ))⌋₊

lemma upperBandCount_bounds {K : ℝ} {n : ℕ}
    (hK : 0 ≤ K) (hs : 0 ≤ resolutionScale n) :
    K * resolutionScale n ≤ upperBandCount K n ∧
      (upperBandCount K n : ℝ) < K * resolutionScale n + 1 := by
  constructor
  · simpa [upperBandCount] using Nat.le_ceil (K * resolutionScale n)
  · exact Nat.ceil_lt_add_one (mul_nonneg hK hs)

lemma upperBandCount_tendsto_atTop {K : ℝ} (hK : 0 < K) :
    Tendsto (upperBandCount K) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    (resolutionScale_tendsto_atTop.const_mul_atTop hK)

lemma eventually_resolutionScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < resolutionScale n :=
  resolutionScale_tendsto_atTop.eventually (eventually_gt_atTop 0)

lemma upperSieveCutoff_tendsto_atTop {S : ℕ} (hS : 0 < S) :
    Tendsto (upperSieveCutoff S) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop
      (by positivity : (0 : ℝ) < 1 / (10 * S : ℝ))).comp
        tendsto_natCast_atTop_atTop)

lemma upperSieveCutoff_depthError {S n : ℕ} (hS : 0 < S) :
    (((upperSieveCutoff S n) ^ S : ℕ) : ℝ) ^ 2 ≤
      Real.rpow (n : ℝ) (1 / 5 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hfloor : (upperSieveCutoff S n : ℝ) ≤
      Real.rpow (n : ℝ) (1 / (10 * S : ℝ)) := by
    exact Nat.floor_le (Real.rpow_nonneg hn _)
  calc
    (((upperSieveCutoff S n) ^ S : ℕ) : ℝ) ^ 2 =
        (upperSieveCutoff S n : ℝ) ^ (2 * S) := by
      push_cast
      rw [← pow_mul]
      ring
    _ ≤ (Real.rpow (n : ℝ) (1 / (10 * S : ℝ))) ^ (2 * S) := by
      gcongr
    _ = Real.rpow (n : ℝ)
        ((1 / (10 * S : ℝ)) * (2 * S : ℕ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hn _ _).symm
    _ = Real.rpow (n : ℝ) (1 / 5 : ℝ) := by
      congr 1
      push_cast
      field_simp
      ring

lemma eventually_log_upperSieveCutoff_lower {S : ℕ} (hS : 0 < S) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (20 * S : ℝ)) * Real.log (n : ℝ) ≤
        Real.log (upperSieveCutoff S n : ℝ) := by
  let e : ℝ := 1 / (10 * S : ℝ)
  have he : 0 < e := by positivity
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually
      (eventually_ge_atTop (2 * Real.log 2 / e)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hlog hn
  have hNpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn
  have hxpos : 0 < Real.rpow (n : ℝ) e :=
    Real.rpow_pos_of_pos hNpos e
  have hlogrpow :
      Real.log (Real.rpow (n : ℝ) e) = e * Real.log (n : ℝ) := by
    exact Real.log_rpow hNpos e
  have hxfloor : Real.rpow (n : ℝ) e <
      (upperSieveCutoff S n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxge : 2 ≤ Real.rpow (n : ℝ) e := by
    rw [← Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hxpos,
      hlogrpow]
    have hmul := (div_le_iff₀ he).mp hlog
    rw [mul_comm (Real.log (n : ℝ)) e] at hmul
    have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
    nlinarith
  have hyNat : 0 < upperSieveCutoff S n := by
    apply Nat.floor_pos.mpr
    change 1 ≤ Real.rpow (n : ℝ) e
    linarith
  have hhalf : Real.rpow (n : ℝ) e / 2 ≤
      (upperSieveCutoff S n : ℝ) := by
    have hyInt : (1 : ℝ) ≤ upperSieveCutoff S n := by exact_mod_cast hyNat
    linarith
  have hypos : (0 : ℝ) < upperSieveCutoff S n := by exact_mod_cast hyNat
  have hloghalf :=
    Real.log_le_log (div_pos hxpos (by norm_num)) hhalf
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0),
    hlogrpow] at hloghalf
  rw [show (1 / (20 * S : ℝ)) = e / 2 by
    dsimp [e]
    field_simp
    ring]
  have heq : (e / 2) * Real.log (n : ℝ) ≤
      e * Real.log (n : ℝ) - Real.log 2 := by
    have hmul := (div_le_iff₀ he).mp hlog
    rw [mul_comm (Real.log (n : ℝ)) e] at hmul
    nlinarith
  exact heq.trans hloghalf

lemma eventually_modulusCutoff_mul_missingPrimeProduct_le_scale :
    ∀ᶠ n : ℕ in atTop,
      modulusPrimeCutoff n *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
        resolutionScale n := by
  have hlog :=
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog :=
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hlarge :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 27 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (6000 : ℝ))
  filter_upwards [eventually_gt_atTop 0, hlog, hloglog, hlarge] with
      n hn hnlog hnloglog hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := missingPrimeProduct_modulusCutoff_cast_le_rpow hn.ne'
  have hzlog : (modulusPrimeCutoff n : ℝ) ≤
      Real.logb 2 (n : ℝ) := by
    calc
      (modulusPrimeCutoff n : ℝ) ≤ Nat.log 2 n := by
        exact_mod_cast Nat.div_le_self (Nat.log 2 n) 100
      _ ≤ Real.logb 2 (n : ℝ) := Real.natLog_le_logb n 2
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hnlog
  have hzlog' : (modulusPrimeCutoff n : ℝ) ≤
      2 * Real.log (n : ℝ) := by
    rw [Real.logb] at hzlog
    have hzmul := (le_div_iff₀ (Real.log_pos one_lt_two)).mp hzlog
    have hznonneg : (0 : ℝ) ≤ modulusPrimeCutoff n := by positivity
    nlinarith
  have hlogpow :=
    Real.log_le_rpow_div hnR.le (show (0 : ℝ) < 1 / 100 by norm_num)
  have hz : (modulusPrimeCutoff n : ℝ) ≤
      200 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    have hlogpow' : Real.log (n : ℝ) ≤
        100 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hlogpow
    calc
      (modulusPrimeCutoff n : ℝ) ≤ 2 * Real.log (n : ℝ) := hzlog'
      _ ≤ 200 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by nlinarith
  have hprod :
      (modulusPrimeCutoff n : ℝ) *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
        200 * Real.rpow (n : ℝ) (3 / 100 : ℝ) := by
    calc
      (modulusPrimeCutoff n : ℝ) *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
          (200 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) *
            Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
              exact mul_le_mul hz hM (Nat.cast_nonneg _)
                (mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _))
      _ = 200 * Real.rpow (n : ℝ) (3 / 100 : ℝ) := by
        have hadd := Real.rpow_add hnR (1 / 100 : ℝ) (1 / 50 : ℝ)
        have hadd' : Real.rpow (n : ℝ) (3 / 100 : ℝ) =
            Real.rpow (n : ℝ) (1 / 100 : ℝ) *
              Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
          convert hadd using 1 <;> norm_num
        rw [hadd']
        ring
  have hpowSplit :
      Real.rpow (n : ℝ) (3 / 10 : ℝ) =
        Real.rpow (n : ℝ) (3 / 100 : ℝ) *
          Real.rpow (n : ℝ) (27 / 100 : ℝ) := by
    have hadd := Real.rpow_add hnR (3 / 100 : ℝ) (27 / 100 : ℝ)
    convert hadd using 1 <;> norm_num
  have hcoarse :=
    resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  have htarget :
      200 * Real.rpow (n : ℝ) (3 / 100 : ℝ) ≤
        (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
    rw [hpowSplit]
    have hp : 0 < Real.rpow (n : ℝ) (3 / 100 : ℝ) :=
      Real.rpow_pos_of_pos hnR _
    dsimp [Function.comp_def] at hnlarge
    calc
      200 * Real.rpow (n : ℝ) (3 / 100 : ℝ) =
          (1 / 30 : ℝ) *
            (6000 * Real.rpow (n : ℝ) (3 / 100 : ℝ)) := by ring
      _ ≤ (1 / 30 : ℝ) *
          (Real.rpow (n : ℝ) (27 / 100 : ℝ) *
            Real.rpow (n : ℝ) (3 / 100 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnlarge hp.le) (by norm_num)
      _ = (1 / 30 : ℝ) *
          (Real.rpow (n : ℝ) (3 / 100 : ℝ) *
            Real.rpow (n : ℝ) (27 / 100 : ℝ)) := by ring
  simpa only [Nat.cast_mul] using hprod.trans (htarget.trans hcoarse)

/-- A rounded fourth root used only to verify that the Bertrand tuning
interval contains a prime not dividing the target. -/
noncomputable def fourthRootCeil (n : ℕ) : ℕ :=
  ⌈Real.rpow (n : ℝ) (1 / 4 : ℝ)⌉₊

lemma eventually_fourthRootCeil_mul_missingPrimeProduct_le_scale :
    ∀ᶠ n : ℕ in atTop,
      fourthRootCeil n *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
        resolutionScale n := by
  have hlog :=
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog := tendsto_log_log_coe_at_top.eventually
    (eventually_ge_atTop (1 : ℝ))
  have hlarge :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (60 : ℝ))
  filter_upwards [eventually_gt_atTop 0, hlog, hloglog, hlarge] with
      n hn hnlog hnloglog hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := missingPrimeProduct_modulusCutoff_cast_le_rpow hn.ne'
  have hNquarter : 1 ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    apply Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hceil : (fourthRootCeil n : ℝ) <
      Real.rpow (n : ℝ) (1 / 4 : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hnR.le _)
  have hceil' : (fourthRootCeil n : ℝ) ≤
      2 * Real.rpow (n : ℝ) (1 / 4 : ℝ) := by linarith
  have hprod :
      (fourthRootCeil n : ℝ) *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
        2 * Real.rpow (n : ℝ) (27 / 100 : ℝ) := by
    calc
      (fourthRootCeil n : ℝ) *
          missingPrimeProduct n (modulusPrimeCutoff n) ≤
          (2 * Real.rpow (n : ℝ) (1 / 4 : ℝ)) *
            Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
        exact mul_le_mul hceil' hM (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _))
      _ = 2 * Real.rpow (n : ℝ) (27 / 100 : ℝ) := by
        have hadd := Real.rpow_add hnR (1 / 4 : ℝ) (1 / 50 : ℝ)
        have hadd' : Real.rpow (n : ℝ) (27 / 100 : ℝ) =
            Real.rpow (n : ℝ) (1 / 4 : ℝ) *
              Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
          convert hadd using 1 <;> norm_num
        rw [hadd']
        ring
  have hsplit : Real.rpow (n : ℝ) (3 / 10 : ℝ) =
      Real.rpow (n : ℝ) (27 / 100 : ℝ) *
        Real.rpow (n : ℝ) (3 / 100 : ℝ) := by
    have hadd := Real.rpow_add hnR (27 / 100 : ℝ) (3 / 100 : ℝ)
    convert hadd using 1 <;> norm_num
  have hcoarse :=
    resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  have htarget : 2 * Real.rpow (n : ℝ) (27 / 100 : ℝ) ≤
      (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
    rw [hsplit]
    have hp : 0 < Real.rpow (n : ℝ) (27 / 100 : ℝ) :=
      Real.rpow_pos_of_pos hnR _
    dsimp [Function.comp_def] at hnlarge
    calc
      2 * Real.rpow (n : ℝ) (27 / 100 : ℝ) =
          (1 / 30 : ℝ) *
            (60 * Real.rpow (n : ℝ) (27 / 100 : ℝ)) := by ring
      _ ≤ (1 / 30 : ℝ) *
          (Real.rpow (n : ℝ) (3 / 100 : ℝ) *
            Real.rpow (n : ℝ) (27 / 100 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnlarge hp.le) (by norm_num)
      _ = _ := by ring
  simpa only [Nat.cast_mul] using hprod.trans (htarget.trans hcoarse)

lemma fourthRootCeil_add_one_pow_four_gt {n : ℕ} (hn : 0 < n) :
    n < (fourthRootCeil n + 1) ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hceil : Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤
      (fourthRootCeil n : ℝ) := by
    simpa [fourthRootCeil] using
      Nat.le_ceil (Real.rpow (n : ℝ) (1 / 4 : ℝ))
  have hlt : Real.rpow (n : ℝ) (1 / 4 : ℝ) <
      (fourthRootCeil n + 1 : ℕ) := hceil.trans_lt (by norm_num)
  have hpowlt := pow_lt_pow_left₀ hlt (Real.rpow_nonneg hnR.le _)
    (by omega : 4 ≠ 0)
  have hid : (Real.rpow (n : ℝ) (1 / 4 : ℝ)) ^ 4 = (n : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (1 / 4 : ℝ)) ^ 4 =
          Real.rpow (Real.rpow (n : ℝ) (1 / 4 : ℝ)) (4 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 4
      _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) * 4) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = (n : ℝ) := by norm_num
  rw [hid] at hpowlt
  exact_mod_cast hpowlt

lemma eventually_exists_tuned_modulus_for_upper {K : ℝ} (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      ∃ d : ℕ, 1 < d ∧ Nat.Coprime n d ∧
        missingPrimeProduct n (modulusPrimeCutoff n) *
            tuningBase n (upperBandCount K n) (modulusPrimeCutoff n) < d ∧
        d ≤ 32 * missingPrimeProduct n (modulusPrimeCutoff n) *
            tuningBase n (upperBandCount K n) (modulusPrimeCutoff n) ∧
        d.primeFactors.card ≤ modulusPrimeCutoff n + 2 ∧
        d.totient ≤ 64 * upperBandCount K n := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_resolutionScale_pos,
    eventually_modulusCutoff_mul_missingPrimeProduct_le_scale,
    eventually_fourthRootCeil_mul_missingPrimeProduct_le_scale,
    eventually_log_modulusPrimeCutoff_lower,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn hscale hzM htM hzlog hll
  let h := upperBandCount K n
  let z := modulusPrimeCutoff n
  let M := missingPrimeProduct n z
  have hKh : resolutionScale n ≤ (h : ℝ) := by
    have hb :=
      (upperBandCount_bounds (zero_le_one.trans hK) (le_of_lt hscale)).1
    dsimp [h]
    calc
      resolutionScale n ≤ K * resolutionScale n := by nlinarith
      _ ≤ upperBandCount K n := hb
  have hh : 0 < h := by
    have : (0 : ℝ) < h := hscale.trans_le hKh
    exact_mod_cast this
  have hzpos : 0 < z := by
    have hzlogpos : 0 < Real.log (z : ℝ) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (by
        calc
          (1 / 2 : ℝ) ≤
              (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) := by
            nlinarith
          _ ≤ Real.log (z : ℝ) := by simpa [z] using hzlog)
    apply Nat.pos_of_ne_zero
    intro hz0
    have hzcast : (z : ℝ) = 0 := by exact_mod_cast hz0
    rw [hzcast, Real.log_zero] at hzlogpos
    exact (lt_irrefl 0) hzlogpos
  have hMpos : 0 < M := by
    simpa [M] using missingPrimeProduct_pos n z
  have hphiMpos : 0 < M.totient := Nat.totient_pos.mpr hMpos
  have hzM_h : z * M ≤ h := by
    have hreal : ((z * M : ℕ) : ℝ) ≤ (h : ℝ) := by
      calc
        ((z * M : ℕ) : ℝ) ≤ resolutionScale n := by
          simpa [z, M] using hzM
        _ ≤ (h : ℝ) := hKh
    exact_mod_cast hreal
  have htM_h : fourthRootCeil n * M ≤ h := by
    have hreal : (((fourthRootCeil n) * M : ℕ) : ℝ) ≤ (h : ℝ) := by
      calc
        ((((fourthRootCeil n) * M : ℕ) : ℝ)) ≤ resolutionScale n := by
          simpa [M] using htM
        _ ≤ (h : ℝ) := hKh
    exact_mod_cast hreal
  have hphi : M.totient ≤ h := by
    calc
      M.totient ≤ M := Nat.totient_le M
      _ ≤ z * M := by simpa using Nat.le_mul_of_pos_left M hzpos
      _ ≤ h := hzM_h
  have hzphi : z * M.totient ≤ h :=
    (Nat.mul_le_mul_left z (Nat.totient_le M)).trans hzM_h
  have hzdiv : z ≤ h / M.totient :=
    (Nat.le_div_iff_mul_le hphiMpos).mpr (by
      simpa [mul_comm] using hzphi)
  have hy : z < tuningBase n h z := by
    change z < h / M.totient + 1
    omega
  have htphi : fourthRootCeil n * M.totient ≤ h :=
    (Nat.mul_le_mul_left _ (Nat.totient_le M)).trans htM_h
  have htdiv : fourthRootCeil n ≤ h / M.totient :=
    (Nat.le_div_iff_mul_le hphiMpos).mpr (by
      simpa [mul_comm] using htphi)
  have hrootle : fourthRootCeil n + 1 ≤ tuningBase n h z := by
    change fourthRootCeil n + 1 ≤ h / M.totient + 1
    omega
  have hpow : n < tuningBase n h z ^ 5 := by
    have hroot := fourthRootCeil_add_one_pow_four_gt hn
    have ha : 1 ≤ tuningBase n h z := by simp [tuningBase]
    calc
      n < (fourthRootCeil n + 1) ^ 4 := hroot
      _ ≤ tuningBase n h z ^ 4 := Nat.pow_le_pow_left hrootle 4
      _ ≤ tuningBase n h z ^ 5 := Nat.pow_le_pow_right ha (by omega)
  simpa [h, z, M] using
    exists_tuned_modulus (n := n) (h := h) (y := z)
      hn hh hphi hy hpow

lemma eventually_upperSieveCutoff_le_band {K : ℝ} (hK : 1 ≤ K)
    {S : ℕ} (hS : 101 ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      upperSieveCutoff S n ≤ upperBandCount K n := by
  have hlog :=
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))
  have hloglog := tendsto_log_log_coe_at_top.eventually
    (eventually_ge_atTop (1 : ℝ))
  have hlarge :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 299 / 1000)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (30 : ℝ))
  filter_upwards [eventually_gt_atTop 0, hlog, hloglog, hlarge] with
      n hn hnlog hnloglog hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (1 / (10 * S : ℝ)) ≤ (1 / 1000 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000)
    have : (1000 : ℕ) ≤ 10 * S := by omega
    exact_mod_cast this
  have hy : (upperSieveCutoff S n : ℝ) ≤
      Real.rpow (n : ℝ) (1 / 1000 : ℝ) := by
    calc
      (upperSieveCutoff S n : ℝ) ≤
          Real.rpow (n : ℝ) (1 / (10 * S : ℝ)) := by
        exact Nat.floor_le (Real.rpow_nonneg hnR.le _)
      _ ≤ Real.rpow (n : ℝ) (1 / 1000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnOne he
  have hsplit : Real.rpow (n : ℝ) (3 / 10 : ℝ) =
      Real.rpow (n : ℝ) (1 / 1000 : ℝ) *
        Real.rpow (n : ℝ) (299 / 1000 : ℝ) := by
    have hadd := Real.rpow_add hnR (1 / 1000 : ℝ) (299 / 1000 : ℝ)
    convert hadd using 1 <;> norm_num
  have hscale :=
    resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  have hyScale : (upperSieveCutoff S n : ℝ) ≤ resolutionScale n := by
    calc
      (upperSieveCutoff S n : ℝ) ≤
          Real.rpow (n : ℝ) (1 / 1000 : ℝ) := hy
      _ ≤ (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
        rw [hsplit]
        have hp := Real.rpow_nonneg hnR.le (1 / 1000 : ℝ)
        dsimp [Function.comp_def] at hnlarge
        calc
          Real.rpow (n : ℝ) (1 / 1000 : ℝ) =
              (1 / 30 : ℝ) *
                (30 * Real.rpow (n : ℝ) (1 / 1000 : ℝ)) := by ring
          _ ≤ (1 / 30 : ℝ) *
              (Real.rpow (n : ℝ) (299 / 1000 : ℝ) *
                Real.rpow (n : ℝ) (1 / 1000 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hnlarge hp) (by norm_num)
          _ = _ := by ring
      _ ≤ resolutionScale n := hscale
  have hbaseNonneg : (0 : ℝ) ≤
      (1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
  have hsnonneg : 0 ≤ resolutionScale n := hbaseNonneg.trans hscale
  have hhScale :=
    (upperBandCount_bounds (zero_le_one.trans hK) hsnonneg).1
  have hScaleH : resolutionScale n ≤ (upperBandCount K n : ℝ) := by
    calc
      resolutionScale n ≤ K * resolutionScale n := by nlinarith
      _ ≤ upperBandCount K n := hhScale
  exact_mod_cast hyScale.trans hScaleH

lemma eventually_upperSieveCutoff_lt_primeAt_band {K : ℝ} (hK : 1 ≤ K)
    {S : ℕ} (hS : 101 ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      upperSieveCutoff S n < primeAt (upperBandCount K n) := by
  filter_upwards [eventually_upperSieveCutoff_le_band hK hS] with n hn
  exact hn.trans_lt ((Nat.lt_add_of_pos_right (by omega : 0 < 2)).trans_le
    (Nat.add_two_le_nth_prime (upperBandCount K n)))

/-- Pure real-algebra core of the eventual upper estimate. -/
lemma analytic_upper_main_term_bound
    {N R L LL H h d Vy Vz B C T : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hL : 0 < L) (hLL : 0 < LL)
    (hH : 0 < H) (hh : 0 < h) (hd : 0 < d)
    (hVy0 : 0 ≤ Vy) (hVz0 : 0 ≤ Vz) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hid : N * R ^ 3 / (L * LL ^ 2 * H ^ 2) = H)
    (hHh : H ≤ h) (hdinv : d⁻¹ ≤ Vz / h)
    (hVy : Vy ≤ 20 * T * C * R / L)
    (hVz : Vz ≤ 2 * C * R / LL) :
    N * B * Vy / d ^ 2 ≤ 80 * T * B * C ^ 3 * H := by
  have hTC : 0 ≤ 20 * T * C * R / L := by positivity
  have hVC : 0 ≤ 2 * C * R / LL := by positivity
  have hdinv0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hVzh0 : 0 ≤ Vz / h := div_nonneg hVz0 hh.le
  have hCH0 : 0 ≤ (2 * C * R / LL) / h := div_nonneg hVC hh.le
  have hCHH0 : 0 ≤ (2 * C * R / LL) / H := div_nonneg hVC hH.le
  calc
    N * B * Vy / d ^ 2 = N * B * Vy * (d⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ N * B * (20 * T * C * R / L) * (Vz / h) ^ 2 := by
      gcongr
    _ ≤ N * B * (20 * T * C * R / L) *
          ((2 * C * R / LL) / h) ^ 2 := by
      gcongr
    _ ≤ N * B * (20 * T * C * R / L) *
          ((2 * C * R / LL) / H) ^ 2 := by
      have hdiv : (2 * C * R / LL) / h ≤ (2 * C * R / LL) / H :=
        div_le_div_of_nonneg_left hVC hH hHh
      gcongr
    _ = 80 * T * B * C ^ 3 *
          (N * R ^ 3 / (L * LL ^ 2 * H ^ 2)) := by
      field_simp [hL.ne', hLL.ne', hH.ne']
      ring
    _ = 80 * T * B * C ^ 3 * H := by rw [hid]

lemma exists_upper_sieve_depth {A : ℝ} (hA : 1 ≤ A) :
    ∃ S : ℕ, 101 ≤ S ∧
      Real.log A ≤ 2 * (S - 100 : ℕ) / 99 := by
  obtain ⟨S, hS⟩ := exists_nat_gt (Real.log A * 99 / 2 + 101)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hSR : (101 : ℝ) < S := by nlinarith
  have hSNat : 101 ≤ S := by exact_mod_cast hSR.le
  refine ⟨S, hSNat, ?_⟩
  rw [Nat.cast_sub (by omega : 100 ≤ S)]
  norm_num at hS ⊢
  nlinarith

lemma eventually_missingEulerProduct_sieveCutoff_le {C : ℝ} (hC : 0 < C)
    (hMertens : ∀ n y : ℕ, 0 < n → 2 ≤ y →
      missingEulerProduct n y ≤
        C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ))
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ n : ℕ in atTop,
      missingEulerProduct n (upperSieveCutoff S n) ≤
        20 * S * C * ((n : ℝ) / Nat.totient n) /
          Real.log (n : ℝ) := by
  filter_upwards [eventually_gt_atTop 0,
    (upperSieveCutoff_tendsto_atTop hS).eventually
      (eventually_ge_atTop 2),
    eventually_log_upperSieveCutoff_lower hS,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop 0)] with
      n hn hy hylog hnlog
  have hbasepos : 0 < Real.log (n : ℝ) / (20 * S : ℝ) := by positivity
  have hylog' : Real.log (n : ℝ) / (20 * S : ℝ) ≤
      Real.log (upperSieveCutoff S n : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hylog
  have hinv : (Real.log (upperSieveCutoff S n : ℝ))⁻¹ ≤
      (Real.log (n : ℝ) / (20 * S : ℝ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hbasepos hylog'
  have hfactor : 0 ≤ C * ((n : ℝ) / Nat.totient n) := by positivity
  calc
    missingEulerProduct n (upperSieveCutoff S n) ≤
        C * ((n : ℝ) / Nat.totient n) /
          Real.log (upperSieveCutoff S n : ℝ) := hMertens n _ hn hy
    _ = (C * ((n : ℝ) / Nat.totient n)) *
          (Real.log (upperSieveCutoff S n : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (C * ((n : ℝ) / Nat.totient n)) *
          (Real.log (n : ℝ) / (20 * S : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = 20 * S * C * ((n : ℝ) / Nat.totient n) /
          Real.log (n : ℝ) := by
      field_simp [hnlog.ne', (show (S : ℝ) ≠ 0 by exact_mod_cast hS.ne')]

lemma eventually_missingEulerProduct_modulusCutoff_le {C : ℝ} (hC : 0 < C)
    (hMertens : ∀ n y : ℕ, 0 < n → 2 ≤ y →
      missingEulerProduct n y ≤
        C * ((n : ℝ) / Nat.totient n) / Real.log (y : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      missingEulerProduct n (modulusPrimeCutoff n) ≤
        2 * C * ((n : ℝ) / Nat.totient n) /
          Real.log (Real.log (n : ℝ)) := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_log_modulusPrimeCutoff_lower,
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop 0)] with
      n hn hzlog hnloglog
  have hzpos : 0 < Real.log (modulusPrimeCutoff n : ℝ) := by
    have : 0 < (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) := by positivity
    exact this.trans_le hzlog
  have hz : 2 ≤ modulusPrimeCutoff n := by
    have hzcast : (1 : ℝ) < modulusPrimeCutoff n :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hzpos
    exact_mod_cast hzcast
  have hbasepos : 0 < (1 / 2 : ℝ) *
      Real.log (Real.log (n : ℝ)) := by positivity
  have hinv : (Real.log (modulusPrimeCutoff n : ℝ))⁻¹ ≤
      ((1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hbasepos hzlog
  have hfactor : 0 ≤ C * ((n : ℝ) / Nat.totient n) := by positivity
  calc
    missingEulerProduct n (modulusPrimeCutoff n) ≤
        C * ((n : ℝ) / Nat.totient n) /
          Real.log (modulusPrimeCutoff n : ℝ) := hMertens n _ hn hz
    _ = (C * ((n : ℝ) / Nat.totient n)) *
          (Real.log (modulusPrimeCutoff n : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (C * ((n : ℝ) / Nat.totient n)) *
          ((1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = 2 * C * ((n : ℝ) / Nat.totient n) /
          Real.log (Real.log (n : ℝ)) := by
      field_simp [hnloglog.ne']

/-- The complete asymptotic upper half of the Conlon--Fox--Pham bound. -/
theorem exists_resolution_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * resolutionScale n := by
  obtain ⟨A, hA, hcover⟩ := exists_f_upperCover_real_bound_modulus
  obtain ⟨CM, hCM, hMertens⟩ := exists_missingEulerProduct_upper
  obtain ⟨S, hS, hSlog⟩ := exists_upper_sieve_depth hA
  let B : ℝ := 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let C : ℝ := 265 + 80 * S * B * CM ^ 3
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_gt_atTop 0,
    resolutionScale_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_exists_tuned_modulus_for_upper (K := 1) (by norm_num),
    (upperSieveCutoff_tendsto_atTop (by omega : 0 < S)).eventually
      (eventually_ge_atTop 2),
    eventually_upperSieveCutoff_lt_primeAt_band (K := 1) (by norm_num) hS,
    eventually_missingEulerProduct_sieveCutoff_le hCM hMertens
      (by omega : 0 < S),
    eventually_missingEulerProduct_modulusCutoff_le hCM hMertens,
    eventually_modulusCutoff_mul_missingPrimeProduct_le_scale,
    eventually_rpow_one_fifth_le_resolutionScale,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop 0),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop 0)] with
      n hn hscale hdexist hy2 hyprime hVy hVz hzM hdepth hnlog hnloglog
  obtain ⟨d, hd, hcop, hdlarge, _hdupper, hcard, htot⟩ := hdexist
  let H := resolutionScale n
  let h := upperBandCount (1 : ℝ) n
  let y := upperSieveCutoff S n
  let z := modulusPrimeCutoff n
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hHnonneg : 0 ≤ resolutionScale n := by linarith
  have hhceil := (upperBandCount_bounds (K := (1 : ℝ))
    (n := n) (by norm_num) hHnonneg).2
  have hhR : (h : ℝ) ≤ 2 * H := by
    dsimp [h, H]
    norm_num at hhceil
    linarith
  have hHh : H ≤ (h : ℝ) := by
    dsimp [H, h]
    simpa using (upperBandCount_bounds (K := (1 : ℝ))
      (n := n) (by norm_num) hHnonneg).1
  have hh : 0 < h := by
    have : (0 : ℝ) < h := hHpos.trans_le hHh
    exact_mod_cast this
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hMpos : 0 < missingPrimeProduct n z :=
    missingPrimeProduct_pos n z
  have hzle : (z : ℝ) ≤ H := by
    have hzNat : z ≤ z * missingPrimeProduct n z :=
      Nat.le_mul_of_pos_right z hMpos
    calc
      (z : ℝ) ≤ ((z * missingPrimeProduct n z : ℕ) : ℝ) := by
        exact_mod_cast hzNat
      _ ≤ H := by simpa [z, H] using hzM
  have hcardR : (d.primeFactors.card : ℝ) ≤ 3 * H := by
    have hc : (d.primeFactors.card : ℝ) ≤ (z : ℝ) + 2 := by
      exact_mod_cast (by simpa [z] using hcard)
    linarith
  have htotR : (2 * d.totient : ℕ) ≤ 128 * h := by omega
  have htotRR : ((2 * d.totient : ℕ) : ℝ) ≤ 256 * H := by
    calc
      ((2 * d.totient : ℕ) : ℝ) ≤ ((128 * h : ℕ) : ℝ) := by
        exact_mod_cast htotR
      _ ≤ 256 * H := by
        push_cast
        nlinarith
  have hdinv : (d : ℝ)⁻¹ ≤ missingEulerProduct n z / h := by
    apply tuned_modulus_inv_le hh
    simpa [h, z] using hdlarge
  have hmain :
      ((n / d : ℕ) : ℝ) *
          (B * missingEulerProduct n y) / d ≤
        80 * S * B * CM ^ 3 * H := by
    have hcastdiv : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d :=
      Nat.cast_div_le
    have hBVy : 0 ≤ B * missingEulerProduct n y :=
      mul_nonneg hB (missingEulerProduct_pos n y).le
    calc
      ((n / d : ℕ) : ℝ) *
            (B * missingEulerProduct n y) / d ≤
          ((n : ℝ) / d) *
            (B * missingEulerProduct n y) / d := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcastdiv hBVy) hdR.le
      _ = (n : ℝ) * B * missingEulerProduct n y / (d : ℝ) ^ 2 := by
        field_simp [hdR.ne']
      _ ≤ 80 * S * B * CM ^ 3 * H := by
        apply analytic_upper_main_term_bound
            (N := (n : ℝ))
            (R := (n : ℝ) / Nat.totient n)
            (L := Real.log (n : ℝ))
            (LL := Real.log (Real.log (n : ℝ)))
            (H := H) (h := (h : ℝ)) (d := (d : ℝ))
            (Vy := missingEulerProduct n y)
            (Vz := missingEulerProduct n z)
            (B := B) (C := CM) (T := S)
        · positivity
        · positivity
        · exact hnlog
        · exact hnloglog
        · exact hHpos
        · exact_mod_cast hh
        · exact hdR
        · exact (missingEulerProduct_pos n y).le
        · exact (missingEulerProduct_pos n z).le
        · exact hB
        · exact hCM.le
        · positivity
        · simpa [H] using resolutionScale_mainTerm_identity hn hnlog hnloglog
        · exact hHh
        · exact hdinv
        · simpa [y] using hVy
        · simpa [z] using hVz
  have herror : ((((y ^ S : ℕ) : ℝ) ^ 2) / d) ≤ H := by
    have he := upperSieveCutoff_depthError (n := n) (by omega : 0 < S)
    have he' : (((y ^ S : ℕ) : ℝ) ^ 2) ≤
        Real.rpow (n : ℝ) (1 / 5 : ℝ) := by simpa [y] using he
    calc
      (((y ^ S : ℕ) : ℝ) ^ 2) / d ≤
          (((y ^ S : ℕ) : ℝ) ^ 2) := by
        exact div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ d by omega))
      _ ≤ Real.rpow (n : ℝ) (1 / 5 : ℝ) := he'
      _ ≤ H := by simpa [H] using hdepth
  have hfinite := hcover n h d y S hn hd hcop
    (by simpa [h, y] using hyprime) (by simpa [y] using hy2) hS hSlog
  dsimp only at hfinite
  change (f n : ℝ) ≤
      2 * h + d.primeFactors.card + 2 * d.totient +
        (((n / d : ℕ) : ℝ) *
            (B * missingEulerProduct n y) +
          (((y ^ S : ℕ) : ℝ) ^ 2)) / d + 1 at hfinite
  calc
    (f n : ℝ) ≤
        2 * h + d.primeFactors.card + 2 * d.totient +
          (((n / d : ℕ) : ℝ) *
              (B * missingEulerProduct n y) +
            (((y ^ S : ℕ) : ℝ) ^ 2)) / d + 1 := hfinite
    _ = 2 * (h : ℝ) + d.primeFactors.card + (2 * d.totient : ℕ) +
          (((n / d : ℕ) : ℝ) *
              (B * missingEulerProduct n y) / d +
            (((y ^ S : ℕ) : ℝ) ^ 2) / d) + 1 := by
      push_cast
      ring
    _ ≤ 4 * H + 3 * H + 256 * H +
          ((80 * S * B * CM ^ 3 * H) + H) + H := by
      nlinarith [hhR, hcardR, htotRR, hmain, herror]
    _ = C * resolutionScale n := by
      dsimp [C, H]
      ring

/-- Explicit eventual form of the statement `f(n) ≍ resolutionScale(n)`. -/
def Resolution : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * resolutionScale n ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ C * resolutionScale n

end Erdos360
