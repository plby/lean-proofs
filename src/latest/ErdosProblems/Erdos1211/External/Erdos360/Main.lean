/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos1211.External.Erdos4.ResidualPrimeFiberMertens
import ErdosProblems.Erdos1211.External.Erdos587Core.Main
import ErdosProblems.Erdos13.Erdos13Kneser
import ErdosProblems.Erdos13.Erdos13Additive
import ErdosProblems.Erdos1211.External.Erdos360.DiverseSampling
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
open scoped BigOperators Pointwise
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open Erdos851.BetaSieveFundamental

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
  letI : NeZero d := ⟨hd.ne'⟩
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
  letI : NeZero d := ⟨hd.ne'⟩
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
  letI : NeZero d := ⟨by omega⟩
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
  letI : NeZero d := ⟨by omega⟩
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
      letI : NeZero t := ⟨htPos.ne'⟩
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
  letI : NeZero d := ⟨hd.ne'⟩
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
  letI : NeZero d := ⟨hd.ne'⟩
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
  letI : NeZero q := ⟨hq.ne'⟩
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
    letI : NeZero q := ⟨hq.ne'⟩
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
    (a d : ZMod b) (hproper : IsProperCyclicCosetProgression H a d length)
    (hsmall : (Nat.card H) ^ 3 <
      (cyclicCosetProgression H a d length).card) :
    HasLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (6 * (cyclicCosetProgression H a d length).card) := by
  let Hn := b / q
  let n := Nat.sqrt length
  let m := n + 1
  have hHn : 0 < Hn := by
    exact Nat.div_pos (Nat.le_of_dvd hb hqb) hq
  have hn : 0 < n := by simpa [n] using Nat.sqrt_pos.2 hlength
  have hm : 0 < m := by dsimp [m]; omega
  have hcardH : Nat.card H = Hn := by
    exact natCard_subgroup_of_generator_modulus hb hq hqb H hHdiv hmult
  have hRcard : (cyclicCosetProgression H a d length).card = length * Hn := by
    rw [cyclicCosetProgression_card_eq_of_proper H a d hproper, hcardH]
  have hsmall' : Hn ^ 3 < length * Hn := by
    simpa [hcardH, hRcard] using hsmall
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
      _ = 6 * (cyclicCosetProgression H a d length).card := by rw [hRcard]
  · intro idx
    rw [card_shiftedZmodValues, hRcard]
    have hQlen : (Q idx).length = m := by simp [Q]
    rw [hQlen]
    exact hlong.le


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
  · exact small_subgroup_shifted_longProgressionCover hb hq hqb hlength
      H hHdiv hmult a d hproper (Nat.lt_of_not_ge hlarge)

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
  letI : NeZero d := ⟨hdpos.ne'⟩
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : NeZero q := ⟨hq.ne'⟩
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) ↦ x.1)
      Subtype.val_injective
  simp [liftFinsetToClosure]

lemma card_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : (liftFinsetToClosure X).card = X.card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
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
  letI : Fintype H :=
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
  letI : Fintype H :=
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

/-! ## Deterministic modular phase recursion -/

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
  letI : Fintype H :=
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

/-- A canonical choice for the next phase.  In a growth phase it uses the
internal multiplicative-growth witness; in an unsaturated phase it uses the
large-translation witness; otherwise it removes an arbitrary remaining
element. -/
noncomputable def modularPhasePick
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · by_cases hg : IsModularGrowthPhase hb R₀ R E
    · exact (Classical.choose
        (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
          (fun d hd hdq => hdiverse d hd
            (hdq.trans (closureModulus_dvd hb R))) hg)).1
    · by_cases hu : HasUnsaturatedFiber R₀ R E
      · exact Classical.choose
          (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
            (fun d hd hdq => hdiverse d hd
              (hdq.trans (closureModulus_dvd hb R))) hg hu)
      · exact hR.choose
  · exact 0

lemma modularPhasePick_mem
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (R : Finset (ZMod b)) (hR : R.Nonempty) :
    modularPhasePick hb R₀ E hE hdiverse R ∈ R := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR]
  by_cases hg : IsModularGrowthPhase hb R₀ R E
  · rw [dif_pos hg]
    exact (Classical.choose_spec
        (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
          (fun d hd hdq => hdiverse d hd
            (hdq.trans (closureModulus_dvd hb R))) hg)).1
  · rw [dif_neg hg]
    by_cases hu : HasUnsaturatedFiber R₀ R E
    · rw [dif_pos hu]
      exact (Classical.choose_spec
        (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
          (fun d hd hdq => hdiverse d hd
            (hdq.trans (closureModulus_dvd hb R))) hg hu)).1
    · rw [dif_neg hu]
      exact hR.choose_spec

lemma modularPhasePick_internal_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
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
    (fun d hd hdq => hdiverse d hd
      (hdq.trans (closureModulus_dvd hb R))) hg
  let x := Classical.choose hex
  have hxSpec := (Classical.choose_spec hex).2
  have hpick : modularPhasePick hb R₀ E hE hdiverse R = x.1 := by
    simp only [modularPhasePick, dif_pos hR, dif_pos hg, hex, x]
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hg : ¬IsModularGrowthPhase hb R₀ R E)
    (hu : HasUnsaturatedFiber R₀ R E) :
    R.card ≤ 16 * (Erdos360.translationNew
      (E + (R₀ \ R).subsetSum)
      (modularPhasePick hb R₀ E hE hdiverse R)).card := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR, dif_neg hg, dif_pos hu]
  exact (Classical.choose_spec
    (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
      (fun d hd hdq => hdiverse d hd
        (hdq.trans (closureModulus_dvd hb R))) hg hu)).2

noncomputable def modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (i : ℕ) : Finset (ZMod b) :=
  E + (R₀ \ modularRemainder hb R₀ E hE hdiverse i).subsetSum

@[simp] lemma modularRemainder_zero
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    modularRemainder hb R₀ E hE hdiverse 0 = R₀ := rfl

lemma modularRemainder_succ_of_nonempty
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    ∀ i : ℕ, modularRemainder hb R₀ E hE hdiverse i ⊆ R₀ := by
  intro i
  induction i with
  | zero => exact fun _ hx => hx
  | succ i ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse i).trans ih

lemma card_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (R₀ \ modularRemainder hb R₀ E hE hdiverse i).card = i := by
  rw [Finset.card_sdiff_of_subset
    (modularRemainder_subset_initial hb R₀ E hE hdiverse i)]
  rw [card_modularRemainder hb R₀ E hE hdiverse hi]
  omega

lemma modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i : ℕ} (hi : i < R₀.card)
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
  have hused : R₀ \ T = insert x U := by
    rw [hT]
    exact sdiff_erase_eq_insert_sdiff hxR
      (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hgrowth := modularPhasePick_internal_growth
    hb R₀ E hE hdiverse R hRne hg
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
  letI : Fintype H :=
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun i =>
    IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E

/-- Binary logarithms of the current subgroup modulus and its internal
subset-sum cardinality.  Both coordinates lie between zero and `log₂ b`. -/
noncomputable def modularGrowthCode
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < R₀.card)
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
      (by omega) hgi hqiSucc
  have hmonoIJ : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) ≤ cj := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqiSucc.symm.trans hqEqIJ
  have hgrowJ : 3 * cj ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) hgj hqjSucc
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
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {k : ℕ} (hk : k ≤ R₀.card) :
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

/-! ### Saturation-or-quadratic modular growth -/

noncomputable def modularNonGrowthIndices
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun i =>
    ¬IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E

lemma card_modularGrowth_add_nonGrowth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (k : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse k).card +
      (modularNonGrowthIndices hb R₀ E hE hdiverse k).card = k := by
  classical
  simpa [modularGrowthIndices, modularNonGrowthIndices] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range k) (p := fun i =>
        IsModularGrowthPhase hb R₀
          (modularRemainder hb R₀ E hE hdiverse i) E))

lemma modularPhaseSums_succ_subset
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i : ℕ} (hi : i < R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆
      modularPhaseSums hb R₀ E hE hdiverse (i + 1) := by
  rw [modularPhaseSums_succ hb R₀ E hE hdiverse hi]
  exact Finset.subset_union_left

lemma modularPhaseSums_mono
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆
      modularPhaseSums hb R₀ E hE hdiverse j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      have ih' := ih (by omega) (by omega)
      exact ih'.trans (modularPhaseSums_succ_subset hb R₀ E hE hdiverse
        (by omega))

lemma card_modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {i : ℕ} (hi : i < R₀.card) :
    (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card =
      (modularPhaseSums hb R₀ E hE hdiverse i).card +
        (translationNew
          (modularPhaseSums hb R₀ E hE hdiverse i)
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))).card := by
  rw [modularPhaseSums_succ hb R₀ E hE hdiverse hi]
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate
      (modularPhasePick hb R₀ E hE hdiverse
        (modularRemainder hb R₀ E hE hdiverse i))
      (modularPhaseSums hb R₀ E hE hdiverse i))
    (modularPhaseSums hb R₀ E hE hdiverse i)
  dsimp [translationNew] at hsdiff ⊢
  rw [Finset.union_comm] at hsdiff
  omega

lemma modular_nonGrowth_quadratic_lower
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {k : ℕ} (hk : k ≤ R₀.card)
    (hunsat : ∀ i < k, ¬IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E →
      HasUnsaturatedFiber R₀
        (modularRemainder hb R₀ E hE hdiverse i) E) :
    (modularNonGrowthIndices hb R₀ E hE hdiverse k).card *
        (R₀.card - k) ≤
      16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  classical
  induction k with
  | zero => simp [modularNonGrowthIndices]
  | succ k ih =>
      have hklt : k < R₀.card := by omega
      have ih' := ih (by omega)
        (fun i hi => hunsat i (by omega))
      have hcardR :
          (modularRemainder hb R₀ E hE hdiverse k).card = R₀.card - k :=
        card_modularRemainder hb R₀ E hE hdiverse (by omega)
      have hcardS := card_modularPhaseSums_succ
        hb R₀ E hE hdiverse hklt
      by_cases hg : IsModularGrowthPhase hb R₀
          (modularRemainder hb R₀ E hE hdiverse k) E
      · have hng :
          (modularNonGrowthIndices hb R₀ E hE hdiverse (k + 1)).card =
            (modularNonGrowthIndices hb R₀ E hE hdiverse k).card := by
          change ((Finset.range (Nat.succ k)).filter fun i =>
              ¬IsModularGrowthPhase hb R₀
                (modularRemainder hb R₀ E hE hdiverse i) E).card =
            ((Finset.range k).filter fun i =>
              ¬IsModularGrowthPhase hb R₀
                (modularRemainder hb R₀ E hE hdiverse i) E).card
          rw [show Nat.succ k = k + 1 by omega,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hng]
        calc
          (modularNonGrowthIndices hb R₀ E hE hdiverse k).card *
                (R₀.card - (k + 1)) ≤
              (modularNonGrowthIndices hb R₀ E hE hdiverse k).card *
                (R₀.card - k) := by gcongr <;> omega
          _ ≤ 16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := ih'
          _ ≤ 16 * (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card := by
            rw [hcardS]
            omega
      · have hu := hunsat k (by omega) hg
        have hstep := modularPhasePick_unsaturated_growth
          hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse k)
          (by
            apply Finset.card_pos.mp
            rw [hcardR]
            omega)
          hg hu
        have hng :
          (modularNonGrowthIndices hb R₀ E hE hdiverse (k + 1)).card =
            (modularNonGrowthIndices hb R₀ E hE hdiverse k).card + 1 := by
          change ((Finset.range (Nat.succ k)).filter fun i =>
              ¬IsModularGrowthPhase hb R₀
                (modularRemainder hb R₀ E hE hdiverse i) E).card =
            ((Finset.range k).filter fun i =>
              ¬IsModularGrowthPhase hb R₀
                (modularRemainder hb R₀ E hE hdiverse i) E).card + 1
          rw [show Nat.succ k = k + 1 by omega,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hng]
        change (modularRemainder hb R₀ E hE hdiverse k).card ≤ 16 *
          (translationNew (modularPhaseSums hb R₀ E hE hdiverse k)
            (modularPhasePick hb R₀ E hE hdiverse
              (modularRemainder hb R₀ E hE hdiverse k))).card at hstep
        rw [hcardR] at hstep
        calc
          ((modularNonGrowthIndices hb R₀ E hE hdiverse k).card + 1) *
                (R₀.card - (k + 1)) ≤
              ((modularNonGrowthIndices hb R₀ E hE hdiverse k).card + 1) *
                (R₀.card - k) := by gcongr <;> omega
          _ = (modularNonGrowthIndices hb R₀ E hE hdiverse k).card *
                (R₀.card - k) + (R₀.card - k) := by ring
          _ ≤ 16 * (modularPhaseSums hb R₀ E hE hdiverse k).card +
                16 * (translationNew
                  (modularPhaseSums hb R₀ E hE hdiverse k)
                  (modularPhasePick hb R₀ E hE hdiverse
                    (modularRemainder hb R₀ E hE hdiverse k))).card :=
            Nat.add_le_add ih' hstep
          _ = 16 * (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card := by
            rw [hcardS]
            ring

theorem saturated_or_modular_quadratic_lower
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    {k : ℕ} (hk : k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      (k - 2 * (Nat.log 2 b + 1) ^ 2) * (R₀.card - k) ≤
        16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  classical
  by_cases hs : ∃ i < k, ¬HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E
  · left
    obtain ⟨i, hik, hiSat⟩ := hs
    have hiR : i ≤ R₀.card := hik.le.trans hk
    have hsat := saturated_modularPhase_card hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E hE
      (fun d hd hdq => hdiverse d hd
        (hdq.trans (closureModulus_dvd hb _))) hiSat
    exact hsat.trans (Nat.mul_le_mul_left 4
      (Finset.card_le_card
        (modularPhaseSums_mono hb R₀ E hE hdiverse hik.le hk)))
  · right
    push_neg at hs
    have hquad := modular_nonGrowth_quadratic_lower hb R₀ E hE hdiverse hk
      (fun i hi _ => hs i hi)
    have hgcard := card_modularGrowthIndices_le
      hb R₀ E hE hdiverse hk
    have hpartition := card_modularGrowth_add_nonGrowth
      hb R₀ E hE hdiverse k
    have hng : k - 2 * (Nat.log 2 b + 1) ^ 2 ≤
        (modularNonGrowthIndices hb R₀ E hE hdiverse k).card := by
      omega
    exact (Nat.mul_le_mul_right (R₀.card - k) hng).trans hquad

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

/-- The real-valued scale in the Conlon--Fox--Pham resolution. -/
noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (1 / 3 : ℝ) *
      ((n : ℝ) / (Nat.totient n : ℝ)) /
    (Real.rpow (Real.log n) (1 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log n)) (2 / 3 : ℝ))

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
