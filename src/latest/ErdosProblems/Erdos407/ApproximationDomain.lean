/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicSubspaceDefs

/-!
# Approximation domains for the rational `{infinity, 2, 3}` problem

This file packages the elementary part of the approximation-domain argument
used in the rational Subspace Theorem.  An array of integer exponents gives,
at each of the three places and for each form, a radius which is a power of a
common integral height parameter.  The rank of a domain is the dimension of
its rational span; equivalently, it is the largest size of a linearly
independent family of points in the domain.

No compactness, geometry of numbers, or Subspace-Theorem input is used here.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

/-- One integer exponent for every local form at each of the three places. -/
abbrev LocalExponents (n : ℕ) := Place23 → Fin n → ℤ

/-- Exponent arrays whose entries lie in one fixed integer interval form a
finite set.  Height-box estimates can therefore turn the reverse bucketing
lemma below into a genuinely finite union of domains once they supply uniform
lower and upper bounds for the individual local exponents. -/
theorem finite_localExponent_box (n : ℕ) (lo hi : ℤ) :
    {e : LocalExponents n | ∀ v i, lo ≤ e v i ∧ e v i ≤ hi}.Finite := by
  let I : Finset ℤ := Finset.Icc lo hi
  have hfinite :
      (Set.univ.pi fun _ : Place23 ↦
        Set.univ.pi fun _ : Fin n ↦ (I : Set ℤ)).Finite :=
    Set.Finite.pi fun _ ↦ Set.Finite.pi fun _ ↦ I.finite_toSet
  apply hfinite.subset
  intro e he v _ i _
  exact Finset.mem_Icc.mpr (he v i)

/-- The finite box of local exponent arrays with entries in `[lo, hi]`. -/
noncomputable def localExponentBox (n : ℕ) (lo hi : ℤ) :
    Finset (LocalExponents n) :=
  (finite_localExponent_box n lo hi).toFinset

@[simp] theorem mem_localExponentBox {n : ℕ} {lo hi : ℤ}
    {e : LocalExponents n} :
    e ∈ localExponentBox n lo hi ↔ ∀ v i, lo ≤ e v i ∧ e v i ≤ hi := by
  simp [localExponentBox]

/-- The sum of all `3n` local exponents. -/
def localExponentSum {n : ℕ} (e : LocalExponents n) : ℤ :=
  ∑ v, ∑ i, e v i

/-- The rational radius `Q^a` attached to an integral height and an integer
local exponent. -/
def localRadius (Q : ℕ) (a : ℤ) : ℚ :=
  (Q : ℚ) ^ a

theorem localRadius_nonneg (Q : ℕ) (a : ℤ) : 0 ≤ localRadius Q a := by
  exact zpow_nonneg (Nat.cast_nonneg Q) a

theorem localRadius_pos {Q : ℕ} (hQ : 0 < Q) (a : ℤ) : 0 < localRadius Q a := by
  exact zpow_pos (by exact_mod_cast hQ) a

theorem localRadius_add {Q : ℕ} (hQ : 0 < Q) (a b : ℤ) :
    localRadius Q (a + b) = localRadius Q a * localRadius Q b := by
  exact zpow_add₀ (by positivity : (Q : ℚ) ≠ 0) a b

/-- Every positive rational number lies in a half-open bucket between two
successive powers of an integral base greater than one. -/
theorem exists_strict_localExponent_bucket {Q : ℕ} (hQ : 2 ≤ Q)
    {q : ℚ} (hq : 0 < q) :
    ∃ a : ℤ, localRadius Q (a - 1) < q ∧ q ≤ localRadius Q a := by
  have hbase : (1 : ℚ) < Q := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hQ)
  obtain ⟨a, ha, ha'⟩ := exists_mem_Ioc_zpow hq hbase
  refine ⟨a + 1, ?_, ?_⟩
  · simpa [localRadius] using ha
  · simpa [localRadius] using ha'

/-- A weak upper bucket also exists for zero. -/
theorem exists_upper_localExponent {Q : ℕ} (hQ : 2 ≤ Q)
    {q : ℚ} (hq : 0 ≤ q) :
    ∃ a : ℤ, q ≤ localRadius Q a := by
  obtain rfl | hq := hq.eq_or_lt
  · exact ⟨0, localRadius_nonneg Q 0⟩
  · obtain ⟨a, _ha, ha'⟩ := exists_strict_localExponent_bucket hQ hq
    exact ⟨a, ha'⟩

/-- The rational points satisfying all local approximation inequalities at
height `Q`. -/
def approximationDomain {n : ℕ} (Q : ℕ)
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n) :
    Set (Fin n → ℚ) :=
  {x | ∀ v i, placeNorm v (L v i x) ≤ localRadius Q (e v i)}

@[simp] theorem mem_approximationDomain {n Q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} {e : LocalExponents n}
    {x : Fin n → ℚ} :
    x ∈ approximationDomain Q L e ↔
      ∀ v i, placeNorm v (L v i x) ≤ localRadius Q (e v i) :=
  Iff.rfl

theorem zero_mem_approximationDomain {n Q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n) :
    (0 : Fin n → ℚ) ∈ approximationDomain Q L e := by
  intro v i
  simp only [map_zero, placeNorm_zero]
  exact localRadius_nonneg Q (e v i)

/-- Increasing every exponent enlarges the domain when `Q ≥ 1`. -/
theorem approximationDomain_mono_exponents {n Q : ℕ} (hQ : 1 ≤ Q)
    (L : Place23 → Fin n → RatLinearForm n) {e f : LocalExponents n}
    (hef : ∀ v i, e v i ≤ f v i) :
    approximationDomain Q L e ⊆ approximationDomain Q L f := by
  intro x hx v i
  exact (hx v i).trans
    (zpow_le_zpow_right₀ (by exact_mod_cast hQ) (hef v i))

/-- For nonnegative exponents, increasing the height parameter enlarges the
domain. -/
theorem approximationDomain_mono_height {n Q R : ℕ} (hQR : Q ≤ R)
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n)
    (he : ∀ v i, 0 ≤ e v i) :
    approximationDomain Q L e ⊆ approximationDomain R L e := by
  intro x hx v i
  exact (hx v i).trans
    (zpow_le_zpow_left₀ (he v i) (Nat.cast_nonneg Q) (by exact_mod_cast hQR))

/-- Add a place-dependent exponent to every form exponent. -/
def shiftLocalExponents {n : ℕ} (e : LocalExponents n) (s : Place23 → ℤ) :
    LocalExponents n :=
  fun v i ↦ e v i + s v

@[simp] theorem shiftLocalExponents_apply {n : ℕ} (e : LocalExponents n)
    (s : Place23 → ℤ) (v : Place23) (i : Fin n) :
    shiftLocalExponents e s v i = e v i + s v :=
  rfl

/-- Scaling a point shifts all exponents at a fixed place by the same amount,
provided the scalar has the corresponding local bounds. -/
theorem smul_mem_approximationDomain {n Q : ℕ} (hQ : 0 < Q)
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n)
    {x : Fin n → ℚ} (hx : x ∈ approximationDomain Q L e)
    (a : ℚ) (s : Place23 → ℤ)
    (ha : ∀ v, placeNorm v a ≤ localRadius Q (s v)) :
    a • x ∈ approximationDomain Q L (shiftLocalExponents e s) := by
  intro v i
  rw [LinearMap.map_smul]
  change placeNorm v (a * L v i x) ≤ _
  rw [placeNorm_mul, shiftLocalExponents_apply,
    localRadius_add hQ]
  rw [mul_comm (localRadius Q (e v i)) (localRadius Q (s v))]
  exact mul_le_mul (ha v) (hx v i) (placeNorm_nonneg v (L v i x))
    (localRadius_nonneg Q (s v))

/-- The product of the radii in an exponent array is the power belonging to
the sum of its entries. -/
theorem prod_localRadius {n Q : ℕ} (hQ : 0 < Q) (e : LocalExponents n) :
    (∏ v, ∏ i, localRadius Q (e v i)) =
      localRadius Q (localExponentSum e) := by
  classical
  simp only [localRadius, localExponentSum]
  have hQ0 : (Q : ℚ) ≠ 0 := by positivity
  have hinner (v : Place23) (s : Finset (Fin n)) :
      (∏ i ∈ s, (Q : ℚ) ^ e v i) = (Q : ℚ) ^ (∑ i ∈ s, e v i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hQ0]
  have houter (s : Finset Place23) :
      (∏ v ∈ s, (Q : ℚ) ^ (∑ i, e v i)) =
        (Q : ℚ) ^ (∑ v ∈ s, ∑ i, e v i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
        rw [Finset.prod_insert hv, Finset.sum_insert hv, ih, zpow_add₀ hQ0]
  calc
    (∏ v, ∏ i, (Q : ℚ) ^ e v i) =
        ∏ v, (Q : ℚ) ^ (∑ i, e v i) := by
          apply Finset.prod_congr rfl
          intro v _
          simpa using hinner v Finset.univ
    _ = (Q : ℚ) ^ (∑ v, ∑ i, e v i) := by
      simpa using houter Finset.univ

/-- Local coordinate bounds imply the corresponding bound for the full local
form product. -/
theorem localFormProduct_le_of_mem_approximationDomain {n Q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} {e : LocalExponents n}
    {x : Fin n → ℚ} (hx : x ∈ approximationDomain Q L e) :
    localFormProduct L x ≤ ∏ v, ∏ i, localRadius Q (e v i) := by
  refine Finset.prod_le_prod ?_ ?_
  · intro v _
    exact Finset.prod_nonneg fun i _ ↦ placeNorm_nonneg v (L v i x)
  · intro v _
    refine Finset.prod_le_prod ?_ ?_
    · intro i _
      exact placeNorm_nonneg v (L v i x)
    · intro i _
      exact hx v i

/-- An exponent array whose total exponent is at most `-1` turns membership
in the height-`Q` approximation domain into the strong product inequality for
every integral point of box height at most `Q`. -/
theorem satisfiesStrongInequality_of_mem_approximationDomain {n Q : ℕ}
    (hQ : 1 ≤ Q) {L : Place23 → Fin n → RatLinearForm n}
    {e : LocalExponents n} (hesum : localExponentSum e ≤ -1)
    {x : Fin n → ℤ} (hxQ : boxHeight x ≤ Q)
    (hx : intCastVec x ∈ approximationDomain Q L e) :
    SatisfiesStrongInequality L x := by
  have hprod : localFormProduct L (intCastVec x) ≤
      localRadius Q (localExponentSum e) := by
    exact (localFormProduct_le_of_mem_approximationDomain hx).trans_eq
      (prod_localRadius (Nat.zero_lt_of_lt hQ) e)
  have hpow : localRadius Q (localExponentSum e) ≤ localRadius Q (-1) := by
    exact zpow_le_zpow_right₀ (by exact_mod_cast hQ) hesum
  have hheight : (boxHeight x : ℚ) ≤ Q := by exact_mod_cast hxQ
  have hQpos : (0 : ℚ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  calc
    localFormProduct L (intCastVec x) * boxHeight x
        ≤ localRadius Q (localExponentSum e) * boxHeight x :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
    _ ≤ localRadius Q (-1) * boxHeight x :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ localRadius Q (-1) * Q :=
          mul_le_mul_of_nonneg_left hheight (localRadius_nonneg Q (-1))
    _ = 1 := by
          simp [localRadius, ne_of_gt hQpos]

/-- The integral points in a small-total-exponent domain are contained in the
set cut out by the strong inequality. -/
theorem approximationDomain_intCast_subset_strong {n Q : ℕ}
    (hQ : 1 ≤ Q) (L : Place23 → Fin n → RatLinearForm n)
    (e : LocalExponents n) (hesum : localExponentSum e ≤ -1) :
    {x : Fin n → ℤ |
        boxHeight x ≤ Q ∧ intCastVec x ∈ approximationDomain Q L e} ⊆
      {x | SatisfiesStrongInequality L x} := by
  intro x hx
  exact satisfiesStrongInequality_of_mem_approximationDomain hQ hesum hx.1 hx.2

/-! ## Reverse bucketing of a strong solution -/

/-- The nested sum defining `localExponentSum` can equivalently be written as
a single sum over local-form pairs. -/
theorem localExponentSum_eq_sum_prod {n : ℕ} (e : LocalExponents n) :
    localExponentSum e = ∑ p : Place23 × Fin n, e p.1 p.2 := by
  classical
  rw [localExponentSum, ← Finset.sum_product' Finset.univ Finset.univ]
  simp

/-- The local form product can likewise be flattened to local-form pairs. -/
theorem localFormProduct_eq_prod_prod {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : Fin n → ℚ) :
    localFormProduct L x =
      ∏ p : Place23 × Fin n, placeNorm p.1 (L p.1 p.2 x) := by
  classical
  rw [localFormProduct, ← Finset.prod_product' Finset.univ Finset.univ]
  simp

/-- A strong solution can be bucketed in an integer-exponent approximation
domain.  Because rounding is done independently in `3n` coordinates, the
sharp elementary total available without additional slack is `3n - 2`.
If a local factor vanishes, the construction in fact gives total `-1` by
putting all balancing error in that zero coordinate.

The scale is taken below the actual box height, which is the direction needed
to convert `product * height ≤ 1` into `product ≤ Q⁻¹`. -/
theorem exists_exponents_mem_approximationDomain_of_strong {n Q : ℕ}
    (hn : 0 < n) (hQ : 2 ≤ Q)
    {L : Place23 → Fin n → RatLinearForm n} {x : Fin n → ℤ}
    (hx : SatisfiesStrongInequality L x) (hQx : Q ≤ boxHeight x) :
    ∃ e : LocalExponents n,
      intCastVec x ∈ approximationDomain Q L e ∧
        localExponentSum e ≤ 3 * (n : ℤ) - 2 := by
  classical
  let A : Place23 → Fin n → ℚ :=
    fun v i ↦ placeNorm v (L v i (intCastVec x))
  have hA_nonneg (v : Place23) (i : Fin n) : 0 ≤ A v i :=
    placeNorm_nonneg v (L v i (intCastVec x))
  have hQposN : 0 < Q := by omega
  have hQpos : (0 : ℚ) < Q := by exact_mod_cast hQposN
  have hprodQ : localFormProduct L (intCastVec x) * Q ≤ 1 := by
    calc
      localFormProduct L (intCastVec x) * Q ≤
          localFormProduct L (intCastVec x) * boxHeight x :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hQx)
          (localFormProduct_nonneg L (intCastVec x))
      _ ≤ 1 := hx
  have hprod : localFormProduct L (intCastVec x) ≤ localRadius Q (-1) := by
    simpa [localRadius, div_eq_mul_inv] using (le_div_iff₀ hQpos).2 hprodQ
  by_cases hzero : ∃ p : Place23 × Fin n, A p.1 p.2 = 0
  · obtain ⟨j, hj⟩ := hzero
    choose u hu using fun (v : Place23) (i : Fin n) ↦
      exists_upper_localExponent hQ (hA_nonneg v i)
    let u' : Place23 × Fin n → ℤ := fun p ↦ u p.1 p.2
    let b : ℤ := -1 - ∑ p ∈ (Finset.univ.erase j), u' p
    let e : LocalExponents n := fun v i ↦ if (v, i) = j then b else u v i
    refine ⟨e, ?_, ?_⟩
    · intro v i
      by_cases hvi : (v, i) = j
      · have hzero' : A v i = 0 := by
          cases hvi
          exact hj
        change A v i ≤ localRadius Q (e v i)
        rw [hzero']
        exact localRadius_nonneg Q (e v i)
      · change A v i ≤ localRadius Q (e v i)
        simpa [e, hvi] using hu v i
    · have hsum : localExponentSum e = -1 := by
        rw [localExponentSum_eq_sum_prod]
        change (∑ p : Place23 × Fin n,
          if p = j then b else u' p) = -1
        rw [← Finset.sum_erase_add Finset.univ
          (fun p ↦ if p = j then b else u' p) (Finset.mem_univ j)]
        have herase :
            (∑ p ∈ Finset.univ.erase j, if p = j then b else u' p) =
              ∑ p ∈ Finset.univ.erase j, u' p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [(Finset.mem_erase.mp hp).1]
        rw [herase]
        simp [b]
      rw [hsum]
      have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
      omega
  · push Not at hzero
    have hA_pos (v : Place23) (i : Fin n) : 0 < A v i :=
      (hA_nonneg v i).lt_of_ne (Ne.symm (hzero (v, i)))
    choose e he_lower he_upper using fun (v : Place23) (i : Fin n) ↦
      exists_strict_localExponent_bucket hQ (hA_pos v i)
    refine ⟨e, ?_, ?_⟩
    · intro v i
      exact he_upper v i
    · let e' : LocalExponents n := fun v i ↦ e v i - 1
      have hinner (v : Place23) :
          (∏ i, localRadius Q (e' v i)) < ∏ i, A v i := by
        apply Finset.prod_lt_prod_of_nonempty
        · intro i _
          exact localRadius_pos hQposN (e' v i)
        · intro i _
          exact he_lower v i
        · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have hstrict :
          (∏ v, ∏ i, localRadius Q (e' v i)) <
            localFormProduct L (intCastVec x) := by
        rw [localFormProduct]
        apply Finset.prod_lt_prod_of_nonempty
        · intro v _
          exact Finset.prod_pos fun i _ ↦ localRadius_pos hQposN (e' v i)
        · intro v _
          exact hinner v
        · exact Finset.univ_nonempty
      have hsum_e' :
          localExponentSum e' = localExponentSum e - 3 * (n : ℤ) := by
        simp only [e', localExponentSum, Finset.sum_sub_distrib]
        simp
      have hpowers :
          localRadius Q (localExponentSum e - 3 * (n : ℤ)) <
            localRadius Q (-1) := by
        rw [← hsum_e', ← prod_localRadius hQposN e']
        exact hstrict.trans_le hprod
      have hexponents : localExponentSum e - 3 * (n : ℤ) < -1 :=
        (zpow_lt_zpow_iff_right₀ (by exact_mod_cast
          (lt_of_lt_of_le (by omega : 1 < 2) hQ))).mp hpowers
      omega

/-! ## Rank and hyperplane containment -/

/-- The rank of a set of rational vectors: the dimension of its rational
linear span. -/
noncomputable def rationalSetRank {n : ℕ} (D : Set (Fin n → ℚ)) : ℕ :=
  D.finrank ℚ

/-- The rank of an approximation domain. -/
noncomputable def approximationDomainRank {n : ℕ} (Q : ℕ)
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n) : ℕ :=
  rationalSetRank (approximationDomain Q L e)

/-- A set contains an independent family whose size is its rank. -/
theorem exists_independent_family_card_rationalSetRank {n : ℕ}
    (D : Set (Fin n → ℚ)) :
    ∃ f : Fin (rationalSetRank D) → (Fin n → ℚ),
      LinearIndependent ℚ f ∧ ∀ i, f i ∈ D := by
  obtain ⟨f, hfD, _hspan, hfi⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ D
  exact ⟨f, hfi, hfD⟩

/-- Every independent family drawn from a set has size at most its rank. -/
theorem card_le_rationalSetRank_of_linearIndependent {n r : ℕ}
    {D : Set (Fin n → ℚ)} {f : Fin r → (Fin n → ℚ)}
    (hfi : LinearIndependent ℚ f) (hfD : ∀ i, f i ∈ D) :
    r ≤ rationalSetRank D := by
  have hspan : Submodule.span ℚ (Set.range f) ≤ Submodule.span ℚ D :=
    Submodule.span_mono fun x hx ↦ by
      obtain ⟨i, rfl⟩ := hx
      exact hfD i
  calc
    r = Module.finrank ℚ (Submodule.span ℚ (Set.range f)) := by
      simpa using (finrank_span_eq_card hfi).symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ D) :=
      Submodule.finrank_mono hspan
    _ = rationalSetRank D := rfl

/-- `rationalSetRank` is exactly the largest number of independent points
which can be chosen from the set. -/
theorem rationalSetRank_eq_maximal_independent {n : ℕ}
    (D : Set (Fin n → ℚ)) :
    (∃ f : Fin (rationalSetRank D) → (Fin n → ℚ),
        LinearIndependent ℚ f ∧ ∀ i, f i ∈ D) ∧
      (∀ (r : ℕ) (f : Fin r → (Fin n → ℚ)),
        LinearIndependent ℚ f → (∀ i, f i ∈ D) → r ≤ rationalSetRank D) := by
  exact ⟨exists_independent_family_card_rationalSetRank D,
    fun _ _ hfi hfD ↦ card_le_rationalSetRank_of_linearIndependent hfi hfD⟩

theorem rationalSetRank_mono {n : ℕ} {D E : Set (Fin n → ℚ)}
    (hDE : D ⊆ E) : rationalSetRank D ≤ rationalSetRank E := by
  exact Submodule.finrank_mono (Submodule.span_mono hDE)

theorem approximationDomainRank_mono {n Q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} {e f : LocalExponents n}
    (hef : approximationDomain Q L e ⊆ approximationDomain Q L f) :
    approximationDomainRank Q L e ≤ approximationDomainRank Q L f :=
  rationalSetRank_mono hef

/-- No set of rational `n`-vectors has rank greater than `n`. -/
theorem rationalSetRank_le_dimension {n : ℕ} (D : Set (Fin n → ℚ)) :
    rationalSetRank D ≤ n := by
  simpa [rationalSetRank, Set.finrank] using
    (Submodule.finrank_le (Submodule.span ℚ D))

theorem approximationDomainRank_le_dimension {n Q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n) :
    approximationDomainRank Q L e ≤ n :=
  rationalSetRank_le_dimension _

/-- If a set of rational vectors has rank below the ambient dimension, it is
contained in the kernel of a nonzero rational linear form. -/
theorem exists_nonzero_form_vanishes_on_of_rank_lt {n : ℕ}
    (D : Set (Fin n → ℚ)) (hrank : rationalSetRank D < n) :
    ∃ f : RatLinearForm n, f ≠ 0 ∧ ∀ x ∈ D, f x = 0 := by
  have hspan : Submodule.span ℚ D < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have : rationalSetRank D = n := by
      unfold rationalSetRank Set.finrank
      rw [htop]
      simp
    omega
  obtain ⟨f, hf, hle, _hker⟩ :=
    GeneralPosition.properSubspace_le_kernel (Submodule.span ℚ D) hspan
  exact ⟨f, hf, fun x hx ↦ hle (Submodule.subset_span hx)⟩

/-- In particular, rank drop for an approximation domain puts the whole
domain in one proper rational hyperplane. -/
theorem approximationDomain_subset_hyperplane_of_rank_lt {n Q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (e : LocalExponents n)
    (hrank : approximationDomainRank Q L e < n) :
    ∃ f : RatLinearForm n, f ≠ 0 ∧
      ∀ x ∈ approximationDomain Q L e, f x = 0 :=
  exists_nonzero_form_vanishes_on_of_rank_lt _ hrank

end Erdos407.PadicSubspace
