import ErdosProblems.Erdos486.FiniteAveraging

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weighted enumeration for the biased four-colouring argument

This file is a purely finite replacement for conditioning on anchor colours.
It proves that a product of one-coordinate weights read through an injective
oracle has the product of the corresponding one-coordinate averages.  The
biased candidate weight then has exact average

`(1 / 8) ^ |S| * (21 / 32) ^ (k - |S|)`.

For `k = 6r`, summing over all `S` and multiplying by `2 ^ (2r)` gives
exactly `(15625 / 16384) ^ (2r)`, which is at most
`(63 / 64) ^ (2r)`.  No probability or measure theory is used.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section ColoringEnumeration

/-! ## Product averages through an injective oracle -/

variable {α β κ ι : Type*}

/-- Uniform averages are invariant under a finite equivalence. -/
theorem fintypeAverage_comp_equiv [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℚ) :
    fintypeAverage (fun x ↦ f (e x)) = fintypeAverage f := by
  rw [fintypeAverage, fintypeAverage, e.sum_comp,
    Fintype.card_congr e]

/-- Averaging a function of the first coordinate over a nonempty finite
product is the same as averaging over the first coordinate. -/
theorem fintypeAverage_prod_fst [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℚ) :
    fintypeAverage (fun x : α × β ↦ f x.1) = fintypeAverage f := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum :
      (∑ x : α × β, f x.1) =
        (Fintype.card β : ℚ) * ∑ x : α, f x := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [Finset.mul_sum]
  rw [fintypeAverage, fintypeAverage, hsum, Fintype.card_prod,
    Nat.cast_mul]
  field_simp

/-- The complement of the range of an embedding, as an explicit subtype. -/
abbrev EmbeddingComplement (e : κ ↪ ι) :=
  {x : ι // x ∉ Set.range e}

/-- Split the target of an embedding into its range and its complement, with
the original domain as the range summand. -/
noncomputable def embeddingSplitEquiv [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) : κ ⊕ EmbeddingComplement e ≃ ι := by
  classical
  exact
    (Equiv.sumCongr e.toEquivRange
      (Equiv.refl (EmbeddingComplement e))).trans
      (Equiv.sumCompl fun x : ι ↦ x ∈ Set.range e)

@[simp]
theorem embeddingSplitEquiv_apply_inl [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) (j : κ) :
    embeddingSplitEquiv e (Sum.inl j) = e j := by
  classical
  rfl

/-- A colouring of the target of an embedding is equivalently a colouring of
the embedded coordinates together with a colouring of the complement. -/
noncomputable def oracleColoringEquiv [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) :
    (FourColoring κ × FourColoring (EmbeddingComplement e)) ≃
      FourColoring ι :=
  (Equiv.sumArrowEquivProdArrow κ (EmbeddingComplement e) (Fin 4)).symm |>.trans
    ((embeddingSplitEquiv e).arrowCongr (Equiv.refl (Fin 4)))

@[simp]
theorem oracleColoringEquiv_apply_embedding [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι)
    (c : FourColoring κ × FourColoring (EmbeddingComplement e)) (j : κ) :
    oracleColoringEquiv e c (e j) = c.1 j := by
  classical
  have hsplit : (embeddingSplitEquiv e).symm (e j) = Sum.inl j := by
    apply (embeddingSplitEquiv e).injective
    simp
  change
    (Equiv.sumArrowEquivProdArrow κ (EmbeddingComplement e) (Fin 4)).symm c
        ((embeddingSplitEquiv e).symm (e j)) = c.1 j
  rw [hsplit]
  rcases c with ⟨c₁, c₂⟩
  exact Equiv.sumArrowEquivProdArrow_symm_apply_inl c₁ c₂ j

/-- Independent coordinate enumeration on a full finite function space. -/
theorem fintypeAverage_pi_prod [Fintype κ] [DecidableEq κ]
    (weight : κ → Fin 4 → ℚ) :
    fintypeAverage
        (fun c : FourColoring κ ↦ ∏ j, weight j (c j)) =
      ∏ j, (∑ colour : Fin 4, weight j colour) / 4 := by
  classical
  have hsum :
      (∑ c : FourColoring κ, ∏ j, weight j (c j)) =
        ∏ j, ∑ colour : Fin 4, weight j colour := by
    simpa [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (R := ℚ)
        (Finset.univ : Finset (Fin 4)) weight)
  have hcard : Fintype.card (FourColoring κ) =
      4 ^ Fintype.card κ := by
    simp [FourColoring]
  rw [fintypeAverage, hsum, hcard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  symm
  calc
    (∏ j, (∑ colour : Fin 4, weight j colour) / 4) =
        (∏ j, ∑ colour : Fin 4, weight j colour) /
          ∏ _j : κ, (4 : ℚ) := by
      exact Finset.prod_div_distrib _ _
    _ = (∏ j, ∑ colour : Fin 4, weight j colour) /
        4 ^ Fintype.card κ := by
      simp

/-- Generic oracle-product lemma.  Distinct oracle indices read distinct
coordinates of the four-colouring, so their uniform weighted average factors
exactly. -/
theorem expect_oracle_prod_embedding [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    (oracle : κ ↪ ι) (weight : κ → Fin 4 → ℚ) :
    fintypeAverage
        (fun c : FourColoring ι ↦
          ∏ j, weight j (c (oracle j))) =
      ∏ j, (∑ colour : Fin 4, weight j colour) / 4 := by
  classical
  let E := oracleColoringEquiv oracle
  calc
    fintypeAverage
        (fun c : FourColoring ι ↦
          ∏ j, weight j (c (oracle j))) =
        fintypeAverage
          (fun c : FourColoring κ × FourColoring (EmbeddingComplement oracle) ↦
            ∏ j, weight j ((E c) (oracle j))) := by
      exact (fintypeAverage_comp_equiv E _).symm
    _ = fintypeAverage
          (fun c : FourColoring κ × FourColoring (EmbeddingComplement oracle) ↦
            ∏ j, weight j (c.1 j)) := by
      congr 1
      funext c
      apply Fintype.prod_congr
      intro j
      exact congrArg (weight j) (by simp [E])
    _ = fintypeAverage
          (fun c : FourColoring κ ↦ ∏ j, weight j (c j)) := by
      exact fintypeAverage_prod_fst
        (α := FourColoring κ)
        (β := FourColoring (EmbeddingComplement oracle))
        (fun c : FourColoring κ ↦ ∏ j, weight j (c j))
    _ = ∏ j, (∑ colour : Fin 4, weight j colour) / 4 :=
      fintypeAverage_pi_prod weight

/-! ## One-coordinate weights -/

/-- Weight `1/2` on black and `1` on each non-black colour. -/
def halfBlackWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 1 / 2 else 1

/-- A selected anchor must be black and contributes its `1/2` weight. -/
def selectedAnchorWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 1 / 2 else 0

/-- A fresh query must be non-black. -/
def nonblackQueryWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 0 else 1

theorem average_selectedAnchorWeight :
    (∑ colour : Fin 4, selectedAnchorWeight colour) / 4 =
      (1 : ℚ) / 8 := by
  rw [Fin.sum_univ_four]
  norm_num [selectedAnchorWeight, Fin.ext_iff]

theorem average_halfBlackWeight :
    (∑ colour : Fin 4, halfBlackWeight colour) / 4 =
      (7 : ℚ) / 8 := by
  rw [Fin.sum_univ_four]
  norm_num [halfBlackWeight, Fin.ext_iff]

theorem average_nonblackQueryWeight :
    (∑ colour : Fin 4, nonblackQueryWeight colour) / 4 =
      (3 : ℚ) / 4 := by
  rw [Fin.sum_univ_four]
  norm_num [nonblackQueryWeight, Fin.ext_iff]

/-! ## Candidate oracle and its exact weighted average -/

/-- Oracle indices consist of all anchors and one fresh query for each index
outside `S`. -/
abbrev CandidateOracleIndex {k : ℕ} (S : Finset (Fin k)) :=
  Fin k ⊕ ↥(Sᶜ)

/-- The oracle sends the left summand to anchors and the right summand to
fresh query coordinates. -/
def candidateOracle {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) : CandidateOracleIndex S → ι
  | Sum.inl i => anchor i
  | Sum.inr i => query i.1

/-- Local factors whose product is the weighted indicator of candidate `S`. -/
def candidateOracleWeight {k : ℕ} (S : Finset (Fin k)) :
    CandidateOracleIndex S → Fin 4 → ℚ
  | Sum.inl i =>
      if i ∈ S then selectedAnchorWeight else halfBlackWeight
  | Sum.inr _ => nonblackQueryWeight

/-- Weighted indicator of candidate `S` in a four-colouring. -/
def weightedCandidate {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) (c : FourColoring ι) : ℚ :=
  ∏ o : CandidateOracleIndex S,
    candidateOracleWeight S o (c (candidateOracle anchor query S o))

/-- Product of two constants selected by membership in a subset of `Fin k`. -/
theorem prod_ite_mem_fin {k : ℕ} (S : Finset (Fin k)) (a b : ℚ) :
    (∏ i : Fin k, if i ∈ S then a else b) =
      a ^ S.card * b ^ (k - S.card) := by
  classical
  rw [Finset.prod_ite]
  have hS : (Finset.univ.filter fun i : Fin k ↦ i ∈ S) = S := by
    ext i
    simp
  have hSc : (Finset.univ.filter fun i : Fin k ↦ ¬i ∈ S) = Sᶜ := by
    ext i
    simp
  rw [hS, hSc]
  simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- The biased candidate has the advertised exact weighted average.  The
injectivity hypothesis packages injectivity of anchors, fresh queries, and
disjointness between those two coordinate families. -/
theorem average_weightedCandidate {k : ℕ} [Fintype ι] [DecidableEq ι]
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (horacle : Function.Injective (candidateOracle anchor query S)) :
    fintypeAverage (weightedCandidate anchor query S) =
      ((1 : ℚ) / 8) ^ S.card *
        ((21 : ℚ) / 32) ^ (k - S.card) := by
  classical
  let oracle : CandidateOracleIndex S ↪ ι :=
    ⟨candidateOracle anchor query S, horacle⟩
  unfold weightedCandidate
  change fintypeAverage
      (fun c : FourColoring ι ↦
        ∏ o, candidateOracleWeight S o (c (oracle o))) = _
  rw [expect_oracle_prod_embedding oracle (candidateOracleWeight S)]
  rw [Fintype.prod_sum_type]
  have hanchor :
      (∏ i : Fin k,
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inl i) colour) / 4) =
        ((1 : ℚ) / 8) ^ S.card *
          ((7 : ℚ) / 8) ^ (k - S.card) := by
    have hlocal : ∀ i : Fin k,
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inl i) colour) / 4 =
          if i ∈ S then (1 : ℚ) / 8 else 7 / 8 := by
      intro i
      by_cases hi : i ∈ S
      · simp [candidateOracleWeight, hi, average_selectedAnchorWeight]
      · simp [candidateOracleWeight, hi, average_halfBlackWeight]
    simp_rw [hlocal]
    exact prod_ite_mem_fin S ((1 : ℚ) / 8) (7 / 8)
  have hquery :
      (∏ i : ↥(Sᶜ),
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inr i) colour) / 4) =
        ((3 : ℚ) / 4) ^ (k - S.card) := by
    simp only [candidateOracleWeight, average_nonblackQueryWeight,
      Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin]
  rw [hanchor, hquery]
  have hcombine :
      ((7 : ℚ) / 8) ^ (k - S.card) *
          ((3 : ℚ) / 4) ^ (k - S.card) =
        ((21 : ℚ) / 32) ^ (k - S.card) := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, hcombine]

/-! ## Pointwise domination on the good event -/

/-- Number of black anchor coordinates. -/
def anchorBlackCount {k : ℕ} {ι : Type*} (anchor : Fin k → ι)
    (c : FourColoring ι) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
    c (anchor i) = 0).card

/-- Candidate `S` occurs when its anchors are black and every fresh query is
non-black. -/
def CandidateOccurs {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) (c : FourColoring ι) : Prop :=
  (∀ i ∈ S, c (anchor i) = 0) ∧
    ∀ i, i ∉ S → c (query i) ≠ 0

theorem half_pow_anchorBlackCount_eq_prod {k : ℕ} {ι : Type*}
    (anchor : Fin k → ι) (c : FourColoring ι) :
    ((1 : ℚ) / 2) ^ anchorBlackCount anchor c =
      ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
  classical
  rw [anchorBlackCount]
  calc
    ((1 : ℚ) / 2) ^
        ((Finset.univ : Finset (Fin k)).filter fun i ↦
          c (anchor i) = 0).card =
        ∏ i ∈ (Finset.univ : Finset (Fin k)).filter
          (fun i ↦ c (anchor i) = 0), ((1 : ℚ) / 2) := by
      simp
    _ = ∏ i : Fin k,
        if c (anchor i) = 0 then (1 : ℚ) / 2 else 1 := by
      rw [Finset.prod_filter]
    _ = ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp [halfBlackWeight]

/-- On an occurring candidate, the weighted indicator is exactly
`(1/2)^(number of black anchors)`. -/
theorem weightedCandidate_eq_half_pow {k : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι) (hoccurs : CandidateOccurs anchor query S c) :
    weightedCandidate anchor query S c =
      ((1 : ℚ) / 2) ^ anchorBlackCount anchor c := by
  classical
  rw [weightedCandidate, Fintype.prod_sum_type]
  have hanchor :
      (∏ i : Fin k,
        candidateOracleWeight S (Sum.inl i)
          (c (candidateOracle anchor query S (Sum.inl i)))) =
        ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hiS : i ∈ S
    · simp [candidateOracle, candidateOracleWeight, hiS,
        hoccurs.1 i hiS, selectedAnchorWeight, halfBlackWeight]
    · simp [candidateOracle, candidateOracleWeight, hiS]
  have hquery :
      (∏ i : ↥(Sᶜ),
        candidateOracleWeight S (Sum.inr i)
          (c (candidateOracle anchor query S (Sum.inr i)))) = 1 := by
    apply Finset.prod_eq_one
    intro i _hi
    have hiS : (i : Fin k) ∉ S := Finset.mem_compl.mp i.property
    simp [candidateOracle, candidateOracleWeight, nonblackQueryWeight,
      hoccurs.2 i hiS]
  rw [hanchor, hquery, mul_one, ← half_pow_anchorBlackCount_eq_prod]

/-- If `t ≤ 2r`, then `1 ≤ 2^(2r) (1/2)^t`. -/
theorem one_le_two_pow_mul_half_pow {r t : ℕ} (ht : t ≤ 2 * r) :
    (1 : ℚ) ≤ 2 ^ (2 * r) * ((1 : ℚ) / 2) ^ t := by
  have hexponent : 2 * r = t + (2 * r - t) := by omega
  have hcancel :
      (2 : ℚ) ^ t * ((1 : ℚ) / 2) ^ t = 1 := by
    rw [← mul_pow]
    norm_num
  have hscaled :
      (2 : ℚ) ^ (2 * r) * ((1 : ℚ) / 2) ^ t =
        2 ^ (2 * r - t) := by
    calc
      (2 : ℚ) ^ (2 * r) * ((1 : ℚ) / 2) ^ t =
          2 ^ (t + (2 * r - t)) * ((1 : ℚ) / 2) ^ t := by
        rw [← hexponent]
      _ = 2 ^ t * 2 ^ (2 * r - t) * ((1 : ℚ) / 2) ^ t := by
        rw [pow_add]
      _ = 2 ^ (2 * r - t) *
          ((2 : ℚ) ^ t * ((1 : ℚ) / 2) ^ t) := by
        ring
      _ = 2 ^ (2 * r - t) := by rw [hcancel, mul_one]
  calc
    (1 : ℚ) ≤ 2 ^ (2 * r - t) := one_le_pow₀ (by norm_num)
    _ = 2 ^ (2 * r) * ((1 : ℚ) / 2) ^ t := hscaled.symm

/-- Pointwise domination used on the good event. -/
theorem one_le_scaled_weightedCandidate_of_good {k r : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι)
    (hgood : anchorBlackCount anchor c ≤ 2 * r)
    (hoccurs : CandidateOccurs anchor query S c) :
    (1 : ℚ) ≤ 2 ^ (2 * r) * weightedCandidate anchor query S c := by
  rw [weightedCandidate_eq_half_pow anchor query S c hoccurs]
  exact one_le_two_pow_mul_half_pow hgood

/-! ## Weighted subset sum -/

/-- The subset expansion used in the weighted union bound.  This is the
constant-factor specialization of `Finset.prod_add`. -/
theorem weighted_subset_sum (k : ℕ) (a b : ℚ) :
    (∑ S : Finset (Fin k), a ^ S.card * b ^ (k - S.card)) =
      (a + b) ^ k := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin k) a b

/-- Exact arithmetic for `k = 6r`. -/
theorem scaled_weighted_subset_sum_eq (r : ℕ) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          ((1 : ℚ) / 8) ^ S.card *
            ((21 : ℚ) / 32) ^ (6 * r - S.card)) =
      ((15625 : ℚ) / 16384) ^ (2 * r) := by
  rw [weighted_subset_sum]
  have hbase : (1 : ℚ) / 8 + 21 / 32 = 25 / 32 := by norm_num
  rw [hbase]
  have hexponent : 6 * r = 3 * (2 * r) := by omega
  have hpow : ((25 : ℚ) / 32) ^ (6 * r) =
      (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
    rw [hexponent, pow_mul]
  rw [hpow, ← mul_pow]
  norm_num

/-- Numerical weighted subset-sum bound used by the finite block. -/
theorem scaled_weighted_subset_sum_le (r : ℕ) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          ((1 : ℚ) / 8) ^ S.card *
            ((21 : ℚ) / 32) ^ (6 * r - S.card)) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  rw [scaled_weighted_subset_sum_eq]
  exact pow_le_pow_left₀ (by norm_num)
    (by norm_num : (15625 : ℚ) / 16384 ≤ 63 / 64) _

/-- Direct form after replacing every candidate's weighted average by its
exact oracle-product value. -/
theorem scaled_sum_average_weightedCandidate_le [Fintype ι] [DecidableEq ι]
    (r : ℕ) (anchor : Fin (6 * r) → ι)
    (query : Finset (Fin (6 * r)) → Fin (6 * r) → ι)
    (horacle : ∀ S,
      Function.Injective (candidateOracle anchor (query S) S)) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          fintypeAverage (weightedCandidate anchor (query S) S)) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have havg : ∀ S : Finset (Fin (6 * r)),
      fintypeAverage (weightedCandidate anchor (query S) S) =
        ((1 : ℚ) / 8) ^ S.card *
          ((21 : ℚ) / 32) ^ (6 * r - S.card) := by
    intro S
    exact average_weightedCandidate anchor (query S) S (horacle S)
  simp_rw [havg]
  exact scaled_weighted_subset_sum_le r

end ColoringEnumeration

end Erdos486
