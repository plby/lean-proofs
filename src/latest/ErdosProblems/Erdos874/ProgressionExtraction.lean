import ErdosProblems.Erdos874.Foundations

/-!
# Progression extraction for Erdős Problem 874

This file contains the elementary final step in the restricted-sum progression
argument of Deshouillers--Freiman.  The structural part of that argument first
normalizes a finite integer sumset and proves that a long interval has few
holes.  The lemmas below extract a genuinely long interval from that statement
and transport it back to an arithmetic progression with the original common
difference.

The quantitative lemma `exists_longAP_of_few_holes` is deliberately phrased in
terms of a finite interval and its holes.  An interval of length
`(R + 1) * L` with at most `R` holes contains one of the `R + 1` disjoint
blocks of length `L` in its entirety.  This is the exact finite pigeonhole
step needed after slow-growth arguments have produced a dense normalized
sumset.
-/

open scoped BigOperators

namespace Erdos874

/-- The finite arithmetic progression with first term `a`, common difference
`q`, and `L` terms.  The empty progression is allowed. -/
def arithmeticProgression (a q : ℤ) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image fun i : ℕ => a + q * (i : ℤ)

/-- A finset contains an arithmetic progression of a specified difference and
length. -/
def ContainsAP (S : Finset ℤ) (q : ℤ) (L : ℕ) : Prop :=
  ∃ a : ℤ, arithmeticProgression a q L ⊆ S

/-- A finset is contained in an arithmetic progression of a specified
difference and length.  No nonzeroness assumption on the difference is built
into the definition; it is only needed for cardinality consequences. -/
def ContainedInSomeAP (S : Finset ℤ) (q : ℤ) (L : ℕ) : Prop :=
  ∃ a : ℤ, S ⊆ arithmeticProgression a q L

/-- Apply the integer affine map `x ↦ c + q*x` to a finset. -/
def affineImage (c q : ℤ) (S : Finset ℤ) : Finset ℤ :=
  S.image fun x => c + q * x

@[simp]
lemma mem_arithmeticProgression {x a q : ℤ} {L : ℕ} :
    x ∈ arithmeticProgression a q L ↔
      ∃ i < L, x = a + q * (i : ℤ) := by
  simp [arithmeticProgression, eq_comm]

@[simp]
lemma arithmeticProgression_zero (a q : ℤ) :
    arithmeticProgression a q 0 = ∅ := by
  simp [arithmeticProgression]

lemma arithmeticProgression_subset_of_le {a q : ℤ} {L M : ℕ} (hLM : L ≤ M) :
    arithmeticProgression a q L ⊆ arithmeticProgression a q M := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticProgression.mp hx
  exact mem_arithmeticProgression.mpr ⟨i, lt_of_lt_of_le hi hLM, rfl⟩

lemma arithmeticProgression_card {a q : ℤ} (hq : q ≠ 0) (L : ℕ) :
    (arithmeticProgression a q L).card = L := by
  rw [arithmeticProgression, Finset.card_image_of_injective]
  · exact Finset.card_range L
  · intro i j hij
    have hmul : q * (i : ℤ) = q * (j : ℤ) := add_left_cancel hij
    have hcast : (i : ℤ) = (j : ℤ) := mul_left_cancel₀ hq hmul
    exact_mod_cast hcast

lemma arithmeticProgression_one_eq_Ico (a : ℤ) (L : ℕ) :
    arithmeticProgression a 1 L = Finset.Ico a (a + L) := by
  ext x
  simp only [mem_arithmeticProgression, one_mul, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega
  · rintro ⟨hax, hxa⟩
    refine ⟨(x - a).toNat, ?_, ?_⟩
    · omega
    · omega

lemma arithmeticProgression_one_eq_Icc (a : ℤ) (L : ℕ) :
    arithmeticProgression a 1 L = Finset.Icc a (a + (L : ℤ) - 1) := by
  rw [arithmeticProgression_one_eq_Ico]
  ext x
  simp

/-- Reversing the enumeration of a progression negates its common
difference and moves its initial term to the other endpoint. -/
lemma arithmeticProgression_reverse (a q : ℤ) (L : ℕ) :
    arithmeticProgression a q L =
      arithmeticProgression (a + q * ((L : ℤ) - 1)) (-q) L := by
  ext x
  simp only [mem_arithmeticProgression]
  constructor
  · rintro ⟨i, hi, rfl⟩
    let j := L - 1 - i
    have hj : j < L := by dsimp [j]; omega
    have hjcast : (j : ℤ) = (L : ℤ) - 1 - (i : ℤ) := by
      dsimp [j]
      omega
    refine ⟨j, hj, ?_⟩
    rw [hjcast]
    ring
  · rintro ⟨j, hj, rfl⟩
    let i := L - 1 - j
    have hi : i < L := by dsimp [i]; omega
    have hicast : (i : ℤ) = (L : ℤ) - 1 - (j : ℤ) := by
      dsimp [i]
      omega
    refine ⟨i, hi, ?_⟩
    rw [hicast]
    ring

@[simp]
lemma mem_affineImage {x c q : ℤ} {S : Finset ℤ} :
    x ∈ affineImage c q S ↔ ∃ y ∈ S, x = c + q * y := by
  simp [affineImage, eq_comm]

lemma affineImage_mono {S T : Finset ℤ} (hST : S ⊆ T) (c q : ℤ) :
    affineImage c q S ⊆ affineImage c q T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_affineImage.mp hx
  exact mem_affineImage.mpr ⟨y, hST hy, rfl⟩

lemma affineImage_arithmeticProgression (c q a d : ℤ) (L : ℕ) :
    affineImage c q (arithmeticProgression a d L) =
      arithmeticProgression (c + q * a) (q * d) L := by
  ext x
  simp only [mem_affineImage, mem_arithmeticProgression]
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    ring
  · rintro ⟨i, hi, rfl⟩
    refine ⟨a + d * (i : ℤ), ⟨i, hi, rfl⟩, ?_⟩
    ring

lemma ContainsAP.mono {S T : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainsAP S q L) (hST : S ⊆ T) : ContainsAP T q L := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.trans hST⟩

/-- A nondegenerate progression contained in `S` gives the expected lower
bound on the cardinality of `S`. -/
lemma ContainsAP.length_le_card {S : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainsAP S q L) (hq : q ≠ 0) : L ≤ S.card := by
  obtain ⟨a, ha⟩ := h
  rw [← arithmeticProgression_card hq L]
  exact Finset.card_le_card ha

lemma ContainedInSomeAP.mono {S T : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainedInSomeAP T q L) (hST : S ⊆ T) : ContainedInSomeAP S q L := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, hST.trans ha⟩

lemma ContainedInSomeAP.card_le {S : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainedInSomeAP S q L) (hq : q ≠ 0) : S.card ≤ L := by
  obtain ⟨a, ha⟩ := h
  exact (Finset.card_le_card ha).trans_eq (arithmeticProgression_card hq L)

lemma ContainsAP.of_length_le {S : Finset ℤ} {q : ℤ} {L M : ℕ}
    (h : ContainsAP S q M) (hLM : L ≤ M) : ContainsAP S q L := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, (arithmeticProgression_subset_of_le hLM).trans ha⟩

/-- A contained progression can be read in reverse, changing `q` to `-q`. -/
lemma ContainsAP.neg_step {S : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainsAP S q L) : ContainsAP S (-q) L := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a + q * ((L : ℤ) - 1), ?_⟩
  rw [← arithmeticProgression_reverse a q L]
  exact ha

/-- Replace a nonzero integer common difference by its positive natural
absolute value.  This is the interface used by structure theorems that store
progression differences as natural numbers. -/
lemma ContainsAP.natAbs_step {S : Finset ℤ} {q : ℤ} {L : ℕ}
    (h : ContainsAP S q L) (hq : q ≠ 0) :
    ContainsAP S (q.natAbs : ℤ) L := by
  rcases lt_or_gt_of_ne hq with hqneg | hqpos
  · have habs : (q.natAbs : ℤ) = -q := by
      rw [Int.natCast_natAbs, abs_of_neg hqneg]
    simpa [habs] using h.neg_step
  · have habs : (q.natAbs : ℤ) = q := by
      rw [Int.natCast_natAbs, abs_of_pos hqpos]
    simpa [habs] using h

lemma ContainsAP.affineImage {S : Finset ℤ} {d : ℤ} {L : ℕ}
    (h : ContainsAP S d L) (c q : ℤ) :
    ContainsAP (affineImage c q S) (q * d) L := by
  obtain ⟨a, ha⟩ := h
  refine ⟨c + q * a, ?_⟩
  rw [← affineImage_arithmeticProgression]
  exact affineImage_mono ha c q

lemma ContainedInSomeAP.affineImage {S : Finset ℤ} {d : ℤ} {L : ℕ}
    (h : ContainedInSomeAP S d L) (c q : ℤ) :
    ContainedInSomeAP (affineImage c q S) (q * d) L := by
  obtain ⟨a, ha⟩ := h
  refine ⟨c + q * a, ?_⟩
  rw [← affineImage_arithmeticProgression]
  exact affineImage_mono ha c q

/-- A complete normalized integer interval is a progression of difference
one. -/
lemma containsAP_one_of_Ico_subset {S : Finset ℤ} {a : ℤ} {L : ℕ}
    (h : Finset.Ico a (a + L) ⊆ S) : ContainsAP S 1 L := by
  exact ⟨a, (arithmeticProgression_one_eq_Ico a L).trans_le h⟩

/-- Inclusive-interval version of `containsAP_one_of_Ico_subset`. -/
lemma containsAP_one_of_Icc_subset {S : Finset ℤ} {a b : ℤ}
    (hab : a ≤ b) (h : Finset.Icc a b ⊆ S) :
    ContainsAP S 1 (b + 1 - a).toNat := by
  refine ⟨a, ?_⟩
  rw [arithmeticProgression_one_eq_Ico]
  intro x hx
  apply h
  simp only [Finset.mem_Ico] at hx
  simp only [Finset.mem_Icc]
  constructor
  · exact hx.1
  · have hnonneg : 0 ≤ b + 1 - a := by omega
    have hcast : ((b + 1 - a).toNat : ℤ) = b + 1 - a :=
      Int.toNat_of_nonneg hnonneg
    rw [hcast] at hx
    omega

/-- Transport a normalized interval contained in `S` to an arithmetic
progression in an affine image of `S`. -/
lemma containsAP_of_Ico_subset_affineImage {S : Finset ℤ} {a : ℤ} {L : ℕ}
    (h : Finset.Ico a (a + L) ⊆ S) (c q : ℤ) :
    ContainsAP (affineImage c q S) q L := by
  simpa using (containsAP_one_of_Ico_subset h).affineImage c q

private noncomputable def holeInBlock (S : Finset ℤ) (a : ℤ) (L j : ℕ)
    (h : ¬Finset.Ico (a + (j * L : ℕ)) (a + ((j + 1) * L : ℕ)) ⊆ S) : ℤ :=
  Classical.choose (Finset.not_subset.mp h)

private lemma holeInBlock_mem (S : Finset ℤ) (a : ℤ) (L j : ℕ)
    (h : ¬Finset.Ico (a + (j * L : ℕ)) (a + ((j + 1) * L : ℕ)) ⊆ S) :
    holeInBlock S a L j h ∈
      Finset.Ico (a + (j * L : ℕ)) (a + ((j + 1) * L : ℕ)) :=
  (Classical.choose_spec (Finset.not_subset.mp h)).1

private lemma holeInBlock_not_mem (S : Finset ℤ) (a : ℤ) (L j : ℕ)
    (h : ¬Finset.Ico (a + (j * L : ℕ)) (a + ((j + 1) * L : ℕ)) ⊆ S) :
    holeInBlock S a L j h ∉ S :=
  (Classical.choose_spec (Finset.not_subset.mp h)).2

/-- **Dense interval extraction.**  If an interval of length
`(R + 1) * L` has at most `R` holes in `S`, one of its `R + 1` consecutive
blocks of length `L` is contained in `S`. -/
theorem exists_full_block_of_few_holes (S : Finset ℤ) (a : ℤ) (R L : ℕ)
    (hholes :
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ S).card ≤ R) :
    ∃ j < R + 1,
      Finset.Ico (a + (j * L : ℕ)) (a + ((j + 1) * L : ℕ)) ⊆ S := by
  classical
  by_contra h
  push Not at h
  let f : ℕ → ℤ := fun j =>
    if hj : j < R + 1 then holeInBlock S a L j (h j hj) else 0
  have hf_mem (j : ℕ) (hj : j ∈ Finset.range (R + 1)) :
      f j ∈ Finset.Ico a (a + ((R + 1) * L : ℕ)) \ S := by
    have hjlt : j < R + 1 := Finset.mem_range.mp hj
    rw [show f j = holeInBlock S a L j (h j hjlt) by
      simp [f, show j ≤ R by omega]]
    have hblock := holeInBlock_mem S a L j (h j hjlt)
    have hnot := holeInBlock_not_mem S a L j (h j hjlt)
    rw [Finset.mem_Ico] at hblock
    simp only [Finset.mem_sdiff, Finset.mem_Ico]
    constructor
    · constructor
      · exact le_trans (by omega : a ≤ a + (j * L : ℕ)) hblock.1
      · have hjle : j + 1 ≤ R + 1 := by omega
        have hmul : (j + 1) * L ≤ (R + 1) * L := Nat.mul_le_mul_right L hjle
        have hmulZ : (((j + 1) * L : ℕ) : ℤ) ≤ (((R + 1) * L : ℕ) : ℤ) := by
          exact_mod_cast hmul
        omega
    · exact hnot
  have hf_inj : (Finset.range (R + 1) : Set ℕ).InjOn f := by
    intro i hi j hj hij
    have hilt : i < R + 1 := Finset.mem_range.mp hi
    have hjlt : j < R + 1 := Finset.mem_range.mp hj
    simp [f, show i ≤ R by omega, show j ≤ R by omega] at hij
    have hiBlock := holeInBlock_mem S a L i (h i hilt)
    have hjBlock := holeInBlock_mem S a L j (h j hjlt)
    simp only [Finset.mem_Ico] at hiBlock hjBlock
    by_contra hijne
    rcases lt_or_gt_of_ne hijne with hijlt | hjilt
    · have hsucc : i + 1 ≤ j := by omega
      have hmul : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L hsucc
      have hmulZ : (((i + 1) * L : ℕ) : ℤ) ≤ ((j * L : ℕ) : ℤ) := by
        exact_mod_cast hmul
      omega
    · have hsucc : j + 1 ≤ i := by omega
      have hmul : (j + 1) * L ≤ i * L := Nat.mul_le_mul_right L hsucc
      have hmulZ : (((j + 1) * L : ℕ) : ℤ) ≤ ((i * L : ℕ) : ℤ) := by
        exact_mod_cast hmul
      omega
  have hcard : R + 1 ≤
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ S).card := by
    simpa using Finset.card_le_card_of_injOn f hf_mem hf_inj
  omega

/-- Quantitative progression extraction from a dense normalized sumset. -/
theorem exists_longAP_of_few_holes (S : Finset ℤ) (a : ℤ) (R L : ℕ)
    (hholes :
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ S).card ≤ R) :
    ContainsAP S 1 L := by
  obtain ⟨j, hj, hblock⟩ := exists_full_block_of_few_holes S a R L hholes
  have hend : a + ((j + 1) * L : ℕ) = a + (j * L : ℕ) + L := by
    push_cast
    ring
  rw [hend] at hblock
  exact containsAP_one_of_Ico_subset hblock

/-- Affine form of the dense extraction lemma.  This is the final
normalization/denormalization seam used in the progression engine. -/
theorem exists_longAP_of_few_holes_affineImage
    (S : Finset ℤ) (a c q : ℤ) (R L : ℕ)
    (hholes :
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ S).card ≤ R) :
    ContainsAP (affineImage c q S) q L := by
  simpa using (exists_longAP_of_few_holes S a R L hholes).affineImage c q

/-- Restricted-sumset specialization of the dense extraction lemma.  The
slow-growth part of the Deshouillers--Freiman argument supplies precisely the
finite hole bound appearing here. -/
theorem restrictedSumset_contains_longAP_of_few_holes
    (r : ℕ) (A : Finset ℤ) (a : ℤ) (R L : ℕ)
    (hholes :
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ restrictedSumset r A).card ≤ R) :
    ContainsAP (restrictedSumset r A) 1 L := by
  exact exists_longAP_of_few_holes (restrictedSumset r A) a R L hholes

/-- Affine-denormalized restricted-sumset specialization. -/
theorem restrictedSumset_affineImage_contains_longAP_of_few_holes
    (r : ℕ) (A : Finset ℤ) (a c q : ℤ) (R L : ℕ)
    (hholes :
      (Finset.Ico a (a + ((R + 1) * L : ℕ)) \ restrictedSumset r A).card ≤ R) :
    ContainsAP (affineImage c q (restrictedSumset r A)) q L := by
  exact exists_longAP_of_few_holes_affineImage
    (restrictedSumset r A) a c q R L hholes

end Erdos874
