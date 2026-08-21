import ErdosProblems.Erdos88.SliceCouplingAsymptotic

/-!
# Finite mixtures of slice couplings

This file supplies the probability-kernel bookkeeping used in KSSS
Lemma 11.3.  Real-valued coupling weights are more convenient than choosing
one large common finite denominator when couplings for different slice-size
vectors have different sample-space cardinalities.
-/

open scoped BigOperators

namespace Erdos88.BooleanSlices

open Classical Finset

/-- A coupling of the uniform laws on two nonempty finite types, represented
by its nonnegative joint probability mass function. -/
structure FiniteWeightedCoupling (A B : Type*) [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] where
  weight : A → B → ℝ
  weight_nonneg : ∀ a b, 0 ≤ weight a b
  left_sum : ∀ a, ∑ b, weight a b = 1 / (Fintype.card A : ℝ)
  right_sum : ∀ b, ∑ a, weight a b = 1 / (Fintype.card B : ℝ)

namespace FiniteUniformCoupling

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- The joint mass function encoded by a finite uniform coupling. -/
noncomputable def jointWeight (C : FiniteUniformCoupling A B) (a : A) (b : B) : ℝ :=
  ((Finset.univ.filter fun ω : Fin C.size ↦ C.left ω = a ∧ C.right ω = b).card : ℝ) /
    C.size

lemma jointWeight_nonneg (C : FiniteUniformCoupling A B) (a : A) (b : B) :
    0 ≤ C.jointWeight a b := by
  unfold jointWeight
  positivity

/-- Forget the common denominator of a finite uniform coupling and retain its
joint probability mass function. -/
noncomputable def toWeighted (C : FiniteUniformCoupling A B) :
    FiniteWeightedCoupling A B where
  weight := C.jointWeight
  weight_nonneg := C.jointWeight_nonneg
  left_sum a := by
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    have hleft := C.left_uniform_real (fun x : A ↦ if x = a then 1 else 0)
    rw [Fintype.expect_eq_sum_div_card,
      Fintype.expect_eq_sum_div_card] at hleft
    simp only [Fintype.card_fin] at hleft
    rw [show (∑ b, C.jointWeight a b) =
        ((Finset.univ.filter fun ω : Fin C.size ↦ C.left ω = a).card : ℝ) /
          C.size by
      unfold jointWeight
      rw [← Finset.sum_div]
      congr 1
      norm_cast
      simp_rw [Finset.card_eq_sum_ones]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : C.left ω = a <;> simp [h]]
    simpa [Finset.sum_ite] using hleft
  right_sum b := by
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    have hright := C.right_uniform_real (fun y : B ↦ if y = b then 1 else 0)
    rw [Fintype.expect_eq_sum_div_card,
      Fintype.expect_eq_sum_div_card] at hright
    simp only [Fintype.card_fin] at hright
    rw [show (∑ a, C.jointWeight a b) =
        ((Finset.univ.filter fun ω : Fin C.size ↦ C.right ω = b).card : ℝ) /
          C.size by
      unfold jointWeight
      rw [← Finset.sum_div]
      congr 1
      norm_cast
      simp_rw [Finset.card_eq_sum_ones]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : C.right ω = b <;> simp [h]]
    simpa [Finset.sum_ite] using hright

end FiniteUniformCoupling

namespace FiniteWeightedCoupling

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- The probability mass of an event under a weighted finite coupling. -/
noncomputable def mass (C : FiniteWeightedCoupling A B)
    (p : A → B → Prop) : ℝ :=
  ∑ a, ∑ b, if p a b then C.weight a b else 0

lemma mass_nonneg (C : FiniteWeightedCoupling A B)
    (p : A → B → Prop) : 0 ≤ C.mass p := by
  unfold mass
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  by_cases h : p a b <;> simp [h, C.weight_nonneg]

lemma mass_univ (C : FiniteWeightedCoupling A B) :
    C.mass (fun _ _ ↦ True) = 1 := by
  rw [mass]
  simp only [if_true, C.left_sum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A source-exact closeness certificate for a weighted coupling. -/
def IsClose (C : FiniteWeightedCoupling A B)
    (X : A → ℝ) (Y : B → ℝ) (r q : ℝ) : Prop :=
  1 - q ≤ C.mass (fun a b ↦ |X a - Y b| ≤ r)

lemma IsClose.mono_failure (C : FiniteWeightedCoupling A B)
    {X : A → ℝ} {Y : B → ℝ} {r q q' : ℝ}
    (h : C.IsClose X Y r q) (hqq' : q ≤ q') :
    C.IsClose X Y r q' := by
  unfold IsClose at h ⊢
  linarith

/-- The independent coupling of two uniform finite laws. -/
noncomputable def independent : FiniteWeightedCoupling A B where
  weight _ _ := 1 / ((Fintype.card A : ℝ) * Fintype.card B)
  weight_nonneg _ _ := by positivity
  left_sum _ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  right_sum _ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

variable {E : Type*} [Fintype E] [Nonempty E]

/-- Transport the right marginal of a weighted coupling through an
equivalence. -/
noncomputable def mapRight (C : FiniteWeightedCoupling A B) (e : B ≃ E) :
    FiniteWeightedCoupling A E where
  weight a y := C.weight a (e.symm y)
  weight_nonneg a y := C.weight_nonneg a (e.symm y)
  left_sum a := by
    calc
      (∑ y, C.weight a (e.symm y)) = ∑ b, C.weight a b :=
        e.symm.sum_comp (fun b ↦ C.weight a b)
      _ = 1 / Fintype.card A := C.left_sum a
  right_sum y := by
    calc
      (∑ a, C.weight a (e.symm y)) = 1 / Fintype.card B :=
        C.right_sum (e.symm y)
      _ = 1 / Fintype.card E := by rw [Fintype.card_congr e]

lemma mapRight_mass (C : FiniteWeightedCoupling A B) (e : B ≃ E)
    (p : A → E → Prop) :
    (C.mapRight e).mass p = C.mass (fun a b ↦ p a (e b)) := by
  unfold mass mapRight
  apply Finset.sum_congr rfl
  intro a ha
  let g : E → ℝ := fun y ↦ if p a y then C.weight a (e.symm y) else 0
  simpa only [g, e.symm_apply_apply] using
    (e.sum_comp g).symm

lemma mapRight_isClose (C : FiniteWeightedCoupling A B) (e : B ≃ E)
    (X : A → ℝ) (Y : E → ℝ) (r q : ℝ)
    (h : C.IsClose X (fun b ↦ Y (e b)) r q) :
    (C.mapRight e).IsClose X Y r q := by
  unfold IsClose
  rw [mapRight_mass]
  exact h

variable {J : Type*} [Fintype J] [Nonempty J]
  {D : J → Type*} [(j : J) → Fintype (D j)]
  [(j : J) → Nonempty (D j)]

noncomputable instance sigmaNonempty : Nonempty (Sigma D) := by
  let j : J := Classical.choice inferInstance
  exact ⟨⟨j, Classical.choice (inferInstance : Nonempty (D j))⟩⟩

/-- Mix uniform couplings to the fibers `D j` with the weights forced by the
uniform law on the sigma type. -/
noncomputable def sigmaMixture
    (C : (j : J) → FiniteWeightedCoupling A (D j)) :
    FiniteWeightedCoupling A (Sigma D) where
  weight a s :=
    (Fintype.card (D s.1) : ℝ) / Fintype.card (Sigma D) *
      (C s.1).weight a s.2
  weight_nonneg a s := mul_nonneg (by positivity) ((C s.1).weight_nonneg a s.2)
  left_sum a := by
    rw [Fintype.sum_sigma]
    apply Eq.trans ?_ (show
      (∑ j, (Fintype.card (D j) : ℝ) / Fintype.card (Sigma D) *
        (1 / Fintype.card A)) = 1 / Fintype.card A by
        rw [← Finset.sum_mul]
        rw [← Finset.sum_div]
        simp only [Fintype.card_sigma, Nat.cast_sum]
        field_simp)
    apply Finset.sum_congr rfl
    intro j hj
    change (∑ x : D j, (Fintype.card (D j) : ℝ) /
      Fintype.card (Sigma D) * (C j).weight a x) = _
    rw [← (C j).left_sum a, Finset.mul_sum]
  right_sum s := by
    calc
      (∑ a, (Fintype.card (D s.1) : ℝ) / Fintype.card (Sigma D) *
          (C s.1).weight a s.2) =
          (Fintype.card (D s.1) : ℝ) / Fintype.card (Sigma D) *
            (∑ a, (C s.1).weight a s.2) := by rw [Finset.mul_sum]
      _ = (Fintype.card (D s.1) : ℝ) / Fintype.card (Sigma D) *
          (1 / Fintype.card (D s.1)) := by rw [(C s.1).right_sum]
      _ = 1 / Fintype.card (Sigma D) := by field_simp

lemma sigmaMixture_mass
    (C : (j : J) → FiniteWeightedCoupling A (D j))
    (p : A → Sigma D → Prop) :
    (sigmaMixture C).mass p =
      ∑ j, (Fintype.card (D j) : ℝ) / Fintype.card (Sigma D) *
        (C j).mass (fun a b ↦ p a ⟨j, b⟩) := by
  unfold mass sigmaMixture
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : p a ⟨j, b⟩ <;> simp [h]

/-- The marginal probability of a set of sigma indices. -/
noncomputable def indexMass (E : J → Prop) : ℝ :=
  ∑ j, if E j then
    (Fintype.card (D j) : ℝ) / Fintype.card (Sigma D)
  else 0

lemma indexMass_nonneg (E : J → Prop) :
    0 ≤ indexMass (D := D) E := by
  unfold indexMass
  apply Finset.sum_nonneg
  intro j hj
  by_cases hE : E j <;> simp [hE]
  positivity

lemma indexMass_add_compl (E : J → Prop) :
    indexMass (D := D) E + indexMass (D := D) (fun j ↦ ¬ E j) = 1 := by
  classical
  simp only [indexMass]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j, (Fintype.card (D j) : ℝ) /
          Fintype.card (Sigma D) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hE : E j <;> simp [hE]
    _ = 1 := by
      rw [← Finset.sum_div]
      simp only [Fintype.card_sigma, Nat.cast_sum]
      field_simp

/-- Conditional close couplings on all good fibers combine into a close
coupling of the sigma mixture.  The only extra failure probability is the
uniform mass of the bad fibers. -/
lemma sigmaMixture_isClose_of_good
    (C : (j : J) → FiniteWeightedCoupling A (D j))
    (good : J → Prop) (X : A → ℝ) (Y : Sigma D → ℝ)
    (r q : ℝ) (hq : 0 ≤ q)
    (hclose : ∀ j, good j →
      (C j).IsClose X (fun b ↦ Y ⟨j, b⟩) r q) :
    (sigmaMixture C).IsClose X Y r
      (q + indexMass (D := D) (fun j ↦ ¬ good j)) := by
  let badMass := indexMass (D := D) (fun j ↦ ¬ good j)
  have hbad0 : 0 ≤ badMass := indexMass_nonneg _
  have hpartition := indexMass_add_compl (D := D) good
  have hgood : indexMass (D := D) good = 1 - badMass := by
    dsimp only [badMass]
    linarith
  have hconditional :
      indexMass (D := D) good * (1 - q) ≤
        (sigmaMixture C).mass
          (fun a s ↦ |X a - Y s| ≤ r) := by
    rw [sigmaMixture_mass]
    unfold indexMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjgood : good j
    · simp only [hjgood, if_true]
      apply mul_le_mul_of_nonneg_left (hclose j hjgood)
      positivity
    · simp only [hjgood, if_false, zero_mul]
      exact mul_nonneg (by positivity) ((C j).mass_nonneg _)
  unfold IsClose
  change 1 - (q + badMass) ≤ _
  calc
    1 - (q + badMass) ≤ (1 - badMass) * (1 - q) := by
      nlinarith [mul_nonneg hq hbad0]
    _ = indexMass (D := D) good * (1 - q) := by rw [hgood]
    _ ≤ _ := hconditional

end FiniteWeightedCoupling

namespace FiniteUniformCoupling

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

lemma toWeighted_mass_maps (C : FiniteUniformCoupling A B)
    (p : A → B → Prop) :
    C.toWeighted.mass p =
      C.probability (fun ω ↦ p (C.left ω) (C.right ω)) := by
  have hnumNat :
      (∑ a, ∑ b, if p a b then
        (Finset.univ.filter fun ω : Fin C.size ↦
          C.left ω = a ∧ C.right ω = b).card else 0) =
        (Finset.univ.filter fun ω : Fin C.size ↦
          p (C.left ω) (C.right ω)).card := by
    have hpair (a : A) (b : B) :
        (if p a b then
          (Finset.univ.filter fun ω : Fin C.size ↦
            C.left ω = a ∧ C.right ω = b).card else 0) =
          (Finset.univ.filter fun ω : Fin C.size ↦
            p a b ∧ C.left ω = a ∧ C.right ω = b).card := by
      by_cases hp : p a b <;> simp [hp]
    simp_rw [hpair, Finset.card_filter]
    rw [show (∑ a, ∑ b, ∑ ω : Fin C.size,
        if p a b ∧ C.left ω = a ∧ C.right ω = b then 1 else 0) =
        ∑ ω : Fin C.size, ∑ a, ∑ b,
          if p a b ∧ C.left ω = a ∧ C.right ω = b then 1 else 0 by
      apply Eq.trans ?_ (Finset.sum_comm)
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.sum_eq_single (C.left ω)]
    · rw [Finset.sum_eq_single (C.right ω)]
      · simp
      · intro b hb hbne
        simp [Ne.symm hbne]
      · simp
    · intro a ha hane
      simp [Ne.symm hane]
    · simp
  have hnumReal := congrArg (fun z : ℕ ↦ (z : ℝ)) hnumNat
  push_cast at hnumReal
  unfold FiniteWeightedCoupling.mass toWeighted jointWeight probability
  calc
    (∑ a, ∑ b,
        if p a b then
          ((Finset.univ.filter fun ω : Fin C.size ↦
            C.left ω = a ∧ C.right ω = b).card : ℝ) / C.size
        else 0) =
        ∑ a, ∑ b,
          (if p a b then
            ((Finset.univ.filter fun ω : Fin C.size ↦
              C.left ω = a ∧ C.right ω = b).card : ℝ) else 0) /
            C.size := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hp : p a b <;> simp [hp]
    _ = (∑ a, ∑ b, if p a b then
          ((Finset.univ.filter fun ω : Fin C.size ↦
            C.left ω = a ∧ C.right ω = b).card : ℝ) else 0) /
          C.size := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_div]
    _ = ((Finset.univ.filter fun ω : Fin C.size ↦
          p (C.left ω) (C.right ω)).card : ℝ) / C.size := by
      rw [hnumReal]

lemma toWeighted_isClose (C : FiniteUniformCoupling A B)
    (X : A → ℝ) (Y : B → ℝ) (r q : ℝ)
    (h : C.IsClose X Y r q) :
    C.toWeighted.IsClose X Y r q := by
  unfold FiniteWeightedCoupling.IsClose
  rw [C.toWeighted_mass_maps]
  exact h

end FiniteUniformCoupling

/-- Choose the weighted coupling encoded by an existing
`HasQuadraticSliceCoupling` certificate. -/
noncomputable def weightedCouplingOfHasQuadraticSliceCoupling
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (radius failure : ℝ)
    [Nonempty (ProductSlicePoint P ell)]
    [Nonempty (ProductSlicePoint P ell')]
    (h : HasQuadraticSliceCoupling P ell ell' f₀ f F radius failure) :
    FiniteWeightedCoupling (ProductSlicePoint P ell)
      (ProductSlicePoint P ell') := by
  unfold HasQuadraticSliceCoupling at h
  let C := h.choose_spec.choose_spec.choose
  exact C.toWeighted

lemma weightedCouplingOfHasQuadraticSliceCoupling_isClose
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (radius failure : ℝ)
    [Nonempty (ProductSlicePoint P ell)]
    [Nonempty (ProductSlicePoint P ell')]
    (h : HasQuadraticSliceCoupling P ell ell' f₀ f F radius failure) :
    (weightedCouplingOfHasQuadraticSliceCoupling P ell ell' f₀ f F
      radius failure h).IsClose
        (productSliceQuadratic P ell f₀ f F)
        (productSliceQuadratic P ell' f₀ f F) radius failure := by
  unfold HasQuadraticSliceCoupling at h
  let C := h.choose_spec.choose_spec.choose
  have hC := h.choose_spec.choose_spec.choose_spec
  simpa only [weightedCouplingOfHasQuadraticSliceCoupling] using
    C.toWeighted_isClose _ _ _ _ hC

section SliceCountDecomposition

variable {α κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype κ] [DecidableEq κ]

/-- The vector of all admissible slice sizes for the buckets of `P`. -/
abbrev BucketCountVector (P : BucketPartition α κ) :=
  (k : κ) → Fin ((P.fiber k).card + 1)

/-- The bucket-count vector of a subset of the coordinate set. -/
def bucketCounts (P : BucketPartition α κ) (S : Finset α) :
    BucketCountVector P :=
  fun k ↦ ⟨(S ∩ P.fiber k).card,
    Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)⟩

@[simp] lemma bucketCounts_apply (P : BucketPartition α κ)
    (S : Finset α) (k : κ) :
    (bucketCounts P S k).val = (S ∩ P.fiber k).card := rfl

/-- Subsets of the coordinate set are exactly the disjoint union of all
product slices, indexed by their bucket-count vectors. -/
noncomputable def finsetEquivSigmaProductSlices (P : BucketPartition α κ) :
    Finset α ≃ Sigma (fun ell : BucketCountVector P ↦
      ProductSlicePoint P (fun k ↦ (ell k).val)) where
  toFun S := ⟨bucketCounts P S, ⟨S, by
    rw [mem_productBooleanSlice]
    intro k
    rfl⟩⟩
  invFun T := T.2.1
  left_inv S := rfl
  right_inv T := by
    rcases T with ⟨ell, ⟨S, hS⟩⟩
    have hell : bucketCounts P S = ell := by
      funext k
      apply Fin.ext
      exact (mem_productBooleanSlice P (fun k ↦ (ell k).val) S).mp hS k
    subst ell
    rfl

lemma productSlicePoint_nonempty_of_countVector
    (P : BucketPartition α κ) (ell : BucketCountVector P) :
    Nonempty (ProductSlicePoint P (fun k ↦ (ell k).val)) := by
  apply productSlicePoint_nonempty
  intro k
  exact Nat.le_of_lt_succ (ell k).isLt

noncomputable instance productSlicePointCountVectorNonempty
    (P : BucketPartition α κ) (ell : BucketCountVector P) :
    Nonempty (ProductSlicePoint P (fun k ↦ (ell k).val)) :=
  productSlicePoint_nonempty_of_countVector P ell

end SliceCountDecomposition

section BooleanCubeCounts

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Boolean functions and subsets of a finite type are the same finite
probability space. -/
noncomputable def boolFunEquivFinset : (α → Bool) ≃ Finset α where
  toFun x := Finset.univ.filter fun i ↦ x i = true
  invFun S i := decide (i ∈ S)
  left_inv x := by
    funext i
    cases h : x i <;> simp [h]
  right_inv S := by
    ext i
    simp

@[simp] lemma mem_boolFunEquivFinset (x : α → Bool) (i : α) :
    i ∈ boolFunEquivFinset x ↔ x i = true := by
  simp [boolFunEquivFinset]

lemma bernoulliWeight_half_finite (W : Finset α) :
    Probability.bernoulliWeight (1 / 2 : ℝ) W =
      (1 / 2 : ℝ) ^ Fintype.card α := by
  rw [Probability.bernoulliWeight, Erdos202.ParkPham.bernoulliMass]
  have hcardUniv : W.card ≤ (Finset.univ : Finset α).card :=
    Finset.card_le_card (by simp)
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add]
  congr 1
  exact (Nat.add_sub_of_le hcardUniv).trans (Finset.card_univ.trans rfl)

lemma uniformExpectation_finset_eq_probability_half_finite
    (X : Finset α → ℝ) :
    Concentration.uniformExpectation X =
      Probability.expectation (1 / 2 : ℝ) X := by
  rw [Concentration.uniformExpectation]
  unfold Probability.expectation
  simp_rw [bernoulliWeight_half_finite]
  rw [← Finset.mul_sum]
  simp only [Fintype.card_finset, one_div, inv_pow]
  rw [div_eq_mul_inv, mul_comm]
  norm_num [Nat.cast_pow]

lemma probability_expectation_card_inter_half (I : Finset α) :
    Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset α ↦ ((S ∩ I).card : ℝ)) =
      (I.card : ℝ) / 2 := by
  have hfun : (fun S : Finset α ↦ ((S ∩ I).card : ℝ)) =
      (fun S ↦ ∑ i ∈ I, Probability.bit i S) := by
    funext S
    rw [Finset.card_eq_sum_ones]
    push_cast
    simp [Probability.bit, Finset.inter_comm]
  rw [hfun, Probability.expectation_sum]
  simp_rw [Probability.expectation_bit (p := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)]
  simp
  ring

lemma uniformExpectation_card_inter_half (I : Finset α) :
    Concentration.uniformExpectation
        (fun S : Finset α ↦ ((S ∩ I).card : ℝ)) =
      (I.card : ℝ) / 2 := by
  rw [uniformExpectation_finset_eq_probability_half_finite]
  exact probability_expectation_card_inter_half I

/-- Number of `true` coordinates in `I`, written on the Boolean-function
model used by the finite-cube concentration theorem. -/
def boolCount (I : Finset α) (x : α → Bool) : ℝ :=
  ∑ i ∈ I, if x i = true then 1 else 0

lemma boolCount_eq_card_inter (I : Finset α) (x : α → Bool) :
    boolCount I x = ((boolFunEquivFinset x ∩ I).card : ℝ) := by
  have hset : boolFunEquivFinset x ∩ I =
      I.filter (fun i ↦ x i = true) := by
    ext i
    simp [boolFunEquivFinset, and_comm]
  rw [hset, Finset.card_filter]
  push_cast
  rfl

lemma boolCount_boundedDifference (I : Finset α) :
    ∀ i x y, (∀ j, j ≠ i → x j = y j) →
      |boolCount I x - boolCount I y| ≤ if i ∈ I then 1 else 0 := by
  intro i x y hxy
  by_cases hi : i ∈ I
  · have hrest :
        (∑ j ∈ I.erase i, if x j = true then (1 : ℝ) else 0) =
          ∑ j ∈ I.erase i, if y j = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxy j (by
        intro hji
        subst j
        exact (Finset.mem_erase.mp hj).1 rfl)]
    rw [boolCount, boolCount, ← Finset.sum_erase_add I _ hi,
      ← Finset.sum_erase_add I _ hi, hrest, if_pos hi]
    cases x i <;> cases y i <;> norm_num
  · have hall :
        (∑ j ∈ I, if x j = true then (1 : ℝ) else 0) =
          ∑ j ∈ I, if y j = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxy j (fun hji ↦ hi (hji ▸ hj))]
    rw [boolCount, boolCount, hall, sub_self, abs_zero, if_neg hi]

lemma sum_boolCount_lipschitzSq (I : Finset α) :
    (∑ i : α, (if i ∈ I then (1 : ℝ) else 0) ^ 2) = I.card := by
  simp only [ite_pow, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp [Finset.sum_ite]

lemma boolCount_mean {n : ℕ} (I : Finset (Fin n)) :
    (∑ x : Fin n → Bool, boolCount I x) / (2 ^ n : ℝ) =
      (I.card : ℝ) / 2 := by
  let e : (Fin n → Bool) ≃ Finset (Fin n) := boolFunEquivFinset
  let g : Finset (Fin n) → ℝ := fun S ↦ ((S ∩ I).card : ℝ)
  calc
    (∑ x : Fin n → Bool, boolCount I x) / (2 ^ n : ℝ) =
        Concentration.uniformExpectation g := by
      rw [Concentration.uniformExpectation]
      rw [← e.sum_comp g]
      simp only [e, g, boolCount_eq_card_inter]
      simp [Fintype.card_finset, Fintype.card_fin]
    _ = (I.card : ℝ) / 2 := uniformExpectation_card_inter_half I

/-- One-sided lower tail for the number of selected coordinates in a fixed
set, in the exact counting form returned by the finite-cube theorem. -/
lemma boolCount_lower_tail_count {n : ℕ} (I : Finset (Fin n))
    (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x : Fin n → Bool ↦
        boolCount I x ≤ (I.card : ℝ) / 2 - t).card : ℝ) ≤
      (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / I.card) := by
  have h := Concentration.cube_lower_tail n (boolCount I)
    (fun i ↦ if i ∈ I then 1 else 0)
    (boolCount_boundedDifference I)
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi]) t ht
  dsimp only at h
  rw [boolCount_mean I, sum_boolCount_lipschitzSq I] at h
  exact h

/-- The matching upper-tail bound, obtained by applying the lower-tail
theorem to the negated count. -/
lemma boolCount_upper_tail_count {n : ℕ} (I : Finset (Fin n))
    (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x : Fin n → Bool ↦
        (I.card : ℝ) / 2 + t ≤ boolCount I x).card : ℝ) ≤
      (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / I.card) := by
  have hdiff : ∀ i x y, (∀ j, j ≠ i → x j = y j) →
      |(-boolCount I x) - (-boolCount I y)| ≤
        if i ∈ I then 1 else 0 := by
    intro i x y hxy
    simpa only [neg_sub_neg, abs_sub_comm] using
      boolCount_boundedDifference I i x y hxy
  have hmeanNeg :
      (∑ x : Fin n → Bool, -boolCount I x) / (2 ^ n : ℝ) =
        -(I.card : ℝ) / 2 := by
    rw [Finset.sum_neg_distrib, neg_div, boolCount_mean I]
    ring
  have h := Concentration.cube_lower_tail n
    (fun x ↦ -boolCount I x)
    (fun i ↦ if i ∈ I then 1 else 0) hdiff
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi]) t ht
  dsimp only at h
  rw [hmeanNeg, sum_boolCount_lipschitzSq I] at h
  have hfilter :
      (Finset.univ.filter fun x : Fin n → Bool ↦
        -boolCount I x ≤ -(I.card : ℝ) / 2 - t) =
      Finset.univ.filter fun x : Fin n → Bool ↦
        (I.card : ℝ) / 2 + t ≤ boolCount I x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hx <;> linarith
  rwa [hfilter] at h

lemma boolCount_two_sided_tail_count {n : ℕ} (I : Finset (Fin n))
    (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x : Fin n → Bool ↦
        t < |boolCount I x - (I.card : ℝ) / 2|).card : ℝ) ≤
      2 * (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / I.card) := by
  let A : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦
    boolCount I x ≤ (I.card : ℝ) / 2 - t
  let B : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦
    (I.card : ℝ) / 2 + t ≤ boolCount I x
  let E : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦
    t < |boolCount I x - (I.card : ℝ) / 2|
  have hEA : E ⊆ A ∪ B := by
    intro x hx
    simp only [E, A, B, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hx ⊢
    rcases lt_abs.mp hx with hx | hx
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  have hcardNat : E.card ≤ A.card + B.card :=
    (Finset.card_le_card hEA).trans (Finset.card_union_le A B)
  have hcard : (E.card : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast hcardNat
  have hA := boolCount_lower_tail_count I t ht
  have hB := boolCount_upper_tail_count I t ht
  change (E.card : ℝ) ≤ _
  change (A.card : ℝ) ≤ _ at hA
  change (B.card : ℝ) ≤ _ at hB
  nlinarith [Real.exp_pos (-2 * t ^ 2 / (I.card : ℝ))]

/-- Two-sided binomial concentration for the intersection of a uniform
random subset with one fixed coordinate set. -/
lemma uniformProbability_card_inter_two_sided {n : ℕ}
    (I : Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
    Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        t < |((S ∩ I).card : ℝ) - (I.card : ℝ) / 2|) ≤
      2 * Real.exp (-2 * t ^ 2 / I.card) := by
  let e : (Fin n → Bool) ≃ Finset (Fin n) := boolFunEquivFinset
  let Q : Finset (Fin n) → Prop := fun S ↦
    t < |((S ∩ I).card : ℝ) - (I.card : ℝ) / 2|
  have htail := boolCount_two_sided_tail_count I t ht
  have hcard :
      ((Finset.univ.filter fun x : Fin n → Bool ↦ Q (e x)).card : ℝ) =
        (Finset.univ.filter Q).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact_mod_cast e.sum_comp (fun S ↦ if Q S then (1 : ℕ) else 0)
  rw [Concentration.uniformProbability]
  rw [← hcard]
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num [Nat.cast_pow]
  apply (div_le_iff₀ hpow).2
  change ((Finset.univ.filter fun x : Fin n → Bool ↦ Q (e x)).card : ℝ) ≤ _
  have hQ : (fun x : Fin n → Bool ↦ Q (e x)) =
      (fun x ↦ t < |boolCount I x - (I.card : ℝ) / 2|) := by
    funext x
    simp only [Q, e, boolCount_eq_card_inter]
  have hfilterQ :
      (Finset.univ.filter fun x : Fin n → Bool ↦ Q (e x)) =
        Finset.univ.filter fun x ↦
          t < |boolCount I x - (I.card : ℝ) / 2| := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (congrFun hQ x)
  rw [hfilterQ]
  have hexp : -2 * t ^ 2 / (I.card : ℝ) =
      -(2 * t ^ 2) / I.card := by ring
  rw [hexp] at htail
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htail

lemma uniformProbability_bucketCounts_not_near
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (W : ℝ) (hW : 0 ≤ W) :
    Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        ¬ ∀ k, |((S ∩ P.fiber k).card : ℝ) -
          ((P.fiber k).card : ℝ) / 2| ≤ W) ≤
      ∑ k : Fin m,
        2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card) := by
  calc
    Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        ¬ ∀ k, |((S ∩ P.fiber k).card : ℝ) -
          ((P.fiber k).card : ℝ) / 2| ≤ W) =
        Concentration.uniformProbability (fun S ↦ ∃ k,
          W < |((S ∩ P.fiber k).card : ℝ) -
            ((P.fiber k).card : ℝ) / 2|) := by
      congr 1
      funext S
      simp only [not_forall, not_le]
    _ ≤ ∑ k : Fin m, Concentration.uniformProbability
          (fun S : Finset (Fin n) ↦
            W < |((S ∩ P.fiber k).card : ℝ) -
              ((P.fiber k).card : ℝ) / 2|) :=
      uniformProbability_exists_le_sum _
    _ ≤ ∑ k : Fin m,
          2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card) := by
      apply Finset.sum_le_sum
      intro k hk
      exact uniformProbability_card_inter_two_sided (P.fiber k) W hW

lemma uniformProbability_not_isNearBalanced_le
    {n m : ℕ} (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (hW : 0 ≤ ksssSliceMargin n d) :
    Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        ¬ IsNearBalanced d P (fun k ↦ (bucketCounts P S k).val)) ≤
      ∑ k : Fin m, 2 * Real.exp
        (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card) := by
  simpa only [IsNearBalanced, ksssSliceMargin, bucketCounts_apply] using
    uniformProbability_bucketCounts_not_near P (ksssSliceMargin n d) hW

end BooleanCubeCounts

section CountVectorLaw

variable {α κ : Type*} [Fintype α] [DecidableEq α]
  [Fintype κ] [DecidableEq κ]

/-- Probability mass of a set of bucket-count vectors under a uniform random
subset of the coordinates.  The displayed slice cardinalities make the
binomial-mixture weights explicit. -/
noncomputable def countVectorMass (P : BucketPartition α κ)
    (E : BucketCountVector P → Prop) : ℝ :=
  ∑ ell, if E ell then
    (Fintype.card (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
      Fintype.card (Finset α)
    else 0

lemma countVectorMass_eq_uniformProbability
    (P : BucketPartition α κ) (E : BucketCountVector P → Prop) :
    countVectorMass P E =
      Concentration.uniformProbability (fun S : Finset α ↦ E (bucketCounts P S)) := by
  let D := fun ell : BucketCountVector P ↦
    ProductSlicePoint P (fun k ↦ (ell k).val)
  let e : Finset α ≃ Sigma D := finsetEquivSigmaProductSlices P
  have hnumNat :
      (Finset.univ.filter fun S : Finset α ↦ E (bucketCounts P S)).card =
        ∑ ell : BucketCountVector P,
          if E ell then Fintype.card (D ell) else 0 := by
    rw [Finset.card_filter]
    have he (S : Finset α) : (e S).1 = bucketCounts P S := rfl
    calc
      (∑ S : Finset α, if E (bucketCounts P S) then 1 else 0) =
          ∑ s : Sigma D, if E s.1 then 1 else 0 := by
        simpa only [he] using
          e.sum_comp (fun s : Sigma D ↦ if E s.1 then (1 : ℕ) else 0)
      _ = ∑ ell : BucketCountVector P,
          if E ell then Fintype.card (D ell) else 0 := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro ell hell
        by_cases hE : E ell <;> simp [hE]
  calc
    countVectorMass P E =
        (∑ ell : BucketCountVector P,
          if E ell then (Fintype.card (D ell) : ℝ) else 0) /
            Fintype.card (Finset α) := by
      rw [countVectorMass, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hE : E ell <;> simp [hE, D]
    _ = (((∑ ell : BucketCountVector P,
          if E ell then Fintype.card (D ell) else 0 : ℕ) : ℝ) /
            Fintype.card (Finset α)) := by
      rw [Nat.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hE : E ell <;> simp [hE]
    _ = Concentration.uniformProbability
        (fun S : Finset α ↦ E (bucketCounts P S)) := by
      rw [← hnumNat]
      rfl

/-- Exact finite disintegration of a uniform expectation by the vector of
bucket counts.  The weight of a count vector is the cardinality of its
product slice divided by the cardinality of the full Boolean cube. -/
lemma uniformExpectation_eq_sum_countVector
    (P : BucketPartition α κ) (X : Finset α → ℝ) :
    Concentration.uniformExpectation X =
      ∑ ell : BucketCountVector P,
        (Fintype.card
            (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
            Fintype.card (Finset α) *
          Concentration.uniformExpectation
            (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ X S.1) := by
  classical
  let D := fun ell : BucketCountVector P ↦
    ProductSlicePoint P (fun k ↦ (ell k).val)
  let e : Finset α ≃ Sigma D := finsetEquivSigmaProductSlices P
  have hsum : (∑ S : Finset α, X S) =
      ∑ ell : BucketCountVector P, ∑ S : D ell, X S.1 := by
    calc
      (∑ S : Finset α, X S) = ∑ T : Sigma D, X T.2.1 := by
        change (∑ S : Finset α, X (e S).2.1) =
          ∑ T : Sigma D, X T.2.1
        exact e.sum_comp (fun T : Sigma D ↦ X T.2.1)
      _ = ∑ ell : BucketCountVector P, ∑ S : D ell, X S.1 := by
        rw [Fintype.sum_sigma]
  rw [Concentration.uniformExpectation, hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [Concentration.uniformExpectation]
  have hcard : (Fintype.card (D ell) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (D ell) ≠ 0)
  dsimp only [D]
  field_simp

/-- Exact finite law of total probability over all bucket-count vectors.
Unlike `countVectorMass_eq_uniformProbability`, the event may depend on the
point inside the product slice, not only on its count vector. -/
lemma uniformProbability_eq_sum_countVector
    (P : BucketPartition α κ) (E : Finset α → Prop) :
    Concentration.uniformProbability E =
      ∑ ell : BucketCountVector P,
        (Fintype.card
            (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
            Fintype.card (Finset α) *
          Concentration.uniformProbability
            (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ E S.1) := by
  classical
  have hleft : Concentration.uniformProbability E =
      Concentration.uniformExpectation (fun S ↦ if E S then 1 else 0) := by
    rw [Concentration.uniformProbability, Concentration.uniformExpectation,
      Finset.card_filter]
    push_cast
    rfl
  rw [hleft, uniformExpectation_eq_sum_countVector P
    (fun S ↦ if E S then 1 else 0)]
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  rw [Concentration.uniformProbability, Concentration.uniformExpectation,
    Finset.card_filter]
  push_cast
  rfl

lemma sigmaMixture_indexMass
    {A : Type*} [Fintype A] [Nonempty A]
    (P : BucketPartition α κ)
    (C : (ell : BucketCountVector P) →
      FiniteWeightedCoupling A
        (ProductSlicePoint P (fun k ↦ (ell k).val)))
    (E : BucketCountVector P → Prop) :
    (FiniteWeightedCoupling.sigmaMixture C).mass
        (fun _ s ↦ E s.1) = countVectorMass P E := by
  rw [FiniteWeightedCoupling.sigmaMixture_mass]
  rw [countVectorMass]
  have hcard : Fintype.card
      (Sigma fun ell : BucketCountVector P ↦
        ProductSlicePoint P (fun k ↦ (ell k).val)) =
      Fintype.card (Finset α) := by
    exact (Fintype.card_congr (finsetEquivSigmaProductSlices P)).symm
  rw [hcard]
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hE : E ell
  · simp only [hE, if_true]
    rw [(C ell).mass_univ]
    ring
  · simp only [hE, if_false]
    unfold FiniteWeightedCoupling.mass
    simp [hE]

lemma sliceSigma_indexMass_eq_countVectorMass
    (P : BucketPartition α κ) (E : BucketCountVector P → Prop) :
    FiniteWeightedCoupling.indexMass
        (D := fun ell : BucketCountVector P ↦
          ProductSlicePoint P (fun k ↦ (ell k).val)) E =
      countVectorMass P E := by
  unfold FiniteWeightedCoupling.indexMass countVectorMass
  rw [show Fintype.card
      (Sigma fun ell : BucketCountVector P ↦
        ProductSlicePoint P (fun k ↦ (ell k).val)) =
      Fintype.card (Finset α) by
    exact (Fintype.card_congr (finsetEquivSigmaProductSlices P)).symm]

end CountVectorLaw

section QuadraticMixtureCoupling

/-- A weighted coupling between a fixed product slice and the uniform
Rademacher sign set. -/
def HasQuadraticRademacherWeightedCoupling {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (radius failure : ℝ) : Prop :=
  ∃ hleft : Nonempty (ProductSlicePoint P ell),
    letI := hleft
    ∃ C : FiniteWeightedCoupling
        (ProductSlicePoint P ell) (Finset (Fin n)),
      C.IsClose (productSliceQuadratic P ell f₀ f F)
        (sliceQuadratic f₀ f F) radius failure

/-- Finite conditional-mixture form of KSSS Lemma 11.3.  It turns a
Lemma 11.2 coupling on every good count vector into a coupling with the full
uniform Boolean cube; the count-vector bad probability is kept exact. -/
theorem quadraticRademacherWeightedCoupling_of_conditional
    {n m : ℕ} (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (radius failure : ℝ)
    (hell : IsNearBalanced d P ell) (hfailure : 0 ≤ failure)
    (hconditional : ∀ ell' : Fin m → ℕ,
      IsNearBalanced d P ell' →
      HasQuadraticSliceCoupling P ell ell' f₀ f F radius failure) :
    HasQuadraticRademacherWeightedCoupling P ell f₀ f F radius
      (failure + Concentration.uniformProbability
        (fun S : Finset (Fin n) ↦
          ¬ IsNearBalanced d P (fun k ↦ (bucketCounts P S k).val))) := by
  have hself := hconditional ell hell
  unfold HasQuadraticSliceCoupling at hself
  let hleft : Nonempty (ProductSlicePoint P ell) := hself.choose
  refine ⟨hleft, ?_⟩
  let D := fun j : BucketCountVector P ↦
    ProductSlicePoint P (fun k ↦ (j k).val)
  let good : BucketCountVector P → Prop := fun j ↦
    IsNearBalanced d P (fun k ↦ (j k).val)
  let X : ProductSlicePoint P ell → ℝ :=
    productSliceQuadratic P ell f₀ f F
  let Y : Sigma D → ℝ := fun s ↦
    productSliceQuadratic P (fun k ↦ (s.1 k).val) f₀ f F s.2
  let C : (j : BucketCountVector P) →
      FiniteWeightedCoupling (ProductSlicePoint P ell) (D j) := fun j ↦
    if hj : good j then
      weightedCouplingOfHasQuadraticSliceCoupling P ell
        (fun k ↦ (j k).val) f₀ f F radius failure
        (hconditional (fun k ↦ (j k).val) hj)
    else FiniteWeightedCoupling.independent
  have hCclose : ∀ j, good j →
      (C j).IsClose X (fun b ↦ Y ⟨j, b⟩) radius failure := by
    intro j hj
    simp only [C, dif_pos hj]
    exact weightedCouplingOfHasQuadraticSliceCoupling_isClose P ell
      (fun k ↦ (j k).val) f₀ f F radius failure
      (hconditional (fun k ↦ (j k).val) hj)
  have hmix := FiniteWeightedCoupling.sigmaMixture_isClose_of_good
    C good X Y radius failure hfailure hCclose
  have hbad : FiniteWeightedCoupling.indexMass (D := D)
      (fun j ↦ ¬ good j) =
      Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        ¬ IsNearBalanced d P (fun k ↦ (bucketCounts P S k).val)) := by
    rw [sliceSigma_indexMass_eq_countVectorMass P,
      countVectorMass_eq_uniformProbability]
  rw [hbad] at hmix
  let e : Finset (Fin n) ≃ Sigma D := finsetEquivSigmaProductSlices P
  let Cfinal := (FiniteWeightedCoupling.sigmaMixture C).mapRight e.symm
  refine ⟨Cfinal, ?_⟩
  apply FiniteWeightedCoupling.mapRight_isClose
  have heinv (s : Sigma D) : e.symm s = s.2.1 := rfl
  simpa only [X, Y, productSliceQuadratic, heinv] using hmix

theorem quadraticRademacherWeightedCoupling_of_conditional_tail
    {n m : ℕ} (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (radius failure : ℝ)
    (hell : IsNearBalanced d P ell) (hfailure : 0 ≤ failure)
    (hW : 0 ≤ ksssSliceMargin n d)
    (hconditional : ∀ ell' : Fin m → ℕ,
      IsNearBalanced d P ell' →
      HasQuadraticSliceCoupling P ell ell' f₀ f F radius failure) :
    HasQuadraticRademacherWeightedCoupling P ell f₀ f F radius
      (failure + ∑ k : Fin m, 2 * Real.exp
        (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card)) := by
  have h := quadraticRademacherWeightedCoupling_of_conditional d P ell
    f₀ f F radius failure hell hfailure hconditional
  unfold HasQuadraticRademacherWeightedCoupling at h ⊢
  rcases h with ⟨hleft, C, hC⟩
  refine ⟨hleft, C,
    FiniteWeightedCoupling.IsClose.mono_failure C hC ?_⟩
  have hbad := uniformProbability_not_isNearBalanced_le d P hW
  linarith

/-- Lemma 11.3 before its final asymptotic simplification: the two failure
terms are the Lemma 11.2 error and the exact bucket-count Chernoff sum. -/
def KSSSLemma113Raw : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 / 4 →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m))
        (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
        (F : Fin n → Fin n → ℝ),
        IsKSSSPartition d P → IsNearBalanced d P ell →
        HasKSSSBalancedCoefficients d P f F →
        HasQuadraticRademacherWeightedCoupling P ell f₀ f F
          (scale n (3 / 4 + 4 * d))
          (Real.exp (-scale n (d / 2)) +
            ∑ k : Fin m, 2 * Real.exp
              (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card))

theorem ksssLemma113Raw : KSSSLemma113Raw := by
  intro d hd hd4
  have h112 := ksssLemma112 d hd hd4
  filter_upwards [h112, Filter.eventually_ge_atTop 1] with n hn112 hn
  intro m P ell f₀ f F hpart hell hcoeff
  apply quadraticRademacherWeightedCoupling_of_conditional_tail d P ell
    f₀ f F (scale n (3 / 4 + 4 * d))
      (Real.exp (-scale n (d / 2))) hell (Real.exp_nonneg _)
  · rw [ksssSliceMargin]
    exact mul_nonneg (scale_nonneg n _) (Real.log_nonneg (by exact_mod_cast hn))
  · intro ell' hell'
    exact hn112 m P ell ell' f₀ f F hpart hell hell' hcoeff

/-- The count-vector Chernoff sum has the source's Gaussian-in-logarithm
decay, up to the harmless polynomial prefactor. -/
lemma ksss_countTail_sum_le {n m : ℕ} {d : ℝ}
    (hn : 0 < n) (P : BucketPartition (Fin n) (Fin m))
    (hpart : IsKSSSPartition d P) :
    (∑ k : Fin m, 2 * Real.exp
        (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card)) ≤
      2 * n * Real.exp (-(Real.log n) ^ 2) := by
  have hm : 0 < m :=
    lt_of_le_of_lt (Nat.zero_le _) (P.bucket ⟨0, hn⟩).isLt
  let k₀ : Fin m := ⟨0, hm⟩
  let s : ℕ := (P.fiber k₀).card
  have hsEq : ∀ k, (P.fiber k).card = s := by
    intro k
    exact hpart.1 k k₀
  have hmulNat : m * s = n := bucketCount_mul_fiberCard P hpart.1 k₀
  have hmspos : 0 < m * s := hmulNat.symm ▸ hn
  have hs : 0 < s := by
    by_contra hs0
    have hsEq0 : s = 0 := Nat.eq_zero_of_not_pos hs0
    simp [hsEq0] at hmspos
  have hmle : m ≤ n := by
    calc
      m = m * 1 := by simp
      _ ≤ m * s := Nat.mul_le_mul_left m hs
      _ = n := hmulNat
  have hmul : (m : ℝ) * s = n := by exact_mod_cast hmulNat
  have hscale : scale n d * scale n (1 - d) = (n : ℝ) :=
    scale_one_sub_mul_scale hn d
  have hscaleD : scale n d ≤ 2 * (m : ℝ) := by
    linarith [hpart.2.1]
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hsBound : (s : ℝ) ≤ 2 * scale n (1 - d) := by
    have hscaleDpos : 0 < scale n d := scale_pos hn d
    have hmulIneq := mul_le_mul_of_nonneg_right hscaleD hsR
    have hprod :
        scale n d * (s : ℝ) ≤
          scale n d * (2 * scale n (1 - d)) := by
      calc
        scale n d * (s : ℝ) ≤ 2 * (m : ℝ) * s := hmulIneq
        _ = 2 * (n : ℝ) := by
          calc
            2 * (m : ℝ) * s = 2 * ((m : ℝ) * s) := by ring
            _ = 2 * (n : ℝ) := by rw [hmul]
        _ = scale n d * (2 * scale n (1 - d)) := by
          rw [← hscale]
          ring
    exact (mul_le_mul_iff_right₀ hscaleDpos).mp hprod
  have hWsq : ksssSliceMargin n d ^ 2 =
      scale n (1 - d) * Real.log n ^ 2 := by
    rw [ksssSliceMargin]
    calc
      (scale n ((1 - d) / 2) * Real.log n) ^ 2 =
          (scale n ((1 - d) / 2) * scale n ((1 - d) / 2)) *
            Real.log n ^ 2 := by ring
      _ = scale n (((1 - d) / 2) + ((1 - d) / 2)) *
            Real.log n ^ 2 := by rw [scale_mul hn]
      _ = scale n (1 - d) * Real.log n ^ 2 := by
        congr 1
        ring
  have hratio : Real.log n ^ 2 ≤
      2 * ksssSliceMargin n d ^ 2 / (s : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hs)).2
    rw [hWsq]
    nlinarith [mul_le_mul_of_nonneg_left hsBound (sq_nonneg (Real.log n))]
  calc
    (∑ k : Fin m, 2 * Real.exp
        (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card)) =
        ∑ _k : Fin m, 2 * Real.exp
          (-2 * ksssSliceMargin n d ^ 2 / (s : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hsEq k]
    _ ≤ ∑ _k : Fin m, 2 * Real.exp (-(Real.log n) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hneg := neg_le_neg hratio
      simpa only [neg_div, neg_mul] using hneg
    _ = (m : ℝ) * (2 * Real.exp (-(Real.log n) ^ 2)) := by simp
    _ ≤ (n : ℝ) * (2 * Real.exp (-(Real.log n) ^ 2)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmle)
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = 2 * n * Real.exp (-(Real.log n) ^ 2) := by ring

/-- A linear prefactor is absorbed by seven eighths of the logarithmic
Gaussian exponent. -/
lemma eventually_one_add_two_natCast_le_exp_log_sq :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 + 2 * (n : ℝ) ≤ Real.exp ((7 / 8 : ℝ) * Real.log n ^ 2) := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 4)
  filter_upwards [Filter.eventually_ge_atTop 3, hlog] with n hn hlog
  change (4 : ℝ) ≤ Real.log n at hlog
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hexpLog : Real.exp (Real.log n) = (n : ℝ) := Real.exp_log hnR
  calc
    1 + 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    _ = Real.exp (2 * Real.log n) := by
      rw [show 2 * Real.log n = Real.log n + Real.log n by ring,
        Real.exp_add, hexpLog]
      simp [pow_two]
    _ ≤ Real.exp ((7 / 8 : ℝ) * Real.log n ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The two raw failure terms in the slice mixture are eventually bounded by
the single error term stated in KSSS Lemma 11.3. -/
lemma ksss_mixture_failure_le {n m : ℕ} {d : ℝ}
    (hn : 0 < n) (P : BucketPartition (Fin n) (Fin m))
    (hpart : IsKSSSPartition d P)
    (hscale : Real.log n ^ 2 ≤ scale n (d / 2))
    (hpref : 1 + 2 * (n : ℝ) ≤
      Real.exp ((7 / 8 : ℝ) * Real.log n ^ 2)) :
    Real.exp (-scale n (d / 2)) +
        ∑ k : Fin m, 2 * Real.exp
          (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card) ≤
      Real.exp (-(Real.log n) ^ 2 / 8) := by
  have hfirst : Real.exp (-scale n (d / 2)) ≤
      Real.exp (-(Real.log n) ^ 2) :=
    Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hcount := ksss_countTail_sum_le hn P hpart
  calc
    Real.exp (-scale n (d / 2)) +
        ∑ k : Fin m, 2 * Real.exp
          (-2 * ksssSliceMargin n d ^ 2 / (P.fiber k).card) ≤
        Real.exp (-(Real.log n) ^ 2) +
          2 * n * Real.exp (-(Real.log n) ^ 2) :=
      add_le_add hfirst hcount
    _ = (1 + 2 * (n : ℝ)) * Real.exp (-(Real.log n) ^ 2) := by ring
    _ ≤ Real.exp ((7 / 8 : ℝ) * Real.log n ^ 2) *
          Real.exp (-(Real.log n) ^ 2) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _)
    _ = Real.exp (-(Real.log n) ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- KSSS Lemma 11.3: a fixed near-balanced product slice quadratic can be
coupled to the unrestricted Rademacher quadratic with the source's exact
`exp (-(log n)^2 / 8)` exceptional mass. -/
def KSSSLemma113 : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 / 4 →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m))
        (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
        (F : Fin n → Fin n → ℝ),
        IsKSSSPartition d P → IsNearBalanced d P ell →
        HasKSSSBalancedCoefficients d P f F →
        HasQuadraticRademacherWeightedCoupling P ell f₀ f F
          (scale n (3 / 4 + 4 * d))
          (Real.exp (-(Real.log n) ^ 2 / 8))

theorem ksssLemma113 : KSSSLemma113 := by
  intro d hd hd4
  have hraw := ksssLemma113Raw d hd hd4
  have hscale := eventually_const_mul_log_sq_le_scale 1 (d / 2)
    (by norm_num) (div_pos hd (by norm_num))
  filter_upwards [hraw, hscale, eventually_one_add_two_natCast_le_exp_log_sq,
    Filter.eventually_ge_atTop 1] with n hraw hscale hpref hn
  intro m P ell f₀ f F hpart hell hcoeff
  have hcoupling := hraw m P ell f₀ f F hpart hell hcoeff
  unfold HasQuadraticRademacherWeightedCoupling at hcoupling ⊢
  rcases hcoupling with ⟨hleft, C, hC⟩
  refine ⟨hleft, C, FiniteWeightedCoupling.IsClose.mono_failure C hC ?_⟩
  apply ksss_mixture_failure_le (show 0 < n by omega) P hpart
  · simpa using hscale
  · exact hpref

end QuadraticMixtureCoupling

end Erdos88.BooleanSlices
