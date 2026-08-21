/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.BooleanSlices
import ErdosProblems.Erdos88.ProductPermutationConcentration

open scoped BigOperators

namespace Erdos88
namespace BooleanSlices

open Classical Finset
open FiniteSliceConcentration

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The signed-slice decoder only depends on the first `plus + minus`
images of its input permutation. -/
lemma signedSliceDecode_eq_of_prefix (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ τ : Equiv.Perm (Fin I.card))
    (hστ : ∀ i : Fin (plus + minus),
      σ (Fin.castLE hcount i) = τ (Fin.castLE hcount i)) :
    signedSliceDecode I plus minus hcount e σ =
      signedSliceDecode I plus minus hcount e τ := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [signedSliceDecode]
    unfold signedSlicePositiveSupport
    congr 1
    ext i
    change (e (σ (Fin.castLE
      (le_trans (Nat.le_add_right plus minus) hcount) i)) : ↑I).1 =
      (e (τ (Fin.castLE
        (le_trans (Nat.le_add_right plus minus) hcount) i)) : ↑I).1
    apply congrArg Subtype.val
    apply congrArg e
    simpa using hστ (Fin.castLE (Nat.le_add_right plus minus) i)
  · simp only [signedSliceDecode]
    unfold signedSliceNegativeSupport
    congr 1
    ext i
    let j : Fin (plus + minus) :=
      ⟨plus + i, Nat.add_lt_add_left i.isLt plus⟩
    change (e (σ (finIntervalEmbedding I.card plus minus hcount i)) : ↑I).1 =
      (e (τ (finIntervalEmbedding I.card plus minus hcount i)) : ↑I).1
    apply congrArg Subtype.val
    apply congrArg e
    have hfi : finIntervalEmbedding I.card plus minus hcount i =
        Fin.castLE hcount j := by
      apply Fin.ext
      rfl
    rw [hfi]
    exact hστ j

/-- Decoding after a left transposition of permutation images transposes the
corresponding two actual coordinates. -/
lemma decodedCoordinateEmbedding_left_swap (I : Finset α)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card))
    (p q r : Fin I.card) :
    decodedCoordinateEmbedding I e (Equiv.swap p q * σ) r =
      Equiv.swap (e p).1 (e q).1 (decodedCoordinateEmbedding I e σ r) := by
  have he : Function.Injective (fun z : Fin I.card => (e z).1) := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact hxy
  change (e ((Equiv.swap p q * σ) r)).1 =
    Equiv.swap (e p).1 (e q).1 (e (σ r)).1
  rw [Equiv.Perm.mul_apply]
  exact he.map_swap p q (σ r)

lemma signedSlicePositiveSupport_left_swap (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card))
    (p q : Fin I.card) :
    signedSlicePositiveSupport I plus minus hcount e
        (Equiv.swap p q * σ) =
      (signedSlicePositiveSupport I plus minus hcount e σ).map
        (Equiv.swap (e p).1 (e q).1).toEmbedding := by
  unfold signedSlicePositiveSupport
  rw [Finset.map_map]
  congr 1
  ext r
  exact decodedCoordinateEmbedding_left_swap I e σ p q _

lemma signedSliceNegativeSupport_left_swap (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card))
    (p q : Fin I.card) :
    signedSliceNegativeSupport I plus minus hcount e
        (Equiv.swap p q * σ) =
      (signedSliceNegativeSupport I plus minus hcount e σ).map
        (Equiv.swap (e p).1 (e q).1).toEmbedding := by
  unfold signedSliceNegativeSupport
  rw [Finset.map_map]
  congr 1
  ext r
  exact decodedCoordinateEmbedding_left_swap I e σ p q _

/-- A left transposition in the sampler swaps the two corresponding ternary
coordinates in the decoded signed-slice value. -/
lemma signedSliceValue_decode_left_swap (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card))
    (p q : Fin I.card) (v : α) :
    signedSliceValue
        (signedSliceDecode I plus minus hcount e (Equiv.swap p q * σ)) v =
      signedSliceValue (signedSliceDecode I plus minus hcount e σ)
        (Equiv.swap (e p).1 (e q).1 v) := by
  simp only [signedSliceValue, signedSliceDecode]
  simp [signedSlicePositiveSupport_left_swap,
    signedSliceNegativeSupport_left_swap] <;> rfl

variable {κ : Type*}

/-- The product decoder only depends on the prescribed positive and negative
prefix in every bucket permutation. -/
lemma productSignedSliceDecode_eq_of_prefix [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ τ : ProductSignedSliceSampler P)
    (hστ : ∀ k (i : Fin (plus k + minus k)),
      σ k (Fin.castLE (hcount k) i) =
        τ k (Fin.castLE (hcount k) i)) :
    productSignedSliceDecode P plus minus hcount e σ =
      productSignedSliceDecode P plus minus hcount e τ := by
  funext k
  exact signedSliceDecode_eq_of_prefix (P.fiber k) (plus k) (minus k)
    (hcount k) (e k) (σ k) (τ k) (hστ k)

/-- Left-transposing one bucket permutation either leaves the decoded point
unchanged or gives exactly one product signed switch. -/
lemma productSignedSliceDecode_left_swap [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ τ : ProductSignedSliceSampler P) (k : κ)
    (p q : Fin (P.fiber k).card)
    (hk : τ k = Equiv.swap p q * σ k)
    (hsame : ∀ j, j ≠ k → τ j = σ j) :
    productSignedSliceDecode P plus minus hcount e τ =
        productSignedSliceDecode P plus minus hcount e σ ∨
      IsProductSignedSwitch P
        (productSignedSliceDecode P plus minus hcount e σ)
        (productSignedSliceDecode P plus minus hcount e τ) := by
  classical
  by_cases hpq : p = q
  · left
    apply congrArg (productSignedSliceDecode P plus minus hcount e)
    funext j
    by_cases hj : j = k
    · subst j
      rw [hpq, Equiv.swap_self] at hk
      exact hk.trans (by ext x; rfl)
    · exact hsame j hj
  · right
    let i : α := (e k p).1
    let j : α := (e k q).1
    have hi : i ∈ P.fiber k := (e k p).2
    have hj : j ∈ P.fiber k := (e k q).2
    have hij : i ≠ j := by
      intro hij
      apply hpq
      apply (e k).injective
      apply Subtype.ext
      exact hij
    have hbi : P.bucket i = k := (P.mem_fiber k i).mp hi
    have hbj : P.bucket j = k := (P.mem_fiber k j).mp hj
    have hbp : P.bucket (e k p).1 = k := (P.mem_fiber k _).mp (e k p).2
    have hbq : P.bucket (e k q).1 = k := (P.mem_fiber k _).mp (e k q).2
    refine ⟨k, i, j, hi, hj, hij, ?_⟩
    intro v
    by_cases hvk : P.bucket v = k
    · simp only [productSignedSliceValue, productSignedSliceDecode]
      rw [hvk, hk]
      rw [signedSliceValue_decode_left_swap]
      by_cases hvi : v = i
      · subst v
        rw [hbq]
        simp [i, j, hbi, hbj, hij]
      · by_cases hvj : v = j
        · subst v
          rw [hbp]
          simp [i, j, hbi, hbj, hij, hij.symm]
        · rw [Equiv.swap_apply_of_ne_of_ne hvi hvj]
          simp [i, j, hbi, hbj, hvk, hvi, hvj]
    · have hvi : v ≠ i := by
        intro h
        apply hvk
        calc
          P.bucket v = P.bucket i := congrArg P.bucket h
          _ = k := hbi
      have hvj : v ≠ j := by
        intro h
        apply hvk
        calc
          P.bucket v = P.bucket j := congrArg P.bucket h
          _ = k := hbj
      simp only [productSignedSliceValue, productSignedSliceDecode]
      rw [hsame (P.bucket v) hvk]
      simp [hvi, hvj]

/-- KSSS Lemma 4.17: exact two-sided bounded-differences concentration on a
product of fixed-count ternary slices. -/
theorem productSignedSlice_two_sided_probability {K : ℕ}
    (P : BucketPartition α (Fin K)) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f : ProductSignedSlicePoint P plus minus → ℝ) (a t : ℝ)
    (hL : 0 < ∑ k : Fin K, (plus k + minus k : ℕ))
    (ha : 0 < a) (ht : 0 ≤ t)
    (hlip : ∀ S T, IsProductSignedSwitch P S T → |f S - f T| ≤ a) :
    Concentration.uniformProbability (fun S =>
        t ≤ |f S - Concentration.uniformExpectation f|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * a ^ 2)) := by
  let decode : ProductSignedSliceSampler P →
      ProductSignedSlicePoint P plus minus :=
    productSignedSliceDecode P plus minus hcount e
  let G : ProductSignedSliceSampler P → ℝ := fun σ => f (decode σ)
  have hprefix : PermutationProductPrefixDependent hcount G := by
    intro σ τ hστ
    dsimp only [G, decode]
    rw [productSignedSliceDecode_eq_of_prefix P plus minus hcount e σ τ hστ]
  have hswitch : PermutationProductSwitchLipschitz G a := by
    intro σ τ k p q hk hsame
    rcases productSignedSliceDecode_left_swap P plus minus hcount e
        σ τ k p q hk hsame with heq | hsw
    · dsimp only [G, decode]
      rw [heq]
      simpa using ha.le
    · exact hlip _ _ hsw
  have hmean : Concentration.uniformExpectation G =
      Concentration.uniformExpectation f := by
    exact uniformExpectation_productSignedSliceDecode
      P plus minus hcount e f
  have htail := permutationProduct_two_sided_probability hcount G a t
    hL ha ht hprefix hswitch
  rw [hmean] at htail
  let Q : ProductSignedSlicePoint P plus minus → Prop := fun S =>
    t ≤ |f S - Concentration.uniformExpectation f|
  calc
    Concentration.uniformProbability Q =
        Concentration.uniformProbability (fun σ => Q (decode σ)) := by
      symm
      exact uniformProbability_productSignedSliceDecode
        P plus minus hcount e Q
    _ ≤ 2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * a ^ 2)) := by
      simpa only [Nat.cast_sum] using htail

/-! ### Linear--quadratic functions on signed slices -/

lemma abs_signedSliceValue_le_one {I : Finset α} {plus minus : ℕ}
    (S : SignedSlicePoint I plus minus) (i : α) :
    |signedSliceValue S i| ≤ 1 := by
  unfold signedSliceValue
  split_ifs <;> norm_num

lemma abs_signedSliceValue_eq_indicator {I : Finset α} {plus minus : ℕ}
    (S : SignedSlicePoint I plus minus) (i : α) :
    |signedSliceValue S i| =
      if i ∈ S.1.1 ∪ S.1.2 then 1 else 0 := by
  have hdisj := (mem_signedSlice.mp S.2).2.2.1
  by_cases hiP : i ∈ S.1.1
  · have hiN : i ∉ S.1.2 := Finset.disjoint_left.mp hdisj hiP
    simp [signedSliceValue, hiP, hiN]
  · by_cases hiN : i ∈ S.1.2
    · simp [signedSliceValue, hiP, hiN]
    · simp [signedSliceValue, hiP, hiN]

lemma sum_abs_productSignedSliceValue {K : ℕ}
    (P : BucketPartition α (Fin K)) (plus minus : Fin K → ℕ)
    (S : ProductSignedSlicePoint P plus minus) :
    (∑ i : α, |productSignedSliceValue P S i|) =
      ∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset α) P.bucket
    (fun i ↦ |productSignedSliceValue P S i|)]
  simp only [Nat.cast_add]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ i ∈ P.fiber k, |productSignedSliceValue P S i|) = _
  have hsupport : (S k).1.1 ∪ (S k).1.2 ⊆ P.fiber k :=
    Finset.union_subset (mem_signedSlice.mp (S k).2).1
      (mem_signedSlice.mp (S k).2).2.1
  calc
    (∑ i ∈ P.fiber k, |productSignedSliceValue P S i|) =
        ∑ i ∈ P.fiber k,
          if i ∈ (S k).1.1 ∪ (S k).1.2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hbucket : P.bucket i = k := (P.mem_fiber k i).mp hi
      rw [productSignedSliceValue, hbucket,
        abs_signedSliceValue_eq_indicator]
    _ = ((S k).1.1 ∪ (S k).1.2).card := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr hsupport]
    _ = (plus k : ℝ) + (minus k : ℝ) := by
      rw [Finset.card_union_of_disjoint
        (mem_signedSlice.mp (S k).2).2.2.1,
        (mem_signedSlice.mp (S k).2).2.2.2.1,
        (mem_signedSlice.mp (S k).2).2.2.2.2]
      exact Nat.cast_add _ _

lemma sum_abs_sub_productSignedSliceValue_le_four {K : ℕ}
    (P : BucketPartition α (Fin K)) {plus minus : Fin K → ℕ}
    {S T : ProductSignedSlicePoint P plus minus}
    (hST : IsProductSignedSwitch P S T) :
    (∑ i : α, |productSignedSliceValue P S i -
      productSignedSliceValue P T i|) ≤ 4 := by
  classical
  obtain ⟨k, p, q, hp, hq, hpq, hswap⟩ := hST
  calc
    (∑ i : α, |productSignedSliceValue P S i -
        productSignedSliceValue P T i|) ≤
        ∑ i : α, if i = p ∨ i = q then (2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hip : i = p
      · simp only [hip, true_or, if_true]
        calc
          |productSignedSliceValue P S p - productSignedSliceValue P T p| ≤
              |productSignedSliceValue P S p| +
                |productSignedSliceValue P T p| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add
            (abs_signedSliceValue_le_one (S (P.bucket p)) p)
            (abs_signedSliceValue_le_one (T (P.bucket p)) p)
          _ = 2 := by norm_num
      · by_cases hiq : i = q
        · simp only [hip, hiq, or_true, if_true]
          calc
            |productSignedSliceValue P S q - productSignedSliceValue P T q| ≤
                |productSignedSliceValue P S q| +
                  |productSignedSliceValue P T q| := abs_sub _ _
            _ ≤ 1 + 1 := add_le_add
              (abs_signedSliceValue_le_one (S (P.bucket q)) q)
              (abs_signedSliceValue_le_one (T (P.bucket q)) q)
            _ = 2 := by norm_num
        · simp only [hip, hiq, or_false, if_false]
          rw [hswap i, if_neg hip, if_neg hiq, sub_self, abs_zero]
    _ = 4 := by
      rw [Finset.sum_ite]
      have hfilter : (Finset.univ.filter fun i : α ↦ i = p ∨ i = q) =
          {p, q} := by
        ext i
        simp [eq_comm]
      rw [hfilter]
      norm_num [hpq]

/-- The portion of a linear--quadratic polynomial supported on the ternary
coordinates exposed by the first stage of the KSSS coupling. -/
noncomputable def signedSliceQuadratic {K : ℕ}
    (P : BucketPartition α (Fin K)) (plus minus : Fin K → ℕ)
    (f : α → ℝ) (F : α → α → ℝ)
    (S : ProductSignedSlicePoint P plus minus) : ℝ :=
  (∑ i, f i * productSignedSliceValue P S i) +
    ∑ i, ∑ j, F i j * productSignedSliceValue P S i *
      productSignedSliceValue P S j

/-- A legal signed-slice switch changes the restricted polynomial by at
most `4B + 8LA`, where `L` is the total exposed support.  This is the
deterministic estimate used in KSSS Lemma 11.2 before applying Lemma 4.17. -/
lemma abs_signedSliceQuadratic_sub_le {K : ℕ}
    (P : BucketPartition α (Fin K)) {plus minus : Fin K → ℕ}
    (f : α → ℝ) (F : α → α → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    {S T : ProductSignedSlicePoint P plus minus}
    (hST : IsProductSignedSwitch P S T) :
    |signedSliceQuadratic P plus minus f F S -
        signedSliceQuadratic P plus minus f F T| ≤
      4 * B + 8 * (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * A := by
  let x : α → ℝ := productSignedSliceValue P S
  let y : α → ℝ := productSignedSliceValue P T
  let L : ℝ := ∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)
  have hdx : (∑ i, |x i - y i|) ≤ 4 := by
    simpa only [x, y] using sum_abs_sub_productSignedSliceValue_le_four P hST
  have hx : (∑ i, |x i|) = L := by
    simpa only [x, L] using
      sum_abs_productSignedSliceValue P plus minus S
  have hy : (∑ i, |y i|) = L := by
    simpa only [y, L] using
      sum_abs_productSignedSliceValue P plus minus T
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hlin : |∑ i, f i * (x i - y i)| ≤ 4 * B := by
    calc
      |∑ i, f i * (x i - y i)| ≤
          ∑ i, |f i * (x i - y i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, B * |x i - y i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)
      _ = B * ∑ i, |x i - y i| := by rw [Finset.mul_sum]
      _ ≤ B * 4 := mul_le_mul_of_nonneg_left hdx hB
      _ = 4 * B := by ring
  have hquad : |∑ i, ∑ j, F i j * (x i * x j - y i * y j)| ≤
      8 * L * A := by
    calc
      |∑ i, ∑ j, F i j * (x i * x j - y i * y j)| ≤
          ∑ i, ∑ j, |F i j * (x i * x j - y i * y j)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j,
          A * (|x i - y i| * |x j| + |y i| * |x j - y j|) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have hprod : |x i * x j - y i * y j| ≤
            |x i - y i| * |x j| + |y i| * |x j - y j| := by
          rw [show x i * x j - y i * y j =
            (x i - y i) * x j + y i * (x j - y j) by ring]
          exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
        exact (mul_le_mul (hF i j) hprod (abs_nonneg _) hA)
      _ = A * ((∑ i, |x i - y i|) * (∑ j, |x j|) +
          (∑ i, |y i|) * (∑ j, |x j - y j|)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc,
          ← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ A * (4 * L + L * 4) := by
        apply mul_le_mul_of_nonneg_left _ hA
        rw [hx, hy]
        exact add_le_add
          (mul_le_mul_of_nonneg_right hdx hL)
          (mul_le_mul_of_nonneg_left hdx hL)
      _ = 8 * L * A := by ring
  have hlinEq : (∑ i, f i * x i) - (∑ i, f i * y i) =
      ∑ i, f i * (x i - y i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquadEq : (∑ i, ∑ j, F i j * x i * x j) -
      (∑ i, ∑ j, F i j * y i * y j) =
        ∑ i, ∑ j, F i j * (x i * x j - y i * y j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change |((∑ i, f i * x i) + ∑ i, ∑ j, F i j * x i * x j) -
      ((∑ i, f i * y i) + ∑ i, ∑ j, F i j * y i * y j)| ≤ _
  rw [show ((∑ i, f i * x i) + ∑ i, ∑ j, F i j * x i * x j) -
      ((∑ i, f i * y i) + ∑ i, ∑ j, F i j * y i * y j) =
      ((∑ i, f i * x i) - ∑ i, f i * y i) +
        ((∑ i, ∑ j, F i j * x i * x j) -
          ∑ i, ∑ j, F i j * y i * y j) by ring,
    hlinEq, hquadEq]
  exact (abs_add_le _ _).trans (add_le_add hlin hquad)

/-- Lemma 4.17 specialized to the exposed linear--quadratic portion in the
two-stage coupling of KSSS Lemma 11.2. -/
theorem signedSliceQuadratic_two_sided_probability {K : ℕ}
    (P : BucketPartition α (Fin K)) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f : α → ℝ) (F : α → α → ℝ) (A B t : ℝ)
    (hL : 0 < ∑ k : Fin K, (plus k + minus k : ℕ))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (ha : 0 < 4 * B + 8 *
      (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    Concentration.uniformProbability
        (fun S : ProductSignedSlicePoint P plus minus =>
          t ≤ |signedSliceQuadratic P plus minus f F S -
            Concentration.uniformExpectation
              (signedSliceQuadratic P plus minus f F)|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) *
            (4 * B + 8 *
              (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * A) ^ 2)) := by
  apply productSignedSlice_two_sided_probability P plus minus hcount e
    (signedSliceQuadratic P plus minus f F)
    (4 * B + 8 *
      (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * A) t
      hL ha ht
  intro S T hST
  exact abs_signedSliceQuadratic_sub_le P f F A B hA hB hf hF hST

end BooleanSlices
end Erdos88
