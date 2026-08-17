/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.External.Erdos88.BooleanSlices
import ErdosProblems.Erdos636.External.Erdos88.ProductPermutationConcentration

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

end BooleanSlices
end Erdos88
