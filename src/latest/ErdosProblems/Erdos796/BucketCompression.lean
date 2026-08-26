import ErdosProblems.Erdos796.Core
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Compressing indexed fibres by quotient buckets

Given finitely many compatible fibres indexed by primes, choose a largest
fibre in each quotient bucket.  Replacing every fibre in a bucket by that
representative preserves compatibility and dominates the total cardinality
with the correct bucket multiplicity.
-/

namespace Erdos796

open scoped BigOperators

namespace BucketCompression

def bucketFiber (Q : Finset ℕ) (bucket : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  Q.filter fun q => bucket q = j

def bucketIndices (Q : Finset ℕ) (bucket : ℕ → ℕ) : Finset ℕ :=
  Q.image bucket

def bucketMultiplicity (Q : Finset ℕ) (bucket : ℕ → ℕ) (j : ℕ) : ℕ :=
  (bucketFiber Q bucket j).card

@[simp]
theorem mem_bucketFiber {Q : Finset ℕ} {bucket : ℕ → ℕ} {j q : ℕ} :
    q ∈ bucketFiber Q bucket j ↔ q ∈ Q ∧ bucket q = j := by
  simp [bucketFiber]

@[simp]
theorem mem_bucketIndices {Q : Finset ℕ} {bucket : ℕ → ℕ} {j : ℕ} :
    j ∈ bucketIndices Q bucket ↔ ∃ q ∈ Q, bucket q = j := by
  simp [bucketIndices]

theorem bucketFiber_nonempty_of_mem {Q : Finset ℕ} {bucket : ℕ → ℕ}
    {j : ℕ} (hj : j ∈ bucketIndices Q bucket) :
    (bucketFiber Q bucket j).Nonempty := by
  rcases mem_bucketIndices.mp hj with ⟨q, hq, rfl⟩
  exact ⟨q, mem_bucketFiber.mpr ⟨hq, rfl⟩⟩

/-- An index at which the largest fibre in bucket `j` is attained.  Its
value outside the finite bucket image is irrelevant. -/
noncomputable def representative
    (Q : Finset ℕ) (bucket : ℕ → ℕ) (S : ℕ → Finset ℕ) (j : ℕ) : ℕ := by
  classical
  exact if h : (bucketFiber Q bucket j).Nonempty then
    Classical.choose
      (Finset.exists_max_image (bucketFiber Q bucket j)
        (fun q => (S q).card) h)
  else 0

theorem representative_spec
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ} {j : ℕ}
    (hj : j ∈ bucketIndices Q bucket) :
    representative Q bucket S j ∈ bucketFiber Q bucket j ∧
      ∀ q ∈ bucketFiber Q bucket j,
        (S q).card ≤ (S (representative Q bucket S j)).card := by
  classical
  have hne := bucketFiber_nonempty_of_mem hj
  rw [representative, dif_pos hne]
  exact Classical.choose_spec
    (Finset.exists_max_image (bucketFiber Q bucket j)
      (fun q => (S q).card) hne)

theorem representative_mem
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ} {j : ℕ}
    (hj : j ∈ bucketIndices Q bucket) :
    representative Q bucket S j ∈ Q :=
  (mem_bucketFiber.mp (representative_spec hj).1).1

theorem representative_bucket
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ} {j : ℕ}
    (hj : j ∈ bucketIndices Q bucket) :
    bucket (representative Q bucket S j) = j :=
  (mem_bucketFiber.mp (representative_spec hj).1).2

theorem card_le_representative
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ}
    {j q : ℕ} (hj : j ∈ bucketIndices Q bucket)
    (hq : q ∈ Q) (hbq : bucket q = j) :
    (S q).card ≤ (S (representative Q bucket S j)).card :=
  (representative_spec hj).2 q (mem_bucketFiber.mpr ⟨hq, hbq⟩)

/-- Keep the largest original fibre in each nonempty bucket. -/
noncomputable def compressedFamily
    (Q : Finset ℕ) (bucket : ℕ → ℕ) (S : ℕ → Finset ℕ) (j : ℕ) :
    Finset ℕ := by
  classical
  exact if j ∈ bucketIndices Q bucket then S (representative Q bucket S j)
    else ∅

theorem compressedFamily_eq_of_mem
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ} {j : ℕ}
    (hj : j ∈ bucketIndices Q bucket) :
    compressedFamily Q bucket S j = S (representative Q bucket S j) := by
  classical
  simp [compressedFamily, hj]

theorem compressedFamily_eq_empty_of_not_mem
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ} {j : ℕ}
    (hj : j ∉ bucketIndices Q bucket) :
    compressedFamily Q bucket S j = ∅ := by
  classical
  simp [compressedFamily, hj]

/-- Range bounds descend from the original indexed fibres to their bucket
representatives. -/
theorem compressedFamily_range
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, S q ⊆ positiveIcc (bucket q)) (j : ℕ) :
    compressedFamily Q bucket S j ⊆ positiveIcc j := by
  classical
  by_cases hj : j ∈ bucketIndices Q bucket
  · have hmem : representative Q bucket S j ∈ Q :=
      representative_mem (Q := Q) (bucket := bucket) (S := S) hj
    have hb : bucket (representative Q bucket S j) = j :=
      representative_bucket (Q := Q) (bucket := bucket) (S := S) hj
    rw [compressedFamily_eq_of_mem hj]
    intro x hx
    have hr := hrange _ hmem hx
    simpa [hb] using! hr
  · rw [compressedFamily_eq_empty_of_not_mem hj]
    exact Finset.empty_subset _

/-- Compatibility of all original displayed fibres is inherited by the
bucket representatives. -/
theorem compressedFamily_compatible
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (hcompat : ∀ q ∈ Q, ∀ r ∈ Q, ∀ m : ℕ,
      productRepCount (S q) (S r) m ≤ 2) :
    ∀ i j m : ℕ,
      productRepCount (compressedFamily Q bucket S i)
        (compressedFamily Q bucket S j) m ≤ 2 := by
  classical
  intro i j m
  by_cases hi : i ∈ bucketIndices Q bucket
  · by_cases hj : j ∈ bucketIndices Q bucket
    · rw [compressedFamily_eq_of_mem hi, compressedFamily_eq_of_mem hj]
      exact hcompat _
        (representative_mem (Q := Q) (bucket := bucket) (S := S) hi) _
        (representative_mem (Q := Q) (bucket := bucket) (S := S) hj) m
    · rw [compressedFamily_eq_empty_of_not_mem hj]
      simp [productRepCount]
  · rw [compressedFamily_eq_empty_of_not_mem hi]
    simp [productRepCount]

/-- The total size of the original fibres is at most the bucket-weighted
size of the selected representatives. -/
theorem sum_card_le_bucketMultiplicity_mul_compressed
    (Q : Finset ℕ) (bucket : ℕ → ℕ) (S : ℕ → Finset ℕ) :
    ∑ q ∈ Q, (S q).card ≤
      ∑ j ∈ bucketIndices Q bucket,
        bucketMultiplicity Q bucket j *
          (compressedFamily Q bucket S j).card := by
  classical
  change ∑ q ∈ Q, (S q).card ≤
    ∑ j ∈ Q.image bucket,
      (Q.filter fun q => bucket q = j).card *
        (compressedFamily Q bucket S j).card
  have hmap : Set.MapsTo bucket (Q : Set ℕ) (Q.image bucket : Set ℕ) := by
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun q => (S q).card)]
  apply Finset.sum_le_sum
  intro j hj
  calc
    ∑ q ∈ Q with bucket q = j, (S q).card ≤
        ∑ q ∈ Q with bucket q = j,
          (compressedFamily Q bucket S j).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      rw [compressedFamily_eq_of_mem hj]
      exact card_le_representative
        (Q := Q) (bucket := bucket) (S := S) hj hq'.1 hq'.2
    _ = bucketMultiplicity Q bucket j *
        (compressedFamily Q bucket S j).card := by
      simp [bucketMultiplicity, bucketFiber]

/-- The compressed family is a genuine compatible cofactor family whenever
the original fibres obey the quotient range bound. -/
theorem compatible_compressedFamily
    {Q : Finset ℕ} {bucket : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, S q ⊆ positiveIcc (bucket q))
    (hcompat : ∀ q ∈ Q, ∀ r ∈ Q, ∀ m : ℕ,
      productRepCount (S q) (S r) m ≤ 2) :
    Compatible (compressedFamily Q bucket S) := by
  exact ⟨compressedFamily_range hrange,
    compressedFamily_compatible hcompat⟩

end BucketCompression

end Erdos796
