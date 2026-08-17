import ErdosProblems.Erdos49.Arithmetic
import ErdosProblems.Erdos49.Combinatorics

/-!
# The finite primary packing calculation

This file isolates the sharp-constant bookkeeping in Tao's primary set.
All analytic information is supplied through a pointwise estimate for one
`d`-slice of one interval hull.  The theorem then combines disjoint hulls with
the exact reciprocal-mass bound for a totient-ratio fibre.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def primaryKey (bucket d : ℕ → ℕ) (n : ℕ) : ℕ × ℚ :=
  (bucket n, totientRatio (d n))

def primaryKeys (A : Finset ℕ) (bucket d : ℕ → ℕ) : Finset (ℕ × ℚ) :=
  A.image (primaryKey bucket d)

def primaryCell (A : Finset ℕ) (bucket d : ℕ → ℕ) (k : ℕ × ℚ) :
    Finset ℕ :=
  A.filter fun n ↦ primaryKey bucket d n = k

def ratioFibre (D : ℕ) (q : ℚ) : Finset ℕ :=
  (Finset.Icc 1 D).filter fun d ↦ totientRatio d = q

@[simp] lemma mem_ratioFibre {D d : ℕ} {q : ℚ} :
    d ∈ ratioFibre D q ↔ 1 ≤ d ∧ d ≤ D ∧ totientRatio d = q := by
  simp [ratioFibre, and_assoc]

lemma ratioFibre_card_le (D : ℕ) (q : ℚ) :
    (ratioFibre D q).card ≤ D := by
  apply (Finset.card_le_card (show ratioFibre D q ⊆ Finset.Icc 1 D by
    intro d hd
    exact (Finset.mem_filter.mp hd).1)).trans
  simp

lemma ratioFibre_reciprocal_sum_real_le_one (D : ℕ) (q : ℚ) :
    (∑ d ∈ ratioFibre D q, (1 : ℝ) / d) ≤ 1 := by
  have hq := sum_totientRatio_fibre_reciprocal_le_one q D
  have hcast :
      (((∑ d ∈ (Finset.Icc 1 D).filter
          (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q),
          (1 : ℚ) / (d : ℚ)) : ℚ) : ℝ) ≤ (1 : ℝ) := by
    exact_mod_cast hq
  calc
    (∑ d ∈ ratioFibre D q, (1 : ℝ) / d) =
        ∑ d ∈ (Finset.Icc 1 D).filter
          (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q),
          (1 : ℝ) / d := by rfl
    _ =
        (((∑ d ∈ (Finset.Icc 1 D).filter
          (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q),
          (1 : ℚ) / (d : ℚ)) : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    _ ≤ 1 := hcast

/-- Sharp finite primary packing theorem.  The error `E` is paid once for
each possible denominator in each occupied `(bucket,ratio)` cell; the leading
term pays only the total length of the disjoint integer hulls. -/
theorem primary_packing_bound
    {N D : ℕ} {A : Finset ℕ} {bucket d : ℕ → ℕ} {K E : ℝ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hd : ∀ n ∈ A, 1 ≤ d n ∧ d n ≤ D)
    (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hdisj : ((primaryKeys A bucket d : Finset (ℕ × ℚ)) : Set (ℕ × ℚ)).PairwiseDisjoint
      (fun k ↦ intervalHull (primaryCell A bucket d k)))
    (hcount : ∀ k ∈ primaryKeys A bucket d, ∀ d₀ ∈ ratioFibre D k.2,
      (((primaryCell A bucket d k).filter fun n ↦ d n = d₀).card : ℝ) ≤
        K * ((intervalHull (primaryCell A bucket d k)).card : ℝ) /
          (d₀ : ℝ) + E) :
    (A.card : ℝ) ≤ K * N +
      ((primaryKeys A bucket d).card : ℝ) * D * E := by
  let keys := primaryKeys A bucket d
  let cell := primaryCell A bucket d
  let hull := fun k ↦ intervalHull (cell k)
  have hcellSub (k : ℕ × ℚ) : cell k ⊆ A := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcellD (k : ℕ × ℚ) (hk : k ∈ keys) :
      ((cell k).card : ℝ) =
        ∑ d₀ ∈ ratioFibre D k.2,
          (((cell k).filter fun n ↦ d n = d₀).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    apply Finset.card_eq_sum_card_fiberwise
    intro n hn
    have hnA := hcellSub k hn
    have hdk := hd n hnA
    have hnkey := (Finset.mem_filter.mp hn).2
    exact mem_ratioFibre.mpr ⟨hdk.1, hdk.2, by
      have := congrArg Prod.snd hnkey
      simpa [primaryKey] using this⟩
  have hcellBound (k : ℕ × ℚ) (hk : k ∈ keys) :
      ((cell k).card : ℝ) ≤ K * ((hull k).card : ℝ) + D * E := by
    rw [hcellD k hk]
    calc
      (∑ d₀ ∈ ratioFibre D k.2,
          (((cell k).filter fun n ↦ d n = d₀).card : ℝ)) ≤
          ∑ d₀ ∈ ratioFibre D k.2,
            (K * ((hull k).card : ℝ) / (d₀ : ℝ) + E) := by
        exact Finset.sum_le_sum fun d₀ hd₀ ↦ hcount k hk d₀ hd₀
      _ = K * ((hull k).card : ℝ) *
            (∑ d₀ ∈ ratioFibre D k.2, (1 : ℝ) / d₀) +
          ((ratioFibre D k.2).card : ℝ) * E := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d₀ hd₀
          ring
        · simp
      _ ≤ K * ((hull k).card : ℝ) * 1 + (D : ℝ) * E := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
            (ratioFibre_reciprocal_sum_real_le_one D k.2)
          positivity
        · apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast ratioFibre_card_le D k.2
      _ = K * ((hull k).card : ℝ) + D * E := by ring
  have hcardA : (A.card : ℝ) = ∑ k ∈ keys, ((cell k).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    exact Finset.card_eq_sum_card_image (primaryKey bucket d) A
  have hhullSub (k : ℕ × ℚ) (hk : k ∈ keys) :
      hull k ⊆ Finset.Icc 1 N :=
    intervalHull_subset_Icc ((hcellSub k).trans hA)
  have hhullSum : ∑ k ∈ keys, (hull k).card ≤ N := by
    exact sum_card_Icc_le_of_pairwiseDisjoint keys hull N hhullSub hdisj
  have hhullSumReal :
      (∑ k ∈ keys, ((hull k).card : ℝ)) ≤ (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hhullSum
  rw [hcardA]
  calc
    (∑ k ∈ keys, ((cell k).card : ℝ)) ≤
        ∑ k ∈ keys, (K * ((hull k).card : ℝ) + D * E) :=
      Finset.sum_le_sum hcellBound
    _ = K * (∑ k ∈ keys, ((hull k).card : ℝ)) +
        (keys.card : ℝ) * (D * E) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ ≤ K * N + (keys.card : ℝ) * (D * E) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hhullSumReal hK) le_rfl
    _ = K * N + (keys.card : ℝ) * D * E := by ring

#print axioms primary_packing_bound

end

end Erdos49
