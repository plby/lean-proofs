import ErdosProblems.Erdos4.ConditionalProductMoments

/-!
# Aggregate second and mixed moments

Off-diagonal source pairs use the joint-survival estimate. Diagonal
pairs are bounded by the small atom estimate. The mixed moment uses the
same-source collision count, yielding explicit errors proportional to
the total unconditioned hitting mass.
-/

open scoped BigOperators

namespace Erdos4.AggregatedTupleMoments

open AffineTuples TupleCollisionMass ConditionalTupleMoments ConditionalProductMoments

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem mean_square_sum {I : Type*} [Fintype I] (q : ℕ)
    (f : I → (∀ l, ZMod (ell l)) → ℝ) :
    mean ell q (fun a => (∑ i, f i a) ^ 2) =
      ∑ i, ∑ j, mean ell q (fun a => f i a * f j a) := by
  have hpoint (a : ∀ l, ZMod (ell l)) : (∑ i, f i a) ^ 2 = ∑ i, ∑ j, f i a * f j a := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [hpoint, mean_sum]

variable {k : ℕ}

theorem diagonal_mean_square_le (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    mean ell q (fun a => hittingMass ell h p Y μ q a ^ 2) ≤
      (k : ℝ) * α * hitMass h p Y μ q := by
  have hpoint (a : ∀ l, ZMod (ell l)) : hittingMass ell h p Y μ q a ^ 2 ≤
      hitMass h p Y μ q ^ 2 :=
    (sq_le_sq₀ (hittingMass_nonneg ell h p Y μ q hμ0 a)
      (hitMass_nonneg h p Y μ q hμ0)).mpr (hittingMass_le_hitMass ell h p Y μ q hμ0 a)
  exact ((mean_mono ell q _ _ hpoint).trans_eq (mean_const ell q _)).trans
    (hitMass_sq_le h p Y μ q hα hμ0 hμ)

theorem secondMoment_le (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α)
    (hlocal : ∀ p ∈ sources, ∀ p' ∈ sources, p ≠ p' →
      ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y,
        q ∈ tuple h p n → q ∈ tuple h p' m →
          mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p' m)) ≤ L) :
    mean ell q (fun a => (∑ p : sources, hittingMass ell h p Y (μ p) q a) ^ 2) ≤
      L * (∑ p : sources, hitMass h p Y (μ p) q) ^ 2 +
        (k : ℝ) * α * ∑ p : sources, hitMass h p Y (μ p) q := by
  classical
  let τ : sources → ℝ := fun p => hitMass h p Y (μ p) q
  have hτ (p : sources) : 0 ≤ τ p := hitMass_nonneg h p Y (μ p) q (hμ0 p p.property)
  have hpair (p p' : sources) : mean ell q (fun a =>
      hittingMass ell h p Y (μ p) q a * hittingMass ell h p' Y (μ p') q a) ≤
      L * τ p * τ p' + if p = p' then (k : ℝ) * α * τ p else 0 := by
    by_cases hpp : p = p'
    · subst p'
      rw [if_pos rfl]
      have hd := diagonal_mean_square_le ell h p Y (μ p) q hα (hμ0 p p.property) (hμ p p.property)
      have hnonneg : 0 ≤ L * τ p * τ p := mul_nonneg (mul_nonneg hL (hτ p)) (hτ p)
      simpa only [pow_two] using hd.trans (le_add_of_nonneg_left hnonneg)
    · rw [if_neg hpp, add_zero]
      exact off_diagonal_product_le ell h p p' Y (μ p) (μ p') q
        (hμ0 p p.property) (hμ0 p' p'.property)
        (hlocal p p.property p' p'.property (fun heq => hpp (Subtype.ext heq)))
  rw [mean_square_sum]
  calc
    _ ≤ ∑ p : sources, ∑ p' : sources,
        (L * τ p * τ p' + if p = p' then (k : ℝ) * α * τ p else 0) :=
      Finset.sum_le_sum (fun p _hp => Finset.sum_le_sum (fun p' _hp' => hpair p p'))
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · simp only [← Finset.mul_sum, ← Finset.sum_mul]
        change L * (∑ p, τ p) * (∑ p, τ p) = L * (∑ p, τ p) ^ 2
        ring
      · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [← Finset.mul_sum]

theorem mixedMoment_le (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources : Finset ℕ) (hp : ∀ p ∈ sources, 0 < p) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α)
    (hμsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 Y, μ p n = 1)
    (hlocal : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y,
      q ∈ tuple h p m → Disjoint (tuple h p n) (tuple h p m) →
        mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p m)) ≤ L) :
    mean ell q (fun a => ∑ p : sources,
      tupleMass ell h p Y (μ p) a * hittingMass ell h p Y (μ p) q a) ≤
        (L + (k : ℝ) ^ 2 * α) * ∑ p : sources, hitMass h p Y (μ p) q := by
  rw [mean_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun p _hp => mixed_product_le ell h hh (hp p p.property) Y (μ p) q
    (hμ0 p p.property) (hμsum p p.property) hα hL (hμ p p.property) (hlocal p p.property))

theorem firstMoment_lower (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) {L : ℝ}
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hlocal : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, q ∈ tuple h p n →
      L ≤ mean ell q (fun a => indicator ell a (tuple h p n))) :
    L * (∑ p : sources, hitMass h p Y (μ p) q) ≤
      mean ell q (fun a => ∑ p : sources, hittingMass ell h p Y (μ p) q a) := by
  rw [mean_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _hp
  exact (firstMoment_bounds ell h p Y (μ p) q (hμ0 p p.property)
    (fun n hn hqn => ⟨hlocal p p.property n hn hqn, mean_indicator_le_one ell q _⟩)).1

end Erdos4.AggregatedTupleMoments
