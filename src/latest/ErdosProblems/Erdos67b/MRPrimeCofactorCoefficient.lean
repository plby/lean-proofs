import ErdosProblems.Erdos67b.MRBandDivisorMean
import ErdosProblems.Erdos67b.MRFiniteRamareLargeValues

/-!
# Coefficients of a prime power times an arbitrary cofactor

The prime set need not be the one used in the cofactor's denominator.
Grouping by the prime tuple product gives a factorial times the number
of divisors supported on the prime band.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67b

noncomputable section

/-- The actual integer support of a power of a prime polynomial. -/
def primePowerSupport (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  Finset.univ.image (tupleFromProduct (P := P) (k := k))

theorem tupleFromProduct_mem_factoredNumbers {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {k : ℕ} (v : TupleFrom P k) :
    tupleFromProduct v ∈ Nat.factoredNumbers P := by
  classical
  have hprime (i : Fin k) : (v i : ℕ) ∈ Nat.factoredNumbers P := by
    rw [Nat.mem_factoredNumbers]
    refine ⟨(hP (v i) (v i).2).ne_zero, ?_⟩
    simpa only [Nat.primeFactorsList_prime (hP (v i) (v i).2), List.mem_singleton,
      forall_eq] using (v i).2
  have hprod (S : Finset (Fin k)) :
      (∏ i ∈ S, (v i : ℕ)) ∈ Nat.factoredNumbers P := by
    induction S using Finset.induction_on with
    | empty => simp [Nat.mem_factoredNumbers]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact Nat.mul_mem_factoredNumbers (hprime i) ih
  exact hprod Finset.univ

theorem primePowerSupport_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {k n : ℕ} (hn : n ∈ primePowerSupport P k) : 0 < n := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
  exact tupleFromProduct_pos (fun p hp ↦ (hP p hp).pos) v

theorem primePowerSupport_factored {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {k n : ℕ} (hn : n ∈ primePowerSupport P k) : n ∈ Nat.factoredNumbers P := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
  exact tupleFromProduct_mem_factoredNumbers hP v

theorem primePowerSupport_bounds {P : Finset ℕ} {L U k n : ℕ}
    (hL : ∀ p ∈ P, L ≤ p) (hU : ∀ p ∈ P, p ≤ U)
    (hn : n ∈ primePowerSupport P k) : L ^ k ≤ n ∧ n ≤ U ^ k := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
  refine ⟨?_, tupleFromProduct_le_pow hU v⟩
  calc
    L ^ k = ∏ _i : Fin k, L := by simp
    _ ≤ tupleFromProduct v := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      (fun i _ ↦ hL (v i) (v i).2)

/-- Exact power expansion on the actual prime-product support. -/
theorem logarithmicDirichletPolynomial_pow_eq_primePowerSupport
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ → ℂ) (k : ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial P a t ^ k =
      logarithmicDirichletPolynomial (primePowerSupport P k)
        (primePowerCoefficient P a k) t := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp ↦ (hP p hp).pos
  unfold logarithmicDirichletPolynomial
  rw [Finset.sum_subtype P (fun _ ↦ Iff.rfl)
    (fun n ↦ a n * logarithmicPhase n t), Fintype.sum_pow]
  calc
    (∑ v : TupleFrom P k, ∏ i, (a (v i) * logarithmicPhase (v i) t)) =
        ∑ v : TupleFrom P k,
          tupleFromCoefficient a v * logarithmicPhase (tupleFromProduct v) t := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.prod_mul_distrib, logarithmicPhase_tupleFromProduct hPpos]
      rfl
    _ = ∑ n ∈ primePowerSupport P k,
        ∑ v ∈ primeTupleProductFiber P k n,
          tupleFromCoefficient a v * logarithmicPhase (tupleFromProduct v) t := by
      symm
      simpa only [primeTupleProductFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (TupleFrom P k)))
          (t := primePowerSupport P k) (g := tupleFromProduct)
          (fun v hv ↦ Finset.mem_image.mpr ⟨v, hv, rfl⟩)
          (fun v ↦ tupleFromCoefficient a v * logarithmicPhase (tupleFromProduct v) t))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primePowerCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mem_primeTupleProductFiber.mp hv]

theorem norm_primePowerCoefficient_le_factorial_inv
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹) (k n : ℕ) :
    ‖primePowerCoefficient P a k n‖ ≤ (k.factorial : ℝ) * (n : ℝ)⁻¹ := by
  classical
  have hterm (v : TupleFrom P k) :
      ‖tupleFromCoefficient a v‖ ≤ (tupleFromProduct v : ℝ)⁻¹ := by
    unfold tupleFromCoefficient tupleCoefficient tupleFromProduct tupleProduct
    rw [norm_prod, Nat.cast_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
      (fun i _ ↦ ha (v i) (v i).2)
  calc
    _ ≤ ∑ v ∈ primeTupleProductFiber P k n, ‖tupleFromCoefficient a v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ primeTupleProductFiber P k n, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [mem_primeTupleProductFiber.mp hv] using hterm v
    _ = ((primeTupleProductFiber P k n).card : ℝ) * (n : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k.factorial : ℝ) * (n : ℝ)⁻¹ := by
      gcongr
      exact_mod_cast card_primeTupleProductFiber_le_factorial hP k n

/-- The product coefficient, with no multiplicativity condition on the
cofactor and no relation between its support and the prime band. -/
def primeCofactorCoefficient (P S : Finset ℕ) (a b : ℕ → ℂ) (k n : ℕ) : ℂ :=
  finiteProductCoefficient (primePowerSupport P k) S (primePowerCoefficient P a k) b n

theorem norm_primeCofactorCoefficient_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖primeCofactorCoefficient P S a b k n‖ ≤
      (k.factorial : ℝ) * bandDivisorCount P n / n := by
  classical
  let F := natProductFiber (primePowerSupport P k) S n
  have hterm (x : ℕ × ℕ) (hx : x ∈ F) :
      ‖primePowerCoefficient P a k x.1 * b x.2‖ ≤ (k.factorial : ℝ) / n := by
    have hxmem := mem_natProductFiber.mp hx
    rw [norm_mul]
    calc
      _ ≤ ((k.factorial : ℝ) * (x.1 : ℝ)⁻¹) * (x.2 : ℝ)⁻¹ :=
        mul_le_mul (norm_primePowerCoefficient_le_factorial_inv hP ha k x.1)
          (hb x.2 hxmem.2.1) (norm_nonneg _) (by positivity)
      _ = (k.factorial : ℝ) / n := by
        rw [mul_assoc, ← mul_inv, ← Nat.cast_mul, hxmem.2.2, div_eq_mul_inv]
  have hcard : F.card ≤ bandDivisorCount P n := by
    have hinj : Set.InjOn (fun x : ℕ × ℕ ↦ x.1) F := by
      intro x hx y hy hxy
      have hxmem := mem_natProductFiber.mp hx
      have hymem := mem_natProductFiber.mp hy
      have hxpos := primePowerSupport_pos hP hxmem.1
      change x.1 = y.1 at hxy
      apply Prod.ext hxy
      apply Nat.eq_of_mul_eq_mul_left hxpos
      rw [hxmem.2.2, hxy, hymem.2.2]
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    have hxmem := mem_natProductFiber.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨⟨x.2, hxmem.2.2.symm⟩, hn.ne'⟩,
      primePowerSupport_factored hP hxmem.1⟩
  calc
    _ ≤ ∑ x ∈ F, ‖primePowerCoefficient P a k x.1 * b x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ F, (k.factorial : ℝ) / n := Finset.sum_le_sum hterm
    _ = (F.card : ℝ) * ((k.factorial : ℝ) / n) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (bandDivisorCount P n : ℝ) * ((k.factorial : ℝ) / n) := by
      gcongr
    _ = (k.factorial : ℝ) * bandDivisorCount P n / n := by ring

end

end Erdos67b
