import ErdosProblems.Erdos380.TupleResidues

/-!
# Second moment of prime divisibility hits

Distinct residues at the same prime are disjoint. Residues at distinct primes
are handled by the proved CRT correlation estimate. This is the large-prime
part of the smooth-interval probability argument.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

def primeResidueHitCount (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ)
    (a : ∀ p : ℕ, Fin H → ZMod p) (f : ∀ i, s i) : ℝ :=
  ∑ p ∈ t, ∑ j : Fin H, tupleResidueIndicator s p (a p j) f

lemma prime_residue_hit_first_moment (s : Fin 10 → Finset ℕ) {p : ℕ}
    (hp : p.Prime) (a : ZMod p) (ha : IsUnit a)
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty) :
    (1 / (p.totient : ℝ)) - tenPrimeResidueError s p ≤
        𝔼 f : ∀ i, s i, tupleResidueIndicator s p a f := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := (abs_le.mp (expect_ten_prime_residue_error_le s ha hs hne)).1
  linarith

lemma prime_residue_hit_pair_moment (s : Fin 10 → Finset ℕ) {H : ℕ}
    (t : Finset ℕ) (a : ∀ p : ℕ, Fin H → ZMod p)
    (ht : ∀ p ∈ t, p.Prime) (ha : ∀ p ∈ t, ∀ j, IsUnit (a p j))
    (hinj : ∀ p ∈ t, Function.Injective (a p))
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty)
    (i j : ℕ × Fin H) (hi : i ∈ t ×ˢ Finset.univ) (hj : j ∈ t ×ˢ Finset.univ) :
    (𝔼 f : ∀ k, s k,
      tupleResidueIndicator s i.1 (a i.1 i.2) f *
        tupleResidueIndicator s j.1 (a j.1 j.2) f) ≤
      (1 / (i.1.totient : ℝ)) * (1 / (j.1.totient : ℝ)) +
        ((if i = j then (1 / (i.1.totient : ℝ)) + tenPrimeResidueError s i.1 else 0) +
          tenPrimeResidueError s (i.1 * j.1)) := by
  classical
  have hip := (Finset.mem_product.mp hi).1
  have hjp := (Finset.mem_product.mp hj).1
  letI : NeZero i.1 := ⟨(ht i.1 hip).ne_zero⟩
  letI : NeZero j.1 := ⟨(ht j.1 hjp).ne_zero⟩
  by_cases hij : i = j
  · subst j
    simp only [ite_true, if_pos rfl, ← pow_two, tupleResidueIndicator_sq]
    have h := (abs_le.mp (expect_ten_prime_residue_error_le s (ha i.1 hip i.2) hs hne)).2
    have hD := tenPrimeResidueError_nonneg s (i.1 ^ 2)
    nlinarith [sq_nonneg (1 / (i.1.totient : ℝ))]
  · rw [if_neg hij, zero_add]
    by_cases hpq : i.1 = j.1
    · have hres : a i.1 i.2 ≠ a i.1 j.2 := by
        intro heq
        exact hij (Prod.ext hpq (hinj i.1 hip heq))
      have heq : tupleResidueIndicator s j.1 (a j.1 j.2) =
          tupleResidueIndicator s i.1 (a i.1 j.2) :=
        congrArg (fun p : ℕ => tupleResidueIndicator s p (a p j.2)) hpq.symm
      rw [heq, expect_tupleResidueIndicator_mul_same s hres]
      exact add_nonneg (by positivity) (tenPrimeResidueError_nonneg _ _)
    · have hcop : i.1.Coprime j.1 := (Nat.coprime_primes (ht i.1 hip) (ht j.1 hjp)).mpr hpq
      have h := (abs_le.mp (expect_ten_prime_residue_pair_error_le s hcop
        (ha i.1 hip i.2) (ha j.1 hjp j.2) hs hne)).2
      linarith

lemma sum_hit_index_weight (t : Finset ℕ) (H : ℕ) (F : ℕ → ℝ) :
    (∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)), F i.1) = (H : ℝ) * ∑ p ∈ t, F p := by
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

lemma sum_hit_pair_weight (t : Finset ℕ) (H : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
      ∑ j ∈ t ×ˢ (Finset.univ : Finset (Fin H)), F i.1 j.1) =
        (H : ℝ) ^ 2 * ∑ p ∈ t, ∑ q ∈ t, F p q := by
  simp_rw [sum_hit_index_weight, ← Finset.mul_sum]
  rw [sum_hit_index_weight t H (fun p => ∑ q ∈ t, F p q)]
  ring

lemma sum_hit_pair_error (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ) :
    (∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
      ∑ j ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
        ((if i = j then (1 / (i.1.totient : ℝ)) + tenPrimeResidueError s i.1 else 0) +
          tenPrimeResidueError s (i.1 * j.1))) =
      (H : ℝ) * (∑ p ∈ t, 1 / (p.totient : ℝ)) +
        (H : ℝ) * (∑ p ∈ t, tenPrimeResidueError s p) +
        (H : ℝ) ^ 2 * (∑ p ∈ t, ∑ q ∈ t, tenPrimeResidueError s (p * q)) := by
  classical
  simp_rw [Finset.sum_add_distrib]
  have hdiag : (∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
      ∑ j ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
        if i = j then (1 / (i.1.totient : ℝ)) + tenPrimeResidueError s i.1 else 0) =
      ∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
        ((1 / (i.1.totient : ℝ)) + tenPrimeResidueError s i.1) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  rw [hdiag, sum_hit_pair_weight t H (fun p q => tenPrimeResidueError s (p * q)),
    sum_hit_index_weight t H (fun p => (1 / (p.totient : ℝ)) + tenPrimeResidueError s p),
    Finset.sum_add_distrib]
  ring

lemma primeResidueHitCount_second_moment_raw_le
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ) (a : ∀ p : ℕ, Fin H → ZMod p)
    (ht : ∀ p ∈ t, p.Prime) (ha : ∀ p ∈ t, ∀ j, IsUnit (a p j))
    (hinj : ∀ p ∈ t, Function.Injective (a p))
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty) :
    (𝔼 f : ∀ i, s i,
      (primeResidueHitCount s t H a f - (H : ℝ) * ∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2) ≤
      (H : ℝ) * (∑ p ∈ t, 1 / (p.totient : ℝ)) +
        (H : ℝ) * (∑ p ∈ t, tenPrimeResidueError s p) +
        (H : ℝ) ^ 2 * (∑ p ∈ t, ∑ q ∈ t, tenPrimeResidueError s (p * q)) +
        2 * ((H : ℝ) * ∑ p ∈ t, 1 / (p.totient : ℝ)) *
          ((H : ℝ) * ∑ p ∈ t, tenPrimeResidueError s p) := by
  classical
  let I := t ×ˢ (Finset.univ : Finset (Fin H))
  have hΩ : (Finset.univ : Finset (∀ i, s i)).Nonempty :=
    ⟨fun i => ⟨Classical.choose (hne i), Classical.choose_spec (hne i)⟩, Finset.mem_univ _⟩
  have hfinite := finite_centered_second_moment_le I Finset.univ hΩ
    (fun i f => tupleResidueIndicator s i.1 (a i.1 i.2) f)
    (fun i => 1 / (i.1.totient : ℝ)) (fun i => tenPrimeResidueError s i.1)
    (fun i j => (if i = j then (1 / (i.1.totient : ℝ)) + tenPrimeResidueError s i.1 else 0) +
      tenPrimeResidueError s (i.1 * j.1))
    (fun i _ => by positivity)
    (fun i hi => prime_residue_hit_first_moment s (ht i.1 (Finset.mem_product.mp hi).1)
      (a i.1 i.2) (ha i.1 (Finset.mem_product.mp hi).1 i.2) hs hne)
    (fun i hi j hj => prime_residue_hit_pair_moment s t a ht ha hinj hs hne i j hi hj)
  dsimp only [I] at hfinite
  rw [sum_hit_pair_error, sum_hit_index_weight t H (fun p => 1 / (p.totient : ℝ)),
    sum_hit_index_weight t H (tenPrimeResidueError s)] at hfinite
  have hW (f : ∀ i, s i) :
      (∑ i ∈ t ×ˢ (Finset.univ : Finset (Fin H)),
        tupleResidueIndicator s i.1 (a i.1 i.2) f) = primeResidueHitCount s t H a f :=
    Finset.sum_product _ _ _
  simp_rw [hW] at hfinite
  exact hfinite

lemma prime_hit_moment_error_combine (H : ℕ) {r d e : ℝ}
    (hr0 : 0 ≤ r) (hd0 : 0 ≤ d) (he0 : 0 ≤ e) :
    (H : ℝ) * r + (H : ℝ) * d + (H : ℝ) ^ 2 * e +
      2 * ((H : ℝ) * r) * ((H : ℝ) * d) ≤
        (H : ℝ) * r + 2 * (H : ℝ) ^ 2 * (1 + r) * (d + e) := by
  have hH : (H : ℝ) ≤ (H : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · norm_num
    · have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
      nlinarith
  have hhd := mul_le_mul_of_nonneg_right hH hd0
  have hde : d ≤ d + e := by linarith
  have hmain := mul_le_mul_of_nonneg_left hde
    (by positivity : 0 ≤ 2 * (H : ℝ) ^ 2 * r)
  have hnonneg : 0 ≤ (H : ℝ) ^ 2 * (d + e) := by positivity
  nlinarith

/-- The large-prime hit count has variance of order `H` once the summed
residue discrepancy is small compared with `1/H`. -/
theorem primeResidueHitCount_second_moment_le
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ) (a : ∀ p : ℕ, Fin H → ZMod p)
    (ht : ∀ p ∈ t, p.Prime) (ha : ∀ p ∈ t, ∀ j, IsUnit (a p j))
    (hinj : ∀ p ∈ t, Function.Injective (a p))
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty) :
    (𝔼 f : ∀ i, s i,
      (primeResidueHitCount s t H a f - (H : ℝ) * ∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2) ≤
      (H : ℝ) * (∑ p ∈ t, 1 / (p.totient : ℝ)) +
        2 * (H : ℝ) ^ 2 * (1 + ∑ p ∈ t, 1 / (p.totient : ℝ)) *
          modulusPairSum t (tenPrimeResidueError s) := by
  refine (primeResidueHitCount_second_moment_raw_le s t H a ht ha hinj hs hne).trans ?_
  exact prime_hit_moment_error_combine H
    (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun p _ => tenPrimeResidueError_nonneg s p)
    (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => tenPrimeResidueError_nonneg s (p * q))

lemma prime_hit_variance_scalar_le (H : ℕ) {r S E : ℝ}
    (hr : 0 ≤ r) (hrS : r ≤ S) (hE : 0 ≤ E) (hsmall : (H : ℝ) * E ≤ 1) :
    (H : ℝ) * r + 2 * (H : ℝ) ^ 2 * (1 + r) * E ≤ (H : ℝ) * (2 + 3 * S) := by
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hS : 0 ≤ S := hr.trans hrS
  calc
    _ = (H : ℝ) * r + (2 * (H : ℝ) * (1 + r)) * ((H : ℝ) * E) := by ring
    _ ≤ (H : ℝ) * S + (2 * (H : ℝ) * (1 + S)) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hrS hH)
        (mul_le_mul (by gcongr) hsmall (mul_nonneg hH hE) (by positivity))
    _ = _ := by ring

theorem primeResidueHitCount_second_moment_le_of_small_error
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ) (a : ∀ p : ℕ, Fin H → ZMod p)
    (ht : ∀ p ∈ t, p.Prime) (ha : ∀ p ∈ t, ∀ j, IsUnit (a p j))
    (hinj : ∀ p ∈ t, Function.Injective (a p))
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty)
    {S : ℝ} (hS : (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ S)
    (hsmall : (H : ℝ) * modulusPairSum t (tenPrimeResidueError s) ≤ 1) :
    (𝔼 f : ∀ i, s i,
      (primeResidueHitCount s t H a f - (H : ℝ) * ∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2) ≤
        (H : ℝ) * (2 + 3 * S) := by
  refine (primeResidueHitCount_second_moment_le s t H a ht ha hinj hs hne).trans ?_
  apply prime_hit_variance_scalar_le H (Finset.sum_nonneg fun _ _ => by positivity) hS
    _ hsmall
  exact add_nonneg (Finset.sum_nonneg fun p _ => tenPrimeResidueError_nonneg s p)
    (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => tenPrimeResidueError_nonneg s (p * q))

lemma finite_upper_tail_le_centered_second_moment {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) {μ b t : ℝ} (ht : 0 < t) (hbt : μ + t ≤ b) :
    ((Finset.univ.filter fun ω => b ≤ f ω).card : ℝ) / (Fintype.card Ω : ℝ) ≤
      (𝔼 ω, (f ω - μ) ^ 2) / t ^ 2 := by
  classical
  have hsub : (Finset.univ.filter fun ω => b ≤ f ω) ⊆
      (Finset.univ.filter fun ω => t ≤ |f ω - μ|) := by
    intro ω hω
    have hb := (Finset.mem_filter.mp hω).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [le_abs_self (f ω - μ)]⟩
  have hcard : ((Finset.univ.filter fun ω => b ≤ f ω).card : ℝ) ≤
      ((Finset.univ.filter fun ω => t ≤ |f ω - μ|).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)).trans ?_
  simpa only [Finset.card_univ] using finite_chebyshev Finset.univ f μ t ht

/-- The `1/(H U^2)` tail estimate for the large-prime hit contribution. -/
theorem primeResidueHitCount_tail_le
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H : ℕ) (a : ∀ p : ℕ, Fin H → ZMod p)
    (ht : ∀ p ∈ t, p.Prime) (ha : ∀ p ∈ t, ∀ j, IsUnit (a p j))
    (hinj : ∀ p ∈ t, Function.Injective (a p))
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty)
    {S U : ℝ} (hS : (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ S)
    (hsmall : (H : ℝ) * modulusPairSum t (tenPrimeResidueError s) ≤ 1)
    (hH : 0 < H) (hU : 0 < U) (hUS : 2 * S ≤ U) :
    ((Finset.univ.filter fun f : ∀ i, s i => (H : ℝ) * U ≤ primeResidueHitCount s t H a f).card : ℝ) /
        (Fintype.card (∀ i, s i) : ℝ) ≤ 4 * (2 + 3 * S) / ((H : ℝ) * U ^ 2) := by
  classical
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hgap : (H : ℝ) * (∑ p ∈ t, 1 / (p.totient : ℝ)) + (H : ℝ) * U / 2 ≤
      (H : ℝ) * U := by
    have h := mul_le_mul_of_nonneg_left hS hHR.le
    have h' := mul_le_mul_of_nonneg_left hUS hHR.le
    nlinarith
  have hcheb := finite_upper_tail_le_centered_second_moment
    (primeResidueHitCount s t H a) (by positivity : 0 < (H : ℝ) * U / 2) hgap
  have hvar := primeResidueHitCount_second_moment_le_of_small_error s t H a
    ht ha hinj hs hne hS hsmall
  refine hcheb.trans ((div_le_div_of_nonneg_right hvar (sq_nonneg _)).trans_eq ?_)
  field_simp
  ring

end

end Erdos380
