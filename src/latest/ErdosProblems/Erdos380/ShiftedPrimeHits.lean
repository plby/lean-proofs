import ErdosProblems.Erdos380.PrimeHitVariance

/-!
# Divisibility of shifted prime products

Both directions from an anchor are represented by an integer unit `ε`, so
negative shifts use integer subtraction rather than truncated subtraction
of natural numbers. Primes dividing the fixed coefficient are excluded
explicitly when applying the residue estimates.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

def progressionResidue (c : ∀ p : ℕ, (ZMod p)ˣ) {H : ℕ} (p : ℕ) (j : Fin H) : ZMod p :=
  (c p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)

lemma progressionResidue_isUnit (c : ∀ p : ℕ, (ZMod p)ˣ) {H p : ℕ}
    (hp : p.Prime) (hH : H < p) (j : Fin H) : IsUnit (progressionResidue c p j) := by
  have hjpos : 0 < j.val + 1 := by omega
  have hjp : j.val + 1 < p := by have := j.isLt; omega
  have hcop : (j.val + 1).Coprime p :=
    ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hjpos hjp)).symm
  exact (c p).isUnit.mul ((ZMod.isUnit_iff_coprime _ _).mpr hcop)

lemma progressionResidue_injective (c : ∀ p : ℕ, (ZMod p)ˣ) {H p : ℕ}
    (hH : H < p) : Function.Injective (progressionResidue c (H := H) p) := by
  intro i j hij
  have hcast : ((i.val + 1 : ℕ) : ZMod p) = ((j.val + 1 : ℕ) : ZMod p) :=
    (c p).isUnit.mul_left_cancel hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hval
  apply Fin.ext
  omega

def naturalCoefficientUnit (c p : ℕ) : (ZMod p)ˣ :=
  if h : c.Coprime p then ZMod.unitOfCoprime c h else 1

lemma naturalCoefficientUnit_val {c p : ℕ} (hc : c.Coprime p) :
    (naturalCoefficientUnit c p : ZMod p) = c := by
  unfold naturalCoefficientUnit
  rw [dif_pos hc]
  exact ZMod.coe_unitOfCoprime c hc

def shiftedCoefficientUnit (c : ℕ) (ε : ℤˣ) (p : ℕ) : (ZMod p)ˣ :=
  -(naturalCoefficientUnit c p)⁻¹ * Units.map (Int.castRingHom (ZMod p)).toMonoidHom ε

lemma unit_affine_zero_iff {p : ℕ} (c e : (ZMod p)ˣ) (x h : ZMod p) :
    (c : ZMod p) * x + (e : ZMod p) * h = 0 ↔
      x = ((-c⁻¹ * e : (ZMod p)ˣ) : ZMod p) * h := by
  have heq : (c : ZMod p) * (((-c⁻¹ * e : (ZMod p)ˣ) : ZMod p) * h) =
      -((e : ZMod p) * h) := by simp [← mul_assoc]
  constructor
  · intro hx
    apply c.isUnit.mul_left_cancel
    rw [heq]
    exact eq_neg_of_add_eq_zero_left hx
  · intro hx
    rw [hx, heq]
    ring

lemma shifted_divisibility_iff_residue {c p H : ℕ} (ε : ℤˣ) (hc : c.Coprime p)
    (j : Fin H) (V : ℕ) :
    ((p : ℤ) ∣ (c * V : ℕ) + (ε : ℤ) * (j.val + 1 : ℕ)) ↔
      (V : ZMod p) = progressionResidue (shiftedCoefficientUnit c ε) p j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [← naturalCoefficientUnit_val hc]
  exact unit_affine_zero_iff (naturalCoefficientUnit c p)
    (Units.map (Int.castRingHom (ZMod p)).toMonoidHom ε) V (j.val + 1 : ℕ)

def shiftedPrimeHitCount (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H c : ℕ) (ε : ℤˣ)
    (f : ∀ i, s i) : ℝ :=
  ∑ p ∈ t, ∑ j : Fin H,
    if (p : ℤ) ∣ (c * tupleNaturalProduct s f : ℕ) + (ε : ℤ) * (j.val + 1 : ℕ) then 1 else 0

lemma shiftedPrimeHitCount_eq (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H c : ℕ) (ε : ℤˣ)
    (hc : ∀ p ∈ t, c.Coprime p) (f : ∀ i, s i) :
    shiftedPrimeHitCount s t H c ε f =
      primeResidueHitCount s t H (progressionResidue (shiftedCoefficientUnit c ε)) f := by
  classical
  unfold shiftedPrimeHitCount primeResidueHitCount
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [tupleResidueIndicator, shifted_divisibility_iff_residue ε (hc p hp)]

theorem shiftedPrimeHitCount_tail_le
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H c : ℕ) (ε : ℤˣ)
    (ht : ∀ p ∈ t, p.Prime) (hHt : ∀ p ∈ t, H < p) (hc : ∀ p ∈ t, c.Coprime p)
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty)
    {S U : ℝ} (hS : (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ S)
    (hsmall : (H : ℝ) * modulusPairSum t (tenPrimeResidueError s) ≤ 1)
    (hH : 0 < H) (hU : 0 < U) (hUS : 2 * S ≤ U) :
    ((Finset.univ.filter fun f : ∀ i, s i => (H : ℝ) * U ≤ shiftedPrimeHitCount s t H c ε f).card : ℝ) /
        (Fintype.card (∀ i, s i) : ℝ) ≤ 4 * (2 + 3 * S) / ((H : ℝ) * U ^ 2) := by
  classical
  simp only [shiftedPrimeHitCount_eq s t H c ε hc]
  exact primeResidueHitCount_tail_le s t H (progressionResidue (shiftedCoefficientUnit c ε)) ht
    (fun p hp j => progressionResidue_isUnit _ (ht p hp) (hHt p hp) j)
    (fun p hp => progressionResidue_injective _ (hHt p hp)) hs hne hS hsmall hH hU hUS

lemma shifted_not_dvd_of_not_coprime {c p H : ℕ} (ε : ℤˣ)
    (hp : p.Prime) (hH : H < p) (hc : ¬ c.Coprime p) (j : Fin H) (V : ℕ) :
    ¬ ((p : ℤ) ∣ (c * V : ℕ) + (ε : ℤ) * (j.val + 1 : ℕ)) := by
  have hpc : p ∣ c := by
    by_contra h
    exact hc ((hp.coprime_iff_not_dvd.mpr h).symm)
  have hcz : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).mpr hpc
  intro hdiv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    hcz, zero_mul, zero_add] at hz
  have hε : IsUnit ((ε : ℤ) : ZMod p) := ε.isUnit.map (Int.castRingHom (ZMod p))
  have hjz : ((j.val + 1 : ℕ) : ZMod p) = 0 := hε.mul_left_cancel (by simpa using hz)
  have hjdiv := (ZMod.natCast_eq_zero_iff (j.val + 1) p).mp hjz
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by have := j.isLt; omega) hjdiv

lemma shiftedPrimeHitCount_eq_filter_coprime
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H c : ℕ) (ε : ℤˣ)
    (ht : ∀ p ∈ t, p.Prime) (hHt : ∀ p ∈ t, H < p) (f : ∀ i, s i) :
    shiftedPrimeHitCount s t H c ε f =
      shiftedPrimeHitCount s (t.filter fun p => c.Coprime p) H c ε f := by
  classical
  unfold shiftedPrimeHitCount
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hcp : ¬ c.Coprime p := fun h => hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
  apply Finset.sum_eq_zero
  intro j _hj
  exact if_neg (shifted_not_dvd_of_not_coprime ε (ht p hp) (hHt p hp) hcp j _)

lemma modulusPairSum_mono_set {u t : Finset ℕ} (hut : u ⊆ t) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) : modulusPairSum u F ≤ modulusPairSum t F := by
  unfold modulusPairSum
  apply add_le_add
  · exact Finset.sum_le_sum_of_subset_of_nonneg hut (fun n _ _ => hF n)
  · calc
      _ ≤ ∑ p ∈ u, ∑ q ∈ t, F (p * q) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg hut (fun q _ _ => hF (p * q))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hut
        (fun p _ _ => Finset.sum_nonneg fun q _ => hF (p * q))

/-- Primes dividing the fixed coefficient contribute no hits for the short
nonzero shifts, so the coefficient need not be assumed coprime to every modulus. -/
theorem shiftedPrimeHitCount_tail_le_unrestricted_coefficient
    (s : Fin 10 → Finset ℕ) (t : Finset ℕ) (H c : ℕ) (ε : ℤˣ)
    (ht : ∀ p ∈ t, p.Prime) (hHt : ∀ p ∈ t, H < p)
    (hs : ∀ i r, r ∈ s i → r.Prime) (hne : ∀ i, (s i).Nonempty)
    {S U : ℝ} (hS : (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ S)
    (hsmall : (H : ℝ) * modulusPairSum t (tenPrimeResidueError s) ≤ 1)
    (hH : 0 < H) (hU : 0 < U) (hUS : 2 * S ≤ U) :
    ((Finset.univ.filter fun f : ∀ i, s i => (H : ℝ) * U ≤ shiftedPrimeHitCount s t H c ε f).card : ℝ) /
        (Fintype.card (∀ i, s i) : ℝ) ≤ 4 * (2 + 3 * S) / ((H : ℝ) * U ^ 2) := by
  classical
  let u := t.filter fun p => c.Coprime p
  have hut : u ⊆ t := Finset.filter_subset _ _
  have heq : shiftedPrimeHitCount s t H c ε = shiftedPrimeHitCount s u H c ε := by
    funext f
    exact shiftedPrimeHitCount_eq_filter_coprime s t H c ε ht hHt f
  rw [heq]
  apply shiftedPrimeHitCount_tail_le s u H c ε
    (fun p hp => ht p (hut hp)) (fun p hp => hHt p (hut hp))
    (fun p hp => (Finset.mem_filter.mp hp).2) hs hne
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hut (fun _ _ _ => by positivity)).trans hS
  · exact (mul_le_mul_of_nonneg_left
      (modulusPairSum_mono_set hut _ (tenPrimeResidueError_nonneg s)) (Nat.cast_nonneg H)).trans hsmall
  · exact hH
  · exact hU
  · exact hUS

/-- Uniform large-prime concentration for the actual dyadic prime pools.
The admissible length condition is explicit in the scale parameter. -/
theorem exists_uniform_shifted_prime_hit_tail :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ T₀ : ℕ,
      ∀ T : ℕ, T₀ ≤ T → ∀ N : Fin 10 → ℕ,
        (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) →
        ∀ H : ℕ, 0 < H → H ≤ T →
          (H : ℝ) * (C * ((Real.log T) ^ 5 / (T : ℝ))) ≤ 1 →
          ∀ (c : ℕ) (ε : ℤˣ) (U : ℝ), U₀ ≤ U →
            ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (N i) =>
                (H : ℝ) * U ≤ shiftedPrimeHitCount (fun i => dyadicPrimes (N i))
                  (mixingModulusPrimes T) H c ε f).card : ℝ) /
              (Fintype.card (∀ i, dyadicPrimes (N i)) : ℝ) ≤ K / ((H : ℝ) * U ^ 2) := by
  obtain ⟨C, hC, Tm, hm⟩ := exists_uniform_ten_prime_mixing_bound
  obtain ⟨S, hS0, hS⟩ := exists_mixingModulusPrimes_totient_bound
  obtain ⟨Tp, hp⟩ := Filter.eventually_atTop.mp eventually_dyadic_pool_estimates
  refine ⟨C, 4 * (2 + 3 * S), 2 * S + 1, hC, by positivity, by positivity,
    max Tm (max Tp 2), fun T hT N hNlo hNhi H hH hHT hsmall c ε U hU => ?_⟩
  have hTm : Tm ≤ T := (le_max_left _ _).trans hT
  have hTp : Tp ≤ T := (le_max_left Tp 2).trans ((le_max_right Tm _).trans hT)
  have hT2 : 2 ≤ T := (le_max_right Tp 2).trans ((le_max_right Tm _).trans hT)
  have hTpow : T ≤ T ^ 90 := by
    calc
      T = T ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hne (i : Fin 10) : (dyadicPrimes (N i)).Nonempty :=
    (hp (N i) (hTp.trans (hTpow.trans (hNlo i)))).1
  have hmix := hm T hTm N hNlo hNhi
  apply shiftedPrimeHitCount_tail_le_unrestricted_coefficient
    (fun i => dyadicPrimes (N i)) (mixingModulusPrimes T) H c ε
    (fun p hp => mixingModulusPrimes_prime hp)
    (fun p hp => hHT.trans_lt (mixingModulusPrimes_lower hp))
    (fun i r hr => dyadicPrimes_prime hr) hne (hS T hT2)
  · exact (mul_le_mul_of_nonneg_left hmix (Nat.cast_nonneg H)).trans hsmall
  · exact hH
  · linarith
  · linarith

end

end Erdos380
