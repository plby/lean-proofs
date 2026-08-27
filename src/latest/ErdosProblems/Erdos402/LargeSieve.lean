import ErdosProblems.Erdos402.Ramanujan
import ErdosProblems.Erdos402.SieveDenominator
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ReducedFractionLargeSieve

namespace Erdos402.Sieve

open BoundedGaps.Maynard

noncomputable section

def fourierEnergy (S : Finset ℕ) (q : ℕ) [NeZero q] : ℝ :=
  ∑ u : (ZMod q)ˣ,
    ‖∑ n ∈ S, ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))‖ ^ 2

lemma fourierEnergy_nonneg (S : Finset ℕ) (q : ℕ) [NeZero q] :
    0 ≤ fourierEnergy S q := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private lemma norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i ↦ a i * b i)
  calc
    _ ≤ (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖a i‖) (fun i ↦ ‖b i‖)

/-- If the affine values on `S` are coprime to a squarefree modulus, their
reduced-frequency energy is at least `|S|²/φ(q)`. -/
theorem card_sq_le_totient_mul_energy {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (S : Finset ℕ) (c m : ℕ) (hm : m.Coprime q)
    (hS : ∀ n ∈ S, (c + m * n).Coprime q) :
    (S.card : ℝ) ^ 2 ≤ (q.totient : ℝ) * fourierEnergy S q := by
  classical
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let a : (ZMod q)ˣ → ℂ := fun u ↦ ψ ((u : ZMod q) * c)
  let b : (ZMod q)ˣ → ℂ := fun u ↦
    ∑ n ∈ S, ψ (((u : ZMod q) * m) * (n : ZMod q))
  have hsum : (∑ u : (ZMod q)ˣ, a u * b u) = (S.card : ℂ) * unitSum ψ := by
    calc
      _ = ∑ u : (ZMod q)ˣ, ∑ n ∈ S, ψ ((u : ZMod q) * (c + m * n : ℕ)) := by
        apply Finset.sum_congr rfl
        intro u _
        dsimp only [a, b]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [← ψ.map_add_eq_mul]
        congr 1
        push_cast
        ring
      _ = ∑ n ∈ S, ∑ u : (ZMod q)ˣ, ψ ((u : ZMod q) * (c + m * n : ℕ)) :=
        Finset.sum_comm
      _ = ∑ n ∈ S, unitSum ψ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact sum_units_mul_coprime ψ _ (hS n hn)
      _ = _ := by simp
  have ha : (∑ u : (ZMod q)ˣ, ‖a u‖ ^ 2) = (q.totient : ℝ) := by
    have hnorm (u : (ZMod q)ˣ) : ‖a u‖ = 1 :=
      (ZMod.toCircle ((u : ZMod q) * (c : ZMod q))).norm_coe
    simp [hnorm, ZMod.card_units_eq_totient]
  have hb : (∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2) = fourierEnergy S q := by
    apply Fintype.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime m hm))
    intro u
    change ‖∑ n ∈ S, ψ (((u : ZMod q) * (m : ZMod q)) * (n : ZMod q))‖ ^ 2 =
      ‖∑ n ∈ S, ψ (((u * ZMod.unitOfCoprime m hm : (ZMod q)ˣ) : ZMod q) * (n : ZMod q))‖ ^ 2
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime]
  have hram := norm_unitSum_squarefree q hsq ψ (ZMod.isPrimitive_stdAddChar q)
  have hCS := norm_sum_mul_sq_le Finset.univ a b
  rwa [hsum, ha, hb, norm_mul, Complex.norm_natCast, hram, mul_one] at hCS

def totalEnergy (S : Finset ℕ) (Q : ℕ) : ℝ :=
  ∑ q : positiveModuliUpTo Q, fourierEnergy S q.1

lemma denominator_eq_sum_positive (k Q : ℕ) :
    denominator k Q = ∑ q : positiveModuliUpTo Q,
      if Squarefree q.1 ∧ q.1.Coprime k then (1 : ℝ) / q.1.totient else 0 := by
  classical
  unfold denominator
  rw [Finset.sum_filter]
  exact (Finset.sum_coe_sort (Finset.Icc 1 Q) _).symm

theorem card_sq_mul_denominator_le_energy (S : Finset ℕ) (Q c m : ℕ)
    (hS : ∀ n ∈ S, ∀ d ∈ Finset.Icc 1 Q, (c + m * n).Coprime d) :
    (S.card : ℝ) ^ 2 * denominator m Q ≤ totalEnergy S Q := by
  classical
  rw [denominator_eq_sum_positive, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hd : Squarefree q.1 ∧ q.1.Coprime m
  · rw [if_pos hd, mul_one_div]
    have htpos : (0 : ℝ) < q.1.totient := by
      exact_mod_cast Nat.totient_pos.mpr ((Finset.mem_Icc.mp q.2).1)
    apply (div_le_iff₀ htpos).mpr
    simpa only [mul_comm] using card_sq_le_totient_mul_energy hd.1 S c m hd.2.symm
      (fun n hn ↦ hS n hn q.1 q.2)
  · rw [if_neg hd, mul_zero]
    exact fourierEnergy_nonneg S q.1

theorem totalEnergy_le_interval (S : Finset ℕ) (Q a H : ℕ)
    (hS : S ⊆ Finset.Ioc a (a + H)) :
    totalEnergy S Q ≤ ((H : ℝ) + (Q : ℝ) ^ 2) * S.card := by
  classical
  let C : ℕ → ℂ := fun n ↦ if n ∈ S then 1 else 0
  have htrig (q : positiveModuliUpTo Q) (u : (ZMod q.1)ˣ) :
      (∑ n ∈ Finset.Ioc a (a + H), C n * ZMod.stdAddChar ((u : ZMod q.1) * (n : ZMod q.1))) =
        ∑ n ∈ S, ZMod.stdAddChar ((u : ZMod q.1) * (n : ZMod q.1)) := by
    calc
      _ = ∑ n ∈ S, C n * ZMod.stdAddChar ((u : ZMod q.1) * (n : ZMod q.1)) := by
        symm
        apply Finset.sum_subset hS
        intro n _ hn
        simp [C, hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [C, hn]
  have hmass : (∑ n ∈ Finset.Ioc a (a + H), ‖C n‖ ^ 2) = (S.card : ℝ) := by
    calc
      _ = ∑ n ∈ S, ‖C n‖ ^ 2 := by
        symm
        apply Finset.sum_subset hS
        intro n _ hn
        simp [C, hn]
      _ = ∑ n ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [C, hn]
      _ = _ := by simp
  have h := sum_norm_sq_reducedFraction_stdAddChar_Ioc_le Q a H C
  simp_rw [htrig, hmass] at h
  have heq : totalEnergy S Q = ∑ z : reducedFractionIndices Q,
      ‖∑ n ∈ S, ZMod.stdAddChar ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2 := by
    unfold totalEnergy fourierEnergy
    rw [Finset.sum_sigma']
    apply Finset.sum_congr
    · ext z
      simp
    · intro z _
      rfl
  rwa [heq]

/-- The effective large-sieve upper bound with an arbitrary cutoff `Q`.
The hypothesis only says that the affine values avoid the small prime
divisors; it is automatic for prime values larger than `Q`. -/
theorem card_mul_denominator_le (S : Finset ℕ) (Q a H c m : ℕ)
    (hS : S ⊆ Finset.Ioc a (a + H))
    (hcop : ∀ n ∈ S, ∀ d ∈ Finset.Icc 1 Q, (c + m * n).Coprime d) :
    (S.card : ℝ) * denominator m Q ≤ (H : ℝ) + (Q : ℝ) ^ 2 := by
  have h := (card_sq_mul_denominator_le_energy S Q c m hcop).trans
    (totalEnergy_le_interval S Q a H hS)
  by_cases hcard : S.card = 0
  · simp only [hcard, Nat.cast_zero, zero_mul]
    positivity
  · have hcardR : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hcard
    apply (mul_le_mul_iff_right₀ hcardR).mp
    nlinarith [h]

theorem card_le_log_bound {m Q : ℕ} (hm : 0 < m) (hQ : 0 < Q)
    (S : Finset ℕ) (a H c : ℕ) (hS : S ⊆ Finset.Ioc a (a + H))
    (hcop : ∀ n ∈ S, ∀ d ∈ Finset.Icc 1 Q, (c + m * n).Coprime d) :
    (S.card : ℝ) ≤ (m : ℝ) / m.totient *
      ((H : ℝ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hlog : 0 < Real.log (Q + 1 : ℕ) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hQ)
  have h := (mul_le_mul_of_nonneg_left (totient_div_mul_log_add_one_le_denominator hm Q)
    (Nat.cast_nonneg S.card)).trans (card_mul_denominator_le S Q a H c m hS hcop)
  apply (le_div_iff₀ hlog).mpr
  apply (mul_le_mul_iff_right₀ (div_pos htR hmR)).mp
  have heq : (m.totient : ℝ) / m * ((m : ℝ) / m.totient *
      ((H : ℝ) + (Q : ℝ) ^ 2)) = (H : ℝ) + (Q : ℝ) ^ 2 := by field_simp
  nlinarith [h, heq]

/-- An explicit prime-in-progression bound, with a freely chosen sieve
cutoff. Primes in the set are required to exceed that cutoff. -/
theorem primeValues_card_le_log_bound {m Q : ℕ} (hm : 0 < m) (hQ : 0 < Q)
    (S : Finset ℕ) (a H c : ℕ) (hS : S ⊆ Finset.Ioc a (a + H))
    (hprime : ∀ n ∈ S, (c + m * n).Prime)
    (hlarge : ∀ n ∈ S, Q < c + m * n) :
    (S.card : ℝ) ≤ (m : ℝ) / m.totient *
      ((H : ℝ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) := by
  apply card_le_log_bound hm hQ S a H c hS
  intro n hn d hd
  apply (hprime n hn).coprime_iff_not_dvd.mpr
  intro hdiv
  have hdI := Finset.mem_Icc.mp hd
  have hpd := Nat.le_of_dvd hdI.1 hdiv
  exact (not_lt_of_ge (hpd.trans hdI.2)) (hlarge n hn)

end
end Erdos402.Sieve
