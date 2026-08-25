import Util.Bernays.LocalPrimePackets
import Util.Bernays.FiniteAvoidance

/-!
# The exact local asymptotic after removing finitely many allowed primes
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem prime_prod_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    apply (hP p hp).coprime_iff_not_dvd.mpr
    exact fun hdvd => hpq ((Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q hq)).mp hdvd)

noncomputable def localAvoidValues (S : ℕ → Prop) (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (localValues S N).filter fun n => ∀ p ∈ P, ¬p ∣ n

noncomputable def avoidFactor (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

theorem avoidFactor_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 < avoidFactor P := by
  apply Finset.prod_pos
  intro p hp
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hP p hp).one_lt))

theorem localAvoidValues_card_eq (S : ℕ → Prop) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬S p) (N : ℕ) :
    ((localAvoidValues S P N).card : ℝ) =
      ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * localCount S (N / ∏ p ∈ T, p) := by
  have heq : ((localAvoidValues S P N).card : ℝ) =
      (eventCount (localValues S N) (fun n => ∀ p ∈ P, ¬p ∣ n) : ℝ) := by
    unfold localAvoidValues eventCount
    congr
  rw [heq, eventCount_avoid_eq_sum_powerset]
  apply Finset.sum_congr rfl
  intro T hT
  have hTP : T ⊆ P := Finset.mem_powerset.mp hT
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (hP p (hTP hp)).1
  have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos (fun p hp => (hTprime p hp).pos)
  have hS : ∀ q : ℕ, q.Prime → S q → ¬q ∣ ∏ p ∈ T, p := by
    intro q hq hSq hdiv
    obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff (fun p : ℕ => p)).mp hdiv
    have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq (hTprime p hp)).mp hqp
    exact (hP p (hTP hp)).2 (hqp' ▸ hSq)
  have hevent : (fun n : ℕ => ∀ p ∈ T, p ∣ n) = (fun n : ℕ => (∏ p ∈ T, p) ∣ n) := by
    funext n
    exact propext (prime_prod_dvd_iff T hTprime n).symm
  rw [hevent, eventCount_localValues_dvd S hpos hS]

theorem avoidFactor_eq_sum_powerset (P : Finset ℕ) :
    avoidFactor P = ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ) := by
  rw [avoidFactor, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib]

theorem localAvoidValues_card_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p ≠ -1) :
    Tendsto (fun N : ℕ => ((localAvoidValues (fun p : ℕ => χ p = -1) P N).card : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) * avoidFactor P)) := by
  let C := characterLocalConstant χ / sqrt π
  have hterm (T : Finset ℕ) (hT : T ∈ P.powerset) :
      Tendsto (fun N : ℕ => (-1 : ℝ) ^ T.card *
        (localCount (fun p : ℕ => χ p = -1) (N / ∏ p ∈ T, p) : ℝ) / scale N)
        atTop (𝓝 (C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)))) := by
    have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp =>
      (hP p ((Finset.mem_powerset.mp hT) hp)).1.pos
    have h := (localCount_dilation_limit χ hχ₂ hχ hpos).const_mul ((-1 : ℝ) ^ T.card)
    change Tendsto _ _ (𝓝 ((-1 : ℝ) ^ T.card * (C / ((∏ p ∈ T, p : ℕ) : ℝ)))) at h
    have heq : (-1 : ℝ) ^ T.card * (C / ((∏ p ∈ T, p : ℕ) : ℝ)) =
        C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)) := by ring
    rw [heq] at h
    convert h using 1
    ext N
    ring
  have h := tendsto_finsetSum P.powerset hterm
  have hvalue : (∑ T ∈ P.powerset, C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ))) =
      C * avoidFactor P := by rw [avoidFactor_eq_sum_powerset, Finset.mul_sum]
  rw [hvalue] at h
  convert h using 1
  ext N
  rw [localAvoidValues_card_eq _ P hP N, Finset.sum_div]

end Bernays
