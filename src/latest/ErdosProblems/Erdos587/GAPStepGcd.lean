import ErdosProblems.Erdos587.ReserveHomogeneity
import ErdosProblems.Erdos587.DenseHighFold

/-!
Track the gcd of progression steps independently of coordinate rank.
Covering a noncollapsed progression can only decrease this gcd. Uniform
coordinate multipliers increase it by a bounded integer factor. These are
the arithmetic invariants needed when the amplified progression changes rank.
-/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

def stepGcd (P : GeneralizedAP) : ℤ := Finset.univ.gcd P.step

theorem stepGcd_dvd_step (P : GeneralizedAP) (i : Fin P.rank) : P.stepGcd ∣ P.step i :=
  Finset.gcd_dvd (Finset.mem_univ i)

theorem hasHomogeneousBase_iff_stepGcd_dvd (P : GeneralizedAP) :
    P.HasHomogeneousBase ↔ P.stepGcd ∣ P.base := by
  constructor
  · intro h
    exact h P.stepGcd P.stepGcd_dvd_step
  · intro h d hd
    exact (Finset.dvd_gcd (fun i _ => hd i)).trans h

theorem stepGcd_dvd_sub_base (P : GeneralizedAP) {x : ℤ} (hx : x ∈ P.carrier) :
    P.stepGcd ∣ x - P.base := by
  obtain ⟨v, rfl⟩ := P.mem_carrier_iff.mp hx
  simp only [eval, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (P.stepGcd_dvd_step i) (v i : ℤ)

theorem base_add_step_mem (P : GeneralizedAP) (i : Fin P.rank) (hi : 0 < P.length i) :
    P.base + P.step i ∈ P.carrier := by
  classical
  let v : P.Param := fun j => if hji : j = i then
    ⟨1, by simpa only [hji] using Nat.succ_lt_succ hi⟩ else 0
  apply P.mem_carrier_iff.mpr
  refine ⟨v, ?_⟩
  have hv (j : Fin P.rank) : (v j : ℤ) = if j = i then 1 else 0 := by
    by_cases hji : j = i <;> simp [v, hji]
  simp [eval, hv]

theorem stepGcd_dvd_of_carrier_subset (P Q : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) (hsub : P.carrier ⊆ Q.carrier) :
    Q.stepGcd ∣ P.stepGcd := by
  apply Finset.dvd_gcd
  intro i _
  have hbase : P.base ∈ P.carrier := P.mem_carrier_iff.mpr
    ⟨fun _ => 0, by simp [eval]⟩
  have h₀ := Q.stepGcd_dvd_sub_base (hsub hbase)
  have h₁ := Q.stepGcd_dvd_sub_base (hsub (P.base_add_step_mem i (hpos i)))
  have hd := dvd_sub h₁ h₀
  convert hd using 1 <;> ring

theorem homogeneousBase_of_carrier_subset (P Q : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) (hsub : P.carrier ⊆ Q.carrier)
    (hP : P.HasHomogeneousBase) : Q.HasHomogeneousBase := by
  apply Q.hasHomogeneousBase_iff_stepGcd_dvd.mpr
  have hbase : P.base ∈ P.carrier := P.mem_carrier_iff.mpr
    ⟨fun _ => 0, by simp [eval]⟩
  have hp : Q.stepGcd ∣ P.base :=
    (P.stepGcd_dvd_of_carrier_subset Q hpos hsub).trans
      (P.hasHomogeneousBase_iff_stepGcd_dvd.mp hP)
  have hd := dvd_sub hp (Q.stepGcd_dvd_sub_base (hsub hbase))
  have heq : P.base - (P.base - Q.base) = Q.base := by ring
  exact heq ▸ hd

theorem stepGcd_dilate (P : GeneralizedAP) (n : ℕ) : (P.dilate n).stepGcd = P.stepGcd := rfl

theorem stepGcd_translateBy (P : GeneralizedAP) (z : ℤ) :
    (P.translateBy z).stepGcd = P.stepGcd := rfl

theorem stepGcd_dvd_mul_of_multipliers (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℤ)
    (hsteps : ∀ i : Fin Q.rank, ∀ j : Fin P.rank,
      i.val = j.val → Q.step i = a j * P.step j) :
    Q.stepGcd ∣ ((∏ i, (a i).natAbs : ℕ) : ℤ) * P.stepGcd := by
  classical
  let K := ∏ i, (a i).natAbs
  have hdiv (i : Fin P.rank) : Q.stepGcd ∣ (K : ℤ) * P.step i := by
    have hprod : (a i).natAbs ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hprod' : ((a i).natAbs : ℤ) ∣ (K : ℤ) := by exact_mod_cast hprod
    have habs : a i ∣ ((a i).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      by_cases ha : 0 ≤ a i
      · rw [abs_of_nonneg ha]
      · rw [abs_of_neg (by omega)]
        exact dvd_neg.mpr (dvd_refl (a i))
    have hstep := Q.stepGcd_dvd_step (Fin.cast hrank.symm i)
    rw [hsteps (Fin.cast hrank.symm i) i rfl] at hstep
    exact hstep.trans (mul_dvd_mul (habs.trans hprod') (dvd_refl (P.step i)))
  obtain ⟨b, hb⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin P.rank)) P.step
  change Q.stepGcd ∣ (K : ℤ) * Finset.univ.gcd P.step
  rw [hb, Finset.mul_sum]
  apply Finset.dvd_sum
  intro i _
  rw [← mul_assoc]
  exact dvd_mul_of_dvd_left (hdiv i) (b i)

theorem exists_stepGcd_multiplier_bound (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (hQ : Q.Proper) (hpos : ∀ i, 0 < Q.length i) (B : ℕ)
    (hstep : Q.StepMultipliersBoundedByConstant P B) :
    ∃ K : ℕ, 0 < K ∧ K ≤ B ^ P.rank ∧ Q.stepGcd ∣ (K : ℤ) * P.stepGcd := by
  classical
  have hmult : ∀ j : Fin P.rank, ∃ a : ℤ, a ≠ 0 ∧ |a| ≤ (B : ℤ) ∧
      Q.step (Fin.cast hrank.symm j) = a * P.step j := by
    intro j
    exact CFP.standardized_step_multiplier_nonzero P Q hQ hpos B hstep
      (Fin.cast hrank.symm j) j rfl
  choose a hane habs haeq using hmult
  have hsteps : ∀ i : Fin Q.rank, ∀ j : Fin P.rank,
      i.val = j.val → Q.step i = a j * P.step j := by
    intro i j hij
    have hidx : Fin.cast hrank.symm j = i := Fin.ext hij.symm
    simpa only [hidx] using haeq j
  let K := ∏ i, (a i).natAbs
  refine ⟨K, ?_, ?_, P.stepGcd_dvd_mul_of_multipliers Q hrank a hsteps⟩
  · exact Finset.prod_pos (fun i _ => Int.natAbs_pos.mpr (hane i))
  · calc
      K ≤ ∏ _i : Fin P.rank, B := by
        apply Finset.prod_le_prod'
        intro i _
        have hi : ((a i).natAbs : ℤ) ≤ (B : ℤ) := by
          simpa only [Int.natCast_natAbs] using habs i
        exact_mod_cast hi
      _ = B ^ P.rank := by simp

end Erdos587.GeneralizedAP
