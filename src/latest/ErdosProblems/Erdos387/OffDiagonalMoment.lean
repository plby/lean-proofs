/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ReciprocalMoment
import ErdosProblems.Erdos387.RoughDivisorFamily

/-!
# Off-diagonal reciprocal moments over a family of moduli

For a fixed nonzero cleared numerator, the modulus condition in a modular
reciprocal-energy solution forces every rough divisor parameter to divide
that numerator.  This file reindexes the pairs `(modulus parameter, tuple)`
by the tuple first and applies `roughDivisorFamily_card_le` fibrewise.
-/

namespace Erdos387

open scoped BigOperators

namespace ReciprocalMoment

theorem swapModulusTuple_injective {ι : Type*} :
    Function.Injective
      (fun x : (Σ _D : ℕ, ι → ℕ) =>
        (⟨x.2, x.1⟩ : Σ _s : ι → ℕ, ℕ)) := by
  rintro ⟨D, s⟩ ⟨E, t⟩ h
  cases h
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate tuples from `U` with a nonzero cleared numerator difference. -/
noncomputable def nonzeroNumeratorTuples
    (A : Finset ι) (U : Finset ℕ) : Finset (ι → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : ι => U).filter fun s =>
    reciprocalNumerator A s ≠
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s

/-- Members of `Q` dividing the absolute cleared-numerator difference. -/
noncomputable def dividingModuli
    (Q : Finset ℕ) (A : Finset ι) (s : ι → ℕ) : Finset ℕ := by
  classical
  exact Q.filter fun D => D ∣ Nat.dist
    (reciprocalNumerator A s)
    (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)

/-- Off-diagonal modular-energy tuples, summed over a finite family `Q` of
rough divisor parameters.  The actual additive-character modulus may also
contain fixed factors and is supplied by `modulus`. -/
noncomputable def offDiagonalModulusTuples
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ) :
    Finset (Σ _D : ℕ, ι → ℕ) := by
  classical
  exact Q.sigma fun D =>
    offDiagonalModularReciprocalTuples (modulus D) A U

theorem offDiagonalModulusTuple_mapsTo_tupleFibres
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ)
    (hDmod : ∀ D ∈ Q, D ∣ modulus D)
    (hUcop : ∀ D ∈ Q, ∀ u ∈ U, u.Coprime (modulus D)) :
    ((offDiagonalModulusTuples Q modulus A U :
        Finset (Σ _D : ℕ, ι → ℕ)) :
      Set (Σ _D : ℕ, ι → ℕ)).MapsTo
      (fun x => ⟨x.2, x.1⟩)
      ((nonzeroNumeratorTuples A U).sigma
        (fun s => dividingModuli Q A s) :
          Set (Σ _s : ι → ℕ, ℕ)) := by
  classical
  rintro ⟨D, s⟩ hs
  change ⟨D, s⟩ ∈ offDiagonalModulusTuples Q modulus A U at hs
  rw [offDiagonalModulusTuples, Finset.mem_sigma] at hs
  obtain ⟨hDQ, hsOff⟩ := hs
  rw [offDiagonalModularReciprocalTuples, Finset.mem_filter] at hsOff
  have hsMod := hsOff.1
  have hcoord : ∀ i, s i ∈ U := fun i =>
    modularReciprocalEnergyTuple_coordinate_mem hsMod i
  have hcop : ∀ i, (s i).Coprime (modulus D) := fun i =>
    hUcop D hDQ (s i) (hcoord i)
  have hmodEq : Nat.ModEq (modulus D)
      (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) :=
    (modularReciprocalSum_eq_iff_numerator_modEq A
      ((Finset.univ : Finset ι) \ A) s hcop).1
        (modularReciprocalEnergyTuple_phase hsMod)
  change (⟨s, D⟩ : Σ _s : ι → ℕ, ℕ) ∈
    (nonzeroNumeratorTuples A U).sigma
      (fun s => dividingModuli Q A s)
  rw [Finset.mem_sigma]
  constructor
  · rw [nonzeroNumeratorTuples, Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.mpr hcoord, hsOff.2⟩
  · rw [dividingModuli, Finset.mem_filter]
    exact ⟨hDQ, (hDmod D hDQ).trans (Nat.ModEq.dvd_dist hmodEq)⟩

/-- Fibrewise rough-divisor bound for the complete off-diagonal family.
The hypotheses `hFPow` and `hPrimeCount` are deliberately stated on the
literal cleared numerator so later scale estimates can be inserted without
changing this finite combinatorial layer. -/
theorem offDiagonalModulusTuples_card_le
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ) {z L P : ℕ}
    (hz : 1 < z)
    (hDmod : ∀ D ∈ Q, D ∣ modulus D)
    (hQrough : ∀ D ∈ Q, IsZRough z D)
    (hUcop : ∀ D ∈ Q, ∀ u ∈ U, u.Coprime (modulus D))
    (hFPow : ∀ s ∈ nonzeroNumeratorTuples A U,
      Nat.dist (reciprocalNumerator A s)
          (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) <
        z ^ (L + 1))
    (hPrimeCount : ∀ s ∈ nonzeroNumeratorTuples A U,
      (Nat.dist (reciprocalNumerator A s)
          (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)).primeFactors.card + 1 ≤ P) :
    (offDiagonalModulusTuples Q modulus A U).card ≤
      U.card ^ Fintype.card ι * P ^ L := by
  classical
  let target : Finset (Σ _s : ι → ℕ, ℕ) :=
    (nonzeroNumeratorTuples A U).sigma fun s => dividingModuli Q A s
  have hmaps :
      ((offDiagonalModulusTuples Q modulus A U :
          Finset (Σ _D : ℕ, ι → ℕ)) :
        Set (Σ _D : ℕ, ι → ℕ)).MapsTo
        (fun x => ⟨x.2, x.1⟩) (target : Set (Σ _s : ι → ℕ, ℕ)) := by
    simpa [target] using
      offDiagonalModulusTuple_mapsTo_tupleFibres Q modulus A U hDmod hUcop
  have hsourceTarget : (offDiagonalModulusTuples Q modulus A U).card ≤
      target.card :=
    Finset.card_le_card_of_injOn _ hmaps swapModulusTuple_injective.injOn
  have hfibre : ∀ s ∈ nonzeroNumeratorTuples A U,
      (dividingModuli Q A s).card ≤ P ^ L := by
    intro s hs
    let F := Nat.dist (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)
    have hF : F ≠ 0 := by
      intro hzero
      have hsne : reciprocalNumerator A s ≠
          reciprocalNumerator ((Finset.univ : Finset ι) \ A) s := by
        exact (Finset.mem_filter.mp hs).2
      apply hsne
      exact Nat.eq_of_dist_eq_zero hzero
    have hrough : ∀ D ∈ dividingModuli Q A s, IsZRough z D := by
      intro D hD
      exact hQrough D (Finset.mem_filter.mp hD).1
    have hdvd : ∀ D ∈ dividingModuli Q A s, D ∣ F := by
      intro D hD
      exact (Finset.mem_filter.mp hD).2
    exact (roughDivisorFamily_card_le hz hF (by simpa [F] using hFPow s hs)
      (dividingModuli Q A s) hrough hdvd).trans
        (Nat.pow_le_pow_left (by simpa [F] using hPrimeCount s hs) L)
  calc
    (offDiagonalModulusTuples Q modulus A U).card ≤ target.card :=
      hsourceTarget
    _ = ∑ s ∈ nonzeroNumeratorTuples A U,
        (dividingModuli Q A s).card := by simp [target]
    _ ≤ ∑ _s ∈ nonzeroNumeratorTuples A U, P ^ L := by
      exact Finset.sum_le_sum hfibre
    _ = (nonzeroNumeratorTuples A U).card * P ^ L := by simp
    _ ≤ U.card ^ Fintype.card ι * P ^ L := by
      apply Nat.mul_le_mul_right
      have hsub : nonzeroNumeratorTuples A U ⊆
          Fintype.piFinset (fun _ : ι => U) := by
        intro s hs
        rw [nonzeroNumeratorTuples, Finset.mem_filter] at hs
        exact hs.1
      exact (Finset.card_le_card hsub).trans_eq (by simp)
    _ = U.card ^ Fintype.card ι * P ^ L := rfl

/-- A cleared reciprocal numerator is bounded by the number of coordinates
times one full coordinate box.  The slightly wasteful extra factor of `T`
keeps the statement uniform when an erased product has fewer coordinates. -/
theorem reciprocalNumerator_le_card_mul_pow
    (A : Finset ι) (s : ι → ℕ) {T : ℕ} (hT : 1 ≤ T)
    (hs : ∀ i, s i ≤ T) :
    reciprocalNumerator A s ≤
      Fintype.card ι * T ^ Fintype.card ι := by
  unfold reciprocalNumerator
  calc
    ∑ i ∈ A, ∏ j ∈ (Finset.univ : Finset ι).erase i, s j ≤
        ∑ _i ∈ A, T ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ∏ j ∈ (Finset.univ : Finset ι).erase i, s j ≤
            ∏ _j ∈ (Finset.univ : Finset ι).erase i, T := by
          apply Finset.prod_le_prod
          · intro j hj
            omega
          · intro j hj
            exact hs j
        _ = T ^ ((Finset.univ : Finset ι).erase i).card := by simp
        _ ≤ T ^ Fintype.card ι := by
          apply Nat.pow_le_pow_right hT
          exact Finset.card_le_univ _
    _ = A.card * T ^ Fintype.card ι := by simp
    _ ≤ Fintype.card ι * T ^ Fintype.card ι := by
      gcongr
      exact Finset.card_le_univ A

theorem numeratorDistance_le_two_mul_card_mul_pow
    (A : Finset ι) (s : ι → ℕ) {T : ℕ} (hT : 1 ≤ T)
    (hs : ∀ i, s i ≤ T) :
    Nat.dist (reciprocalNumerator A s)
        (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) ≤
      2 * Fintype.card ι * T ^ Fintype.card ι := by
  have hA := reciprocalNumerator_le_card_mul_pow A s hT hs
  have hB := reciprocalNumerator_le_card_mul_pow
    ((Finset.univ : Finset ι) \ A) s hT hs
  calc
    Nat.dist (reciprocalNumerator A s)
        (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s) ≤
        reciprocalNumerator A s +
          reciprocalNumerator ((Finset.univ : Finset ι) \ A) s := by
      unfold Nat.dist
      omega
    _ ≤ Fintype.card ι * T ^ Fintype.card ι +
        Fintype.card ι * T ^ Fintype.card ι :=
      Nat.add_le_add hA hB
    _ = 2 * Fintype.card ι * T ^ Fintype.card ι := by ring

/-- Version of the off-diagonal family estimate with all numerator bounds
discharged by a coordinate box. -/
theorem offDiagonalModulusTuples_card_le_of_coordinate_bound
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ) {z T L D : ℕ}
    (hz : 1 < z) (hT : 1 ≤ T)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough z d)
    (hUcop : ∀ d ∈ Q, ∀ u ∈ U, u.Coprime (modulus d))
    (hUle : ∀ u ∈ U, u ≤ T)
    (hZPow : 2 * Fintype.card ι * T ^ Fintype.card ι <
      z ^ (L + 1))
    (hTwoPow : 2 * Fintype.card ι * T ^ Fintype.card ι <
      2 ^ (D + 1)) :
    (offDiagonalModulusTuples Q modulus A U).card ≤
      U.card ^ Fintype.card ι * (D + 1) ^ L := by
  apply offDiagonalModulusTuples_card_le Q modulus A U hz hDmod
    hQrough hUcop
  · intro s hs
    exact (numeratorDistance_le_two_mul_card_mul_pow A s hT
      (fun i => hUle (s i)
        (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hs).1 i))).trans_lt hZPow
  · intro s hs
    let F := Nat.dist (reciprocalNumerator A s)
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s)
    have hF : F ≠ 0 := by
      intro hzero
      exact (Finset.mem_filter.mp hs).2 (Nat.eq_of_dist_eq_zero hzero)
    have hFtwo : F < 2 ^ (D + 1) := by
      exact (numeratorDistance_le_two_mul_card_mul_pow A s hT
        (fun i => hUle (s i)
          (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hs).1 i))).trans_lt hTwoPow
    exact Nat.add_le_add_right
      (primeFactors_card_le_of_lt_two_pow hF hFtwo) 1

end ReciprocalMoment

end Erdos387
