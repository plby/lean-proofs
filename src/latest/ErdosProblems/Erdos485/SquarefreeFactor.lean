import Mathlib

/-!
# Squarefree cofactors in a unique factorization monoid

This file supplies the elementary factorization step used in the proof of
Erdős Problem 485.  It is deliberately stated for an arbitrary commutative
unique factorization monoid with zero, so it applies in particular to
iterated polynomial rings over `ℂ`.
-/

namespace Erdos485

open UniqueFactorizationMonoid

section Multiset

variable {α : Type*}

/-- Every multiset is the sum of twice another multiset and a multiset with
no repetitions.  This is the parity decomposition of its multiplicities. -/
private theorem multiset_exists_twice_add_nodup (s : Multiset α) :
    ∃ t u : Multiset α, s = 2 • t + u ∧ u.Nodup := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      exact ⟨0, 0, by simp, Multiset.nodup_zero⟩
  | @cons a s ih =>
      obtain ⟨t, u, hstu, hu⟩ := ih
      by_cases hau : a ∈ u
      · refine ⟨a ::ₘ t, u.erase a, ?_, hu.erase _⟩
        rw [hstu]
        have hua : a ::ₘ u.erase a = u := Multiset.cons_erase hau
        calc
          a ::ₘ (2 • t + u) = a ::ₘ (2 • t + (a ::ₘ u.erase a)) := by rw [hua]
          _ = 2 • (a ::ₘ t) + u.erase a := by
            simp only [two_nsmul, Multiset.cons_add, Multiset.add_cons]
      · refine ⟨t, a ::ₘ u, ?_, Multiset.nodup_cons.mpr ⟨hau, hu⟩⟩
        rw [hstu]
        simp only [Multiset.add_cons]

end Multiset

section UFM

variable {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

/-- A nonzero element of a commutative unique factorization monoid is,
up to a unit, a square times a squarefree element.  The squarefree cofactor
is also exhibited as a divisor of the original element.

The last field is the useful ``multiplicity one'' form of squarefreeness:
if an irreducible `p` is split off from `h`, it cannot divide the remaining
cofactor. -/
theorem exists_sq_mul_squarefree_factor (F : R) (hF : F ≠ 0) :
    ∃ A H : R,
      Associated F (A ^ 2 * H) ∧
      Squarefree H ∧
      H ∣ F ∧
      ∀ ⦃p K : R⦄, Irreducible p → H = p * K → ¬p ∣ K := by
  let _ : Nontrivial R := nontrivial_of_ne F 0 hF
  let s := normalizedFactors F
  obtain ⟨t, u, hstu, hu⟩ := multiset_exists_twice_add_nodup s
  let A : R := t.prod
  let H : R := u.prod
  have hsirr : ∀ p ∈ s, Irreducible p := fun p hp =>
    irreducible_of_normalized_factor p hp
  have hsnorm : ∀ p ∈ s, normalize p = p := fun p hp =>
    normalize_normalized_factor p hp
  have hu_le : u ≤ s := by
    rw [hstu]
    exact Multiset.le_add_left _ _
  have huirr : ∀ p ∈ u, Irreducible p := fun p hp =>
    hsirr p (Multiset.mem_of_le hu_le hp)
  have hunorm : ∀ p ∈ u, normalize p = p := fun p hp =>
    hsnorm p (Multiset.mem_of_le hu_le hp)
  have hH0 : H ≠ 0 := by
    exact Multiset.prod_ne_zero fun hp => (huirr 0 hp).ne_zero rfl
  have hHfactors : normalizedFactors H = u := by
    dsimp [H]
    rw [normalizedFactors_prod_eq u huirr]
    calc
      u.map normalize = u.map id := Multiset.map_congr rfl hunorm
      _ = u := Multiset.map_id u
  have hHsq : Squarefree H := by
    rw [squarefree_iff_nodup_normalizedFactors hH0, hHfactors]
    exact hu
  have hprod : s.prod = A ^ 2 * H := by
    rw [hstu]
    simp only [Multiset.prod_add, Multiset.prod_nsmul]
    simp [A, H, pow_two]
  have hassoc : Associated F (A ^ 2 * H) := by
    rw [← hprod]
    exact (prod_normalizedFactors hF).symm
  have hHdF : H ∣ F := by
    exact (dvd_mul_left H (A ^ 2)).trans hassoc.dvd'
  refine ⟨A, H, hassoc, hHsq, hHdF, ?_⟩
  intro p K hp hHK hpK
  exact hp.not_isUnit (hHsq p <| hHK.symm ▸ mul_dvd_mul_left p hpK)

end UFM

section Consequences

variable {R : Type*} [CommMonoidWithZero R]

/-- An irreducible factor occurs at most once in a squarefree element: after
it is split off, it cannot divide the remaining cofactor. -/
theorem Squarefree.irreducible_not_dvd_cofactor {H p K : R}
    (hH : Squarefree H) (hp : Irreducible p) (hHK : H = p * K) :
    ¬p ∣ K := by
  intro hpK
  exact hp.not_isUnit (hH p <| hHK.symm ▸ mul_dvd_mul_left p hpK)

/-- Valuation form of multiplicity one: an irreducible divisor of a
squarefree element has extended multiplicity exactly one. -/
theorem Squarefree.emultiplicity_eq_one_of_irreducible_dvd {H p : R}
    (hH : Squarefree H) (hp : Irreducible p) (hpH : p ∣ H) :
    emultiplicity p H = 1 := by
  apply le_antisymm
  · exact ((squarefree_iff_emultiplicity_le_one H).mp hH p).resolve_right hp.not_isUnit
  · exact Order.one_le_iff_pos.mpr (emultiplicity_pos_of_dvd hpH)

/-- Nondivisibility descends from an element to any of its factors.  In
particular this transfers the absence of a polynomial variable from `F` to
the squarefree cofactor supplied by `exists_sq_mul_squarefree_factor`. -/
theorem not_dvd_of_dvd_of_not_dvd {F H q : R} (hHF : H ∣ F) (hqF : ¬q ∣ F) :
    ¬q ∣ H := fun hqH => hqF (hqH.trans hHF)

/-- Simultaneous version of `not_dvd_of_dvd_of_not_dvd`, convenient for the
two distinguished variables in the bivariate reduction. -/
theorem pair_not_dvd_of_dvd_of_pair_not_dvd {F H y z : R} (hHF : H ∣ F)
    (hyF : ¬y ∣ F) (hzF : ¬z ∣ F) :
    ¬y ∣ H ∧ ¬z ∣ H :=
  ⟨not_dvd_of_dvd_of_not_dvd hHF hyF, not_dvd_of_dvd_of_not_dvd hHF hzF⟩

end Consequences

end Erdos485
