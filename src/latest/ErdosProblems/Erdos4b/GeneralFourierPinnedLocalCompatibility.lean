/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedRoots
import ErdosProblems.Erdos4b.GeneralFourierArithmeticEuler

/-!
# A reduced pinned residue exists exactly for the allowed local graph states

The first and companion families each use at most one index at a prime.
Their simultaneous affine equations are solvable precisely when the
companion slope is nonzero and each cross pair is a collision edge.
When no equation is present, the reduced residue `1` is available.
-/

namespace Erdos4b

noncomputable section

def PinnedLocalDivisorSolvable {K : ℕ} (h : Fin K) (w m p₀ p : ℕ)
    (D E : PinnedShiftIndex h → ℕ) : Prop :=
  ∃ q : ZMod p, q ≠ 0 ∧
    (∀ i, p ∣ D i → (p₀ : ZMod p) + pinnedIndexSlope h w p i * q = 0) ∧
    (∀ i, p ∣ E i → (m : ZMod p) * ((p₀ : ZMod p) + pinnedIndexSlope h w p i * q) = 1)

theorem prime_divisor_unique_of_pairwise_coprime
    {ι : Type*} {D : ι → ℕ} {p : ℕ} (hp : p.Prime)
    (hcop : ∀ {i j}, i ≠ j → (D i).Coprime (D j))
    {i j : ι} (hi : p ∣ D i) (hj : p ∣ D j) : i = j := by
  by_contra hij
  exact hp.not_dvd_one (by simpa only [hcop hij] using Nat.dvd_gcd hi hj)

theorem pinnedLocalDivisorSolvable_iff_graph
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (D E : PinnedShiftIndex h → ℕ)
    (hD : ∀ {i j}, i ≠ j → (D i).Coprime (D j))
    (hE : ∀ {i j}, i ≠ j → (E i).Coprime (E j))
    (hfirst : (∃ i, p ∣ D i) → ¬p ∣ p₀)
    (hcompanion : (∃ i, p ∣ E i) → (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    PinnedLocalDivisorSolvable h w m p₀ p D E ↔
      (∀ i, p ∣ E i → ¬p ∣ m) ∧
        (∀ i j, p ∣ D i → p ∣ E j → (i, j) ∈ pinnedIndexFourierEdges h m p₀ p) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨q, hq, hqD, hqE⟩
    have hpm (j : PinnedShiftIndex h) (hj : p ∣ E j) : ¬p ∣ m := by
      intro hdiv
      have hm0 := (ZMod.natCast_eq_zero_iff m p).mpr hdiv
      have he := hqE j hj
      rw [hm0, zero_mul] at he
      exact zero_ne_one he
    refine ⟨hpm, ?_⟩
    intro i j hi hj
    apply (pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp (hpm j hj) i j).mpr
    exact ((pinnedFirstRoot_iff_affine_zero h hp hKw hwp i q).mpr (hqD i hi)).symm.trans
      ((pinnedCompanionRoot_iff_affine_one h hp hKw hwp (hpm j hj) j q).mpr (hqE j hj))
  · rintro ⟨hpm, hedges⟩
    by_cases hactiveD : ∃ i, p ∣ D i
    · obtain ⟨i, hi⟩ := hactiveD
      refine ⟨pinnedFirstRoot h w p₀ p i,
        pinnedFirstRoot_ne_zero h hp hKw hwp (hfirst ⟨i, hi⟩) i, ?_, ?_⟩
      · intro j hj
        have hji := prime_divisor_unique_of_pairwise_coprime hp hD hj hi
        subst j
        exact (pinnedFirstRoot_iff_affine_zero h hp hKw hwp i _).mp rfl
      · intro j hj
        apply (pinnedCompanionRoot_iff_affine_one h hp hKw hwp (hpm j hj) j _).mp
        exact (pinnedIndexFourierEdge_iff_roots_eq h hp hKw hwp (hpm j hj) i j).mp
          (hedges i j hi hj)
    · by_cases hactiveE : ∃ j, p ∣ E j
      · obtain ⟨j, hj⟩ := hactiveE
        refine ⟨pinnedCompanionRoot h w m p₀ p j,
          pinnedCompanionRoot_ne_zero h hp hKw hwp (hpm j hj) (hcompanion ⟨j, hj⟩) j,
          fun i hi ↦ (hactiveD ⟨i, hi⟩).elim, ?_⟩
        intro i hi
        have hij := prime_divisor_unique_of_pairwise_coprime hp hE hi hj
        subst i
        exact (pinnedCompanionRoot_iff_affine_one h hp hKw hwp (hpm j hj) j _).mp rfl
      · exact ⟨1, one_ne_zero, fun i hi ↦ (hactiveD ⟨i, hi⟩).elim,
          fun j hj ↦ (hactiveE ⟨j, hj⟩).elim⟩

theorem pinnedLocalDivisorSolvable_first_unique
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (D E : PinnedShiftIndex h → ℕ) (hpp₀ : ¬p ∣ p₀)
    (hsol : PinnedLocalDivisorSolvable h w m p₀ p D E)
    {i j : PinnedShiftIndex h} (hi : p ∣ D i) (hj : p ∣ D j) : i = j := by
  obtain ⟨q, hq, hD, hE⟩ := hsol
  apply pinnedFirstRoot_injective h hp hKw hwp hpp₀
  exact ((pinnedFirstRoot_iff_affine_zero h hp hKw hwp i q).mpr (hD i hi)).symm.trans
    ((pinnedFirstRoot_iff_affine_zero h hp hKw hwp j q).mpr (hD j hj))

theorem pinnedLocalDivisorSolvable_companion_unique
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (D E : PinnedShiftIndex h → ℕ)
    (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hsol : PinnedLocalDivisorSolvable h w m p₀ p D E)
    {i j : PinnedShiftIndex h} (hi : p ∣ E i) (hj : p ∣ E j) : i = j := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hD, hE⟩ := hsol
  have hpm : ¬p ∣ m := by
    intro hdiv
    have hm0 := (ZMod.natCast_eq_zero_iff m p).mpr hdiv
    have he := hE i hi
    rw [hm0, zero_mul] at he
    exact zero_ne_one he
  apply pinnedCompanionRoot_injective h hp hKw hwp hpm hnum
  exact ((pinnedCompanionRoot_iff_affine_one h hp hKw hwp hpm i q).mpr (hE i hi)).symm.trans
    ((pinnedCompanionRoot_iff_affine_one h hp hKw hwp hpm j q).mpr (hE j hj))

end

end Erdos4b
