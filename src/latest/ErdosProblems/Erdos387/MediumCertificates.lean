/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.TupleCoordinateCRT

/-!
# Certificate reduction for the medium-component error

Every medium error is, in particular, a large-component error at the lower
threshold `medium`.  This gives an immediate independent tuple-certificate
cover.  We also retain the distinguished coordinate and its upper bound,
which are the data needed to pass from the full tuple CRT phase to the
incomplete inverse sum of Proposition 6.3.
-/

namespace Erdos387

namespace CoverBPZ

theorem refinedMediumErrors_subset_largeErrorsAtMedium
    {B K X z medium large : ℕ} (S : BPZSection6Input B K) :
    RefinedMediumErrors S X z medium large ⊆
      RefinedLargeErrors S X z medium := by
  classical
  intro n hn
  rw [RefinedMediumErrors, Finset.mem_filter] at hn
  rw [RefinedLargeErrors, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  obtain ⟨hnk, hprog, d, E, hnd, hdn, hvalue, i, hi, _hiLarge⟩ := hn.2
  exact ⟨hnk, hprog, d, E, hnd, hdn, hvalue, i, hi⟩

/-- The same independent certificate cover used for a large error applies
to medium errors at their lower component threshold. -/
theorem refinedMediumErrors_subset_certificateClasses
    {B K X z medium large : ℕ} (S : BPZSection6Input B K)
    (hz : 2 * S.k ≤ z) :
    RefinedMediumErrors S X z medium large ⊆
      (RefinedLargeTupleCertificates S X medium).biUnion
        (fun C => C.classIoc (X / 2) X) :=
  (refinedMediumErrors_subset_largeErrorsAtMedium S).trans
    (refinedLargeErrors_subset_certificateClasses S hz)

/-- Coarse reciprocal-modulus union bound.  Later Fourier estimates replace
the endpoint term implicit in this inequality, but the independent index set
and its main reciprocal term are already exact here. -/
theorem refinedMediumErrors_card_le_certificateSum
    {B K X z medium large : ℕ} (S : BPZSection6Input B K)
    (hz : 2 * S.k ≤ z) :
    ((RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ C ∈ RefinedLargeTupleCertificates S X medium,
        (((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * C.val.value : ℕ) + 2) := by
  classical
  have hcard := Finset.card_le_card
    (refinedMediumErrors_subset_largeErrorsAtMedium
      (X := X) (z := z) (medium := medium) (large := large) S)
  have hreal :
      ((RefinedMediumErrors S X z medium large).card : ℝ) ≤
        ((RefinedLargeErrors S X z medium).card : ℝ) := by
    exact_mod_cast hcard
  exact hreal.trans
    (refinedLargeErrors_card_le_certificateSum S hz)

/-- Distinguished-coordinate geometry for a medium error.  The complementary
product `D` lies below `X / medium`, while the near-divisor condition and the
upper bound on the distinguished factor give the matching lower product
inequality used in the dyadic decomposition. -/
theorem mediumError_coordinate_data
    {B K X z medium large n : ℕ} (S : BPZSection6Input B K)
    (hnError : n ∈ RefinedMediumErrors S X z medium large) :
    ∃ (hn : S.k < n)
      (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
      (i : Fin S.k)
      (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
      (D : ℕ),
      D = E.otherValue i ∧
      E.factor i * D = E.value ∧
      medium < E.factor i ∧ E.factor i ≤ large ∧
      n < B * E.value ∧ E.value ≤ n ∧
      0 < D ∧
      (medium + 1) * D ≤ X ∧
      X / 2 < B * large * D := by
  classical
  have hnData := hnError
  rw [RefinedMediumErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨⟨hnIoc, _hn, _hnRefined⟩, _hrough⟩,
    hn', hprog', d, E, hnd, hdn, hvalue, i, hiMedium, hiLarge⟩ := hnData
  let D := E.otherValue i
  have hfactorPos : 0 < E.factor i := by omega
  have hDPos : 0 < D := by
    exact E.otherValue_pos (fun j => by
      have hjDvd : E.factor j ∣ n.choose S.k :=
        (E.divides j).trans
          (coverQuotient_dvd_choose
            (S.toCoverFactorization hn' hprog') j.isLt)
      exact Nat.pos_of_dvd_of_pos hjDvd (Nat.choose_pos hn'.le)) i
  have hfactorD : E.factor i * D = E.value := E.factor_mul_otherValue i
  have hvalueX : E.value ≤ X := by
    rw [hvalue]
    exact hdn.trans (Finset.mem_Ioc.mp hnIoc).2
  have hmediumD : (medium + 1) * D ≤ X := by
    calc
      (medium + 1) * D ≤ E.factor i * D := by gcongr; omega
      _ = E.value := hfactorD
      _ ≤ X := hvalueX
  have hlower : X / 2 < B * large * D := by
    calc
      X / 2 < n := (Finset.mem_Ioc.mp hnIoc).1
      _ < B * E.value := by simpa [hvalue] using hnd
      _ = B * (E.factor i * D) := by rw [hfactorD]
      _ ≤ B * (large * D) := by gcongr
      _ = B * large * D := by ring
  exact ⟨hn', hprog', i, E, D, rfl, hfactorD,
    hiMedium, hiLarge, by simpa [hvalue] using hnd,
    by simpa [hvalue] using hdn, hDPos, hmediumD, hlower⟩

end CoverBPZ

end Erdos387
