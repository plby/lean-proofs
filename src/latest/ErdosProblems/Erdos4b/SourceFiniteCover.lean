/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceResidueFamily
import ErdosProblems.Erdos4b.SourceResidualExceptions

/-!
# Finite global cover from fibre probabilities and the three exception budgets

All premises are explicit finite arithmetic, probability or cardinality
conditions. The dyadic construction supplies them after choosing profiles
with a sufficiently large variational ratio.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_sourceSurvivorCoverData_of_fibres
    {U y z B M H : ℕ} (hy : 2 ≤ y) (hz : 2 ≤ z) (hU : U = z * B)
    (E : Finset ℕ) (hE : E = residualEvenCofactors 0 M) (Q : ℕ → Finset ℕ) (R : Finset ℕ)
    (hprimeQ : ∀ m ∈ E, ∀ q ∈ Q m, q.Prime) (hprimeR : ∀ q ∈ R, q.Prime)
    (hsupportQ : ∀ m ∈ E, ∀ q ∈ Q m, z < q) (hsupportR : ∀ q ∈ R, z < q)
    (hdisjointQ : ∀ m ∈ E, ∀ n ∈ E, m ≠ n → Disjoint (Q m) (Q n))
    (hdisjointR : ∀ m ∈ E, Disjoint (Q m) R)
    (μ : ∀ _m q : ℕ, Fin q → ℝ)
    (hμ : ∀ m ∈ E, ∀ q ∈ Q m, ∀ b, 0 ≤ μ m q b)
    (hsum : ∀ m ∈ E, ∀ q ∈ Q m, ∑ b, μ m q b = 1) (t : ℝ)
    (hcoverage : ∀ m, ∀ hm : m ∈ E, ∀ p ∈ residualPrimeFiber U y z m, H ≤ p →
      t ≤ ∑ q : Q m, μ m q.val
        ⟨p % q.val, Nat.mod_lt p (hprimeQ m hm q.val q.property).pos⟩)
    (hcapacity : (smoothResidualException U y).card +
      ((∑ m ∈ residualEvenCofactors M B, (residualPrimeFiber U y z m).card : ℕ) : ℝ) +
      ((∑ m ∈ E, (residualPrimeFiberBelow U y z m H).card : ℕ) : ℝ) +
      ((∑ m ∈ E, (residualPrimeFiber U y z m).card : ℕ) : ℝ) * Real.exp (-t) < (R.card : ℝ) + 1) :
    ∃ data : SurvivorCoverData U y z,
      data.measurePrimes = E.biUnion Q ∧ data.freshPrimes = R := by
  classical
  have hq : ∀ m ∈ E, ∀ q ∈ Q m, 0 < q := fun m hm q hqm ↦ (hprimeQ m hm q hqm).pos
  have hprimeP : ∀ q ∈ E.biUnion Q, q.Prime := by
    intro q hqP
    obtain ⟨m, hm, hqm⟩ := Finset.mem_biUnion.mp hqP
    exact hprimeQ m hm q hqm
  have hsupportP : ∀ q ∈ E.biUnion Q, z < q := by
    intro q hqP
    obtain ⟨m, hm, hqm⟩ := Finset.mem_biUnion.mp hqP
    exact hsupportQ m hm q hqm
  have hdisjoint : Disjoint (E.biUnion Q) R := by
    rw [Finset.disjoint_left]
    intro q hqP hqR
    obtain ⟨m, hm, hqm⟩ := Finset.mem_biUnion.mp hqP
    exact Finset.disjoint_left.mp (hdisjointR m hm) hqm hqR
  have hsumpos : ∀ q : E.biUnion Q, 0 < ∑ b, sourceCombinedResidueWeight E Q μ q b := by
    intro q
    rw [sum_sourceCombinedResidueWeight hq hsum]
    norm_num
  apply exists_survivorCoverData_of_rawWeights_and_good_coverage
    (E.biUnion Q) R (sourceResidualBadSet U y z B M H)
    hprimeP hprimeR hsupportP hsupportR hdisjoint (sourceCombinedResidueWeight E Q μ)
    (sourceCombinedResidueWeight_nonneg hμ) hsumpos t (sourceResidualBadSet_subset U y z B M H)
  · intro i hi hgood
    obtain ⟨m, hm, p, hp, hH, hip⟩ := good_initialSurvivor_small_residual_representation
      hy hz hU hi hgood
    have hmE : m ∈ E := by rwa [hE]
    rw [hip]
    exact (hcoverage m hmE p hp hH).trans
      (sourceFamilyCoverage_ge_fibre hdisjointQ hq hμ hsum hmE p)
  · have hb : ((sourceResidualBadSet U y z B M H).card : ℝ) ≤
        (smoothResidualException U y).card +
          ((∑ m ∈ residualEvenCofactors M B, (residualPrimeFiber U y z m).card : ℕ) : ℝ) +
          ((∑ m ∈ E, (residualPrimeFiberBelow U y z m H).card : ℕ) : ℝ) := by
      rw [hE]
      exact_mod_cast card_sourceResidualBadSet_le U y z B M H
    have hg : ((initialSieveSurvivors U y z \ sourceResidualBadSet U y z B M H).card : ℝ) ≤
        ((∑ m ∈ E, (residualPrimeFiber U y z m).card : ℕ) : ℝ) := by
      rw [hE]
      exact_mod_cast card_good_initialSurvivors_le_small_fibres (M := M) (H := H) hy hz hU
    exact (add_le_add hb (mul_le_mul_of_nonneg_right hg (Real.exp_pos (-t)).le)).trans_lt hcapacity

end

end Erdos4b
