/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveNormalization
import BoundedGaps.Maynard.ImprovedGPY.PreSieve

/-! # Positivity of the presieve density for an admissible tuple -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_preSieveCondition_of_admissible {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (Q : Finset ℕ)
    (hadm : BoundedGaps.IsAdmissible (Finset.univ.image h))
    (hQ : ∀ q ∈ Q, q.Prime) :
    ∃ n : ℤ, preSieveCondition (∏ q ∈ Q, q) (fun i => (h i : ℤ)) n := by
  classical
  obtain ⟨v, _hv, hcop⟩ := BoundedGaps.Maynard.exists_preSieveResidueClass hadm hQ
  refine ⟨v, ?_⟩
  unfold preSieveCondition
  apply Nat.Coprime.prod_left
  intro i _hi
  simpa only [← Nat.cast_add, Int.natAbs_natCast] using
    hcop (h i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem preSieveDensity_admissible_bounds {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (Q : Finset ℕ)
    (hadm : BoundedGaps.IsAdmissible (Finset.univ.image h))
    (hQ : ∀ q ∈ Q, q.Prime) :
    1 / (∏ q ∈ Q, (q : ℝ)) ≤ preSieveDensity (∏ q ∈ Q, q) (fun i => (h i : ℤ)) ∧
      0 < preSieveDensity (∏ q ∈ Q, q) (fun i => (h i : ℤ)) ∧
      preSieveDensity (∏ q ∈ Q, q) (fun i => (h i : ℤ)) ≤ 1 := by
  have hW : 0 < ∏ q ∈ Q, q := Finset.prod_pos fun q hq => (hQ q hq).pos
  obtain ⟨n, hn⟩ := exists_preSieveCondition_of_admissible h Q hadm hQ
  have hl := preSieveDensity_ge_inv_of_witness hW (fun i => (h i : ℤ)) hn
  refine ⟨?_, (by positivity : 0 < 1 / ((∏ q ∈ Q, q : ℕ) : ℝ)).trans_le hl,
    preSieveDensity_le_one hW _⟩
  simpa only [Nat.cast_prod] using hl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveDensity_admissible_bounds
