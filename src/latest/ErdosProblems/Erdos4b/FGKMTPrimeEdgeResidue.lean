/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeTupleEdges
import ErdosProblems.Erdos4b.FGKMTNaturalResidueSieve

/-! # Each original prime edge lies in its translation residue class -/

namespace Erdos4b.FGKMT

noncomputable section

theorem SourceProbabilityData.primeTupleEdge_residue {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S Q : Finset ℕ} {a : ResidueAssignment S}
    {p q : ℕ} {n : ℤ} (hq : q ∈ D.primeTupleEdge S Q a p n) :
    integerResidueIndex p (q : ℤ) = integerResidueIndex p n := by
  obtain ⟨i, hi⟩ := (D.mem_residueTuple p n q).mp ((D.mem_primeTupleEdge S Q a p n q).mp hq).2.1
  unfold integerResidueIndex
  rw [← hi, Int.add_mul_emod_self_right]

end

end Erdos4b.FGKMT
