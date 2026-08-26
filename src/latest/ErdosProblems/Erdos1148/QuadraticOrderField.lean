import ErdosProblems.Erdos1148.PellAutomorphisms

/-! # The rational quadratic algebra and its integral order generator -/

namespace Erdos1148.DukeArithmetic

abbrev QuadraticDiscrAlgebra (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

instance quadraticDiscrAlgebra_noRoot (d : ℤ) [hns : Fact (¬IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := by
  refine ⟨?_⟩
  intro r hr
  apply hns.out
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨r, ?_⟩
  simpa only [zero_mul, add_zero, pow_two] using hr.symm

lemma quadraticDiscrAlgebra_finrank (d : ℤ) :
    Module.finrank ℚ (QuadraticDiscrAlgebra d) = 2 := QuadraticAlgebra.finrank_eq_two _ _

noncomputable def quadraticOrderGenerator (d : ℤ) : QuadraticDiscrAlgebra d :=
  ⟨(d : ℚ) / 2, 1 / 2⟩

def quadraticOrder (d : ℤ) : Subring (QuadraticDiscrAlgebra d) :=
  Subring.closure {quadraticOrderGenerator d}

lemma quadraticOrderGenerator_mem (d : ℤ) : quadraticOrderGenerator d ∈ quadraticOrder d :=
  Subring.subset_closure (Set.mem_singleton _)

lemma int_combination_mem_quadraticOrder (d x y : ℤ) :
    (x : QuadraticDiscrAlgebra d) + (y : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d ∈
      quadraticOrder d :=
  (quadraticOrder d).add_mem (intCast_mem (quadraticOrder d) x)
    ((quadraticOrder d).mul_mem (intCast_mem (quadraticOrder d) y) (quadraticOrderGenerator_mem d))

end Erdos1148.DukeArithmetic
