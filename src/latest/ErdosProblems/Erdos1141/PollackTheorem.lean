import ErdosProblems.Erdos1141.ResiduePrimeTheorem

namespace Pollack17

/--
Pollack, *Bounds for the First Several Prime Character Nonresidues*, Theorem 1.3.
-/
theorem theorem_1_3
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ,
      m > m0 →
      ∀ χ : DirichletCharacter ℂ m,
        MulChar.IsQuadratic χ →
          Real.rpow (Real.log (m : ℝ)) A ≤
            ((residuePrimesUpTo m χ ε).card : ℝ) :=
  residue_prime_count ε A hε hA

/-- info: 'Pollack17.theorem_1_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theorem_1_3

end Pollack17
