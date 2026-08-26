import ErdosProblems.Erdos1123.LogarithmicBlocks
import ErdosProblems.Erdos1123.QuotientTransport

/-!
# Erdős problem 1123

Assuming CH, the Boolean algebras of sets of positive integers modulo ordinary
density zero and modulo logarithmic density zero are isomorphic. CH means
exactly `Cardinal.continuum = Cardinal.aleph 1`.

The proof passes to geometric finite blocks, proves countable extensions by
finite weighted splitting and a diagonal choice, and performs an `ω₁`
back-and-forth. Every extension and block-representation lemma is proved in the
supporting modules. No unconditional nonisomorphism is asserted.
-/

namespace Erdos1123

/-- **Erdős problem 1123, the CH implication.** The only additional set-theoretic
hypothesis is the Continuum Hypothesis, stated explicitly above. -/
theorem erdos1123_ch (hCH : ContinuumHypothesis) : Nonempty (B₁ ≃o B₂) := by
  obtain ⟨e⟩ := block_algebras_isomorphic_of_ch hCH ordinaryBlocks logarithmicBlocks
    ordinaryBlockStructure logarithmicBlockStructure
  let e₁ := ordinaryBlocks.algebraEquivOfNull ordinaryWeights ordinaryBlocks_null_iff
  let e₂ := logarithmicBlocks.algebraEquivOfNull logarithmicWeights logarithmicBlocks_null_iff
  exact ⟨e₁.symm.trans (e.trans e₂)⟩

/-- Under the continuum hypothesis, the ordinary and logarithmic density
quotient Boolean algebras are order-isomorphic. -/
theorem erdos_1123
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    Nonempty (B₁ ≃o B₂) :=
  erdos1123_ch hCH

end Erdos1123
