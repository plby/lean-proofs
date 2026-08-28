import Wikipedia.NoExoticSixSphere.RelativeCoefficientVanishing
import Wikipedia.NoExoticSixSphere.ModTwoLocalClass

/-!
# Actual local finite-coefficient homology vanishes above the manifold dimension

The top integral local group is marked by the original chart computation.
Its torsion-freeness handles the first degree above dimension; the other
degrees use the two adjacent integral vanishing results. This proves
vanishing for the native finite-coefficient local groups, not for groups
assigned by an expected dimension.
-/

noncomputable section

namespace NoExoticSixSphere.LocalCoefficientVanishing

open RelativeSingularHomology RelativeCoefficients

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]

include E

/-- Every actual local group with nonzero finite-cyclic modulus vanishes above dimension. -/
theorem above_subsingleton (p : ℕ) (hp : p ≠ 0) (x : M) (k : ℕ) (hk : n + 3 < k) :
    Subsingleton (ModHomology p ({x}ᶜ : Set M) k) := by
  cases k with
  | zero => omega
  | succ j =>
    let := chartLocalHomology_subsingleton (n + 1) (chartAt E x) x
      (mem_chart_source E x) j (by omega) (by omega)
    apply modHomology_subsingleton_of_mul_injective p hp ({x}ᶜ : Set M) j
    by_cases hj : j = n + 3
    · subst j
      exact multiplication_injective_of_int_equiv p hp ({x}ᶜ : Set M) (n + 3)
        (chartLocalTopEquiv (n + 1) (chartAt E x) x (mem_chart_source E x))
    · have hprev : Subsingleton (LocalHomology x j) := by
        cases j with
        | zero => omega
        | succ q =>
          exact chartLocalHomology_subsingleton (n + 1) (chartAt E x) x
            (mem_chart_source E x) q (by omega) (by omega)
      exact fun a b _ => hprev.elim a b

end NoExoticSixSphere.LocalCoefficientVanishing
