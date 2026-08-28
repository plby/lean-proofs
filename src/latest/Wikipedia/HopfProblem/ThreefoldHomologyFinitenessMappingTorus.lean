import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebra

/-!
# Integral finiteness and dimension bound for actual four-torus mapping tori

Every map used here is the original fibre inclusion or the genuine signed
Wang boundary of the actual two-arc Mayer--Vietoris sequence.  The known
integral homology of the real lattice four-torus therefore gives finite
generation in every degree and vanishing above degree five, for an
arbitrary actual homeomorphism of that torus.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorus

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldHomologyFinitenessAlgebra

/-- Exactness at the actual positive-degree mapping-torus homology, as a
statement about the literal original fibre and Wang maps. -/
theorem fibre_wang_exact (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Function.Exact (fibreHomologyMap f (n + 1)) (wangBoundary f n) :=
  LinearMap.exact_iff.mpr (wang_exact_at_mappingTorus f n).symm

/-- All actual integral homology groups of any four-torus mapping torus
are finitely generated, with no condition on the monodromy action. -/
theorem homology_finite (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (MappingTorus.Torus f) n) := by
  cases n with
  | zero =>
    let := realTorus_homology_finite 0
    exact Module.Finite.of_surjective (fibreHomologyMap f 0)
      (fibreHomologyMap_zero_surjective f)
  | succ n =>
    let := realTorus_homology_finite (n + 1)
    let := realTorus_homology_finite n
    exact finite_of_exact (fibreHomologyMap f (n + 1)) (wangBoundary f n)
      (fibre_wang_exact f n)

/-- The degree bound follows from the vanishing of both actual torus terms
adjacent to mapping-torus homology in the Wang sequence. -/
theorem homology_subsingleton_of_lt (f : RealTorus₄ ≃ₜ RealTorus₄)
    {n : ℕ} (hn : 5 < n) : Subsingleton (SingularHomology (MappingTorus.Torus f) n) := by
  cases n with
  | zero => omega
  | succ n =>
    let := realTorus_homology_subsingleton_of_lt (n := n + 1) (by omega)
    let := realTorus_homology_subsingleton_of_lt (n := n) (by omega)
    exact subsingleton_of_exact (fibreHomologyMap f (n + 1)) (wangBoundary f n)
      (fibre_wang_exact f n)

/-- The actual integral homology object is zero above degree five. -/
theorem homology_isZero_of_lt (f : RealTorus₄ ≃ₜ RealTorus₄)
    {n : ℕ} (hn : 5 < n) : IsZero (SingularHomology (MappingTorus.Torus f) n) := by
  let := homology_subsingleton_of_lt f hn
  exact ModuleCat.isZero_of_subsingleton _

theorem homology_eq_zero_of_lt (f : RealTorus₄ ≃ₜ RealTorus₄)
    {n : ℕ} (hn : 5 < n) (x : SingularHomology (MappingTorus.Torus f) n) : x = 0 :=
  (homology_subsingleton_of_lt f hn).elim x 0

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorus
