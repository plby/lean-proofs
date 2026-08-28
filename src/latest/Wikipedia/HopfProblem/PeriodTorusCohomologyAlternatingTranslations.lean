import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations
import Wikipedia.HopfProblem.SingularCohomologyFreeHomotopy

/-!
# Actual integral cohomology is unchanged by period-torus translations

The existing straight-segment homotopies induce homotopies of the native
singular cochain pullbacks, hence equal pullbacks on actual integral
singular cohomology in every degree. In particular, every elliptic affine
biholomorphism has exactly the same cohomological action as its linear
part, for every integral twist.

These statements use homotopy invariance directly and require no
freeness, projectivity, or universal-coefficient hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open PeriodTorusHigherHomology SingularCohomologyFree

/-- Translation along an actual path acts identically on native integral cohomology. -/
theorem rightTranslation_singularCohomologyPullback_of_path
    {G : Type} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    {a : G} (p : Path (0 : G) a) (n : ℕ) :
    singularCohomologyPullback (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_singularCohomologyPullback (rightTranslationHomotopyAlong p) n,
    singularCohomologyPullback_id]

/-- Every translation of a path-connected topological additive group has
identity pullback on actual integral singular cohomology in every degree. -/
@[simp] theorem rightTranslation_singularCohomologyPullback
    {G : Type} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (a : G) (n : ℕ) :
    singularCohomologyPullback (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularCohomologyPullback_of_path (PathConnectedSpace.somePath 0 a) n

/-- The projected straight segment proves translation invariance on the
actual complex quotient without a discrete-lattice hypothesis. -/
theorem quotientTranslation_singularCohomologyPullback (L : Submodule ℤ ComplexPlane₂)
    (a : ComplexPlane₂ ⧸ L) (n : ℕ) :
    singularCohomologyPullback (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularCohomologyPullback_of_path (quotientTranslationPath L a) n

end Wikipedia.HopfProblem.PeriodTorusCohomology

namespace Wikipedia.HopfProblem.PeriodDomain

open SingularCohomologyFree

/-- The actual holomorphic torus translation has identity pullback on
native integral singular cohomology in every degree. -/
@[simp] theorem translation_singularCohomologyPullback
    (p : PeriodDomain) (a : p.Torus) (n : ℕ) :
    singularCohomologyPullback
        ((Elliptic.torusTranslation p a).toHomeomorph : C(p.Torus, p.Torus)) n =
      LinearMap.id := by
  rw [← homotopy_singularCohomologyPullback (p.translationHomotopy a) n,
    singularCohomologyPullback_id]

end Wikipedia.HopfProblem.PeriodDomain

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open SingularCohomologyFree

/-- Every translation of a full-period torus acts identically on its
actual integral cohomology in every degree. -/
@[simp] theorem translation_singularCohomologyPullback
    (p : FullPeriodMatrix) (a : p.Torus) (n : ℕ) :
    singularCohomologyPullback (p.translationContinuousMap a) n = LinearMap.id := by
  rw [← homotopy_singularCohomologyPullback (p.translationHomotopy a) n,
    singularCohomologyPullback_id]

end Wikipedia.HopfProblem.FullPeriodMatrix

namespace Wikipedia.HopfProblem.Elliptic

open SingularCohomologyFree

/-- For every integral twist, the literal affine and linear elliptic
biholomorphisms have the same native cohomology pullback in every degree. -/
theorem affineBiholomorph_singularCohomologyPullback (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (n : ℕ) :
    singularCohomologyPullback
        ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) n =
      singularCohomologyPullback
        ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) n :=
  (homotopy_singularCohomologyPullback (affineBiholomorphHomotopy j p v) n).symm

end Wikipedia.HopfProblem.Elliptic
