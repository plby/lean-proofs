import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequence

/-!
# The native cycles sequence after the actual obstruction group vanishes

When the stated genuine `Ext²(A,ZⁿK)` group is zero, exactness of the
proved native sequence makes the original edge map surjective. The
resulting short exact sequence retains all three original groups and
both original maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ) (n : ℕ) [Injective (K.X n)]
  [Subsingleton (Ext A (K.cycles n) 2)]

/-- Vanishing of the actual final obstruction group makes the original edge map surjective. -/
theorem cyclesEdgeMap_surjective : Function.Surjective (cyclesEdgeMap A K n) := by
  intro x
  exact (cycles_exact_edge_transgression A K n x).mp (Subsingleton.elim _ _)

instance cyclesEdgeMap_epi : Epi (cyclesEdgeMap A K n) :=
  (AddCommGrpCat.epi_iff_surjective (cyclesEdgeMap A K n)).mpr
    (cyclesEdgeMap_surjective A K n)

/-- The genuine short exact cycles sequence, with exactly the stated Ext vanishing input. -/
theorem cyclesFirstComplex_shortExact : (cyclesFirstComplex A K n).ShortExact where
  exact := cyclesFirstComplex_exact A K n
  mono_f := inferInstanceAs (Mono (cyclesFirstMap A K n))
  epi_g := cyclesEdgeMap_epi A K n

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
