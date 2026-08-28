import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultPairs
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGeometry
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFine

/-!
# Genuine acyclicity of the native torus smooth coefficient sheaves

The original compact quotient torus, with its unchanged charts, is a
finite-dimensional Hausdorff smooth real manifold. Actual partitions of
unity prove that its smooth-function sheaf is locally fine. The same
partition operators act diagonally on genuine smooth pairs, proving
their local fineness and positive-degree Ext cohomology vanishing.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open HolomorphicSheafCohomology

local notation "Iℝ₂" => modelWithCornersSelf ℝ ComplexPlane₂

variable (p : PeriodDomain)

/-- Actual complex scalar endomorphisms of the original smooth-function sheaf. -/
abbrev smoothScalarEnd : ℂ →+* End (smoothSheaf p) :=
  SmoothFunctions.scalarEnd Iℝ₂ p.Torus

/-- The same complex scalars act diagonally on the two genuine coefficients. -/
def pairScalarEnd : ℂ →+* End (pairSheaf p) :=
  (diagonalRingHom p).comp (smoothScalarEnd p)

@[simp] theorem smoothScalarEnd_eq_smul (c : ℂ) (U : Opens p.Torus)
    (s : SmoothSection p U) :
    (smoothScalarEnd p c).asHom.hom.app (op U) s = c • s := rfl

@[simp] theorem pairScalarEnd_eq_smul (c : ℂ) (U : Opens p.Torus)
    (s : PairSection p U) :
    (pairScalarEnd p c).asHom.hom.app (op U) s = c • s := rfl

/-- Diagonal action preserves actual vanishing on every smaller open set. -/
theorem diagonal_isZeroOn {f : smoothSheaf p ⟶ smoothSheaf p} {U : Opens p.Torus}
    (hf : IsZeroOn f U) : IsZeroOn (diagonal p f) U := by
  intro V hVU
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (f.hom.app (op V) s.1, f.hom.app (op V) s.2) = 0
  rw [hf V hVU]
  rfl

/-- The actual locally finite supports and partition operators act on
both smooth coefficients, preserving their local finite-sum identity. -/
def pairDecomposition {ι : Type} {U : ι → Opens p.Torus}
    (d : LocallyFiniteDecomposition (smoothSheaf p) U) :
    LocallyFiniteDecomposition (pairSheaf p) U where
  operator i := diagonal p (d.operator i)
  support := d.support
  support_closed := d.support_closed
  subordinate := d.subordinate
  zeroOutside i := diagonal_isZeroOn p (d.zeroOutside i)
  locallyFinite := d.locallyFinite
  localTotal V s hs := by
    have h := diagonal_isZeroOn p (d.localTotal V s hs)
    have hsum : diagonal p (s.sum d.operator) =
        s.sum (fun i => diagonal p (d.operator i)) :=
      map_sum (diagonalRingHom p) (fun i => End.of (d.operator i)) s
    have hsub : diagonal p (s.sum d.operator - 𝟙 (smoothSheaf p)) =
        diagonal p (s.sum d.operator) - 𝟙 (pairSheaf p) := by
      apply pairSheafEnd_ext p
      intro W t
      rfl
    rw [hsub, hsum] at h
    exact h

/-- Actual smooth partitions on the unchanged compact torus atlas prove
local fineness of the genuine smooth-function sheaf. -/
theorem smooth_locallyFine : LocallyFine (smoothSheaf p) :=
  SmoothFunctions.locallyFine Iℝ₂ p.Torus

/-- The genuine smooth-pair sheaf is locally fine by the same partitions. -/
theorem pair_locallyFine : LocallyFine (pairSheaf p) := by
  intro ι U hU
  obtain ⟨d⟩ := smooth_locallyFine p ι U hU
  exact ⟨pairDecomposition p d⟩

/-- Every positive actual Ext-defined cohomology group of the original
smooth-function sheaf is trivial. -/
theorem smooth_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (smoothSheaf p) (n + 1)) :=
  SmoothFunctions.higher_subsingleton Iℝ₂ p.Torus n

/-- Every positive actual Ext-defined cohomology group of the literal
smooth-pair sheaf is trivial. -/
theorem pair_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (pairSheaf p) (n + 1)) :=
  (pair_locallyFine p).higher_subsingleton (pairScalarEnd p) n

theorem smooth_higher_subsingleton_of_pos (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (smoothSheaf p) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact smooth_higher_subsingleton p k

theorem pair_higher_subsingleton_of_pos (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (pairSheaf p) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact pair_higher_subsingleton p k

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
