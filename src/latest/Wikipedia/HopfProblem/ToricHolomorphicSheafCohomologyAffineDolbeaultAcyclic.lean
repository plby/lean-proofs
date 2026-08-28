import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultPairs
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFine

/-!
# Genuine acyclicity of the affine smooth Dolbeault terms

The actual smooth-function sheaf is locally fine on the noncompact affine
space. Its actual locally finite partition operators act diagonally on
the two genuine smooth form coefficients. The proved locally fine Ext
theorem gives every positive cohomology group of all three smooth terms.
The holomorphic function sheaf is not claimed to be fine.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

/-- Actual complex scalar endomorphisms of the smooth-function sheaf. -/
abbrev smoothScalarEnd : ℂ →+* End smoothSheaf :=
  SmoothFunctions.scalarEnd 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ)

/-- Actual complex scalar endomorphisms of the smooth-pair sheaf. -/
def pairScalarEnd : ℂ →+* End pairSheaf := diagonalRingHom.comp smoothScalarEnd

@[simp] theorem smoothScalarEnd_eq_smul (c : ℂ) (U : Opens (ℂ × ℂ))
    (s : SmoothSection U) : (smoothScalarEnd c).asHom.hom.app (op U) s = c • s := rfl

@[simp] theorem pairScalarEnd_eq_smul (c : ℂ) (U : Opens (ℂ × ℂ))
    (s : PairSection U) : (pairScalarEnd c).asHom.hom.app (op U) s = c • s := rfl

/-- Diagonal action preserves actual vanishing on every smaller open set. -/
theorem diagonal_isZeroOn {f : smoothSheaf ⟶ smoothSheaf} {U : Opens (ℂ × ℂ)}
    (hf : IsZeroOn f U) : IsZeroOn (diagonal f) U := by
  intro V hVU
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (f.hom.app (op V) s.1, f.hom.app (op V) s.2) = 0
  rw [hf V hVU]
  rfl

/-- The exact same closed locally finite supports and partition operators
act on both actual smooth coefficients. -/
def pairDecomposition {ι : Type} {U : ι → Opens (ℂ × ℂ)}
    (d : LocallyFiniteDecomposition smoothSheaf U) :
    LocallyFiniteDecomposition pairSheaf U where
  operator i := diagonal (d.operator i)
  support := d.support
  support_closed := d.support_closed
  subordinate := d.subordinate
  zeroOutside i := diagonal_isZeroOn (d.zeroOutside i)
  locallyFinite := d.locallyFinite
  localTotal V s hs := by
    have h := diagonal_isZeroOn (d.localTotal V s hs)
    have hsum : diagonal (s.sum d.operator) = s.sum (fun i => diagonal (d.operator i)) :=
      map_sum diagonalRingHom (fun i => End.of (d.operator i)) s
    have hsub : diagonal (s.sum d.operator - 𝟙 smoothSheaf) =
        diagonal (s.sum d.operator) - 𝟙 pairSheaf := by
      apply pairSheafEnd_ext
      intro W t
      rfl
    rw [hsub, hsum] at h
    exact h

/-- Genuine local fineness of the literal smooth-pair sheaf on `ℂ²`. -/
theorem pair_locallyFine : LocallyFine pairSheaf := by
  intro ι U hU
  obtain ⟨d⟩ := SmoothFunctions.locallyFine 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ) ι U hU
  exact ⟨pairDecomposition d⟩

/-- Every positive actual Ext-defined cohomology group of smooth affine
functions vanishes, without compactness or a vanishing premise. -/
theorem smooth_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} smoothSheaf (n + 1)) :=
  SmoothFunctions.higher_subsingleton 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ) n

/-- Every positive actual Ext-defined cohomology group of the literal
smooth affine form pairs vanishes. -/
theorem pair_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} pairSheaf (n + 1)) :=
  pair_locallyFine.higher_subsingleton pairScalarEnd n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
