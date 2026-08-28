import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusGroups
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusSurface
import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction

/-!
# Actual higher homology of the elliptic central surfaces and fillings

The proved homeomorphism from the genuine finite affine period quotient
to the explicit mapping torus transfers the genuine Wang calculation.
The proved strong deformation retraction then transfers these groups to
the entire actual filling.  These are the actual singular homology
objects and actual induced maps, not auxiliary abstract groups.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The homology equivalence induced by the actual surface homeomorphism. -/
def surfaceMappingTorusHomologyEquiv (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      SingularHomology (mappingTorusModel j) n :=
  homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n

@[simp] theorem surfaceMappingTorusHomologyEquiv_toLinearMap
    (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (surfaceMappingTorusHomologyEquiv j p n).toLinearMap =
      singularHomologyMap (surfaceMappingTorusHomeomorph j p : C(_, _)) n := rfl

/-- The actual elliptic central surface has second integral homology `ℤ²`. -/
def surfaceH2Equiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 2).trans (mappingTorusH2Equiv j)

/-- The actual elliptic central surface has third integral homology `ℤ²`. -/
def surfaceH3Equiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 3).trans (mappingTorusH3Equiv j)

/-- Its actual fourth integral homology is the orientation group `ℤ`. -/
def surfaceH4Equiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4 ≃ₗ[ℤ] ℤ :=
  (surfaceMappingTorusHomologyEquiv j p 4).trans (mappingTorusH4Equiv j)

theorem surface_h2_finrank (j : Kind) (p : FixedPeriod j) :
    Module.finrank ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 2) = 2 := by
  rw [(surfaceH2Equiv j p).finrank_eq]
  simp

theorem surface_h3_finrank (j : Kind) (p : FixedPeriod j) :
    Module.finrank ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 3) = 2 := by
  rw [(surfaceH3Equiv j p).finrank_eq]
  simp

theorem surface_h4_finrank (j : Kind) (p : FixedPeriod j) :
    Module.finrank ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4) = 1 := by
  rw [(surfaceH4Equiv j p).finrank_eq]
  simp

/-- Actual singular homology vanishes above degree four. -/
theorem surface_homology_subsingleton_of_lt (j : Kind) (p : FixedPeriod j)
    {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  have := threeTorusMappingTorus_homology_subsingleton (fibreTorusHomeomorph j).symm hn
  exact (surfaceMappingTorusHomologyEquiv j p n).injective.subsingleton

/-- In every higher degree the actual central-surface homology is free. -/
theorem surface_higher_homology_free (j : Kind) (p : FixedPeriod j) {n : ℕ} (hn : 2 ≤ n) :
    Module.Free ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  by_cases h2 : n = 2
  · subst n
    exact Module.Free.of_equiv (surfaceH2Equiv j p).symm
  by_cases h3 : n = 3
  · subst n
    exact Module.Free.of_equiv (surfaceH3Equiv j p).symm
  by_cases h4 : n = 4
  · subst n
    exact Module.Free.of_equiv (surfaceH4Equiv j p).symm
  have := surface_homology_subsingleton_of_lt j p (show 4 < n by omega)
  infer_instance

/-- These actual higher homology groups are finitely generated over the integers. -/
theorem surface_higher_homology_finite (j : Kind) (p : FixedPeriod j) {n : ℕ} (hn : 2 ≤ n) :
    Module.Finite ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  by_cases h2 : n = 2
  · subst n
    exact Module.Finite.of_surjective (surfaceH2Equiv j p).symm.toLinearMap
      (surfaceH2Equiv j p).symm.surjective
  by_cases h3 : n = 3
  · subst n
    exact Module.Finite.of_surjective (surfaceH3Equiv j p).symm.toLinearMap
      (surfaceH3Equiv j p).symm.surjective
  by_cases h4 : n = 4
  · subst n
    exact Module.Finite.of_surjective (surfaceH4Equiv j p).symm.toLinearMap
      (surfaceH4Equiv j p).symm.surjective
  have := surface_homology_subsingleton_of_lt j p (show 4 < n by omega)
  infer_instance

/-- In particular, all actual higher homology groups are torsion-free. -/
theorem surface_higher_homology_torsionFree (j : Kind) (p : FixedPeriod j)
    {n : ℕ} (hn : 2 ≤ n) :
    Module.IsTorsionFree ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  let := surface_higher_homology_free j p hn
  infer_instance

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual entire main-twist filling has second homology `ℤ²`. -/
def fillingH2Equiv :
    SingularHomology (D.Space j.twist (mainTwist_admissible j)) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 2).symm.trans
    (surfaceH2Equiv j D.centralPeriod)

/-- The actual entire main-twist filling has third homology `ℤ²`. -/
def fillingH3Equiv :
    SingularHomology (D.Space j.twist (mainTwist_admissible j)) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 3).symm.trans
    (surfaceH3Equiv j D.centralPeriod)

/-- The actual entire main-twist filling has fourth homology `ℤ`. -/
def fillingH4Equiv :
    SingularHomology (D.Space j.twist (mainTwist_admissible j)) 4 ≃ₗ[ℤ] ℤ :=
  (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 4).symm.trans
    (surfaceH4Equiv j D.centralPeriod)

/-- These degree-two coordinates preserve the actual inclusion of the central surface. -/
theorem fillingH2Equiv_centralInclusion
    (a : SingularHomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) 2) :
    fillingH2Equiv D
      (singularHomologyMap (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) 2 a) =
      surfaceH2Equiv j D.centralPeriod a := by
  change surfaceH2Equiv j D.centralPeriod
    ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 2).symm
      (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 2 a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The degree-three coordinates preserve the actual central inclusion. -/
theorem fillingH3Equiv_centralInclusion
    (a : SingularHomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) 3) :
    fillingH3Equiv D
      (singularHomologyMap (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) 3 a) =
      surfaceH3Equiv j D.centralPeriod a := by
  change surfaceH3Equiv j D.centralPeriod
    ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 3).symm
      (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 3 a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The degree-four coordinate preserves the actual central inclusion. -/
theorem fillingH4Equiv_centralInclusion
    (a : SingularHomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) 4) :
    fillingH4Equiv D
      (singularHomologyMap (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) 4 a) =
      surfaceH4Equiv j D.centralPeriod a := by
  change surfaceH4Equiv j D.centralPeriod
    ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 4).symm
      (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 4 a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The genuine deformation retraction also gives the higher vanishing for the entire filling. -/
theorem filling_homology_subsingleton_of_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) := by
  have := surface_homology_subsingleton_of_lt j D.centralPeriod hn
  exact
    (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n).symm.injective.subsingleton

end Wikipedia.HopfProblem.Elliptic.HigherHomology
