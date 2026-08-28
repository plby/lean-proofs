import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# Actual singular homology of a candidate sphere

The sphere computation is the singular suspension calculation from
`Wikipedia.HopfProblem`, followed by its coefficient exact sequence. Both
`SingularHomology` and `ModHomology` are the objects of mathlib's actual
singular homology functors, not modules assigned from the expected ranks.

A homeomorphism transports these groups without changing the candidate's
smooth atlas. In particular the middle group of a candidate six-sphere
vanishes with integral or mod-two coefficients. This is a topological input
to a future geometric obstruction construction, not a nullbordism theorem.
-/

noncomputable section

open CategoryTheory.Limits

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {M : Type} [TopologicalSpace M]

/-- Away from degrees zero and the sphere dimension, the candidate's actual
integral singular homology vanishes. -/
theorem subsingleton_singularHomology_of_homeomorph_sphere {n k : ℕ}
    (hn : 0 < n) (hk : k ≠ 0) (hkn : k ≠ n) (h : M ≃ₜ Sphere n) :
    Subsingleton (SingularHomology M k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let : Subsingleton (SingularHomology (Sphere (n + 1)) k) :=
    unitSphere_homology_subsingleton n k hk hkn
  exact (homeomorphHomologyEquiv h k).injective.subsingleton

/-- The same statement for the native singular homology object with finite
cyclic coefficients, viewed as an integral module. -/
theorem subsingleton_modHomology_of_homeomorph_sphere {n k : ℕ}
    (p : ℕ) (hp : p ≠ 0) (hn : 0 < n) (hk : k ≠ 0) (hkn : k ≠ n)
    (h : M ≃ₜ Sphere n) : Subsingleton (ModHomology p M k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let : Subsingleton (ModHomology p (Sphere (n + 1)) k) :=
    unitSphereModHomology_subsingleton p hp n k hk hkn
  exact (modHomologyHomeomorphEquiv p h k).injective.subsingleton

/-- The actual integral middle homology of any topological six-sphere is zero. -/
theorem sixSphere_middleHomology_subsingleton (h : M ≃ₜ Sphere 6) :
    Subsingleton (SingularHomology M 3) :=
  subsingleton_singularHomology_of_homeomorph_sphere (by decide) (by decide) (by decide) h

/-- The actual mod-two middle homology of any topological six-sphere is zero. -/
theorem sixSphere_middleModTwoHomology_subsingleton (h : M ≃ₜ Sphere 6) :
    Subsingleton (ModHomology 2 M 3) :=
  subsingleton_modHomology_of_homeomorph_sphere 2 (by decide) (by decide)
    (by decide) (by decide) h

theorem sixSphere_middleHomology_isZero (h : M ≃ₜ Sphere 6) :
    IsZero (SingularHomology M 3) := by
  let := sixSphere_middleHomology_subsingleton h
  exact ModuleCat.isZero_of_subsingleton _

theorem sixSphere_middleModTwoHomology_isZero (h : M ≃ₜ Sphere 6) :
    IsZero (ModHomology 2 M 3) := by
  let := sixSphere_middleModTwoHomology_subsingleton h
  exact ModuleCat.isZero_of_subsingleton _

end NoExoticSixSphere
