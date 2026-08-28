import Wikipedia.HopfProblem.SphereHomologyTop
import Wikipedia.HopfProblem.SphereHomologySuspensionOne

/-!
# All other integral homology groups of positive-dimensional spheres vanish

The degree-one step uses the actual connected middle band in the
contractible cone cover. Every higher step uses the previously constructed
singular suspension isomorphism, reducing eventually to the native circle
calculation. In particular no homology-sphere property is an assumption.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual first homology of every Euclidean sphere of dimension at least two vanishes. -/
theorem unitSphere_homology_one_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (UnitSphere (n + 2)) 1) := by
  let := suspension_homology_one_subsingleton (UnitSphere (n + 1))
  exact (homeomorphHomologyEquiv (suspensionSphereHomeomorph (n + 1)).symm 1).injective.subsingleton

/-- Apart from degree zero and the actual sphere dimension, integral singular homology is zero. -/
theorem unitSphere_homology_subsingleton (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (SingularHomology (UnitSphere (n + 1)) k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact (hkn rfl).elim
      | succ k => exact sphereCircle_homology_subsingleton k
  | succ n ih =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact unitSphere_homology_one_subsingleton n
      | succ k =>
        let := ih (k + 1) (Nat.succ_ne_zero _) (by omega)
        exact (unitSphereHomologySuspensionEquiv (n + 1) k).injective.subsingleton

theorem unitSphere_homology_isZero (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    IsZero (SingularHomology (UnitSphere (n + 1)) k) := by
  let := unitSphere_homology_subsingleton n k hk hkn
  exact ModuleCat.isZero_of_subsingleton _

/-- An explicit zero-module equivalence for every other degree. -/
def unitSphereHomologyEquivZero (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    SingularHomology (UnitSphere (n + 1)) k ≃ₗ[ℤ] (Fin 0 → ℤ) := by
  let := unitSphere_homology_subsingleton n k hk hkn
  exact LinearEquiv.ofSubsingleton _ _

/-- The actual integral homology of every positive-dimensional sphere is free in every degree. -/
instance unitSphere_homology_free (n k : ℕ) :
    Module.Free ℤ (SingularHomology (UnitSphere (n + 1)) k) := by
  by_cases hk : k = 0
  · subst k
    exact Module.Free.of_equiv (unitSphereHomologyZeroEquiv n).symm
  by_cases hkn : k = n + 1
  · subst k
    exact Module.Free.of_equiv (unitSphereHomologyTopEquiv n).symm
  let := unitSphere_homology_subsingleton n k hk hkn
  exact Module.Free.of_subsingleton ℤ _

/-- Every actual integral homology group is finitely generated. -/
instance unitSphere_homology_finite (n k : ℕ) :
    Module.Finite ℤ (SingularHomology (UnitSphere (n + 1)) k) := by
  by_cases hk : k = 0
  · subst k
    exact Module.Finite.of_surjective (unitSphereHomologyZeroEquiv n).symm.toLinearMap
      (unitSphereHomologyZeroEquiv n).symm.surjective
  by_cases hkn : k = n + 1
  · subst k
    exact Module.Finite.of_surjective (unitSphereHomologyTopEquiv n).symm.toLinearMap
      (unitSphereHomologyTopEquiv n).symm.surjective
  exact Module.Finite.of_surjective (unitSphereHomologyEquivZero n k hk hkn).symm.toLinearMap
    (unitSphereHomologyEquivZero n k hk hkn).symm.surjective

/-- The two nonzero groups have rank one; every other group has rank zero. -/
theorem unitSphere_homology_finrank (n k : ℕ) :
    Module.finrank ℤ (SingularHomology (UnitSphere (n + 1)) k) =
      if k = 0 ∨ k = n + 1 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa using (unitSphereHomologyZeroEquiv n).finrank_eq
  by_cases hkn : k = n + 1
  · subst k
    simpa using (unitSphereHomologyTopEquiv n).finrank_eq
  let := unitSphere_homology_subsingleton n k hk hkn
  simp [hk, hkn, Module.finrank_zero_of_subsingleton]

end Wikipedia.HopfProblem.SphereHomology
