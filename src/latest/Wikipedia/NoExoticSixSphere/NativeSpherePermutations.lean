import Wikipedia.NoExoticSixSphere.SmoothSphereCubeReflection
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetries

/-!
# Actual sphere permutations and their native orientation signs

The maps descend from the original cube quotient. Native permutation
signs determine their based sphere homotopies to the identity or to an
original coordinate reflection. This is a statement about the actual
maps and native classes, not only their homology degrees.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

def permutation (n : ℕ) (hn : 0 < n) (e : Equiv.Perm (Fin n)) : C(Sphere n, Sphere n) :=
  descend hn (permuteCubeLoop (toGenLoop ⟨ContinuousMap.id _, rfl⟩) e)

theorem permutation_quotient (n : ℕ) (hn : 0 < n) (e : Equiv.Perm (Fin n))
    (u : Fin n → I) :
    permutation n hn e (quotient n u) = quotient n (fun j ↦ u (e j)) :=
  descend_quotient hn _ u

theorem permutation_pole (n : ℕ) (hn : 0 < n) (e : Equiv.Perm (Fin n)) :
    permutation n hn e (spherePole n) = spherePole n := descend_pole hn _

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

def permuted (hn : 0 < n) (e : Equiv.Perm (Fin n)) (f : BasedMap n X x) : BasedMap n X x :=
  ⟨f.val.comp (permutation n hn e),
    (congrArg f.val (permutation_pole n hn e)).trans f.property⟩

theorem permuted_toGenLoop (hn : 0 < n) (e : Equiv.Perm (Fin n)) (f : BasedMap n X x) :
    toGenLoop (permuted hn e f) = permuteCubeLoop (toGenLoop f) e := by
  apply GenLoop.ext
  intro u
  exact congrArg f.val (permutation_quotient n hn e u)

theorem permuted_sphereClass [Nontrivial (Fin n)] (hn : 0 < n) (e : Equiv.Perm (Fin n))
    (f : BasedMap n X x) :
    sphereClass (permuted hn e f) =
      sphereClass f ^ (((Equiv.Perm.sign e : ℤˣ) : ℤ)) := by
  change Quotient.mk' (toGenLoop (permuted hn e f)) = _
  rw [permuted_toGenLoop]
  exact congrArg Additive.toMul (permuteCubeLoop_additiveClass (toGenLoop f) e)

theorem permutation_homotopic_id [Nontrivial (Fin n)] (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) (he : ((Equiv.Perm.sign e : ℤˣ) : ℤ) = 1) :
    (permutation n hn e).HomotopicRel (ContinuousMap.id _) {spherePole n} := by
  let f : BasedMap n (Sphere n) (spherePole n) := ⟨ContinuousMap.id _, rfl⟩
  apply (sphereClass_eq_iff hn (permuted hn e f) f).mp
  rw [permuted_sphereClass, he, zpow_one]

theorem permutation_homotopic_reflection [Nontrivial (Fin n)] [NeZero n] (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) (he : ((Equiv.Perm.sign e : ℤˣ) : ℤ) = -1) (i : Fin n) :
    (permutation n hn e).HomotopicRel (reflection n hn i) {spherePole n} := by
  let f : BasedMap n (Sphere n) (spherePole n) := ⟨ContinuousMap.id _, rfl⟩
  apply (sphereClass_eq_iff hn (permuted hn e f) (reflected hn i f)).mp
  rw [permuted_sphereClass, he, zpow_neg_one, reflected_sphereClass]

end NoExoticSixSphere.SmoothCube
