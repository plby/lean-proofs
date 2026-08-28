import Wikipedia.NoExoticSixSphere.SimplexHomotopySubspace
import Wikipedia.HopfProblem.ThirdHurewiczHomotopyComposition

/-!
# Extending actual relative simplex homotopies in all higher dimensions

Two adjacent coherent homotopy families extend by the explicit simplex
retraction. Iterating that construction supplies all higher families.
The starting maps and subspace-preservation properties are retained,
with literal compatibility on every face.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexHomotopyFamily

variable {X : Type} [TopologicalSpace X]

theorem compose_mem (U : Set X) {n : ℕ}
    (H G : C(Simplex n, X) → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, H smp p ∈ U)
    (hG : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, G smp p ∈ U)
    (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (p : I × Simplex n) :
    ThirdHurewicz.composeSimplexHomotopies H G hH₀ hG₀ smp p ∈ U := by
  let F := ThirdHurewicz.simplexFamilyHomotopy H hH₀ smp
  let K := ThirdHurewicz.simplexFamilyHomotopy G hG₀ (timeSlice (H smp) 1)
  change (F.trans K) p ∈ U
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH smp hs _
  · exact hG (timeSlice (H smp) 1) (fun s ↦ hH smp hs (1, s)) _

structure Stage (U : Set X) (n : ℕ) where
  lower : C(Simplex n, X) → C(I × Simplex n, X)
  upper : C(Simplex (n + 1), X) → C(I × Simplex (n + 1), X)
  lower_zero : ∀ smp s, lower smp (0, s) = smp s
  upper_zero : ∀ smp s, upper smp (0, s) = smp s
  face : FaceCompatibleHomotopies n lower upper
  lower_mem : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, lower smp p ∈ U
  upper_mem : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, upper smp p ∈ U

variable {U : Set X} {n : ℕ}

def Stage.next (D : Stage U n) : Stage U (n + 1) where
  lower := D.upper
  upper := extendCoherentSimplexHomotopy D.lower D.upper D.face D.upper_zero
  lower_zero := D.upper_zero
  upper_zero := extendCoherentSimplexHomotopy_zero D.lower D.upper D.face D.upper_zero
  face := extendCoherentSimplexHomotopy_face D.lower D.upper D.face D.upper_zero
  lower_mem := D.upper_mem
  upper_mem := SimplexHomotopySubspace.coherent_extension_mem U D.lower D.upper
    D.face D.upper_zero D.upper_mem

def Stage.iterate (D : Stage U n) : (k : ℕ) → Stage U (n + k)
  | 0 => D
  | k + 1 => (D.iterate k).next

def Stage.family (D : Stage U n) (k : ℕ) (smp : C(Simplex (n + k), X)) :
    C(I × Simplex (n + k), X) := (D.iterate k).lower smp

theorem Stage.family_zero (D : Stage U n) (smp : C(Simplex n, X)) :
    D.family 0 smp = D.lower smp := rfl

theorem Stage.family_one (D : Stage U n) (smp : C(Simplex (n + 1), X)) :
    D.family 1 smp = D.upper smp := rfl

theorem Stage.family_initial (D : Stage U n) (k : ℕ) (smp : C(Simplex (n + k), X))
    (s : Simplex (n + k)) : D.family k smp (0, s) = smp s :=
  (D.iterate k).lower_zero smp s

theorem Stage.family_face (D : Stage U n) (k : ℕ) :
    FaceCompatibleHomotopies (n + k) (D.family k) (D.family (k + 1)) :=
  (D.iterate k).face

theorem Stage.family_mem (D : Stage U n) (k : ℕ) (smp : C(Simplex (n + k), X))
    (hs : ∀ s, smp s ∈ U) (p : I × Simplex (n + k)) : D.family k smp p ∈ U :=
  (D.iterate k).lower_mem smp hs p

end NoExoticSixSphere.RelativeSimplexHomotopyFamily
