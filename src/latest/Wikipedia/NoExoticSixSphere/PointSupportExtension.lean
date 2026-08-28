import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual point-support extensions and their finite sums

At a point in the target support, the map is the original extension
from its singleton. Outside the target support it is zero. This total
family lets finite sums retain their original support maps without
introducing arbitrary identifications of the component cohomology groups.
-/

noncomputable section

open scoped BigOperators

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- Original singleton-support extension, zero when the point is outside the target support. -/
def pointTo (K : Set X) (p : ℕ) (x : X) : Cohomology ({x} : Set X) p →ₗ[ℤ] Cohomology K p := by
  classical
  exact if hx : x ∈ K then extend (Set.singleton_subset_iff.mpr hx) p else 0

theorem pointTo_of_mem (K : Set X) (p : ℕ) (x : X) (hx : x ∈ K) :
    pointTo K p x = extend (Set.singleton_subset_iff.mpr hx) p := by
  classical
  simp only [pointTo, dif_pos hx]

theorem pointTo_of_not_mem (K : Set X) (p : ℕ) (x : X) (hx : x ∉ K) : pointTo K p x = 0 := by
  classical
  simp only [pointTo, dif_neg hx]

/-- Enlarging support retains the actual singleton inclusion. -/
theorem pointTo_transition {K L : Set X} (h : K ⊆ L) (p : ℕ) (x : X) (hx : x ∈ K)
    (a : Cohomology ({x} : Set X) p) : extend h p (pointTo K p x a) = pointTo L p x a := by
  rw [pointTo_of_mem K p x hx, pointTo_of_mem L p x (h hx)]
  exact (LinearMap.congr_fun (extend_trans (Set.singleton_subset_iff.mpr hx) h p) a).symm

/-- Sum of the actual singleton extensions over the specified finite support. -/
def pointSum (s : Finset X) (p : ℕ) (a : ∀ x : X, Cohomology ({x} : Set X) p) :
    Cohomology (s : Set X) p := ∑ x ∈ s, pointTo (s : Set X) p x (a x)

theorem pointSum_congr (s : Finset X) (p : ℕ) (a b : ∀ x : X, Cohomology ({x} : Set X) p)
    (hab : ∀ x ∈ s, a x = b x) : pointSum s p a = pointSum s p b :=
  Finset.sum_congr rfl (fun x hx => congrArg (pointTo (s : Set X) p x) (hab x hx))

theorem pointSum_add (s : Finset X) (p : ℕ) (a b : ∀ x : X, Cohomology ({x} : Set X) p) :
    pointSum s p (a + b) = pointSum s p a + pointSum s p b := by
  simp only [pointSum, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem pointSum_smul (s : Finset X) (p : ℕ) (z : ℤ)
    (a : ∀ x : X, Cohomology ({x} : Set X) p) :
    pointSum s p (z • a) = z • pointSum s p a := by
  change (∑ x ∈ s, pointTo (s : Set X) p x (z • a x)) =
    z • ∑ x ∈ s, pointTo (s : Set X) p x (a x)
  exact (Finset.sum_congr rfl (fun x _ =>
    (pointTo (s : Set X) p x).toAddMonoidHom.map_zsmul z (a x))).trans
    (Finset.sum_zsmul (fun x => pointTo (s : Set X) p x (a x)) s z)

/-- Inserting a new point is the original sum of singleton and old-support extensions. -/
theorem pointSum_insert [DecidableEq X] (s : Finset X) (x : X) (hx : x ∉ s) (p : ℕ)
    (a : ∀ y : X, Cohomology ({y} : Set X) p) :
    pointSum (insert x s) p a = pointTo (insert x s : Finset X) p x (a x) +
      extend (show (s : Set X) ⊆ (insert x s : Finset X) from
        fun _ hy => Finset.mem_insert_of_mem hy) p (pointSum s p a) := by
  rw [pointSum, Finset.sum_insert hx, pointSum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  exact (pointTo_transition (show (s : Set X) ⊆ (insert x s : Finset X) from
    fun _ hz => Finset.mem_insert_of_mem hz) p y hy (a y)).symm

end NoExoticSixSphere.SupportedModTwoCohomology
