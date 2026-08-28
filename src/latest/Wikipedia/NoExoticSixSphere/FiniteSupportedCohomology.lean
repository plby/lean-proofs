import Wikipedia.NoExoticSixSphere.DisjointSupportedCohomology
import Wikipedia.NoExoticSixSphere.PointSupportExtension

/-!
# Actual finite-supported cohomology is the sum of its singleton components

Induct on the actual finite support. The original disjoint-support
Mayer--Vietoris splitting supplies each singleton component. The
forward map remains the finite sum of the original support extensions.
The components on the finite support are uniquely determined.
-/

noncomputable section

open scoped BigOperators

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- Every actual finite-supported class is a sum of original singleton-supported classes. -/
theorem pointSum_surjective (s : Finset X) (p : ℕ) : Function.Surjective (pointSum s p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro c
      refine ⟨fun _ => 0, ?_⟩
      have hs : Subsingleton (Cohomology ((∅ : Finset X) : Set X) p) := by
        rw [Finset.coe_empty]
        exact cohomology_empty_subsingleton X p
      exact hs.elim _ _
  | @insert x s hx ih =>
      intro c
      have hxs : Disjoint ({x} : Set X) (s : Set X) := Set.disjoint_singleton_left.mpr hx
      have hK : ({x} : Set X) ⊆ (insert x s : Finset X) :=
        Set.singleton_subset_iff.mpr (Finset.mem_insert_self x s)
      have hL : (s : Set X) ⊆ (insert x s : Finset X) :=
        fun _ hy => Finset.mem_insert_of_mem hy
      have hcover : ({x} : Set X) ∪ (s : Set X) = (insert x s : Finset X) := by
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
      obtain ⟨a₀, b, hb⟩ := exists_sum_of_disjoint_union ({x} : Set X) (s : Set X)
        isClosed_singleton s.finite_toSet.isClosed hxs hK hL hcover p c
      obtain ⟨a, ha⟩ := ih b
      refine ⟨Function.update a x a₀, ?_⟩
      have he : pointSum s p (Function.update a x a₀) = b := by
        apply (pointSum_congr s p _ a ?_).trans ha
        intro y hy
        exact Function.update_of_ne (ne_of_mem_of_not_mem hy hx) a₀ a
      rw [pointSum_insert s x hx p, Function.update_self,
        pointTo_of_mem _ p x (Finset.mem_insert_self x s), he]
      exact hb

/-- The original finite extension sum determines every component on its support. -/
theorem pointSum_components_eq (s : Finset X) (p : ℕ)
    (a b : ∀ x : X, Cohomology ({x} : Set X) p)
    (hab : pointSum s p a = pointSum s p b) : ∀ x ∈ s, a x = b x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | @insert x s hx ih =>
      have hxs : Disjoint ({x} : Set X) (s : Set X) := Set.disjoint_singleton_left.mpr hx
      have hK : ({x} : Set X) ⊆ (insert x s : Finset X) :=
        Set.singleton_subset_iff.mpr (Finset.mem_insert_self x s)
      have hL : (s : Set X) ⊆ (insert x s : Finset X) :=
        fun _ hy => Finset.mem_insert_of_mem hy
      have hcover : ({x} : Set X) ∪ (s : Set X) = (insert x s : Finset X) := by
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
      rw [pointSum_insert s x hx p, pointSum_insert s x hx p,
        pointTo_of_mem _ p x (Finset.mem_insert_self x s)] at hab
      obtain ⟨hxab, hsab⟩ := sum_ext_of_disjoint_union ({x} : Set X) (s : Set X)
        isClosed_singleton s.finite_toSet.isClosed hxs hK hL hcover p
        (a x) (b x) (pointSum s p a) (pointSum s p b) hab
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxab
      · exact ih hsab y hy

end NoExoticSixSphere.SupportedModTwoCohomology
