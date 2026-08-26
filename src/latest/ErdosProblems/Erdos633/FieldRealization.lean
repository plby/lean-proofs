import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-!
# Field-valued realizations preserving finitely many points

Over an infinite field, finitely many nonzero vectors can be simultaneously
detected by one linear functional. After including one and normalizing,
this gives a linear retraction of a field extension that fixes the base
field and is injective on any prescribed finite subset.

For the rational-angle conjugation argument, this replaces an approximation
of solutions to a finite linear system. Applying the retraction to coordinate
values preserves all linear incidence equations over the coefficient field.
No geometric tiling preservation is asserted in this algebraic module.
-/

namespace Erdos633

theorem exists_dual_nonzero_on_finset {F V : Type*} [Field F] [Infinite F]
    [AddCommGroup V] [Module F V] (s : Finset V) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ f : V →ₗ[F] F, ∀ x ∈ s, f x ≠ 0 := by
  classical
  have h (x : s) : ∃ f : Module.Dual F V, (Module.Dual.eval F V x.1) f ≠ 0 := by
    exact Module.Projective.exists_dual_ne_zero F (hs x.1 x.2)
  obtain ⟨f, hf⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun x : s => Module.Dual.eval F V x.1) h
  exact ⟨f, fun x hx => hf ⟨x, hx⟩⟩

theorem exists_field_retraction_nonzero_on_finset {F E : Type*}
    [Field F] [Infinite F] [Field E] [Algebra F E]
    (s : Finset E) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ f : E →ₗ[F] F, (∀ a : F, f (algebraMap F E a) = a) ∧
      ∀ x ∈ s, f x ≠ 0 := by
  classical
  have ht : ∀ x ∈ insert (1 : E) s, x ≠ 0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_ne_zero
    · exact hs x hx
  obtain ⟨g, hg⟩ := exists_dual_nonzero_on_finset (F := F) (insert (1 : E) s) ht
  have hg1 : g 1 ≠ 0 := hg 1 (Finset.mem_insert_self _ _)
  let f : E →ₗ[F] F := (g 1)⁻¹ • g
  have hf1 : f 1 = 1 := by
    change (g 1)⁻¹ * g 1 = 1
    exact inv_mul_cancel₀ hg1
  refine ⟨f, ?_, ?_⟩
  · intro a
    rw [show algebraMap F E a = a • (1 : E) by simp [Algebra.smul_def],
      f.map_smul, hf1, smul_eq_mul, mul_one]
  · intro x hx
    change (g 1)⁻¹ * g x ≠ 0
    exact mul_ne_zero (inv_ne_zero hg1) (hg x (Finset.mem_insert_of_mem hx))

theorem exists_field_retraction_injective_on {F E : Type*}
    [Field F] [Infinite F] [Field E] [Algebra F E] (s : Finset E) :
    ∃ f : E →ₗ[F] F, (∀ a : F, f (algebraMap F E a) = a) ∧ Set.InjOn f s := by
  classical
  let d := ((s ×ˢ s).image (fun p : E × E => p.1 - p.2)).filter (fun x => x ≠ 0)
  have hd : ∀ x ∈ d, x ≠ 0 := fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨f, hf, hd⟩ := exists_field_retraction_nonzero_on_finset (F := F) d hd
  refine ⟨f, hf, ?_⟩
  intro x hx y hy heq
  by_contra hxy
  have hmem : x - y ∈ d := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, sub_ne_zero.mpr hxy⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  exact hd (x - y) hmem (by rw [f.map_sub, heq, sub_self])

end Erdos633
