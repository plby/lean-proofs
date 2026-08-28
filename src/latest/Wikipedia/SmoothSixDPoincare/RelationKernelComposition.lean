import Mathlib.LinearAlgebra.Span.Basic

/-!
# The exact kernel when one lifted relation is adjoined

If the next quotient kills the image of one vector, its composite with
the previous presentation kills precisely the old kernel plus that vector.
No rank or unimodularity assumption is used.
-/

namespace Wikipedia.SmoothSixDPoincare.HomologyTransport

variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

theorem ker_comp_span_singleton (p : A →ₗ[R] B) (q : B →ₗ[R] C) (v : A)
    (hq : LinearMap.ker q = Submodule.span R {p v}) :
    LinearMap.ker (q.comp p) = LinearMap.ker p ⊔ Submodule.span R {v} := by
  apply le_antisymm
  · intro a ha
    have hpa : p a ∈ Submodule.span R {p v} := by
      rw [← hq]
      exact ha
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hpa
    have hk : a - r • v ∈ LinearMap.ker p := by
      change p (a - r • v) = 0
      rw [map_sub, map_smul, hr, sub_self]
    exact Submodule.mem_sup.mpr
      ⟨a - r • v, hk, r • v, Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),
        sub_add_cancel _ _⟩
  · apply sup_le
    · intro a ha
      change q (p a) = 0
      change p a = 0 at ha
      rw [ha, map_zero]
    · apply Submodule.span_le.mpr
      intro a ha
      have ha' : a = v := Set.mem_singleton_iff.mp ha
      subst a
      change p v ∈ LinearMap.ker q
      rw [hq]
      exact Submodule.subset_span (by simp)

end Wikipedia.SmoothSixDPoincare.HomologyTransport
