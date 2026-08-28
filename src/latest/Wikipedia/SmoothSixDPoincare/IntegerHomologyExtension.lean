import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Split an actual exact extension by one scalar coordinate

A preimage of one constructs the section. The resulting product
isomorphism retains both the original inclusion and the original integer
coordinate, so it can extend integer homology bases along actual handle attachments.
The algebraic construction works over any commutative coefficient ring.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.HomologyTransport

variable {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B]

theorem exists_split_rank_one_extension (i : A →ₗ[R] B) (p : B →ₗ[R] R)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃ₗ[R] B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨b, hb⟩ := hp 1
  let s : R →ₗ[R] B := LinearMap.toSpanSingleton R B b
  have hs (z : R) : p (s z) = z := by
    change p (z • b) = z
    rw [map_smul, hb, smul_eq_mul, mul_one]
  have hz (a : A) : p (i a) = 0 := by
    have h : i a ∈ LinearMap.range i := ⟨a, rfl⟩
    rw [← hk] at h
    exact h
  let F : (A × R) →ₗ[R] B := i.coprod s
  have hF (z : A × R) : p (F z) = z.2 := by
    change p (i z.1 + s z.2) = z.2
    rw [map_add, hz, hs, zero_add]
  have hinj : Function.Injective F := by
    intro x y h
    have h₂ : x.2 = y.2 := (hF x).symm.trans ((congrArg p h).trans (hF y))
    apply Prod.ext _ h₂
    apply hi
    change i x.1 + s x.2 = i y.1 + s y.2 at h
    rw [h₂] at h
    exact add_right_cancel h
  have hsurj : Function.Surjective F := by
    intro v
    have hv : v - s (p v) ∈ LinearMap.ker p := by
      change p (v - s (p v)) = 0
      rw [map_sub, hs, sub_self]
    rw [hk] at hv
    obtain ⟨a, ha⟩ := hv
    refine ⟨(a, p v), ?_⟩
    change i a + s (p v) = v
    rw [ha, sub_add_cancel]
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, ?_, hF⟩
  intro a
  change i a + s 0 = i a
  rw [map_zero, add_zero]

theorem exists_add_split_rank_one_extension (i : A →ₗ[R] B) (p : B →ₗ[R] R)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃+ B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨e, he, hp⟩ := exists_split_rank_one_extension i p hi hp hk
  exact ⟨e.toAddEquiv, he, hp⟩

end Wikipedia.SmoothSixDPoincare.HomologyTransport
