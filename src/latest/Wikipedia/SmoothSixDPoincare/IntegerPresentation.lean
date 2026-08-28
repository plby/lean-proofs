import Wikipedia.SmoothSixDPoincare.RelationKernelComposition
import Mathlib.Data.Fin.VecNotation

/-!
# Finite integer presentations retaining the original map and relation columns

The presentation is a surjective map from a fixed free coefficient module;
its kernel is exactly the span of the retained columns. Transport through
an actual homology equivalence preserves the columns. Adjoining one quotient
relation chooses a lift, records that lift as a new column, and proves the
new kernel identity.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare

structure IntegerPresentation (B : Type*) [AddCommGroup B] [Module ℤ B] (r c : ℕ) where
  map : (Fin r → ℤ) →ₗ[ℤ] B
  columns : Fin c → (Fin r → ℤ)
  surjective : Surjective map
  kernel_eq : LinearMap.ker map = Submodule.span ℤ (range columns)

namespace IntegerPresentation

variable {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Module ℤ B] [Module ℤ C]
  {r c : ℕ}

def ofEquiv (e : (Fin r → ℤ) ≃ₗ[ℤ] B) : IntegerPresentation B r 0 where
  map := e.toLinearMap
  columns := Fin.elim0
  surjective := e.surjective
  kernel_eq := by
    rw [LinearMap.ker_eq_bot.mpr e.injective]
    simp

variable (P : IntegerPresentation B r c)

theorem map_column (i : Fin c) : P.map (P.columns i) = 0 := by
  have h : P.columns i ∈ Submodule.span ℤ (range P.columns) :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [← P.kernel_eq] at h
  exact h

def transport (e : B ≃ₗ[ℤ] C) : IntegerPresentation C r c where
  map := e.toLinearMap.comp P.map
  columns := P.columns
  surjective := e.surjective.comp P.surjective
  kernel_eq := by
    have h : LinearMap.ker (e.toLinearMap.comp P.map) = LinearMap.ker P.map := by
      ext v
      change e (P.map v) = 0 ↔ P.map v = 0
      constructor
      · intro hv
        exact e.injective (hv.trans (map_zero e).symm)
      · intro hv
        rw [hv, map_zero]
    exact h.trans P.kernel_eq

theorem transport_map (e : B ≃ₗ[ℤ] C) (v : Fin r → ℤ) :
    (P.transport e).map v = e (P.map v) := rfl

def liftRelation (b : B) : Fin r → ℤ := Classical.choose (P.surjective b)

theorem map_liftRelation (b : B) : P.map (P.liftRelation b) = b :=
  Classical.choose_spec (P.surjective b)

def adjoin (q : B →ₗ[ℤ] C) (hq : Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ {b}) : IntegerPresentation C r (c + 1) where
  map := q.comp P.map
  columns := Fin.cons (P.liftRelation b) P.columns
  surjective := hq.comp P.surjective
  kernel_eq := by
    have hk : LinearMap.ker q = Submodule.span ℤ {P.map (P.liftRelation b)} := by
      rw [P.map_liftRelation]
      exact hker
    rw [HomologyTransport.ker_comp_span_singleton P.map q (P.liftRelation b) hk,
      P.kernel_eq, Fin.range_cons, Submodule.span_insert, sup_comm]

theorem adjoin_map (q : B →ₗ[ℤ] C) (hq : Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ {b}) (v : Fin r → ℤ) :
    (P.adjoin q hq b hker).map v = q (P.map v) := rfl

theorem adjoin_column_zero (q : B →ₗ[ℤ] C) (hq : Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ {b}) :
    P.map ((P.adjoin q hq b hker).columns 0) = b := P.map_liftRelation b

theorem adjoin_column_succ (q : B →ₗ[ℤ] C) (hq : Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ {b}) (i : Fin c) :
    (P.adjoin q hq b hker).columns i.succ = P.columns i := rfl

end IntegerPresentation

end Wikipedia.SmoothSixDPoincare
