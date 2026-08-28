import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Augmented ordered formal chains

`FormalChains V n` is the free integral module on ordered lists of `n` vertices.
Thus its geometric degree is `n - 1`, with an actual empty-simplex augmentation
in degree zero. The boundary is the alternating sum of vertex deletions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open scoped BigOperators

variable {V W M : Type*}

/-- Augmented ordered formal simplicial chains. -/
abbrev FormalChains (V : Type*) (n : ℕ) := (Fin n → V) →₀ ℤ

/-- A single ordered formal simplex, with coefficient one. -/
def formalSimplex {n : ℕ} (v : Fin n → V) : FormalChains V n :=
  Finsupp.single v 1

/-- Linear extension from the ordered simplex generators. -/
def formalLift {n : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → M) : FormalChains V n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ f

@[simp] theorem formalLift_simplex {n : ℕ} [AddCommGroup M] [modM : Module ℤ M]
    (f : (Fin n → V) → M) (v : Fin n → V) :
    formalLift f (formalSimplex v) = f v := by
  exact (Finsupp.linearCombination_single ℤ 1 v).trans (modM.one_smul (f v))

/-- Equality of linear maps can be checked on coefficient-one simplices. -/
theorem formalChains_ext {n : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] M}
    (h : ∀ v, f (formalSimplex v) = g (formalSimplex v)) : f = g := by
  apply Finsupp.lhom_ext
  intro v z
  have hs : Finsupp.single v z = z • formalSimplex v := by
    simp [formalSimplex, Finsupp.smul_single]
  rw [hs, f.map_smul, g.map_smul, h]

/-- The formal chain map induced by a map on vertices. -/
def formalMap (f : V → W) (n : ℕ) : FormalChains V n →ₗ[ℤ] FormalChains W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

@[simp] theorem formalMap_simplex (f : V → W) {n : ℕ} (v : Fin n → V) :
    formalMap f n (formalSimplex v) = formalSimplex (f ∘ v) := by
  simp [formalMap, formalSimplex]

/-- Coning an ordered chain to a vertex, by prepending that vertex. -/
def formalCone (a : V) (n : ℕ) : FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun v => Fin.cons a v)

@[simp] theorem formalCone_simplex (a : V) {n : ℕ} (v : Fin n → V) :
    formalCone a n (formalSimplex v) = formalSimplex (Fin.cons a v) := by
  simp [formalCone, formalSimplex]

/-- The augmented boundary: the alternating sum of deleting one vertex. -/
def formalBoundary (n : ℕ) : FormalChains V (n + 1) →ₗ[ℤ] FormalChains V n :=
  formalLift fun v => ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
    formalSimplex (v ∘ i.succAbove)

@[simp] theorem formalBoundary_simplex (n : ℕ) (v : Fin (n + 1) → V) :
    formalBoundary n (formalSimplex v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove) :=
  formalLift_simplex _ _

/-- The augmented boundary of the cone on an empty simplex. -/
theorem formalBoundary_cone_zero (a : V) (c : FormalChains V 0) :
    formalBoundary 0 (formalCone a 0 c) = c := by
  have h : (formalBoundary 0).comp (formalCone a 0) = LinearMap.id := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalBoundary_simplex,
      LinearMap.id_apply]
    change (∑ i : Fin 1, (-1 : ℤ) ^ i.val •
      formalSimplex (Fin.cons a v ∘ i.succAbove)) = formalSimplex v
    simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    congr 1
  exact LinearMap.congr_fun h c

/-- The cone identity in all nonempty formal degrees. -/
theorem formalBoundary_cone (a : V) (n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalCone a (n + 1) c) =
      c - formalCone a n (formalBoundary n c) := by
  have h : (formalBoundary (n + 1)).comp (formalCone a (n + 1)) =
      LinearMap.id - (formalCone a n).comp (formalBoundary n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      formalCone_simplex, formalBoundary_simplex]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul]
    have hz : Fin.cons a v ∘ (0 : Fin (n + 2)).succAbove = v := by
      funext i
      simp
    rw [hz, sub_eq_add_neg]
    congr 1
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      Fin.cons_comp_succ_succAbove, map_smul, formalCone_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- The alternating formal boundary squares to zero, including augmentation. -/
theorem formalBoundary_comp (n : ℕ) :
    (formalBoundary (V := V) n).comp (formalBoundary (n + 1)) = 0 := by
  induction n with
  | zero =>
      apply formalChains_ext
      intro v
      change formalBoundary 0 (formalBoundary 1 (formalSimplex v)) = 0
      have hv : formalSimplex v =
          formalCone (v 0) 1 (formalSimplex (Fin.tail v)) := by
        rw [formalCone_simplex, Fin.cons_self_tail]
      rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone_zero, sub_self]
  | succ n ih =>
      apply formalChains_ext
      intro v
      change formalBoundary (n + 1) (formalBoundary (n + 2) (formalSimplex v)) = 0
      have hv : formalSimplex v =
          formalCone (v 0) (n + 2) (formalSimplex (Fin.tail v)) := by
        rw [formalCone_simplex, Fin.cons_self_tail]
      have hb := LinearMap.congr_fun ih (formalSimplex (Fin.tail v))
      change formalBoundary n (formalBoundary (n + 1) (formalSimplex (Fin.tail v))) = 0 at hb
      rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone, hb,
        map_zero, sub_zero, sub_self]

@[simp] theorem formalBoundary_boundary (n : ℕ) (c : FormalChains V (n + 2)) :
    formalBoundary n (formalBoundary (n + 1) c) = 0 :=
  LinearMap.congr_fun (formalBoundary_comp n) c

/-- Vertex maps commute with the formal boundary. -/
theorem formalMap_boundary (f : V → W) (n : ℕ) (c : FormalChains V (n + 1)) :
    formalMap f n (formalBoundary n c) = formalBoundary n (formalMap f (n + 1) c) := by
  have h : (formalMap f n).comp (formalBoundary n) =
      (formalBoundary n).comp (formalMap f (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalBoundary_simplex, map_sum, map_smul,
      formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

/-- Vertex maps take cones to cones at the image vertex. -/
theorem formalMap_cone (f : V → W) (a : V) (n : ℕ) (c : FormalChains V n) :
    formalMap f (n + 1) (formalCone a n c) = formalCone (f a) n (formalMap f n c) := by
  have h : (formalMap f (n + 1)).comp (formalCone a n) =
      (formalCone (f a) n).comp (formalMap f n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalMap_simplex]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.SingularMayerVietoris
