import Wikipedia.HopfProblem.OrbitPairRealizationDescent
import Wikipedia.HopfProblem.OrbitPairRealizationNaturality

/-!
# Continuous affine coordinates on realized nerves

Assign a geometric simplex point to each object of a category. On every
nerve simplex, interpolate these points with the geometric barycentric
weights. Summation over fibres proves compatibility with every simplex
operator, so this is an actual continuous map from the native realization.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.AffineCoordinates

open FirstHurewicz RealizationSimplex

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]

def weighted (a : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) : stdSimplex ℝ B :=
  ⟨fun b ↦ ∑ i, t i * a i b, fun b ↦
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (stdSimplex.zero_le t i)
      (stdSimplex.zero_le (a i) b)), by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]⟩

theorem weighted_apply (a : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) (b : B) :
    weighted a t b = ∑ i, t i * a i b := rfl

theorem weighted_map (f : A → D) (a : D → stdSimplex ℝ B) (t : stdSimplex ℝ A) :
    weighted a (stdSimplex.map f t) = weighted (a ∘ f) t := by
  classical
  apply Subtype.ext
  funext b
  change (∑ j, FunOnFinite.linearMap ℝ ℝ f t j * a j b) =
    ∑ i, t i * a (f i) b
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  calc
    _ = ∑ j : D, ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), t i * a (f i) b := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun i ↦ t i * a (f i) b)

def weightedMap (a : A → stdSimplex ℝ B) : C(stdSimplex ℝ A, stdSimplex ℝ B) where
  toFun := weighted a
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro b
    apply continuous_finsetSum
    intro i hi
    have h : Continuous (fun t : stdSimplex ℝ A ↦ t i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact h.mul_const (a i b)

theorem weighted_vertex [DecidableEq A] (a : A → stdSimplex ℝ B) (i : A) :
    weighted a (stdSimplex.vertex i) = a i := by
  classical
  apply Subtype.ext
  funext b
  change (∑ j, (Pi.single i (1 : ℝ) : A → ℝ) j * a j b) = a i b
  simp [Pi.single_apply]

theorem weighted_vertices [DecidableEq A] (t : stdSimplex ℝ A) :
    weighted (fun i ↦ stdSimplex.vertex i) t = t := by
  classical
  apply Subtype.ext
  funext i
  change (∑ j, t j * (Pi.single j (1 : ℝ) : A → ℝ) i) = t i
  simp [Pi.single_apply]

theorem weighted_const (b : stdSimplex ℝ B) (t : stdSimplex ℝ A) :
    weighted (fun _ : A ↦ b) t = b := by
  apply Subtype.ext
  funext j
  change (∑ i, t i * b j) = b j
  rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

theorem simplex_map_const [DecidableEq B] (b : B) (t : stdSimplex ℝ A) :
    stdSimplex.map (fun _ : A ↦ b) t = stdSimplex.vertex b :=
  (weighted_vertices (stdSimplex.map (fun _ : A ↦ b) t)).symm.trans
    ((weighted_map (fun _ : A ↦ b) (fun j ↦ stdSimplex.vertex j) t).trans
      (weighted_const (stdSimplex.vertex b) t))

variable (P : Type u) [Category.{v} P] (a : P → stdSimplex ℝ B)

def nerveCell (n : ℕ) (x : (nerve P) _⦋n⦌) : C(Simplex n, stdSimplex ℝ B) :=
  weightedMap (fun i ↦ a (x.obj i))

theorem nerveCell_map (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (x : (nerve P) _⦋n⦌) :
    nerveCell P a m ((nerve P).map f.op x) =
      (nerveCell P a n x).comp (SimplexCategory.toTop₀.map f).hom := by
  apply ContinuousMap.ext
  intro t
  change weighted (fun i ↦ a (x.obj (f.toOrderHom i))) t =
    weighted (fun i ↦ a (x.obj i)) (stdSimplex.map f.toOrderHom t)
  exact (weighted_map f.toOrderHom (fun i ↦ a (x.obj i)) t).symm

def nerveInterpolation : C(SSet.toTop.obj (nerve P), stdSimplex ℝ B) :=
  descend (nerve P) (nerveCell P a) (nerveCell_map P a)

theorem nerveInterpolation_characteristic (n : ℕ) (x : (nerve P) _⦋n⦌)
    (t : Simplex n) :
    nerveInterpolation P a (characteristic (nerve P) n x t) =
      weighted (fun i ↦ a (x.obj i)) t :=
  descend_characteristic (nerve P) (nerveCell P a) (nerveCell_map P a) n x t

theorem nerveInterpolation_vertex (p : P) :
    nerveInterpolation P a (vertex (nerve P) (CategoryTheory.ComposableArrows.mk₀ p)) =
      a p := by
  exact (nerveInterpolation_characteristic P a 0 (CategoryTheory.ComposableArrows.mk₀ p)
    (stdSimplex.vertex (S := ℝ) (0 : Fin 1))).trans
      (weighted_vertex (fun i ↦ a ((CategoryTheory.ComposableArrows.mk₀ p).obj i)) 0)

theorem nerveInterpolation_naturality {Q : Type u} [Category.{v} Q] (F : P ⥤ Q)
    (b : Q → stdSimplex ℝ B) :
    (nerveInterpolation Q b).comp (SSet.toTop.map (nerveMap F)).hom =
      nerveInterpolation P (fun p ↦ b (F.obj p)) := by
  apply continuousMap_ext_characteristic
  intro n x t
  change nerveInterpolation Q b
    ((SSet.toTop.map (nerveMap F)) (characteristic (nerve P) n x t)) = _
  rw [realizedMap_characteristic, nerveInterpolation_characteristic,
    nerveInterpolation_characteristic]
  rfl

end Wikipedia.HopfProblem.OrbitPair.AffineCoordinates
