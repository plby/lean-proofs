import Wikipedia.HopfProblem.ExponentialChernComparisonLocalCochainsAlgebra
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleCochains
import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths

/-!
# Local primitives on the original integral singular chains

Every cochain below is built using the original simplex basis. Its
differential is the original coefficient-general singular differential.
In particular, a local lift of the edge labels gives a genuine integral
one-cochain whose differential is the original group two-cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains

open FirstHurewicz ConstantSheafSingularComparison
open PeriodTorusLineBundle.ChernCocycle

variable {X : Type} [TopologicalSpace X]
variable {A : Type*} [AddCommGroup A]

/-- The actual image of a standard vertex of a singular simplex. -/
abbrev vertex {n : ℕ} (σ : SingularSimplex X n) (i : Fin (n + 1)) : X :=
  σ (stdSimplex.vertex (S := ℝ) i)

@[simp] theorem vertex_face {n : ℕ} (σ : SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    vertex (σ.comp (simplexFace n i)) j = vertex σ (i.succAbove j) := by
  exact congrArg σ (simplexFace_vertex n i j)

/-- A pointwise function gives an actual singular zero-cochain. -/
def pointCochain {B : AddCommGrpCat.{0}} (f : X → B) : Cochains X B 0 :=
  cochainFromValues X B 0 (fun σ => f (vertex σ 0))

@[simp] theorem pointCochain_simplex {B : AddCommGrpCat.{0}} (f : X → B)
    (σ : SingularSimplex X 0) :
    pointCochain f (simplexChain X 0 σ) = f (vertex σ 0) :=
  cochainFromValues_simplex X B 0 _ σ

/-- The actual zero-to-one differential is target minus source. -/
theorem pointCochain_d_simplex {B : AddCommGrpCat.{0}} (f : X → B)
    (σ : SingularSimplex X 1) :
    (singularCochainComplex X B).d 0 1 (pointCochain f) (simplexChain X 1 σ) =
      f (vertex σ 1) - f (vertex σ 0) := by
  rw [singularCochainComplex_d_apply]
  change pointCochain f (boundaryOne X (simplexChain X 1 σ)) = _
  rw [boundaryOne_simplex, map_sub, pointCochain_simplex, pointCochain_simplex]
  rw [vertex_face, vertex_face]
  rfl

/-- The actual one-to-two differential is `12 - 02 + 01`. -/
theorem oneCochain_d_simplex {B : AddCommGrpCat.{0}} (c : Cochains X B 1)
    (σ : SingularSimplex X 2) :
    (singularCochainComplex X B).d 1 2 c (simplexChain X 2 σ) =
      c (simplexChain X 1 (σ.comp (simplexFace 1 0))) -
        c (simplexChain X 1 (σ.comp (simplexFace 1 1))) +
        c (simplexChain X 1 (σ.comp (simplexFace 1 2))) := by
  rw [singularCochainComplex_d_apply]
  change c (boundaryTwo X (simplexChain X 2 σ)) = _
  rw [boundaryTwo_simplex, map_add, map_sub]

/-- The literal local one-cochain `k(r(source), edge label)`. -/
def integralLocalOneCochain (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A)
    (r : X → A) : Cochains X (AddCommGrpCat.of ℤ) 1 :=
  cochainFromValues X (AddCommGrpCat.of ℤ) 1 (fun σ => k (r (vertex σ 0)) (ℓ σ))

@[simp] theorem integralLocalOneCochain_simplex (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A) (σ : SingularSimplex X 1) :
    integralLocalOneCochain ℓ k r (simplexChain X 1 σ) = k (r (vertex σ 0)) (ℓ σ) :=
  cochainFromValues_simplex X (AddCommGrpCat.of ℤ) 1 _ σ

/-- The actual two-cochain evaluated on the ordered edges `01` and `12`. -/
def integralTwoCochain (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    Cochains X (AddCommGrpCat.of ℤ) 2 :=
  cochainFromValues X (AddCommGrpCat.of ℤ) 2 (fun σ =>
    k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))))

@[simp] theorem integralTwoCochain_simplex (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (σ : SingularSimplex X 2) :
    integralTwoCochain ℓ k (simplexChain X 2 σ) =
      k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) :=
  cochainFromValues_simplex X (AddCommGrpCat.of ℤ) 2 _ σ

/-- The additive cochain is exactly the previously constructed integral
singular cochain, not an independent replacement. -/
theorem integralTwoCochain_eq_original (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) :
    integralTwoCochain ℓ k = (twoCochain ℓ k).toAddMonoidHom := by
  apply cochain_ext X (AddCommGrpCat.of ℤ) 2
  intro σ
  exact (integralTwoCochain_simplex ℓ k σ).trans (twoCochain_simplex ℓ k σ).symm

variable (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) (r : X → A)

/-- A genuine local vertex lift makes the integral local one-cochain a
primitive of the original integral two-cochain. -/
theorem integralLocalOneCochain_d
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0)) :
    (singularCochainComplex X (AddCommGrpCat.of ℤ)).d 1 2
      (integralLocalOneCochain ℓ k r) = integralTwoCochain ℓ k := by
  apply cochain_ext X (AddCommGrpCat.of ℤ) 2
  intro σ
  rw [oneCochain_d_simplex]
  simp only [integralLocalOneCochain_simplex, integralTwoCochain_simplex, hr, vertex_face]
  exact integral_vertex_triangle_defect k (r (vertex σ 0))
    (r (vertex σ 1)) (r (vertex σ 2))

/-- Shifting a local lift by a function constant on every edge changes
the actual integral one-cochain by the actual coboundary of `k(d,r)`. -/
theorem integralLocalOneCochain_shift
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (d : X → A)
    (hd : ∀ σ : SingularSimplex X 1, d (vertex σ 1) = d (vertex σ 0)) :
    integralLocalOneCochain ℓ k (fun x => d x + r x) - integralLocalOneCochain ℓ k r =
      (singularCochainComplex X (AddCommGrpCat.of ℤ)).d 0 1
        (pointCochain (fun x => k (d x) (r x))) := by
  apply cochain_ext X (AddCommGrpCat.of ℤ) 1
  intro σ
  rw [AddMonoidHom.sub_apply, integralLocalOneCochain_simplex,
    integralLocalOneCochain_simplex, pointCochain_d_simplex, hr, hd]
  exact integral_vertex_shift_difference k (d (vertex σ 0))
    (r (vertex σ 0)) (r (vertex σ 1))

end Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains
