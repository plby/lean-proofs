import Wikipedia.HopfProblem.ExponentialChernComparisonLocalCochainsBasic

/-!
# The literal local logarithmic singular cochains

For an actual edge cocycle `ℓ`, an actual local vertex lift `r`, and a
pointwise logarithm `L`, the one-cochain here has value
`L(target) - L(source) - k(r(source), ℓ(edge)) * P`. Its differential is
the negative period multiple of the original integral two-cochain.

The difference of two such cochains is the genuine differential of an
explicit zero-cochain, with the later-minus-earlier overlap convention.
No equality of cohomology classes or Chern-class comparison is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains

open FirstHurewicz ConstantSheafSingularComparison
open PeriodTorusLineBundle.ChernCocycle

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Type*} [AddCommGroup A]

/-- The actual complex one-cochain obtained from a pointwise logarithm
and the original integral group cocycle. -/
def logarithmicOneCochain (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A)
    (r : X → A) (L : X → ℂ) (P : ℂ) : Cochains X (AddCommGrpCat.of ℂ) 1 :=
  cochainFromValues X (AddCommGrpCat.of ℂ) 1 (fun σ =>
    L (vertex σ 1) - L (vertex σ 0) - (k (r (vertex σ 0)) (ℓ σ) : ℂ) * P)

@[simp] theorem logarithmicOneCochain_simplex (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A) (L : X → ℂ) (P : ℂ)
    (σ : SingularSimplex X 1) :
    logarithmicOneCochain ℓ k r L P (simplexChain X 1 σ) =
      L (vertex σ 1) - L (vertex σ 0) - (k (r (vertex σ 0)) (ℓ σ) : ℂ) * P :=
  cochainFromValues_simplex X (AddCommGrpCat.of ℂ) 1 _ σ

/-- The original integral two-cochain with its coefficients multiplied
by the chosen complex period. -/
def periodTwoCochain (ℓ : EdgeCocycle X A) (k : IntegralTwoCocycle A) (P : ℂ) :
    Cochains X (AddCommGrpCat.of ℂ) 2 :=
  cochainFromValues X (AddCommGrpCat.of ℂ) 2 (fun σ =>
    (k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) * P)

@[simp] theorem periodTwoCochain_simplex (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (P : ℂ) (σ : SingularSimplex X 2) :
    periodTwoCochain ℓ k P (simplexChain X 2 σ) =
      (k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) * P :=
  cochainFromValues_simplex X (AddCommGrpCat.of ℂ) 2 _ σ

/-- This is literal coefficient postcomposition on the existing
integral two-cochain. -/
theorem periodTwoCochain_eq_coefficientMap (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (P : ℂ) :
    periodTwoCochain ℓ k P =
      (coefficientMap X (AddCommGrpCat.ofHom (integerPeriodHom P))).f 2
        (integralTwoCochain ℓ k) := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 2
  intro σ
  rw [periodTwoCochain_simplex, coefficientMap_apply,
    integralTwoCochain_simplex]
  rfl

/-- The literal one-cochain is the differential of `L` minus the actual
period coefficient image of the integral local one-cochain. -/
theorem logarithmicOneCochain_eq_d_sub (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A) (L : X → ℂ) (P : ℂ) :
    logarithmicOneCochain ℓ k r L P =
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 0 1 (pointCochain L) -
        (coefficientMap X (AddCommGrpCat.ofHom (integerPeriodHom P))).f 1
          (integralLocalOneCochain ℓ k r) := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 1
  intro σ
  rw [logarithmicOneCochain_simplex, AddMonoidHom.sub_apply,
    pointCochain_d_simplex, coefficientMap_apply, integralLocalOneCochain_simplex]
  rfl

/-- On every actual singular triangle, the logarithmic local cochain
has the negative period multiple of the original group cocycle as its
actual differential. -/
theorem logarithmicOneCochain_d_simplex (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A)
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (L : X → ℂ) (P : ℂ) (σ : SingularSimplex X 2) :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 1 2
        (logarithmicOneCochain ℓ k r L P) (simplexChain X 2 σ) =
      -(k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) * P := by
  have hi : k (r (vertex σ 1)) (ℓ (σ.comp (simplexFace 1 0))) -
      k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 1))) +
      k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 2))) =
        k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) := by
    have h := congrArg (fun c : Cochains X (AddCommGrpCat.of ℤ) 2 =>
      c (simplexChain X 2 σ)) (integralLocalOneCochain_d ℓ k r hr)
    rw [oneCochain_d_simplex] at h
    simp only [integralLocalOneCochain_simplex, integralTwoCochain_simplex, vertex_face] at h
    exact h
  have hc := congrArg (fun n : ℤ => (n : ℂ)) hi
  simp only [Int.cast_add, Int.cast_sub] at hc
  rw [oneCochain_d_simplex]
  simp only [logarithmicOneCochain_simplex, vertex_face]
  change (L (vertex σ 2) - L (vertex σ 1) -
      (k (r (vertex σ 1)) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) * P) -
    (L (vertex σ 2) - L (vertex σ 0) -
      (k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 1))) : ℂ) * P) +
    (L (vertex σ 1) - L (vertex σ 0) -
      (k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 2))) : ℂ) * P) = _
  calc
    _ = -((k (r (vertex σ 1)) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) -
        (k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 1))) : ℂ) +
        (k (r (vertex σ 0)) (ℓ (σ.comp (simplexFace 1 2))) : ℂ)) * P := by ring
    _ = _ := by rw [hc]

/-- Equality of the actual cochains, with the negative sign displayed
in the literal simplex-value construction. -/
theorem logarithmicOneCochain_d (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A)
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (L : X → ℂ) (P : ℂ) :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 1 2
      (logarithmicOneCochain ℓ k r L P) =
        cochainFromValues X (AddCommGrpCat.of ℂ) 2 (fun σ =>
          -(k (ℓ (σ.comp (simplexFace 1 2))) (ℓ (σ.comp (simplexFace 1 0))) : ℂ) * P) := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 2
  intro σ
  rw [cochainFromValues_simplex]
  exact logarithmicOneCochain_d_simplex ℓ k r hr L P σ

/-- The same differential is the negative of the genuine coefficient
image of the original integral two-cochain. -/
theorem logarithmicOneCochain_d_eq_neg (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A)
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (L : X → ℂ) (P : ℂ) :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 1 2
      (logarithmicOneCochain ℓ k r L P) = -periodTwoCochain ℓ k P := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 2
  intro σ
  rw [logarithmicOneCochain_d_simplex ℓ k r hr,
    AddMonoidHom.neg_apply, periodTwoCochain_simplex, neg_mul]

/-- The later local logarithmic cochain minus the earlier one is the
actual differential of the pointwise logarithm difference corrected by
`k(d,r)`. -/
theorem logarithmicOneCochain_shift (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r : X → A)
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (d : X → A)
    (hd : ∀ σ : SingularSimplex X 1, d (vertex σ 1) = d (vertex σ 0))
    (Li Lj : X → ℂ) (P : ℂ) :
    logarithmicOneCochain ℓ k (fun x => d x + r x) Lj P -
        logarithmicOneCochain ℓ k r Li P =
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 0 1
        (pointCochain (fun x => Lj x - Li x - (k (d x) (r x) : ℂ) * P)) := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 1
  intro σ
  have hi : k (d (vertex σ 0) + r (vertex σ 0)) (ℓ σ) - k (r (vertex σ 0)) (ℓ σ) =
      k (d (vertex σ 1)) (r (vertex σ 1)) - k (d (vertex σ 0)) (r (vertex σ 0)) := by
    rw [hr σ, hd σ]
    exact integral_vertex_shift_difference k (d (vertex σ 0))
      (r (vertex σ 0)) (r (vertex σ 1))
  have hc := congrArg (fun n : ℤ => (n : ℂ)) hi
  simp only [Int.cast_sub] at hc
  rw [AddMonoidHom.sub_apply, logarithmicOneCochain_simplex,
    logarithmicOneCochain_simplex, pointCochain_d_simplex]
  calc
    _ = (Lj (vertex σ 1) - Li (vertex σ 1)) -
        (Lj (vertex σ 0) - Li (vertex σ 0)) -
        ((k (d (vertex σ 0) + r (vertex σ 0)) (ℓ σ) : ℂ) -
          (k (r (vertex σ 0)) (ℓ σ) : ℂ)) * P := by ring
    _ = (Lj (vertex σ 1) - Li (vertex σ 1)) -
        (Lj (vertex σ 0) - Li (vertex σ 0)) -
        ((k (d (vertex σ 1)) (r (vertex σ 1)) : ℂ) -
          (k (d (vertex σ 0)) (r (vertex σ 0)) : ℂ)) * P := by rw [hc]
    _ = _ := by ring

/-- The overlap identity for separately named actual local lifts. -/
theorem logarithmicOneCochain_difference (ℓ : EdgeCocycle X A)
    (k : IntegralTwoCocycle A) (r s d : X → A)
    (hr : ∀ σ : SingularSimplex X 1, ℓ σ = r (vertex σ 1) - r (vertex σ 0))
    (hs : ∀ x : X, s x = d x + r x)
    (hd : ∀ σ : SingularSimplex X 1, d (vertex σ 1) = d (vertex σ 0))
    (Li Lj : X → ℂ) (P : ℂ) :
    logarithmicOneCochain ℓ k s Lj P - logarithmicOneCochain ℓ k r Li P =
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 0 1
        (pointCochain (fun x => Lj x - Li x - (k (d x) (r x) : ℂ) * P)) := by
  rw [funext hs]
  exact logarithmicOneCochain_shift ℓ k r hr d hd Li Lj P

/-- Actual pullback of point cochains is literal composition of their
pointwise values. -/
theorem pointCochain_pullback {B : AddCommGrpCat.{0}} (g : Y → B) (f : C(X, Y)) :
    (singularPullback B f).f 0 (pointCochain g) = pointCochain (fun x => g (f x)) := by
  apply cochain_ext X B 0
  intro σ
  rw [singularPullback_simplex, pointCochain_simplex, pointCochain_simplex]
  rfl

/-- Actual pullback, and hence actual open-set restriction, preserves
the literal local logarithmic formula. -/
theorem logarithmicOneCochain_pullback (ℓ : EdgeCocycle Y A)
    (k : IntegralTwoCocycle A) (r : Y → A) (L : Y → ℂ) (P : ℂ) (f : C(X, Y)) :
    (singularPullback (AddCommGrpCat.of ℂ) f).f 1 (logarithmicOneCochain ℓ k r L P) =
      logarithmicOneCochain (ℓ.pullback f) k (fun x => r (f x)) (fun x => L (f x)) P := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 1
  intro σ
  rw [singularPullback_simplex, logarithmicOneCochain_simplex,
    logarithmicOneCochain_simplex]
  rfl

/-- Actual pullback preserves the period multiple of the original
integral two-cochain. -/
theorem periodTwoCochain_pullback (ℓ : EdgeCocycle Y A)
    (k : IntegralTwoCocycle A) (P : ℂ) (f : C(X, Y)) :
    (singularPullback (AddCommGrpCat.of ℂ) f).f 2 (periodTwoCochain ℓ k P) =
      periodTwoCochain (ℓ.pullback f) k P := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 2
  intro σ
  rw [singularPullback_simplex, periodTwoCochain_simplex, periodTwoCochain_simplex]
  rfl

end Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains
