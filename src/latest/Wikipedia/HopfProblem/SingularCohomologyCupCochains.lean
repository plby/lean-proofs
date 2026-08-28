import Wikipedia.HopfProblem.SingularCohomologyCupFaces
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular

/-!
# The Alexander–Whitney product on the actual singular cochains

The product is defined on the native singular-simplex generators and
extended using their coproduct universal property. Its formula uses
the actual front and back affine faces of each singular simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz SingularCohomologyFree

/-- Integral cochains of the native singular chain complex. -/
abbrev Cochain (X : Type) [TopologicalSpace X] (n : ℕ) := Chains X n →ₗ[ℤ] ℤ

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Change only a cochain's degree index along an equality. -/
def castCochain {m n : ℕ} (h : m = n) (α : Cochain X m) : Cochain X n := h ▸ α

@[simp] theorem castCochain_rfl {n : ℕ} (α : Cochain X n) :
    castCochain rfl α = α := rfl

@[simp] theorem castCochain_zero {m n : ℕ} (h : m = n) :
    castCochain (X := X) h 0 = 0 := by
  subst n
  rfl

@[simp] theorem castCochain_add {m n : ℕ} (h : m = n) (α β : Cochain X m) :
    castCochain h (α + β) = castCochain h α + castCochain h β := by
  subst n
  rfl

@[simp] theorem castCochain_smul {m n : ℕ} (h : m = n) (a : ℤ) (α : Cochain X m) :
    castCochain h (a • α) = a • castCochain h α := by
  subst n
  rfl

/-- Alexander–Whitney multiplication in an explicitly specified total degree. -/
def cupInDegree {p q n : ℕ} (h : p + q = n)
    (α : Cochain X p) (β : Cochain X q) : Cochain X n :=
  chainLift X n fun σ =>
    α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))) *
      β (simplexChain X q (σ.comp (windowFace p q n (by omega))))

@[simp] theorem cupInDegree_simplex {p q n : ℕ} (h : p + q = n)
    (α : Cochain X p) (β : Cochain X q) (σ : SingularSimplex X n) :
    cupInDegree h α β (simplexChain X n σ) =
      α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))) *
        β (simplexChain X q (σ.comp (windowFace p q n (by omega)))) :=
  chainLift_simplex X n _ σ

/-- The native Alexander–Whitney cochain product. -/
def cup {p q : ℕ} (α : Cochain X p) (β : Cochain X q) : Cochain X (p + q) :=
  cupInDegree rfl α β

/-- The defining front-face times back-face formula on a singular simplex. -/
@[simp] theorem cup_simplex {p q : ℕ} (α : Cochain X p) (β : Cochain X q)
    (σ : SingularSimplex X (p + q)) :
    cup α β (simplexChain X (p + q) σ) =
      α (simplexChain X p (σ.comp (frontFace p q))) *
        β (simplexChain X q (σ.comp (backFace p q))) :=
  chainLift_simplex X (p + q) _ σ

theorem cupInDegree_eq_cast {p q n : ℕ} (h : p + q = n)
    (α : Cochain X p) (β : Cochain X q) :
    cupInDegree h α β = castCochain h (cup α β) := by
  subst n
  rfl

@[simp] theorem cup_zero_left {p q : ℕ} (β : Cochain X q) :
    cup (0 : Cochain X p) β = 0 := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.zero_apply, zero_mul]

@[simp] theorem cup_zero_right {p q : ℕ} (α : Cochain X p) :
    cup α (0 : Cochain X q) = 0 := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.zero_apply, mul_zero]

theorem cup_add_left {p q : ℕ} (α α' : Cochain X p) (β : Cochain X q) :
    cup (α + α') β = cup α β + cup α' β := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.add_apply, add_mul]

theorem cup_add_right {p q : ℕ} (α : Cochain X p) (β β' : Cochain X q) :
    cup α (β + β') = cup α β + cup α β' := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.add_apply, mul_add]

theorem cup_smul_left {p q : ℕ} (a : ℤ) (α : Cochain X p) (β : Cochain X q) :
    cup (a • α) β = a • cup α β := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

theorem cup_smul_right {p q : ℕ} (a : ℤ) (α : Cochain X p) (β : Cochain X q) :
    cup α (a • β) = a • cup α β := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [cup_simplex, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Bilinearity of the actual cup product on singular cochains. -/
def cupLinear (X : Type) [TopologicalSpace X] (p q : ℕ) :
    Cochain X p →ₗ[ℤ] Cochain X q →ₗ[ℤ] Cochain X (p + q) where
  toFun α :=
    { toFun := cup α
      map_add' := cup_add_right α
      map_smul' := fun a β => cup_smul_right a α β }
  map_add' α α' := by
    apply LinearMap.ext
    intro β
    exact cup_add_left α α' β
  map_smul' a α := by
    apply LinearMap.ext
    intro β
    exact cup_smul_left a α β

@[simp] theorem cupLinear_apply {p q : ℕ} (α : Cochain X p) (β : Cochain X q) :
    cupLinear X p q α β = cup α β := rfl

/-- The literal coboundary of the native integral singular cochain complex. -/
def coboundary {n : ℕ} (α : Cochain X n) : Cochain X (n + 1) :=
  ((singularCochainComplex X).d n (n + 1)).hom α

theorem coboundary_eq {n : ℕ} (α : Cochain X n) :
    coboundary α = ((singularCochainComplex X).d n (n + 1)).hom α := rfl

theorem coboundary_simplex {n : ℕ} (α : Cochain X n)
    (σ : SingularSimplex X (n + 1)) :
    coboundary α (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val *
        α (simplexChain X n (σ.comp (simplexFace n i))) :=
  singularCochainComplex_d_simplex X n α σ

@[simp] theorem coboundary_zero (n : ℕ) : coboundary (0 : Cochain X n) = 0 :=
  map_zero _

@[simp] theorem coboundary_add {n : ℕ} (α β : Cochain X n) :
    coboundary (α + β) = coboundary α + coboundary β := map_add _ α β

@[simp] theorem coboundary_smul {n : ℕ} (a : ℤ) (α : Cochain X n) :
    coboundary (a • α) = a • coboundary α := map_smul _ a α

/-- Pullback by the actual singular chain map. -/
def pullback (f : C(X, Y)) (n : ℕ) : Cochain Y n →ₗ[ℤ] Cochain X n :=
  ((singularPullback f).f n).hom

theorem pullback_eq (f : C(X, Y)) (n : ℕ) (α : Cochain Y n) :
    pullback f n α = α.comp (inducedChain f n) := rfl

@[simp] theorem pullback_simplex (f : C(X, Y)) (n : ℕ) (α : Cochain Y n)
    (σ : SingularSimplex X n) :
    pullback f n α (simplexChain X n σ) = α (simplexChain Y n (f.comp σ)) :=
  singularPullback_simplex f n α σ

/-- Alexander–Whitney multiplication is natural under actual continuous maps. -/
theorem pullback_cup (f : C(X, Y)) {p q : ℕ} (α : Cochain Y p) (β : Cochain Y q) :
    pullback f (p + q) (cup α β) = cup (pullback f p α) (pullback f q β) := by
  apply chainMap_ext X (p + q)
  intro σ
  simp only [pullback_simplex, cup_simplex, ContinuousMap.comp_assoc]

end Wikipedia.HopfProblem.SingularCohomologyCup
