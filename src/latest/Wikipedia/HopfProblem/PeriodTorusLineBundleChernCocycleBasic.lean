import Wikipedia.HopfProblem.FirstHurewiczChains

/-!
# Integral group cocycles and actual singular edge cocycles

The edge labels are assigned to actual continuous singular simplices.
Their triangle condition says that the label of the edge `02` is the
sum of the labels of `01` and `12`. The integral group cocycle uses the
inhomogeneous additive convention. Neither datum is assumed to be a
Chern-class comparison, and no normalization at the group identity is
required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle

open FirstHurewicz

/-- An integral inhomogeneous two-cocycle on an additive group. -/
structure IntegralTwoCocycle (A : Type*) [AddGroup A] where
  toFun : A → A → ℤ
  cocycle (a b c : A) :
    toFun a b + toFun (a + b) c = toFun a (b + c) + toFun b c

instance {A : Type*} [AddGroup A] :
    CoeFun (IntegralTwoCocycle A) (fun _ => A → A → ℤ) := ⟨IntegralTwoCocycle.toFun⟩

namespace IntegralTwoCocycle

variable {A B : Type*} [AddGroup A] [AddGroup B]

@[ext] theorem ext {k l : IntegralTwoCocycle A} (h : ∀ a b, k a b = l a b) : k = l := by
  cases k
  cases l
  congr 1
  funext a b
  exact h a b

instance : Zero (IntegralTwoCocycle A) where
  zero := ⟨fun _ _ => 0, by intros; rfl⟩

@[simp] theorem zero_apply (a b : A) : (0 : IntegralTwoCocycle A) a b = 0 := rfl

instance : Add (IntegralTwoCocycle A) where
  add k l :=
    { toFun := fun a b => k a b + l a b
      cocycle := fun a b c => by
        have hk := k.cocycle a b c
        have hl := l.cocycle a b c
        omega }

@[simp] theorem add_apply (k l : IntegralTwoCocycle A) (a b : A) :
    (k + l) a b = k a b + l a b := rfl

instance : Neg (IntegralTwoCocycle A) where
  neg k :=
    { toFun := fun a b => -k a b
      cocycle := fun a b c => by
        have hk := k.cocycle a b c
        omega }

@[simp] theorem neg_apply (k : IntegralTwoCocycle A) (a b : A) :
    (-k) a b = -k a b := rfl

/-- Pullback of the actual group cocycle along an additive homomorphism. -/
def comap (k : IntegralTwoCocycle A) (f : B →+ A) : IntegralTwoCocycle B where
  toFun a b := k (f a) (f b)
  cocycle a b c := by simpa only [map_add] using k.cocycle (f a) (f b) (f c)

@[simp] theorem comap_apply (k : IntegralTwoCocycle A) (f : B →+ A) (a b : B) :
    k.comap f a b = k (f a) (f b) := rfl

/-- The standard inhomogeneous coboundary, with sign fixed by `12 - 02 + 01`. -/
def coboundary (b : A → ℤ) : IntegralTwoCocycle A where
  toFun a c := b a + b c - b (a + c)
  cocycle a c d := by
    simp only [add_assoc]
    ring

@[simp] theorem coboundary_apply (b : A → ℤ) (a c : A) :
    coboundary b a c = b a + b c - b (a + c) := rfl

end IntegralTwoCocycle

/-- Additive labels on genuine singular edges, compatible with every genuine triangle. -/
structure EdgeCocycle (X : Type) [TopologicalSpace X] (A : Type*) [AddGroup A] where
  toFun : SingularSimplex X 1 → A
  triangle (σ : SingularSimplex X 2) :
    toFun (σ.comp (simplexFace 1 1)) =
      toFun (σ.comp (simplexFace 1 2)) + toFun (σ.comp (simplexFace 1 0))

instance {X : Type} [TopologicalSpace X] {A : Type*} [AddGroup A] :
    CoeFun (EdgeCocycle X A) (fun _ => SingularSimplex X 1 → A) := ⟨EdgeCocycle.toFun⟩

namespace EdgeCocycle

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {A B : Type*} [AddGroup A] [AddGroup B]

@[ext] theorem ext {ℓ μ : EdgeCocycle X A}
    (h : ∀ σ : SingularSimplex X 1, ℓ σ = μ σ) : ℓ = μ := by
  cases ℓ
  cases μ
  congr 1
  funext σ
  exact h σ

/-- The edge labels pull back by literal composition of continuous singular simplices. -/
def pullback (ℓ : EdgeCocycle Y A) (f : C(X, Y)) : EdgeCocycle X A where
  toFun σ := ℓ (f.comp σ)
  triangle σ := by
    simpa only [ContinuousMap.comp_assoc] using ℓ.triangle (f.comp σ)

@[simp] theorem pullback_apply (ℓ : EdgeCocycle Y A) (f : C(X, Y))
    (σ : SingularSimplex X 1) : ℓ.pullback f σ = ℓ (f.comp σ) := rfl

/-- Additive changes of the label group preserve the actual triangle condition. -/
def map (ℓ : EdgeCocycle X A) (f : A →+ B) : EdgeCocycle X B where
  toFun σ := f (ℓ σ)
  triangle σ := by rw [ℓ.triangle, map_add]

@[simp] theorem map_apply (ℓ : EdgeCocycle X A) (f : A →+ B)
    (σ : SingularSimplex X 1) : ℓ.map f σ = f (ℓ σ) := rfl

end EdgeCocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle
