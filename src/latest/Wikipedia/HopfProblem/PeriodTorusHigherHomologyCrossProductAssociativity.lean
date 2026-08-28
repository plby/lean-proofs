import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativityTrilinear
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalAssociatorHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyAffineTriple

/-!
# The actual singular-chain associator homotopy

The formal three-factor cone construction is realized in a product of standard
simplices and pushed forward by three singular simplices. This defines a natural
trilinear operation on Mathlib's actual singular-chain modules. No comparison
with a replacement homology theory is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

variable (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Left-associated minus right-associated actual singular cross products. -/
def crossProductAssociatorDefect (n : ℕ) :
    Chains X 1 →ₗ[ℤ] Chains Y 1 →ₗ[ℤ] Chains Z n →ₗ[ℤ] Chains (X × (Y × Z)) (n + 2) :=
  integerTrilinearPostcompose
      (integerTrilinearLeftAssociated (crossProductEdge X Y 1)
        (crossProductTriangle (X × Y) Z n))
      (inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)) -
    integerTrilinearRightAssociated (crossProductEdge X (Y × Z) (n + 1))
      (crossProductEdge Y Z n)

@[simp] theorem crossProductAssociatorDefect_apply (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z n) :
    crossProductAssociatorDefect X Y Z n a b c =
      inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (crossProductTriangle (X × Y) Z n (crossProductEdge X Y 1 a b) c) -
        crossProductEdge X (Y × Z) (n + 1) a (crossProductEdge Y Z n b c) := rfl

/-- The actual singular-chain realization of the formal associator cone. -/
def crossProductAssociatorHomotopy (n : ℕ) :
    Chains X 1 →ₗ[ℤ] Chains Y 1 →ₗ[ℤ] Chains Z n →ₗ[ℤ] Chains (X × (Y × Z)) (n + 3) :=
  chainTrilinearLift X Y Z 1 1 n fun σ τ υ =>
    inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
      (tripleAffineChainMap 1 1 n (n + 3)
        (formalAssociatorHomotopy n (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices n))))

@[simp] theorem crossProductAssociatorHomotopy_simplex (n : ℕ)
    (σ : SingularSimplex X 1) (τ : SingularSimplex Y 1) (υ : SingularSimplex Z n) :
    crossProductAssociatorHomotopy X Y Z n
        (simplexChain X 1 σ) (simplexChain Y 1 τ) (simplexChain Z n υ) =
      inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
        (tripleAffineChainMap 1 1 n (n + 3)
          (formalAssociatorHomotopy n (formalSimplex (stdVertices 1))
            (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices n)))) :=
  chainTrilinearLift_simplex X Y Z 1 1 n _ σ τ υ

/-- The homotopy vanishes when its third argument has degree zero. -/
@[simp] theorem crossProductAssociatorHomotopy_zero
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z 0) :
    crossProductAssociatorHomotopy X Y Z 0 a b c = 0 := by
  have h : crossProductAssociatorHomotopy X Y Z 0 = 0 := by
    apply chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    simp only [crossProductAssociatorHomotopy_simplex, formalAssociatorHomotopy_zero,
      map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun h a) b) c

variable {X Y Z}
variable {X' Y' Z' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace Z']

/-- Naturality of the actual associator homotopy under continuous maps of all factors. -/
theorem crossProductAssociatorHomotopy_natural
    (f : C(X, X')) (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z n) :
    inducedChain (f.prodMap (g.prodMap h)) (n + 3)
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorHomotopy X' Y' Z' n
        (inducedChain f 1 a) (inducedChain g 1 b) (inducedChain h n c) := by
  have heq : integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z n)
        (inducedChain (f.prodMap (g.prodMap h)) (n + 3)) =
      integerTrilinearPrecompose (crossProductAssociatorHomotopy X' Y' Z' n)
        (inducedChain f 1) (inducedChain g 1) (inducedChain h n) := by
    apply chainTrilinearMap_ext X Y Z 1 1 n
    intro σ τ υ
    simp only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      inducedChain_simplex, crossProductAssociatorHomotopy_simplex]
    have hc : (f.comp σ).prodMap ((g.comp τ).prodMap (h.comp υ)) =
        (f.prodMap (g.prodMap h)).comp (σ.prodMap (τ.prodMap υ)) := rfl
    rw [hc, inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- Reassociation commutes with product maps on actual chains. -/
theorem inducedChain_prodAssoc_natural
    (f : C(X, X')) (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ)
    (c : Chains ((X × Y) × Z) n) :
    inducedChain (f.prodMap (g.prodMap h)) n
        (inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) n c) =
      inducedChain (Homeomorph.prodAssoc X' Y' Z' : C(_, _)) n
        (inducedChain ((f.prodMap g).prodMap h) n c) := by
  have hc : (f.prodMap (g.prodMap h)).comp
        (Homeomorph.prodAssoc X Y Z : C(_, _)) =
      (Homeomorph.prodAssoc X' Y' Z' : C(_, _)).comp ((f.prodMap g).prodMap h) := rfl
  have heq := congrArg (fun k => inducedChain k n c) hc
  simpa only [inducedChain_comp, LinearMap.comp_apply] using heq

/-- Naturality of the difference between the two actual parenthesizations. -/
theorem crossProductAssociatorDefect_natural
    (f : C(X, X')) (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ)
    (a : Chains X 1) (b : Chains Y 1) (c : Chains Z n) :
    inducedChain (f.prodMap (g.prodMap h)) (n + 2)
        (crossProductAssociatorDefect X Y Z n a b c) =
      crossProductAssociatorDefect X' Y' Z' n
        (inducedChain f 1 a) (inducedChain g 1 b) (inducedChain h n c) := by
  simp only [crossProductAssociatorDefect_apply, map_sub, inducedChain_prodAssoc_natural,
    crossProductTriangle_natural, crossProductEdge_natural]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
