import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators

/-! # Generator comparisons using actual pointed cube representatives -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators

variable {N X Y Z : Type} [DecidableEq N] [Nonempty N]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def cubeClass {x : X} (p : GenLoop N X x) : HomotopyGroup N X x := ⟦p⟧

theorem mapped_generators_iff (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (p q : GenLoop N X x)
    (hp : Function.Surjective (fun k : ℤ ↦ cubeClass p ^ k))
    (hq : Function.Surjective (fun k : ℤ ↦ cubeClass q ^ k)) :
    Function.Surjective (fun k : ℤ ↦
      cubeClass (pointedMapGenLoop f x y hf p) ^ k) ↔
    Function.Surjective (fun k : ℤ ↦
      cubeClass (pointedMapGenLoop f x y hf q) ^ k) := by
  simp only [cubeClass] at hp hq ⊢
  rw [← pointedMap_mk, ← pointedMap_mk]
  exact (CyclicGenerators.map_generates_iff (pointedMap f x y hf) ⟦p⟧ hp).trans
    (CyclicGenerators.map_generates_iff (pointedMap f x y hf) ⟦q⟧ hq).symm

theorem homeomorph_cube_generates (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y)
    (p : GenLoop N X x)
    (hp : Function.Surjective (fun k : ℤ ↦ cubeClass p ^ k)) :
    Function.Surjective (fun k : ℤ ↦
      cubeClass (pointedMapGenLoop (e : C(X, Y)) x y he p) ^ k) := by
  simp only [cubeClass] at hp ⊢
  rw [← pointedHomeomorphMulEquiv_mk]
  exact (CyclicGenerators.equiv_generates_iff (pointedHomeomorphMulEquiv e x y he) ⟦p⟧).mpr hp

theorem homeomorph_comp_cube_class (f : C(X, Y)) (g : C(X, Z)) (e : Y ≃ₜ Z) (T : C(X, X))
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g x = z) (he : e y = z) (hT : T x = x)
    (h : ∀ a, e (f a) = g (T a)) (p : GenLoop N X x) :
    pointedHomeomorphMulEquiv e y z he
      (⟦pointedMapGenLoop f x y hf p⟧ : HomotopyGroup N Y y) =
      (⟦pointedMapGenLoop g x z hg (pointedMapGenLoop T x x hT p)⟧ : HomotopyGroup N Z z) := by
  rw [pointedHomeomorphMulEquiv_mk]
  apply congrArg (fun q : GenLoop N Z z ↦ (⟦q⟧ : HomotopyGroup N Z z))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact h (p t)

end Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators
