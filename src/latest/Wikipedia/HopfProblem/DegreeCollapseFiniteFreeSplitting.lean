import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!

# A finite free decomposition supplies a decreasing primitive coordinate

Use the proved structure theorem for finitely generated abelian groups.
At each nonzero free rank, the first integer coordinate takes a specified
element to one, and its actual kernel is the remaining free product.
This supplies the algebraic induction parameter for actual surgeries.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegerSplit

theorem exists_finite_free_product (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T), Finite T ∧
      Nonempty (G ≃+ (Fin n → ℤ) × T) := by
  obtain ⟨n, ι, hι, p, hp, a, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ a i) := fun i => ⟨pow_ne_zero (a i) (hp i).ne_zero⟩
  let T := DirectSum ι (fun i => ZMod (p i ^ a i))
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact ⟨n, T, inferInstance, inferInstance,
    ⟨e.trans (Finsupp.addEquivFunOnFinite.prodCongr (AddEquiv.refl T))⟩⟩

theorem exists_primitive_coordinate_with_smaller_free_product
    {G T : Type*} [AddCommGroup G] [AddCommGroup T] {n : ℕ}
    (e : G ≃+ (Fin (n + 1) → ℤ) × T) :
    ∃ (σ : G →+ ℤ) (c : G), σ c = 1 ∧
      Nonempty (σ.ker ≃+ (Fin n → ℤ) × T) := by
  let σ : G →+ ℤ := {
    toFun x := (e x).1 0
    map_zero' := by simp
    map_add' x y := by simp }
  let c := e.symm (Fin.cons 1 (0 : Fin n → ℤ), 0)
  have hc : σ c = 1 := by
    change (e (e.symm (Fin.cons 1 (0 : Fin n → ℤ), 0))).1 0 = 1
    simp
  refine ⟨σ, c, hc, ⟨{
    toFun := fun x => (fun i => (e x.val).1 i.succ, (e x.val).2)
    invFun := fun p => ⟨e.symm (Fin.cons 0 p.1, p.2), by
      change (e (e.symm (Fin.cons 0 p.1, p.2))).1 0 = 0
      simp⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_ }⟩⟩
  · intro x
    apply Subtype.ext
    apply e.injective
    simp only [AddEquiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (show (e x.val).1 0 = 0 from x.property).symm
      · rfl
    · rfl
  · intro p
    apply Prod.ext
    · funext i
      simp
    · simp
  · intro x y
    apply Prod.ext
    · funext i
      simp
    · simp

end Wikipedia.HopfProblem.DegreeCollapse.IntegerSplit
