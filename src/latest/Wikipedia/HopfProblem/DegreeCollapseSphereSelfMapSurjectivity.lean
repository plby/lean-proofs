import Wikipedia.NoExoticSixSphere.NativeSphereComposition
import Wikipedia.NoExoticSixSphere.BasedHomotopyNativeMap

/-!
# A sphere self-map surjective in its own dimension is surjective in every degree

Lift the actual identity sphere class to construct a based right
homotopy inverse. Its induced map gives a right inverse on every native
homotopy group. The statement uses actual sphere maps and their original
based homotopies.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereSelfMapSurjectivity

open NoExoticSixSphere SmoothCube SphereComposition

theorem native_map_id {N X : Type*} [TopologicalSpace X] {x : X}
    (c : HomotopyGroup N X x) :
    HigherHomotopy.map (N := N) (ContinuousMap.id X) rfl c = c := by
  induction c using Quotient.inductionOn with
  | h p => rfl

theorem native_homeomorph_surjective {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) :
    Function.Surjective (HigherHomotopy.map (N := N) (e : C(X, Y)) he) := by
  apply HigherHomotopy.map_surjective (e : C(X, Y)) he e.injective
  intro p
  refine ⟨(e.symm : C(Y, X)).comp p, ?_⟩
  have h : (e : C(X, Y)).comp ((e.symm : C(Y, X)).comp p) = p := by
    apply ContinuousMap.ext
    intro u
    exact e.apply_symm_apply (p u)
  rw [h]
  exact ⟨ContinuousMap.HomotopyRel.refl p _⟩

theorem native_homeomorph_injective {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) :
    Function.Injective (HigherHomotopy.map (N := N) (e : C(X, Y)) he) := by
  apply HigherHomotopy.map_injective (e : C(X, Y)) he
  rintro f g S ⟨H⟩
  have hf : (e.symm : C(Y, X)).comp ((e : C(X, Y)).comp f) = f := by
    apply ContinuousMap.ext
    intro u
    exact e.symm_apply_apply (f u)
  have hg : (e.symm : C(Y, X)).comp ((e : C(X, Y)).comp g) = g := by
    apply ContinuousMap.ext
    intro u
    exact e.symm_apply_apply (g u)
  exact ⟨(H.compContinuousMap (e.symm : C(Y, X))).cast hf hg⟩

theorem exists_right_inverse {n : ℕ} [NeZero n] (f : Based n n)
    (hf : Function.Surjective (mapHom f n)) :
    ∃ g : Based n n, (comp f g).val.HomotopicRel
      (ContinuousMap.id (Sphere n)) {spherePole n} := by
  let e : Based n n := ⟨ContinuousMap.id _, rfl⟩
  obtain ⟨c, hc⟩ := hf (sphereClass e)
  obtain ⟨g, hg⟩ := sphereClass_surjective (Nat.pos_of_neZero n) c
  refine ⟨g, (sphereClass_eq_iff (Nat.pos_of_neZero n) (comp f g) e).mp ?_⟩
  rw [← mapHom_sphereClass, hg, hc]

theorem mapHom_surjective {m n : ℕ} [NeZero m] [NeZero n] (f : Based n n)
    (hf : Function.Surjective (mapHom f n)) : Function.Surjective (mapHom f m) := by
  obtain ⟨g, ⟨H⟩⟩ := exists_right_inverse f hf
  intro c
  obtain ⟨a, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero m) c
  refine ⟨sphereClass (comp g a), ?_⟩
  have h := HigherHomotopy.map_eq_of_based_homotopy (comp f g).val
    (ContinuousMap.id (Sphere n)) (comp f g).property rfl H (sphereClass a)
  change HigherHomotopy.map (N := Fin m) f.val f.property
    (HigherHomotopy.map (N := Fin m) g.val g.property (sphereClass a)) = sphereClass a
  rw [HigherHomotopy.map_comp]
  exact h.trans (native_map_id _)

end Wikipedia.HopfProblem.DegreeCollapse.SphereSelfMapSurjectivity
