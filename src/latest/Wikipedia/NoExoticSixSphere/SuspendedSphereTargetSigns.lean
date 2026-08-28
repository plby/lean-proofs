import Wikipedia.NoExoticSixSphere.NativeSpherePermutations
import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange

/-!
# Target-coordinate signs on actual suspended native sphere classes

Reflection of the first target coordinate reverses the original
suspension clock. Thus it inverts suspended native classes. The proved
surjectivity range supplies this formula for every class in that range.
Actual based homotopies transfer it to negative-sign target permutations.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace NoExoticSixSphere.HigherHomotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a : X} {b : Y}

theorem map_eq_of_homotopicRel (f g : C(X, Y)) (hf : f a = b) (hg : g a = b)
    (H : f.HomotopicRel g {a}) (c : HomotopyGroup N X a) : map f hf c = map g hg c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply Quotient.sound
  obtain ⟨H⟩ := H
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap p.val, prop' := ?_ }⟩
  intro t u hu
  exact H.eq_fst t (p.property u hu)

end NoExoticSixSphere.HigherHomotopy

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube CubicalProductSuspension

theorem reflection_product_formula (n : ℕ) (hn : 0 < n) (t : I) (x : Sphere n) :
    reflection (n + 1) (Nat.succ_pos n) 0
        (sphereHomeomorph n (OnePointProduct.map
          (clock t, (euclideanOnePointSphere n).symm x))) =
      sphereHomeomorph n (OnePointProduct.map
        (clock (σ t), (euclideanOnePointSphere n).symm x)) := by
  obtain ⟨u, rfl⟩ := quotient_surjective hn x
  have h₀ := quotient_product n (Fin.cons t u)
  have h₁ := quotient_product n (Fin.cons (σ t) u)
  change sphereHomeomorph n (OnePointProduct.map
    (clock t, (euclideanOnePointSphere n).symm (SmoothCube.quotient n u))) = _ at h₀
  change sphereHomeomorph n (OnePointProduct.map
    (clock (σ t), (euclideanOnePointSphere n).symm (SmoothCube.quotient n u))) = _ at h₁
  rw [h₀, reflection_quotient]
  have he : (fun j : Fin (n + 1) ↦
      if j = 0 then σ t else (Fin.cons t u : Fin (n + 1) → I) j) =
        (Fin.cons (σ t) u : Fin (n + 1) → I) := by
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · rfl
    · simp only [Fin.succ_ne_zero, if_false, Fin.cons_succ]
  change SmoothCube.quotient (n + 1)
    (fun j ↦ if j = 0 then σ t else (Fin.cons t u : Fin (n + 1) → I) j) = _
  rw [he]
  exact h₁.symm

theorem reflection_loop {d n : ℕ} (hn : 0 < n)
    (p : GenLoop (Fin d) (Sphere n) (spherePole n)) :
    HigherHomotopy.genLoopMap (reflection (n + 1) (Nat.succ_pos n) 0)
      (reflection_pole (n + 1) (Nat.succ_pos n) 0) (loop p) =
      GenLoop.symmAt 0 (loop p) := by
  apply GenLoop.ext
  intro u
  change reflection (n + 1) (Nat.succ_pos n) 0 (loop p u) =
    loop p (fun j ↦ if j = 0 then σ (u 0) else u j)
  rw [loop_apply, loop_apply]
  have ht : tail (fun j : Fin (d + 1) ↦ if j = 0 then σ (u 0) else u j) = tail u := by
    funext j
    change (if j.succ = 0 then σ (u 0) else u j.succ) = u j.succ
    rw [if_neg (Fin.succ_ne_zero j)]
  rw [ht]
  exact reflection_product_formula n hn (u 0) (p (tail u))

theorem reflection_hom {d n : ℕ} [NeZero d] (hn : 0 < n)
    (c : π_ d (Sphere n) (spherePole n)) :
    HigherHomotopy.map (N := Fin (d + 1)) (reflection (n + 1) (Nat.succ_pos n) 0)
      (reflection_pole (n + 1) (Nat.succ_pos n) 0) (hom d n c) = (hom d n c)⁻¹ := by
  refine Quotient.inductionOn c fun p ↦ ?_
  have h := (HomotopyGroup.inv_spec (i := (0 : Fin (d + 1))) (p := loop p)).symm
  rw [← reflection_loop hn p] at h
  exact h

theorem reflection_native {d n : ℕ} [NeZero d] (hd : d + 2 < 2 * (n + 1))
    (c : π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1))) :
    HigherHomotopy.map (N := Fin (d + 1)) (reflection (n + 1) (Nat.succ_pos n) 0)
      (reflection_pole (n + 1) (Nat.succ_pos n) 0) c = c⁻¹ := by
  obtain ⟨a, rfl⟩ := hom_surjective hd c
  exact reflection_hom (by omega) a

theorem permutation_native_negative {d n : ℕ} [NeZero d] [Nontrivial (Fin (n + 1))]
    (hd : d + 2 < 2 * (n + 1)) (e : Equiv.Perm (Fin (n + 1)))
    (he : ((Equiv.Perm.sign e : ℤˣ) : ℤ) = -1)
    (c : π_ (d + 1) (Sphere (n + 1)) (spherePole (n + 1))) :
    HigherHomotopy.map (N := Fin (d + 1)) (permutation (n + 1) (Nat.succ_pos n) e)
      (permutation_pole (n + 1) (Nat.succ_pos n) e) c = c⁻¹ :=
  (HigherHomotopy.map_eq_of_homotopicRel _ _ _ _
    (permutation_homotopic_reflection (Nat.succ_pos n) e he 0) c).trans
      (reflection_native hd c)

end NoExoticSixSphere.CubicalSphereSuspension
