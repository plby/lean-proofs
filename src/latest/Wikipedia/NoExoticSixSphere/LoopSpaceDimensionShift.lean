import Wikipedia.NoExoticSixSphere.GeneralizedLoopCurrying

/-!
# The native loop-space dimension shift

Currying gives the equivalence on homotopy classes. Concatenation in a
parameter coordinate corresponds to concatenation in the successor coordinate
of the enlarged cube, proving compatibility with the native group operation.
-/

namespace NoExoticSixSphere.GeneralizedLoopCurrying

variable {X : Type*} [TopologicalSpace X] {x : X} {d : ℕ}

theorem uncurry_apply (p : GenLoop (Fin d) (Path x x) (Path.refl x))
    (t : Fin (d + 1) → unitInterval) : (uncurry p).1 t = p.1 (Fin.tail t) (t 0) := rfl

theorem transAt_apply {N : Type*} [DecidableEq N] (j : N) (p q : GenLoop N X x)
    (t : N → unitInterval) :
    (GenLoop.transAt j p q).1 t =
      if (t j : ℝ) ≤ 1 / 2 then
        p.1 (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j))) else
        q.1 (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1))) := rfl

theorem uncurry_transAt (j : Fin d) (p q : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    uncurry (GenLoop.transAt j p q) = GenLoop.transAt j.succ (uncurry p) (uncurry q) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [uncurry_apply, transAt_apply, transAt_apply]
  change (if (t j.succ : ℝ) ≤ 1 / 2 then
      p.1 (Function.update (Fin.tail t) j (Set.projIcc 0 1 zero_le_one (2 * t j.succ))) else
      q.1 (Function.update (Fin.tail t) j
        (Set.projIcc 0 1 zero_le_one (2 * t j.succ - 1)))) (t 0) = _
  split_ifs
  · rw [uncurry_apply, Fin.tail_update_succ]
    simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · rw [uncurry_apply, Fin.tail_update_succ]
    simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm]

noncomputable def homotopyEquiv (d : ℕ) (x : X) :
    HomotopyGroup (Fin d) (Path x x) (Path.refl x) ≃ HomotopyGroup (Fin (d + 1)) X x :=
  Quotient.congr (equiv d x) homotopic_iff_uncurry

theorem homotopyEquiv_mk (p : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    homotopyEquiv d x (Quotient.mk' p) = Quotient.mk' (uncurry p) := rfl

theorem homotopyEquiv_mul [NeZero d]
    (p q : HomotopyGroup (Fin d) (Path x x) (Path.refl x)) :
    homotopyEquiv d x (p * q) = homotopyEquiv d x p * homotopyEquiv d x q := by
  let j : Fin d := 0
  refine Quotient.inductionOn₂ p q ?_
  intro f g
  have hY := HomotopyGroup.mul_spec (i := j) (p := f) (q := g)
  have hZ := HomotopyGroup.mul_spec (i := j.succ) (p := uncurry f) (q := uncurry g)
  have hmap := congrArg
    (fun r : GenLoop (Fin (d + 1)) X x ↦ (Quotient.mk' r : HomotopyGroup (Fin (d + 1)) X x))
    (uncurry_transAt j g f)
  exact (congrArg (homotopyEquiv d x) hY).trans (hmap.trans hZ.symm)

noncomputable def homotopyMulEquiv (d : ℕ) [NeZero d] (x : X) :
    HomotopyGroup (Fin d) (Path x x) (Path.refl x) ≃* HomotopyGroup (Fin (d + 1)) X x where
  toEquiv := homotopyEquiv d x
  map_mul' := homotopyEquiv_mul

end NoExoticSixSphere.GeneralizedLoopCurrying
