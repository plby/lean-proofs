import Wikipedia.NoExoticSixSphere.PartialFrameStableThirdGroup

/-!
# The parity obstruction of an actual third-dimensional frame loop

Evaluate the proved native group isomorphism on the given generalized loop.
The value vanishes exactly when that loop contracts relative to its whole
boundary, and adding a column preserves the value. This is an obstruction
for actual frame maps; no geometric quadratic refinement is asserted here.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

def thirdObstruction (r : ℕ) (a : Space (3 + (r + 2)) (r + 2))
    (p : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) : ZMod 2 :=
  stableThirdHomotopyEquivZModTwo r a (Additive.ofMul (Quotient.mk' p))

theorem thirdObstruction_zero_iff (r : ℕ) (a : Space (3 + (r + 2)) (r + 2))
    (p : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) :
    thirdObstruction r a p = 0 ↔ GenLoop.Homotopic p GenLoop.const := by
  unfold thirdObstruction
  rw [LinearEquiv.map_eq_zero_iff]
  change (Quotient.mk' p : HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) =
    Quotient.mk' GenLoop.const ↔ _
  exact Quotient.eq

theorem thirdObstruction_homotopic (r : ℕ) (a : Space (3 + (r + 2)) (r + 2))
    {p q : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a}
    (h : GenLoop.Homotopic p q) : thirdObstruction r a p = thirdObstruction r a q :=
  congrArg (fun x : HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2)) a ↦
    stableThirdHomotopyEquivZModTwo r a (Additive.ofMul x)) (Quotient.sound h)

theorem zmodTwo_eq_of_zero_iff (x y : ZMod 2) (h : x = 0 ↔ y = 0) : x = y := by
  fin_cases x <;> fin_cases y
  · rfl
  · change (0 : ZMod 2) = 0 ↔ 1 = 0 at h
    exact (one_ne_zero (h.mp rfl)).elim
  · change (1 : ZMod 2) = 0 ↔ 0 = 0 at h
    exact (one_ne_zero (h.mpr rfl)).elim
  · rfl

theorem thirdObstruction_reconstruction_zero_iff (r : ℕ)
    (v : UnitSphere (Vector ((r + 2) + 1)))
    (c : UnitSphere (Vector ((3 + (r + 2)) + 1)))
    (a : Space (3 + (r + 2)) (r + 2))
    (p : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) :
    thirdObstruction (r + 1) (ColumnFiber.reconstruct v c a)
      (HigherHomotopy.genLoopMap (ColumnFiber.reconstructionMap v c) rfl p) = 0 ↔
        thirdObstruction r a p = 0 := by
  rw [thirdObstruction_zero_iff, thirdObstruction_zero_iff]
  constructor
  · intro h
    have he : (Quotient.mk' p : HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) =
        Quotient.mk' GenLoop.const := by
      apply reconstruction_homotopyMap_injective v c (m := 3) (by omega) a
      change Quotient.mk' (HigherHomotopy.genLoopMap (ColumnFiber.reconstructionMap v c) rfl p) =
        Quotient.mk' (HigherHomotopy.genLoopMap
          (ColumnFiber.reconstructionMap v c) rfl GenLoop.const)
      rw [HigherHomotopy.genLoopMap_const]
      exact Quotient.sound h
    exact Quotient.exact he
  · intro h
    obtain ⟨H⟩ := h
    have hend : (ColumnFiber.reconstructionMap v c).comp
        (GenLoop.const : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a).val =
        (GenLoop.const : GenLoop (Fin 3) (Space (3 + ((r + 1) + 2)) ((r + 1) + 2))
          (ColumnFiber.reconstruct v c a)).val := rfl
    exact ⟨(H.compContinuousMap (ColumnFiber.reconstructionMap v c)).cast rfl hend⟩

theorem thirdObstruction_reconstruction (r : ℕ)
    (v : UnitSphere (Vector ((r + 2) + 1)))
    (c : UnitSphere (Vector ((3 + (r + 2)) + 1)))
    (a : Space (3 + (r + 2)) (r + 2))
    (p : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) :
    thirdObstruction (r + 1) (ColumnFiber.reconstruct v c a)
      (HigherHomotopy.genLoopMap (ColumnFiber.reconstructionMap v c) rfl p) =
        thirdObstruction r a p :=
  zmodTwo_eq_of_zero_iff _ _ (thirdObstruction_reconstruction_zero_iff r v c a p)

end NoExoticSixSphere.Stiefel
