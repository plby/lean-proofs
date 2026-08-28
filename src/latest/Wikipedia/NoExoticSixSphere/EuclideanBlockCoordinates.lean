import Wikipedia.NoExoticSixSphere.EuclideanBlockInner

/-!
# Exact coordinates of the Euclidean block splitting

The first and second blocks use `Fin.castAdd` and `Fin.natAdd` respectively.
These formulas allow block stabilization to be iterated without replacing
the original coordinate inclusions by unspecified isometries.
-/

noncomputable section

namespace NoExoticSixSphere.EuclideanBlocks

open GLOrthonormalization

theorem fst_apply {n m : ℕ} (x : Vector (n + m)) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd (n := n) (m := m) x).1 i = x (i.castAdd m) := rfl

theorem snd_apply {n m : ℕ} (x : Vector (n + m)) (i : Fin m) :
    (EuclideanSpace.finAddEquivProd (n := n) (m := m) x).2 i = x (i.natAdd n) := rfl

theorem symm_castAdd {n m : ℕ} (u : Vector n) (v : Vector m) (i : Fin n) :
    EuclideanSpace.finAddEquivProd.symm (u, v) (i.castAdd m) = u i := by
  have h := congrArg (fun z : Vector n × Vector m ↦ z.1 i)
    (EuclideanSpace.finAddEquivProd.apply_symm_apply (u, v))
  exact h

theorem symm_natAdd {n m : ℕ} (u : Vector n) (v : Vector m) (i : Fin m) :
    EuclideanSpace.finAddEquivProd.symm (u, v) (i.natAdd n) = v i := by
  have h := congrArg (fun z : Vector n × Vector m ↦ z.2 i)
    (EuclideanSpace.finAddEquivProd.apply_symm_apply (u, v))
  exact h

theorem fst_fst {n m : ℕ} (x : Vector ((n + m) + 1)) :
    (EuclideanSpace.finAddEquivProd (n := n) (m := m)
      (EuclideanSpace.finAddEquivProd (n := n + m) (m := 1) x).1).1 =
        (EuclideanSpace.finAddEquivProd (n := n) (m := m + 1) x).1 := by
  ext i
  rw [fst_apply, fst_apply, fst_apply]
  rfl

end NoExoticSixSphere.EuclideanBlocks
