import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerBased

/-!
# Whiskering as an actual continuous cube of native loops

The target is Mathlib's native one-dimensional generalized-loop space
with its compact-open topology. Its whole codimension-two boundary is the
literal constant loop, including in the low-dimensional edge cases.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual native loop obtained by evaluating a cell along its whisker. -/
def whiskeredLoop (F : BasedCubicalCell (n + 2) x) (u : Fin (n + 1) → I) :
    GenLoop (Fin 1) X x :=
  ⟨⟨fun q => F.val (whiskerMap n (u, q 0)), by fun_prop⟩, by
    intro q hq
    obtain ⟨i, hi⟩ := hq
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    rcases hi with hi | hi
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_start]
      exact whiskerCorner_based F 0 (Or.inl rfl) (Fin.init u)
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_finish]
      exact whiskerCorner_based F 1 (Or.inr rfl) (Fin.init u)⟩

@[simp] theorem whiskeredLoop_apply (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (q : Fin 1 → I) :
    whiskeredLoop F u q = F.val (whiskerMap n (u, q 0)) := rfl

/-- The whiskered loops vary continuously in the actual compact-open topology. -/
def whiskeredLoopMap (F : BasedCubicalCell (n + 2) x) :
    C(Fin (n + 1) → I, GenLoop (Fin 1) X x) where
  toFun := whiskeredLoop F
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (Fin (n + 1) → I) × (Fin 1 → I) =>
      F.val (whiskerMap n (z.1, z.2 0)))
    exact F.val.continuous.comp ((whiskerMap n).continuous.comp (by fun_prop))

/-- Whiskering lowers the cell dimension by one and raises the loop-space degree. -/
def whiskeredCell (F : BasedCubicalCell (n + 2) x) :
    BasedCubicalCell (n + 1) (GenLoop.const : GenLoop (Fin 1) X x) :=
  ⟨whiskeredLoopMap F, by
    intro u i j hij hi hj
    apply GenLoop.ext
    intro q
    exact whiskerMap_codimTwo_based F u (q 0) i j hij hi hj⟩

@[simp] theorem whiskeredCell_apply (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (q : Fin 1 → I) :
    (whiskeredCell F).val u q = F.val (whiskerMap n (u, q 0)) := rfl

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
