import Wikipedia.HopfProblem.FundamentalGroupVanKampenSquarePaths

/-!
# Cancellation along a subdivided homotopy square

The ordered-subpath law turns the boundary equations of adjacent
rectangles into the boundary equation for an entire strip.  This is a
finite induction in an arbitrary, possibly noncommutative, group.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

namespace PathValue

variable (V : PathValue X G)

/-- Every literally constant path has value one, including paths whose
endpoint indices are presented by different equal expressions. -/
theorem value_eq_one_of_constant {x y : X} (p : Path x y)
    (hp : ∀ t, p t = x) : V.value p = 1 := by
  have hy : y = x := p.target.symm.trans (hp 1)
  subst y
  have heq : p = Path.refl x := by
    ext t
    exact hp t
  rw [heq, V.refl]

/-- The rectangle equations telescope across every finite row of a grid. -/
theorem square_strip (F : C(I × I, X)) (s t : I) (d : ℕ → I)
    (hmono : Monotone d) (n : ℕ)
    (hcell : ∀ k < n,
      V.value ((squareHorizontal F s).subpath (d k) (d (k + 1))) *
          V.value ((squareVertical F (d (k + 1))).subpath s t) =
        V.value ((squareVertical F (d k)).subpath s t) *
          V.value ((squareHorizontal F t).subpath (d k) (d (k + 1)))) :
    V.value ((squareHorizontal F s).subpath (d 0) (d n)) *
        V.value ((squareVertical F (d n)).subpath s t) =
      V.value ((squareVertical F (d 0)).subpath s t) *
        V.value ((squareHorizontal F t).subpath (d 0) (d n)) := by
  induction n with
  | zero => simp only [Path.subpath_self, V.refl, one_mul, mul_one]
  | succ n ih =>
    have hprev := ih (fun k hk => hcell k (Nat.lt_succ_of_lt hk))
    rw [V.subpath_mul _ (d 0) (d n) (d (n + 1))
        (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),
      V.subpath_mul _ (d 0) (d n) (d (n + 1))
        (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))]
    calc
      _ = V.value ((squareHorizontal F s).subpath (d 0) (d n)) *
          (V.value ((squareHorizontal F s).subpath (d n) (d (n + 1))) *
            V.value ((squareVertical F (d (n + 1))).subpath s t)) :=
        mul_assoc _ _ _
      _ = V.value ((squareHorizontal F s).subpath (d 0) (d n)) *
          (V.value ((squareVertical F (d n)).subpath s t) *
            V.value ((squareHorizontal F t).subpath (d n) (d (n + 1)))) := by
        rw [hcell n (Nat.lt_succ_self n)]
      _ = (V.value ((squareHorizontal F s).subpath (d 0) (d n)) *
          V.value ((squareVertical F (d n)).subpath s t)) *
            V.value ((squareHorizontal F t).subpath (d n) (d (n + 1))) :=
        (mul_assoc _ _ _).symm
      _ = (V.value ((squareVertical F (d 0)).subpath s t) *
          V.value ((squareHorizontal F t).subpath (d 0) (d n))) *
            V.value ((squareHorizontal F t).subpath (d n) (d (n + 1))) := by
        rw [hprev]
      _ = _ := mul_assoc _ _ _

/-- A horizontal slice of a path homotopy is its usual evaluated path,
up to the harmless endpoint equalities. -/
theorem value_squareHorizontal_homotopy {x y : X} {p q : Path x y}
    (H : Path.Homotopy p q) (s : I) :
    V.value (squareHorizontal H.toContinuousMap s) = V.value (H.eval s) := by
  have heq : squareHorizontal H.toContinuousMap s =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  rw [heq, V.value_cast]

/-- The left side of an endpoint-preserving homotopy is constant. -/
theorem value_squareVertical_homotopy_zero {x y : X} {p q : Path x y}
    (H : Path.Homotopy p q) (s t : I) :
    V.value ((squareVertical H.toContinuousMap 0).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 0) = H (s, 0)
  simp only [Path.Homotopy.source]

/-- The right side of an endpoint-preserving homotopy is constant. -/
theorem value_squareVertical_homotopy_one {x y : X} {p q : Path x y}
    (H : Path.Homotopy p q) (s t : I) :
    V.value ((squareVertical H.toContinuousMap 1).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 1) = H (s, 1)
  simp only [Path.Homotopy.target]

end PathValue

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
