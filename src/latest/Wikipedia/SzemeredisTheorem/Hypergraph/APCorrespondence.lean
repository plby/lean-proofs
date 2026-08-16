import Wikipedia.SzemeredisTheorem.Hypergraph.Simplex

/-!
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Sum of the free coordinates in a fiber of the AP parameter map. -/
def simplexTailSum (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i

/-- First moment of the free coordinates, using their actual positions
`2, ..., r + 1` in the full simplex vector. -/
def simplexTailMoment (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i

/-- Reconstruct simplex coordinates from a cyclic initial term `a`, common
difference `d`, and the remaining `r` free coordinates. -/
def simplexCoordinatesOfAP (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (simplexTailMoment r N y - a - d - simplexTailSum r N y)
    (Fin.cases (a - simplexTailMoment r N y) y)

@[simp]
theorem simplexCoordinatesOfAP_zero (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 0 =
      simplexTailMoment r N y - a - d - simplexTailSum r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_one (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 1 =
      a - simplexTailMoment r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_succ_succ (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    simplexCoordinatesOfAP r N a d y i.succ.succ = y i :=
  rfl

/-- Split the coordinate sum into the first two and the free tail. -/
theorem simplexCoordinateSum_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateSum (r + 2) N x =
      x 0 + x 1 +
        simplexTailSum r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateSum, simplexTailSum, Fin.sum_univ_succ,
    add_assoc]

/-- Split the coordinate moment into coordinate one and the free tail;
coordinate zero has coefficient zero. -/
theorem simplexCoordinateMoment_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateMoment (r + 2) N x =
      x 1 + simplexTailMoment r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateMoment, simplexTailMoment,
    Fin.sum_univ_succ]

@[simp]
theorem simplexCoordinateSum_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateSum (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = -d := by
  rw [simplexCoordinateSum_decompose]
  simp
  ring

@[simp]
theorem simplexCoordinateMoment_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateMoment (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = a := by
  rw [simplexCoordinateMoment_decompose]
  simp

/-- The exact coordinate change: AP parameters, together with `r` free
coordinates, are equivalent to simplex coordinates of length `r + 2`. -/
def simplexAPEquiv (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((simplexCoordinateMoment (r + 2) N x,
      -simplexCoordinateSum (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := simplexCoordinatesOfAP r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [simplexCoordinatesOfAP_zero,
        simplexCoordinateMoment_decompose,
        simplexCoordinateSum_decompose]
      ring
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [simplexCoordinatesOfAP_one,
        simplexCoordinateMoment_decompose]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          simplexCoordinateMoment (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            a
        exact simplexCoordinateMoment_coordinatesOfAP r N a d tail
      · change
          -simplexCoordinateSum (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            d
        rw [simplexCoordinateSum_coordinatesOfAP]
        simp
    · funext i
      change simplexCoordinatesOfAP r N a d tail i.succ.succ = tail i
      exact simplexCoordinatesOfAP_succ_succ r N a d tail i

/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

/-- A normalized average over a product is the corresponding iterated
normalized average. -/
theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

/-- Averaging a function that ignores a nonempty product coordinate does
not change its normalized average. -/
theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]

/-- Exact normalized AP/simplex count correspondence.  The extra `r`
simplex coordinates form a uniform fiber over every pair `(a, d)`, so
normalization removes that fiber with no cardinality factor. -/
theorem apSimplexSystem_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by
  rw [WeightedSimplexSystem.simplexCount, cyclicAPCount]
  calc
    mean (apSimplexSystem (r + 2) N f).simplexWeight =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cyclicAPProduct (r + 2) N f
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact apSimplexSystem_simplexWeight (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cyclicAPProduct (r + 2) N f y.1.1 y.1.2) := by
      apply mean_equiv (simplexAPEquiv r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2) := by
      exact mean_prod_fst
        (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2)
    _ =
        mean₂ (fun a d =>
          cyclicAPProduct (r + 2) N f a d) := by
      exact mean_prod
        (fun a d => cyclicAPProduct (r + 2) N f a d)

end Wikipedia.SzemeredisTheorem
