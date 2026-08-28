import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationGenerators

/-!
# The odd vertex orders in the four-simplex boundary relation

These signs hold in Mathlib's native third homotopy group. The generators
were proved using actual cube-boundary-relative homotopies. In particular,
the vertex order `1,3,0,2` has the inverse coefficient order `2,0,3,1`.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

/-- Exchange the first two vertices; coefficient order `1,0,2,3`. -/
def threeSimplexSwapFirst : C(Simplex 3, Simplex 3) :=
  threeSimplexCycle.comp (threeSimplexCycle.comp (threeSimplexSwapLast.comp
    (threeSimplexCycle.comp threeSimplexCycle)))

@[simp] theorem threeSimplexSwapFirst_zero (s : Simplex 3) :
    threeSimplexSwapFirst s 0 = s 1 := rfl

@[simp] theorem threeSimplexSwapFirst_one (s : Simplex 3) :
    threeSimplexSwapFirst s 1 = s 0 := rfl

@[simp] theorem threeSimplexSwapFirst_two (s : Simplex 3) :
    threeSimplexSwapFirst s 2 = s 2 := rfl

@[simp] theorem threeSimplexSwapFirst_three (s : Simplex 3) :
    threeSimplexSwapFirst s 3 = s 3 := rfl

theorem threeSimplexSwapFirst_coefficients (s : Simplex 3) :
    (threeSimplexSwapFirst s : Fin 4 → ℝ) = ![s 1, s 0, s 2, s 3] := by
  funext i
  fin_cases i <;> rfl

theorem threeSimplexSwapFirst_boundary (s : Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapFirst s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _ (threeSimplexCycle_boundary _
    (threeSimplexSwapLast_boundary _ (threeSimplexCycle_boundary _
      (threeSimplexCycle_boundary _ hs))))

/-- The actual vertex order `1,3,0,2`, with coefficient order `2,0,3,1`. -/
def threeSimplexVertexOrder1302 : C(Simplex 3, Simplex 3) :=
  threeSimplexCycle.comp (threeSimplexSwapLast.comp threeSimplexCycle)

@[simp] theorem threeSimplexVertexOrder1302_zero (s : Simplex 3) :
    threeSimplexVertexOrder1302 s 0 = s 2 := rfl

@[simp] theorem threeSimplexVertexOrder1302_one (s : Simplex 3) :
    threeSimplexVertexOrder1302 s 1 = s 0 := rfl

@[simp] theorem threeSimplexVertexOrder1302_two (s : Simplex 3) :
    threeSimplexVertexOrder1302 s 2 = s 3 := rfl

@[simp] theorem threeSimplexVertexOrder1302_three (s : Simplex 3) :
    threeSimplexVertexOrder1302 s 3 = s 1 := rfl

theorem threeSimplexVertexOrder1302_coefficients (s : Simplex 3) :
    (threeSimplexVertexOrder1302 s : Fin 4 → ℝ) = ![s 2, s 0, s 3, s 1] := by
  funext i
  fin_cases i <;> rfl

theorem threeSimplexVertexOrder1302_boundary (s : Simplex 3)
    (hs : s ∈ threeSimplexBoundary) :
    threeSimplexVertexOrder1302 s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _ (threeSimplexSwapLast_boundary _
    (threeSimplexCycle_boundary _ hs))

variable {X : Type} [TopologicalSpace X] {x : X}

/-- An actual based simplex precomposed with the first vertex transposition. -/
def basedThreeSimplexSwapFirst (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapFirst,
    fun s hs => τ.property _ (threeSimplexSwapFirst_boundary s hs)⟩

@[simp] theorem basedThreeSimplexSwapFirst_apply (τ : BasedThreeSimplex x)
    (s : Simplex 3) : (basedThreeSimplexSwapFirst τ).val s =
      τ.val (threeSimplexSwapFirst s) := rfl

theorem basedThreeSimplexSwapFirst_word (τ : BasedThreeSimplex x) :
    basedThreeSimplexSwapFirst τ = basedThreeSimplexVertexCycle (basedThreeSimplexVertexCycle
      (basedThreeSimplexSwapLast
        (basedThreeSimplexVertexCycle (basedThreeSimplexVertexCycle τ)))) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

/-- Swapping vertices zero and one negates the actual native class. -/
@[simp] theorem basedThreeSimplexSwapFirst_class (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapFirst τ) = -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexSwapFirst_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

/-- An actual based simplex with ordered vertex images `1,3,0,2`. -/
def basedThreeSimplexVertexOrder1302 (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexVertexOrder1302,
    fun s hs => τ.property _ (threeSimplexVertexOrder1302_boundary s hs)⟩

@[simp] theorem basedThreeSimplexVertexOrder1302_apply (τ : BasedThreeSimplex x)
    (s : Simplex 3) : (basedThreeSimplexVertexOrder1302 τ).val s =
      τ.val (threeSimplexVertexOrder1302 s) := rfl

theorem basedThreeSimplexVertexOrder1302_word (τ : BasedThreeSimplex x) :
    basedThreeSimplexVertexOrder1302 τ =
      basedThreeSimplexVertexCycle
        (basedThreeSimplexSwapLast (basedThreeSimplexVertexCycle τ)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

/-- The odd vertex order `1,3,0,2` negates the actual native class. -/
@[simp] theorem basedThreeSimplexVertexOrder1302_class (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexOrder1302 τ) =
      -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexVertexOrder1302_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

end Wikipedia.HopfProblem.ThirdHurewicz
