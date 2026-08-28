import Wikipedia.HopfProblem.FirstHurewiczChainNaturality

/-!
# Point insertions for actual singular cross products

An actual singular zero-simplex is constant. Inserting its value into one
factor gives the literal degree-zero factors of the singular cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The point represented by an actual singular zero-simplex. -/
def zeroSimplexValue (σ : SingularSimplex X 0) : X :=
  σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))

theorem zeroSimplex_apply (σ : SingularSimplex X 0) (t : Simplex 0) :
    σ t = zeroSimplexValue σ := by
  rw [simplexZero_eq_vertex t]
  rfl

@[simp] theorem zeroSimplexValue_comp (f : C(X, X')) (σ : SingularSimplex X 0) :
    zeroSimplexValue (f.comp σ) = f (zeroSimplexValue σ) := rfl

/-- Insert a fixed point in the left factor of a product. -/
def crossInsertLeft (x : X) : C(Y, X × Y) :=
  ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

/-- Insert a fixed point in the right factor of a product. -/
def crossInsertRight (y : Y) : C(X, X × Y) :=
  ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

@[simp] theorem crossInsertLeft_apply (x : X) (y : Y) : crossInsertLeft x y = (x, y) := rfl

@[simp] theorem crossInsertRight_apply (y : Y) (x : X) : crossInsertRight y x = (x, y) := rfl

theorem crossInsertLeft_natural (f : C(X, X')) (g : C(Y, Y')) (x : X) :
    (f.prodMap g).comp (crossInsertLeft x) = (crossInsertLeft (f x)).comp g := rfl

theorem crossInsertRight_natural (f : C(X, X')) (g : C(Y, Y')) (y : Y) :
    (f.prodMap g).comp (crossInsertRight y) = (crossInsertRight (g y)).comp f := rfl

/-- Naturality of left insertion on actual singular chains. -/
theorem inducedChain_crossInsertLeft (f : C(X, X')) (g : C(Y, Y'))
    (x : X) (n : ℕ) (c : Chains Y n) :
    inducedChain (f.prodMap g) n (inducedChain (crossInsertLeft x) n c) =
      inducedChain (crossInsertLeft (f x)) n (inducedChain g n c) := by
  have h := congrArg (fun h : C(Y, X' × Y') => inducedChain h n c)
    (crossInsertLeft_natural f g x)
  simpa only [inducedChain_comp, LinearMap.comp_apply] using h

/-- Naturality of right insertion on actual singular chains. -/
theorem inducedChain_crossInsertRight (f : C(X, X')) (g : C(Y, Y'))
    (y : Y) (n : ℕ) (c : Chains X n) :
    inducedChain (f.prodMap g) n (inducedChain (crossInsertRight y) n c) =
      inducedChain (crossInsertRight (g y)) n (inducedChain f n c) := by
  have h := congrArg (fun h : C(X, X' × Y') => inducedChain h n c)
    (crossInsertRight_natural f g y)
  simpa only [inducedChain_comp, LinearMap.comp_apply] using h

/-- Swapping product factors carries literal left insertion to right insertion. -/
theorem crossInsertLeft_swap (x : X) :
    ContinuousMap.prodSwap.comp (crossInsertLeft (Y := Y) x) = crossInsertRight x := rfl

/-- Swapping product factors carries literal right insertion to left insertion. -/
theorem crossInsertRight_swap (y : Y) :
    ContinuousMap.prodSwap.comp (crossInsertRight (X := X) y) = crossInsertLeft y := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
