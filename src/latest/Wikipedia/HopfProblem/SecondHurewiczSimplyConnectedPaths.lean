import Wikipedia.HopfProblem.SecondHurewicz
import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths

/-!
# Normalized path choices for simply-connected singular-chain straightening

The choices below are actual paths and actual homotopies. The path at the
base point is the constant path, and the chosen nullhomotopy of a constant
loop is constant. These normalizations will keep already-based faces fixed
when extending the homotopies over higher-dimensional simplices.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- An actual singular edge with prescribed equal endpoints, viewed as a based path. -/
def basedEdgePath (x : X) (smp : C(Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : Path x x :=
  (simplexPath smp).cast h₀.symm h₁.symm

@[simp] theorem basedEdgePath_apply (x : X) (smp : C(Simplex 1, X)) (h₀ h₁) (t : I) :
    basedEdgePath x smp h₀ h₁ t = smp (stdSimplexHomeomorphUnitInterval.symm t) := rfl

@[simp] theorem basedEdgePath_const (x : X) :
    basedEdgePath x (ContinuousMap.const (Simplex 1) x) rfl rfl = Path.refl x := by
  apply Path.ext
  funext t
  rfl

variable [SimplyConnectedSpace X]

/-- A chosen path to the base point, normalized to be constant at that point. -/
def chosenBasePath (x y : X) : Path y x := by
  classical
  exact if h : y = x then (Path.refl x).cast h rfl else
    PathConnectedSpace.somePath y x

@[simp] theorem chosenBasePath_self (x : X) : chosenBasePath x x = Path.refl x := by
  simp [chosenBasePath]

/-- A genuine nullhomotopy supplied by simple connectedness, normalized
to be the literal constant homotopy for a constant loop. -/
def chosenNullHomotopy (x : X) (p : Path x x) : p.Homotopy (Path.refl x) := by
  classical
  exact if h : p = Path.refl x then (Path.Homotopy.refl (Path.refl x)).cast h.symm rfl
    else Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl x))

@[simp] theorem chosenNullHomotopy_refl (x : X) :
    chosenNullHomotopy x (Path.refl x) = Path.Homotopy.refl (Path.refl x) := by
  simp [chosenNullHomotopy]
  rfl

/-- The actual vertex homotopy, from its original value to the base point. -/
def vertexHomotopy (x : X) (smp : C(Simplex 0, X)) : C(I × Simplex 0, X) :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C(I × Simplex 0, I))

@[simp] theorem vertexHomotopy_zero (x : X) (smp : C(Simplex 0, X)) (s : Simplex 0) :
    vertexHomotopy x smp (0, s) = smp s := by
  change chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, simplexZero_eq_vertex s]

@[simp] theorem vertexHomotopy_one (x : X) (smp : C(Simplex 0, X)) (s : Simplex 0) :
    vertexHomotopy x smp (1, s) = x :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

@[simp] theorem vertexHomotopy_const (x : X) :
    vertexHomotopy x (ContinuousMap.const (Simplex 0) x) =
      ContinuousMap.const (I × Simplex 0) x := by
  ext t
  change chosenBasePath x x t.1 = x
  rw [chosenBasePath_self]
  rfl

/-- The endpoint-fixed nullhomotopy of an actual singular edge whose
two vertices already equal the base point. -/
def edgeNullHomotopy (x : X) (smp : C(Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : C(I × Simplex 1, X) :=
  (chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)).toContinuousMap.comp
    ((ContinuousMap.id I).prodMap
      ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

@[simp] theorem edgeNullHomotopy_zero (x : X) (smp : C(Simplex 1, X)) (h₀ h₁)
    (s : Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (0, s) = smp s := by
  change chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)
    (0, stdSimplexHomeomorphUnitInterval s) = smp s
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change smp (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = smp s
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

@[simp] theorem edgeNullHomotopy_one (x : X) (smp : C(Simplex 1, X)) (h₀ h₁)
    (s : Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (1, s) = x := by
  change chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)
    (1, stdSimplexHomeomorphUnitInterval s) = x
  rw [ContinuousMap.HomotopyWith.apply_one]
  rfl

@[simp] theorem edgeNullHomotopy_vertex_zero (x : X) (smp : C(Simplex 1, X)) (h₀ h₁)
    (t : I) : edgeNullHomotopy x smp h₀ h₁
      (t, stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)
    (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero]
  exact Path.Homotopy.source _ t

@[simp] theorem edgeNullHomotopy_vertex_one (x : X) (smp : C(Simplex 1, X)) (h₀ h₁)
    (t : I) : edgeNullHomotopy x smp h₀ h₁
      (t, stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := by
  change chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)
    (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_one]
  exact Path.Homotopy.target _ t

@[simp] theorem edgeNullHomotopy_const (x : X) :
    edgeNullHomotopy x (ContinuousMap.const (Simplex 1) x) rfl rfl =
      ContinuousMap.const (I × Simplex 1) x := by
  ext t
  change chosenNullHomotopy x (basedEdgePath x (ContinuousMap.const (Simplex 1) x)
    rfl rfl) (t.1, stdSimplexHomeomorphUnitInterval t.2) = x
  rw [basedEdgePath_const, chosenNullHomotopy_refl]
  rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
