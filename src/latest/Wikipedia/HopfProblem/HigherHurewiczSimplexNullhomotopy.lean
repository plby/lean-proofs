import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyHomeomorph
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyNative

/-!
# Relative nullhomotopies of actual simplices from native homotopy vanishing

The proved boundary-preserving simplex-cube homeomorphism turns an actual
based singular simplex into an actual native generalized loop. Triviality
of the native homotopy quotient gives a cube nullhomotopy, and pullback
gives the required simplex nullhomotopy relative to every boundary point.
Literal constant inputs are assigned literal stationary homotopies.

Every dimension is covered, including zero. No comparison isomorphism,
homotopy extension property, or higher-connectivity theorem is an input.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- The actual generalized loop obtained through the proved boundary-preserving homeomorphism. -/
def basedSimplexNativeLoop (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp ⟨(simplexCubeHomeomorph n).symm, (simplexCubeHomeomorph n).symm.continuous⟩,
    fun u hu => τ.property _ ((simplexCubeHomeomorph_symm_boundary_iff n u).mpr hu)⟩

@[simp] theorem basedSimplexNativeLoop_apply (τ : BasedSimplex n x) (u : Fin n → I) :
    basedSimplexNativeLoop τ u = τ.val ((simplexCubeHomeomorph n).symm u) := rfl

/-- Pulling the actual loop back to the simplex recovers the original map exactly. -/
theorem basedSimplexNativeLoop_comp_homeomorph (τ : BasedSimplex n x) :
    (basedSimplexNativeLoop τ).val.comp
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩ = τ.val := by
  apply ContinuousMap.ext
  intro s
  change τ.val ((simplexCubeHomeomorph n).symm (simplexCubeHomeomorph n s)) = τ.val s
  rw [Homeomorph.symm_apply_apply]

variable [Subsingleton (π_ n X x)]

/-- The genuine relative nullhomotopy before constant-input normalization. -/
def simplexNullHomotopyUnnormalized (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) :=
  ContinuousMap.HomotopyRel.cast
    (nativeCubeNullHomotopy_comp (basedSimplexNativeLoop τ)
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
      (SecondHurewicz.SimplyConnected.simplexBoundary n)
      (fun s hs => (simplexCubeHomeomorph_boundary_iff n s).mpr hs))
    (basedSimplexNativeLoop_comp_homeomorph τ) rfl

/-- An actual nullhomotopy relative to the full boundary, stationary on constant inputs. -/
def simplexNullHomotopy (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
  exact if h : τ = constantBasedSimplex n x then
    ContinuousMap.HomotopyRel.cast
      (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (Simplex n) x)
        (SecondHurewicz.SimplyConnected.simplexBoundary n))
      (congrArg (fun υ : BasedSimplex n x => υ.val) h).symm rfl
  else simplexNullHomotopyUnnormalized τ

@[simp] theorem simplexNullHomotopy_zero (τ : BasedSimplex n x) (s : Simplex n) :
    simplexNullHomotopy τ (0, s) = τ.val s :=
  (simplexNullHomotopy τ).apply_zero s

@[simp] theorem simplexNullHomotopy_one (τ : BasedSimplex n x) (s : Simplex n) :
    simplexNullHomotopy τ (1, s) = x :=
  (simplexNullHomotopy τ).apply_one s

theorem simplexNullHomotopy_boundary (τ : BasedSimplex n x) (t : I) (s : Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    simplexNullHomotopy τ (t, s) = x :=
  (simplexNullHomotopy τ).eq_snd t hs

@[simp] theorem simplexNullHomotopy_constant (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] :
    simplexNullHomotopy (constantBasedSimplex n x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (Simplex n) x)
        (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
  unfold simplexNullHomotopy
  rw [dif_pos rfl]
  rfl

@[simp] theorem simplexNullHomotopy_constant_toContinuousMap (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] :
    (simplexNullHomotopy (constantBasedSimplex n x)).toContinuousMap =
      ContinuousMap.const (I × Simplex n) x := by
  rw [simplexNullHomotopy_constant]
  rfl

theorem simplexNullHomotopy_stationary_of_val_eq_const (τ : BasedSimplex n x)
    (hτ : τ.val = ContinuousMap.const (Simplex n) x) :
    (simplexNullHomotopy τ).toContinuousMap = ContinuousMap.const (I × Simplex n) x := by
  have h : τ = constantBasedSimplex n x := Subtype.ext hτ
  rw [h, simplexNullHomotopy_constant_toContinuousMap]

end Wikipedia.HopfProblem.HigherHurewicz
