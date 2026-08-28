import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetriesRotation
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation signs on native homotopy groups in every finite dimension

Precomposition is defined by `u ↦ (fun i => u (e i))`. A transposition is
the composition of a boundary-preserving coordinate-plane rotation and a
reversal in one coordinate. The native inverse law gives its negative sign;
swap induction then proves the orientation formula for every permutation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {N : Type*}

/-- Input-coordinate permutations, with the same convention in every dimension. -/
def permuteCubeCoordinates (e : Equiv.Perm N) : C(N → I, N → I) where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

theorem permuteCubeCoordinates_boundary (e : Equiv.Perm N)
    (u : N → I) (hu : u ∈ Cube.boundary N) :
    permuteCubeCoordinates e u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Literal precomposition of a native generalized loop by an input permutation. -/
def permuteCubeLoop (p : GenLoop N X x) (e : Equiv.Perm N) : GenLoop N X x :=
  ⟨p.val.comp (permuteCubeCoordinates e),
    fun u hu => p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp] theorem permuteCubeLoop_apply (p : GenLoop N X x)
    (e : Equiv.Perm N) (u : N → I) :
    permuteCubeLoop p e u = p (fun i => u (e i)) := rfl

@[simp] theorem permuteCubeLoop_one (p : GenLoop N X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

/-- The second pullback appears on the left of the product of permutations. -/
theorem permuteCubeLoop_mul (p : GenLoop N X x) (e f : Equiv.Perm N) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

variable [DecidableEq N]

/-- A swap followed by one input-coordinate reversal is literally the quarter turn. -/
theorem nativeCubeQuarterTurnLoop_eq_symmAt_permute (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij =
      GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) := by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change p (fun k => if k = i then u j else if k = j then σ (u i) else u k) =
    p (fun k => if Equiv.swap i j k = i then σ (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

/-- A coordinate-plane quarter turn preserves the actual native class. -/
theorem nativeClass_quarterTurn (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    nativeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeClass p :=
  (nativeClass_homotopic ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩).symm

variable [Nontrivial N]

/-- Exchanging distinct coordinates negates the native additive class. -/
theorem permuteCubeLoop_swap_additiveClass (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) :
    nativeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeClass p := by
  have h := nativeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

/-- Swapping two distinct input coordinates is the native group inverse. -/
theorem permuteCubeLoop_swap_class (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    (⟦permuteCubeLoop p (Equiv.swap i j)⟧ : HomotopyGroup N X x) =
      ((·⁻¹) : HomotopyGroup N X x → HomotopyGroup N X x) ⟦p⟧ :=
  congrArg Additive.toMul (permuteCubeLoop_swap_additiveClass p i j hij)

/-- Every finite input-coordinate permutation acts by its parity on the native group. -/
theorem permuteCubeLoop_additiveClass [Fintype N] (p : GenLoop N X x)
    (e : Equiv.Perm N) :
    nativeClass (permuteCubeLoop p e) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
