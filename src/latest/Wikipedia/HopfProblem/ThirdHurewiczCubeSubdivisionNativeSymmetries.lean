import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeSymmetriesRotation
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic
import Mathlib.GroupTheory.Perm.Sign

/-!
# The sign of an input-coordinate permutation on native third homotopy

Precomposition is defined by `u ↦ (fun i => u (e i))`. A transposition is
the composition of a genuine coordinate-plane rotation and a reversal in
one coordinate. The native inverse law then gives its negative sign, and
swap induction gives the sign formula for every permutation. No Hurewicz,
degree, connectedness, or homology calculation enters this argument.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

/-- The input-coordinate permutation convention used throughout this file. -/
def permuteCubeCoordinates (e : Equiv.Perm (Fin 3)) : C(Fin 3 → I, Fin 3 → I) where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

theorem permuteCubeCoordinates_boundary (e : Equiv.Perm (Fin 3))
    (u : Fin 3 → I) (hu : u ∈ Cube.boundary (Fin 3)) :
    permuteCubeCoordinates e u ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Literal precomposition of a native generalized three-loop by the input
permutation, without changing the physical target or its coordinates. -/
def permuteCubeLoop (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    GenLoop (Fin 3) X x :=
  ⟨p.val.comp (permuteCubeCoordinates e),
    fun u hu => p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp] theorem permuteCubeLoop_apply (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (u : Fin 3 → I) :
    permuteCubeLoop p e u = p (fun i => u (e i)) := rfl

@[simp] theorem permuteCubeLoop_one (p : GenLoop (Fin 3) X x) :
    permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

/-- With the stated input convention the second pullback appears on the
left of the product of permutations. -/
theorem permuteCubeLoop_mul (p : GenLoop (Fin 3) X x)
    (e f : Equiv.Perm (Fin 3)) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

/-- A swap followed by reversal along the first chosen input coordinate is
literally the already-constructed quarter turn. -/
theorem nativeCubeQuarterTurnLoop_eq_symmAt_permute (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
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

/-- A genuine coordinate-plane quarter turn preserves the native additive class. -/
theorem nativeCubeClass_quarterTurn (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeCubeClass p :=
  nativeCubeQuarterTurnLoop_additiveClass p i j hij

/-- The transposition sign in additive notation for the actual third homotopy group. -/
theorem permuteCubeLoop_swap_additiveClass (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeCubeClass p := by
  have h := nativeCubeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeCubeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

/-- Swapping two distinct input coordinates is the native group inverse. -/
theorem permuteCubeLoop_swap_class (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    (⟦permuteCubeLoop p (Equiv.swap i j)⟧ : π_ 3 X x) =
      ((·⁻¹) : π_ 3 X x → π_ 3 X x) ⟦p⟧ :=
  congrArg Additive.toMul (permuteCubeLoop_swap_additiveClass p i j hij)

/-- Every input-coordinate permutation acts by its parity on native `π₃`. -/
theorem permuteCubeLoop_additiveClass (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (permuteCubeLoop p e) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

/-- In particular, exchanging the first two coordinates negates the native class. -/
theorem permuteCubeLoop_swap01_additiveClass (p : GenLoop (Fin 3) X x) :
    nativeCubeClass (permuteCubeLoop p (Equiv.swap 0 1)) = -nativeCubeClass p :=
  permuteCubeLoop_swap_additiveClass p 0 1 (by decide)

/-- Exchanging the last two coordinates also negates the native class. -/
theorem permuteCubeLoop_swap12_additiveClass (p : GenLoop (Fin 3) X x) :
    nativeCubeClass (permuteCubeLoop p (Equiv.swap 1 2)) = -nativeCubeClass p :=
  permuteCubeLoop_swap_additiveClass p 1 2 (by decide)

/-- The cycle taking an input to `[u₁,u₂,u₀]`. -/
def nativeCubeCycle120 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The cycle taking an input to `[u₂,u₀,u₁]`. -/
def nativeCubeCycle201 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

@[simp] theorem permuteCubeLoop_cycle120_apply (p : GenLoop (Fin 3) X x)
    (u : Fin 3 → I) : permuteCubeLoop p nativeCubeCycle120 u = p ![u 1, u 2, u 0] := by
  rw [permuteCubeLoop_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem permuteCubeLoop_cycle201_apply (p : GenLoop (Fin 3) X x)
    (u : Fin 3 → I) : permuteCubeLoop p nativeCubeCycle201 u = p ![u 2, u 0, u 1] := by
  rw [permuteCubeLoop_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem permuteCubeLoop_cycle120_additiveClass (p : GenLoop (Fin 3) X x) :
    nativeCubeClass (permuteCubeLoop p nativeCubeCycle120) = nativeCubeClass p := by
  rw [nativeCubeCycle120, permuteCubeLoop_mul, permuteCubeLoop_swap01_additiveClass,
    permuteCubeLoop_swap12_additiveClass, neg_neg]

theorem permuteCubeLoop_cycle201_additiveClass (p : GenLoop (Fin 3) X x) :
    nativeCubeClass (permuteCubeLoop p nativeCubeCycle201) = nativeCubeClass p := by
  rw [nativeCubeCycle201, permuteCubeLoop_mul, permuteCubeLoop_swap12_additiveClass,
    permuteCubeLoop_swap01_additiveClass, neg_neg]

end Wikipedia.HopfProblem.ThirdHurewicz
