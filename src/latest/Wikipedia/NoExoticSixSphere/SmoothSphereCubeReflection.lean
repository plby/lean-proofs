import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy

/-!
# Actual sphere reflections descended from native cube reversal

The map is obtained from the original smooth-interior cube quotient,
not from a chosen degree marking. Its literal cube formula identifies
precomposition with native reversal, hence with group inversion.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SmoothCube

def reflection (n : ℕ) (hn : 0 < n) (i : Fin n) : C(Sphere n, Sphere n) :=
  descend hn (GenLoop.symmAt i (toGenLoop ⟨ContinuousMap.id _, rfl⟩))

theorem reflection_quotient (n : ℕ) (hn : 0 < n) (i : Fin n) (u : Fin n → I) :
    reflection n hn i (quotient n u) =
      quotient n (fun j ↦ if j = i then σ (u i) else u j) :=
  descend_quotient hn _ u

theorem reflection_pole (n : ℕ) (hn : 0 < n) (i : Fin n) :
    reflection n hn i (spherePole n) = spherePole n := descend_pole hn _

theorem reflection_involutive (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Function.Involutive (reflection n hn i) := by
  intro x
  obtain ⟨u, rfl⟩ := quotient_surjective hn x
  rw [reflection_quotient, reflection_quotient]
  apply congrArg (quotient n)
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true, unitInterval.symm_symm]
  · simp only [if_neg hj]

def reflectionHomeomorph (n : ℕ) (hn : 0 < n) (i : Fin n) : Sphere n ≃ₜ Sphere n where
  toFun := reflection n hn i
  invFun := reflection n hn i
  left_inv := reflection_involutive n hn i
  right_inv := reflection_involutive n hn i
  continuous_toFun := (reflection n hn i).continuous
  continuous_invFun := (reflection n hn i).continuous

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

def reflected (hn : 0 < n) (i : Fin n) (f : BasedMap n X x) : BasedMap n X x :=
  ⟨f.val.comp (reflection n hn i), (congrArg f.val (reflection_pole n hn i)).trans f.property⟩

theorem reflected_toGenLoop (hn : 0 < n) (i : Fin n) (f : BasedMap n X x) :
    toGenLoop (reflected hn i f) = GenLoop.symmAt i (toGenLoop f) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  exact congrArg f.val (reflection_quotient n hn i u)

theorem reflected_sphereClass [NeZero n] (hn : 0 < n) (i : Fin n) (f : BasedMap n X x) :
    sphereClass (reflected hn i f) = (sphereClass f)⁻¹ := by
  change (Quotient.mk' (toGenLoop (reflected hn i f)) : π_ n X x) = _
  rw [reflected_toGenLoop]
  exact (HomotopyGroup.inv_spec (i := i) (p := toGenLoop f)).symm

end NoExoticSixSphere.SmoothCube
