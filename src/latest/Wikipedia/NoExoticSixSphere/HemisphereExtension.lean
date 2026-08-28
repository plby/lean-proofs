import Wikipedia.NoExoticSixSphere.HemisphereCone

/-!
# Extending a nullhomotopic equator map across a hemisphere

A nullhomotopy is constant on each fiber of the explicit cone quotient, and
therefore descends continuously. This proves the extension step; it does not
assert nullhomotopy for any particular general-linear-group-valued map.
-/

open unitInterval

namespace NoExoticSixSphere

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y]

namespace HemisphereCone

variable (v : UnitSphere E) (f : C(Equator v, Y)) (c : Y)
  (H : f.Homotopy (ContinuousMap.const _ c))

/-- A nullhomotopy is constant on all fibers of the cone quotient. -/
theorem homotopy_eq_of_point_eq (p q : I × Equator v) (hpq : point v p = point v q) :
    H p = H q := by
  rcases point_fibers v p q hpq with h | ⟨hp, hq⟩
  · exact congrArg H h
  · have hp' : p = (1, p.2) := Prod.ext hp rfl
    have hq' : q = (1, q.2) := Prod.ext hq rfl
    rw [hp', hq', H.apply_one, H.apply_one]
    rfl

variable [Nonempty (Equator v)]

/-- The nullhomotopy descended as a function on the hemisphere. -/
noncomputable def extensionFun (x : ClosedHemisphere v) : Y :=
  H (Function.surjInv (surjective_point v) x)

/-- The descended function evaluates to the homotopy on every cone representative. -/
theorem extensionFun_point (p : I × Equator v) : extensionFun v f c H (point v p) = H p :=
  homotopy_eq_of_point_eq v f c H _ p (Function.surjInv_eq (surjective_point v) (point v p))

/-- A nullhomotopy extends continuously across the northern closed hemisphere. -/
noncomputable def extension [FiniteDimensional ℝ E] : C(ClosedHemisphere v, Y) where
  toFun := extensionFun v f c H
  continuous_toFun := by
    apply (isQuotientMap_point v).continuous_iff.mpr
    have heq : extensionFun v f c H ∘ point v = H := funext (extensionFun_point v f c H)
    rw [heq]
    exact H.continuous

/-- The extension agrees exactly with the original equator map, not just up to homotopy. -/
theorem extension_boundary [FiniteDimensional ℝ E] (x : Equator v) :
    extension v f c H (equatorNorth v x) = f x := by
  change extensionFun v f c H (equatorNorth v x) = f x
  rw [← point_zero, extensionFun_point, H.apply_zero]

end HemisphereCone

/-- A nullhomotopy also extends across the southern hemisphere, with the same boundary values. -/
theorem exists_southernExtension_of_nullhomotopy [FiniteDimensional ℝ E]
    (v : UnitSphere E) [Nonempty (Equator v)] (f : C(Equator v, Y)) (c : Y)
    (H : f.Homotopy (ContinuousMap.const _ c)) :
    ∃ g : C(ClosedHemisphere (antipode v), Y), ∀ x : Equator v, g (equatorSouth v x) = f x := by
  let e := equatorAntipode v
  let : Nonempty (Equator (antipode v)) := e.symm.toEquiv.nonempty
  let f' : C(Equator (antipode v), Y) := f.comp ⟨e.symm, e.symm.continuous⟩
  let H' : f'.Homotopy (ContinuousMap.const _ c) := {
    toFun := fun p ↦ H (p.1, e.symm p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
    map_zero_left := fun x ↦ H.apply_zero (e.symm x)
    map_one_left := fun x ↦ H.apply_one (e.symm x) }
  refine ⟨HemisphereCone.extension (antipode v) f' c H', ?_⟩
  intro x
  have heq : equatorSouth v x = equatorNorth (antipode v) (e x) := rfl
  rw [heq, HemisphereCone.extension_boundary]
  change f (e.symm (e x)) = f x
  rw [e.symm_apply_apply]

end NoExoticSixSphere
