import Wikipedia.NoExoticSixSphere.RelativeFiberMap

/-!
# Literal cylinder coordinates for a subspace homotopy fiber

A cylinder with its initial face in a subspace and its final face at
the chosen point curries to a map into the actual homotopy fiber.
A homotopy of such cylinders gives a homotopy of those fiber maps.
All constructions keep the original path coordinate.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.RelativeFiberCylinder

open RelativeFiberHomology

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
  (U : Set X) (a : U)

def cylinder (p : C(Z, Fiber U a)) : C(I × Z, X) :=
  (HomotopyFiber.evaluation (subtypeInclusion U) a.val).comp
    ⟨fun z ↦ (z.1, p z.2), continuous_fst.prodMk (p.continuous.comp continuous_snd)⟩

def lift (f : C(I × Z, X)) (h₀ : ∀ z, f (0, z) ∈ U)
    (h₁ : ∀ z, f (1, z) = a.val) : C(Z, Fiber U a) :=
  HomotopyFiber.lift (subtypeInclusion U) a.val
    ⟨fun z ↦ ⟨f (0, z), h₀ z⟩,
      (f.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
    ⟨f, fun _ ↦ rfl, h₁⟩

theorem lift_path (f : C(I × Z, X)) (h₀ : ∀ z, f (0, z) ∈ U)
    (h₁ : ∀ z, f (1, z) = a.val) (z : Z) (t : I) :
    (lift U a f h₀ h₁ z).val.2 t = f (t, z) := rfl

theorem lift_eq_basepoint (f : C(I × Z, X)) (h₀ : ∀ z, f (0, z) ∈ U)
    (h₁ : ∀ z, f (1, z) = a.val) (z : Z) (hz : ∀ t, f (t, z) = a.val) :
    lift U a f h₀ h₁ z = HomotopyFiber.basepoint (subtypeInclusion U) a := by
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (hz 0)
  · exact ContinuousMap.ext (fun t ↦ hz t)

theorem lift_cylinder (p : C(Z, Fiber U a)) :
    lift U a (cylinder U a p)
      (fun z ↦ (p z).property.1 ▸ (p z).val.1.property)
      (fun z ↦ (p z).property.2) = p := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (p z).property.1
  · rfl

def liftHomotopy (f g : C(I × Z, X))
    (hf₀ : ∀ z, f (0, z) ∈ U) (hf₁ : ∀ z, f (1, z) = a.val)
    (hg₀ : ∀ z, g (0, z) ∈ U) (hg₁ : ∀ z, g (1, z) = a.val)
    (H : f.Homotopy g)
    (h₀ : ∀ s z, H (s, (0, z)) ∈ U) (h₁ : ∀ s z, H (s, (1, z)) = a.val) :
    (lift U a f hf₀ hf₁).Homotopy (lift U a g hg₀ hg₁) where
  toFun z := ⟨(⟨H (z.1, (0, z.2)), h₀ z.1 z.2⟩,
    ⟨fun t ↦ H (z.1, (t, z.2)), H.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))⟩), rfl, h₁ z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (H.continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).subtype_mk _
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × Z) × I ↦ H (z.1.1, (z.2, z.1.2)))
      exact H.continuous.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (H.apply_zero (0, z))
    · exact ContinuousMap.ext (fun t ↦ H.apply_zero (t, z))
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (H.apply_one (0, z))
    · exact ContinuousMap.ext (fun t ↦ H.apply_one (t, z))

theorem liftHomotopy_fixed (f g : C(I × Z, X))
    (hf₀ : ∀ z, f (0, z) ∈ U) (hf₁ : ∀ z, f (1, z) = a.val)
    (hg₀ : ∀ z, g (0, z) ∈ U) (hg₁ : ∀ z, g (1, z) = a.val)
    (H : f.Homotopy g)
    (h₀ : ∀ s z, H (s, (0, z)) ∈ U) (h₁ : ∀ s z, H (s, (1, z)) = a.val)
    (s : I) (z : Z) (hz : ∀ t, H (s, (t, z)) = f (t, z)) :
    liftHomotopy U a f g hf₀ hf₁ hg₀ hg₁ H h₀ h₁ (s, z) = lift U a f hf₀ hf₁ z := by
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (hz 0)
  · exact ContinuousMap.ext (fun t ↦ hz t)

end NoExoticSixSphere.RelativeFiberCylinder
