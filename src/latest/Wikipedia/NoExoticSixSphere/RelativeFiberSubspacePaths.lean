import Wikipedia.NoExoticSixSphere.RelativeFiberHomology
import Wikipedia.NoExoticSixSphere.EndingPathSpace

/-!
# The contractible subspace of inclusion-fiber paths lying in the source

The topology is the actual subspace topology on the original homotopy
fiber. Its paths lying entirely in the source are homeomorphic to the
compact-open space of source paths ending at the chosen basepoint.
The existing explicit shortening contraction therefore contracts this
actual subspace, without a connectivity hypothesis on the source.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeFiberSubspacePaths

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def subspace : Set (Fiber U a) := {p | ∀ t, p.val.2 t ∈ U}

def toEndingPath : C(subspace U a, EndingPath.Space a) where
  toFun p := ⟨⟨fun t ↦ ⟨p.val.val.2 t, p.property t⟩,
    p.val.val.2.continuous.subtype_mk _⟩, Subtype.ext p.val.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply Continuous.subtype_mk
    change Continuous (fun p : subspace U a × I ↦ p.1.val.val.2 p.2)
    exact continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)

def fromEndingPath : C(EndingPath.Space a, subspace U a) where
  toFun p := ⟨⟨(p.val 0, (subtypeInclusion U).comp p.val),
    rfl, congrArg Subtype.val p.property⟩, fun t ↦ (p.val t).property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (EndingPath.source a).continuous
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : EndingPath.Space a × I ↦ (p.1.val p.2).val)
      exact continuous_subtype_val.comp
        (continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
          continuous_snd))

def homeomorph : subspace U a ≃ₜ EndingPath.Space a where
  toFun := toEndingPath U a
  invFun := fromEndingPath U a
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext p.val.property.1
    · rfl
  right_inv p := rfl
  continuous_toFun := (toEndingPath U a).continuous
  continuous_invFun := (fromEndingPath U a).continuous

theorem contractibleSpace : ContractibleSpace (subspace U a) :=
  (homeomorph U a).contractibleSpace

end NoExoticSixSphere.RelativeFiberSubspacePaths
