import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing actual holomorphic sections of a native line bundle

The holomorphic maps into the original bundle total space form a sheaf.
Gluing section maps in that sheaf preserves their projection to the base,
and therefore produces a section in the original fibres. No alternative
atlas or separate gluing hypothesis is used.
-/

noncomputable section

open Bundle Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Holomorphic maps into the original native bundle total space. -/
def totalMapSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := I) (I' := I.prod I₁) ω).sheaf M C.TotalSpace

instance totalMapSheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((totalMapSheaf C I).obj.obj U) (fun _ => U.unop → C.TotalSpace) where
  coe f := f.1

namespace Section

/-- Forget only the projection condition, retaining the actual native
total-space map and its holomorphicity. -/
def toHolomorphicMap {U : Opens M} (s : Section C I U) :
    ContMDiffMap I (I.prod I₁) U C.TotalSpace ω :=
  ⟨s.totalSpace C I, s.contMDiff_toFun⟩

@[simp] theorem toHolomorphicMap_apply {U : Opens M} (s : Section C I U) (x : U) :
    toHolomorphicMap C I s x = s.totalSpace C I x := rfl

/-- A holomorphic native total-space map over the identity is an actual
section of the original bundle. -/
def ofHolomorphicMap {U : Opens M}
    (f : ContMDiffMap I (I.prod I₁) U C.TotalSpace ω)
    (hf : ∀ x : U, (f x).proj = (x : M)) : Section C I U where
  toFun x := (f x).2
  contMDiff_toFun := by
    have he : (fun x : U => (⟨(x : M), (f x).2⟩ : C.TotalSpace)) = f := by
      funext x
      exact Bundle.TotalSpace.ext (hf x).symm HEq.rfl
    rw [he]
    exact f.contMDiff

@[simp] theorem ofHolomorphicMap_apply {U : Opens M}
    (f : ContMDiffMap I (I.prod I₁) U C.TotalSpace ω)
    (hf : ∀ x : U, (f x).proj = (x : M)) (x : U) :
    ofHolomorphicMap C I f hf x = (f x).2 := rfl

theorem ofHolomorphicMap_totalSpace {U : Opens M}
    (f : ContMDiffMap I (I.prod I₁) U C.TotalSpace ω)
    (hf : ∀ x : U, (f x).proj = (x : M)) (x : U) :
    (ofHolomorphicMap C I f hf).totalSpace C I x = f x :=
  Bundle.TotalSpace.ext (hf x).symm HEq.rfl

/-- Every compatible family of actual holomorphic sections has a unique
actual holomorphic gluing on the union. -/
theorem existsUnique_gluing {κ : Type*} (U : κ → Opens M)
    (s : ∀ i, Section C I (U i))
    (hs : ∀ i j, restrict C I inf_le_left (s i) =
      restrict C I inf_le_right (s j)) :
    ∃! t : Section C I (iSup U),
      ∀ i, restrict C I (le_iSup U i) t = s i := by
  let sf : ∀ i : κ, (totalMapSheaf C I).obj.obj (op (U i)) :=
    fun i => toHolomorphicMap C I (s i)
  have hsf : TopCat.Presheaf.IsCompatible (totalMapSheaf C I).obj U sf := by
    intro i j
    exact congrArg (toHolomorphicMap C I) (hs i j)
  obtain ⟨f, hf, _⟩ := (totalMapSheaf C I).existsUnique_gluing U sf hsf
  have hproj : ∀ x : ↥(iSup U), (f x).proj = (x : M) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact congrArg
      (fun g : ContMDiffMap I (I.prod I₁) (U i) C.TotalSpace ω =>
        (g ⟨(x : M), hi⟩).proj) (hf i)
  let t : Section C I (iSup U) := ofHolomorphicMap C I f hproj
  have ht : ∀ i, restrict C I (le_iSup U i) t = s i := by
    intro i
    apply Section.ext C I
    intro x
    exact congrArg
      (fun g : ContMDiffMap I (I.prod I₁) (U i) C.TotalSpace ω =>
        id (α := ℂ) (g x).2) (hf i)
  refine ⟨t, ht, ?_⟩
  intro q hq
  apply Section.ext C I
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  have hqi := congrArg (fun z : Section C I (U i) => z ⟨(x : M), hi⟩) (hq i)
  have hti := congrArg (fun z : Section C I (U i) => z ⟨(x : M), hi⟩) (ht i)
  exact hqi.trans hti.symm

end Section

end Wikipedia.HopfProblem.NativeBundleSections
