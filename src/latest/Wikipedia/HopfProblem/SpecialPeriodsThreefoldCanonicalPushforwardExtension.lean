import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# Gluing actual holomorphic extensions from a dense open set

A holomorphic function on the intersection with a dense open set has at
most one holomorphic extension. If actual local holomorphic extensions
exist near every point, the genuine holomorphic-function sheaf glues them
to the unique extension. No compatibility hypothesis is needed: it follows
from density and continuity on each overlap.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalPushforwardExtension

open HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Actual holomorphic functions on an open set are determined by their
values on any ambient dense set. -/
theorem section_eq_of_dense {G : Set M} (hG : Dense G) (U : Opens M)
    (s t : Section I M U) (h : ∀ x : U, (x : M) ∈ G → s x = t x) : s = t := by
  apply ContMDiffMap.ext
  have he : (s : U → ℂ) = t := Continuous.ext_on
    (hG.preimage U.isOpen.isOpenMap_subtype_val)
    s.contMDiff.continuous t.contMDiff.continuous h
  exact congrFun he

/-- Actual local extensions of a holomorphic function from a dense open
set glue uniquely on the original open domain. -/
theorem existsUnique_extension (G U : Opens M) (hG : Dense (G : Set M))
    (f : Section I M (U ⊓ G))
    (hloc : ∀ x : U, ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
      ∃ s : Section I M V, ∀ y : V, ∀ hy : (y : M) ∈ G,
        s y = f ⟨(y : M), ⟨hVU y.property, hy⟩⟩) :
    ∃! s : Section I M U, ∀ x : U, ∀ hx : (x : M) ∈ G,
      s x = f ⟨(x : M), ⟨x.property, hx⟩⟩ := by
  classical
  choose V hVU hmem s hs using hloc
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have hcompatible : TopCat.Presheaf.IsCompatible (sheaf I M).obj V s := by
    intro x y
    apply section_eq_of_dense I M hG (V x ⊓ V y)
    intro z hz
    exact (hs x ⟨z, z.property.1⟩ hz).trans (hs y ⟨z, z.property.2⟩ hz).symm
  obtain ⟨g, hg, _⟩ := (sheaf I M).existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hcompatible
  have hgf : ∀ x : U, ∀ hx : (x : M) ∈ G,
      g x = f ⟨(x : M), ⟨x.property, hx⟩⟩ := by
    intro x hx
    have he := congrArg (fun q : Section I M (V x) => q ⟨x, hmem x⟩) (hg x)
    exact he.trans (hs x ⟨x, hmem x⟩ hx)
  refine ⟨g, hgf, ?_⟩
  intro t ht
  exact section_eq_of_dense I M hG U t g fun x hx => (ht x hx).trans (hgf x hx).symm

end Wikipedia.HopfProblem.CanonicalPushforwardExtension
