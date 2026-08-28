import Wikipedia.HopfProblem.HolomorphicMeromorphicRegular

/-!
# The native holomorphic representative of an everywhere-regular section

An everywhere-regular meromorphic section is represented on its entire
original open domain by its canonical values. This is literal restriction
of the already constructed regular representative, and preserves all of
the original meromorphic germs.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

theorem le_regularDomain {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) : U ≤ regularDomain I M a := by
  intro x hx
  exact ⟨⟨x, hx⟩, ha ⟨x, hx⟩, rfl⟩

/-- The regular locus is the actual whole original domain. -/
theorem regularDomain_eq {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) : regularDomain I M a = U :=
  le_antisymm (regularDomain_le I M a) (le_regularDomain I M a ha)

/-- The native holomorphic section given by the canonical regular values. -/
def holomorphicRepresentative {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) : HolomorphicFunctionSheaf.Section I M U :=
  HolomorphicFunctionSheaf.restrictionAlgHom I M (le_regularDomain I M a ha)
    (regularRepresentative I M a)

@[simp] theorem holomorphicRepresentative_apply {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) (x : U) :
    holomorphicRepresentative I M a ha x = value I M a x := rfl

/-- The holomorphic representative has precisely the given meromorphic germs. -/
theorem holomorphicRepresentative_germ {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) (x : U) :
    sectionGerm I M U x (holomorphicRepresentative I M a ha) = a x := by
  calc
    sectionGerm I M U x (holomorphicRepresentative I M a ha) =
        sectionGerm I M (regularDomain I M a)
          (Set.inclusion (le_regularDomain I M a ha) x) (regularRepresentative I M a) :=
      sectionGerm_restrict I M (le_regularDomain I M a ha) x (regularRepresentative I M a)
    _ = a x := regularRepresentative_germ I M a
      (Set.inclusion (le_regularDomain I M a ha) x)

theorem ofHolomorphic_holomorphicRepresentative {U : Opens M} (a : Section I M U)
    (ha : ∀ x : U, RegularAt I M a x) :
    ofHolomorphic I M U (holomorphicRepresentative I M a ha) = a := by
  apply section_ext
  intro x
  exact (ofHolomorphic_apply I M U _ x).trans
    (holomorphicRepresentative_germ I M a ha x)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition
