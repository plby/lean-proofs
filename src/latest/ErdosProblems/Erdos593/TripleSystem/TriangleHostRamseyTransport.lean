import ErdosProblems.Erdos593.TripleSystem.TriangleHostRamsey
import ErdosProblems.Erdos593.TripleSystem.NonlinearObstruction
import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A universe-exact triangle-host Ramsey transport

This module transports the base-universe triangle host into the precise vertex
and edge universes of an arbitrary source system. It converts the conditional
`PairRamseyTriangle` interface into a linear, uncountably chromatic target and
therefore into the existing nonlinearity obstruction. It does not construct a
Ramsey witness or prove an Erdos--Rado partition relation.
-/

namespace Erdos593

open scoped Cardinal

universe u v u' v'

namespace TripleSystem
namespace TriangleHostTransport

variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}

/-- Simultaneously relabel vertices and edge indices by equivalences. -/
def reindex (F : TripleSystem V E) (vertexEquiv : V ≃ V')
    (edgeEquiv : E ≃ E') : TripleSystem V' E' where
  Inc x e := F.Inc (vertexEquiv.symm x) (edgeEquiv.symm e)
  edge_ncard := by
    intro e
    let s : Set V' := {x | F.Inc (vertexEquiv.symm x) (edgeEquiv.symm e)}
    have hs : s = vertexEquiv '' F.edgeSet (edgeEquiv.symm e) := by
      ext x
      constructor
      · intro hx
        exact ⟨vertexEquiv.symm x, hx, vertexEquiv.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [s, TripleSystem.edgeSet] using! hy
    change s.ncard = 3
    rw [hs, Set.ncard_image_of_injective _ vertexEquiv.injective]
    exact F.edgeSet_ncard _
  simple := by
    intro e₁ e₂ h
    apply edgeEquiv.symm.injective
    apply F.edgeSet_injective
    ext x
    have hx := Set.ext_iff.mp h (vertexEquiv x)
    simpa [TripleSystem.edgeSet] using! hx

/-- Incidence is preserved and reflected by `reindex`. -/
theorem reindex_inc_iff (F : TripleSystem V E) (vertexEquiv : V ≃ V')
    (edgeEquiv : E ≃ E') (x : V) (e : E) :
    (reindex F vertexEquiv edgeEquiv).Inc (vertexEquiv x) (edgeEquiv e) ↔
      F.Inc x e := by
  simp [reindex]

/-- The base-universe triangle host lifted into arbitrary ambient universes. -/
def exactSystem (κ : Type) [DecidableEq κ] :
    TripleSystem (ULift.{u} (TriangleHost.Pair κ))
      (ULift.{v} (TriangleHost.Triangle κ)) :=
  reindex (TriangleHost.system κ)
    (Equiv.ulift : ULift.{u} (TriangleHost.Pair κ) ≃ TriangleHost.Pair κ).symm
    (Equiv.ulift : ULift.{v} (TriangleHost.Triangle κ) ≃ TriangleHost.Triangle κ).symm

/-- The lift has exactly the original incidence relation on lifted data. -/
theorem exactSystem_inc_iff (κ : Type) [DecidableEq κ]
    (p : TriangleHost.Pair κ) (t : TriangleHost.Triangle κ) :
    (exactSystem.{u, v} κ).Inc (ULift.up p) (ULift.up t) ↔
      (TriangleHost.system κ).Inc p t := by
  rfl

/-- Linearity survives the exact universe lift. -/
theorem exactSystem_linear (κ : Type) [DecidableEq κ] :
    (exactSystem.{u, v} κ).Linear := by
  intro e f x y hef hxe hxf hye hyf
  apply ULift.ext
  apply TriangleHost.linear κ
  · intro hdown
    apply hef
    exact ULift.ext _ _ hdown
  · change (TriangleHost.system κ).Inc x.down e.down at hxe
    exact hxe
  · change (TriangleHost.system κ).Inc x.down f.down at hxf
    exact hxf
  · change (TriangleHost.system κ).Inc y.down e.down at hye
    exact hye
  · change (TriangleHost.system κ).Inc y.down f.down at hyf
    exact hyf

/-- A proper countable colouring of the lifted host would induce a natural
proper colouring of the base host. -/
theorem no_countableProperColoring_exactSystem
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.PairRamseyTriangle κ) :
    ¬ ∃ c : ULift.{u} (TriangleHost.Pair κ) → ULift.{u} ℕ,
      (exactSystem.{u, v} κ).IsProperColoring c := by
  rintro ⟨c, hc⟩
  let d : TriangleHost.Pair κ → ℕ := fun p => (c (ULift.up p)).down
  apply TriangleHost.not_isProperColoring_nat_of_pairRamseyTriangle κ hRamsey d
  intro t
  rcases hc (ULift.up t) with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x.down, ?_, y.down, ?_, ?_⟩
  · change (TriangleHost.system κ).Inc x.down t at hx
    exact hx
  · change (TriangleHost.system κ).Inc y.down t at hy
    exact hy
  · intro hdown
    apply hxy
    apply ULift.ext
    simpa [d] using! hdown

/-- Under the Ramsey interface, the lifted host is uncountably chromatic. -/
theorem aleph0_lt_chromaticCardinal_exactSystem
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.PairRamseyTriangle κ) :
    ℵ₀ < (exactSystem.{u, v} κ).chromaticCardinal := by
  by_contra hnot
  have hle : (exactSystem.{u, v} κ).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hnot
  have hle' : (exactSystem.{u, v} κ).chromaticCardinal ≤
      #(ULift.{u} ℕ) := by
    simpa using! hle
  obtain ⟨c, hc⟩ :=
    ((exactSystem.{u, v} κ).chromaticCardinal_le_mk_iff
      (C := ULift.{u} ℕ)).mp hle'
  exact no_countableProperColoring_exactSystem.{u, v} κ hRamsey ⟨c, hc⟩

/-- A non-linear source fails obligatoriness whenever the base-universe
triangle-host Ramsey interface is available. -/
theorem not_isObligatory_of_not_linear_of_exactTriangleHost
    (F : TripleSystem V E) (hnotlinear : ¬ F.Linear)
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.PairRamseyTriangle κ) :
    ¬ F.IsObligatory := by
  let : DecidableEq (TriangleHost.Pair κ) := inferInstance
  let : DecidableEq (ULift.{u} (TriangleHost.Pair κ)) := inferInstance
  apply not_isObligatory_of_not_linear_of_linear_highChromatic
    (H := exactSystem.{u, v} κ)
  · exact hnotlinear
  · exact exactSystem_linear.{u, v} κ
  · exact aleph0_lt_chromaticCardinal_exactSystem.{u, v} κ hRamsey

end TriangleHostTransport
end TripleSystem
end Erdos593
