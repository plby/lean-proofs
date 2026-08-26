import ErdosProblems.Erdos593.Graph.FiniteClosureLayering
import ErdosProblems.Erdos593.TripleSystem.MinimalBadCore
import ErdosProblems.Erdos593.TripleSystem.ObligatoryOnePointAmalgamation
import ErdosProblems.Erdos593.TripleSystem.PredicateColoring

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Same-rank edge colourings

This module packages the fibrewise part of the positive-atom colouring
argument.  A rank map may have arbitrarily many values, but an edge whose
vertices all have one rank can be coloured using only the chosen colouring of
that one fibre.  Consequently no rank value needs to be encoded as a colour.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace TripleSystem

variable {W : Type u} {D : Type v}

/-- The edge indices all of whose incident vertices have one common rank. -/
def sameRankEdge {I : Type u} (H : TripleSystem W D) (rank : W → I) : D → Prop :=
  fun e => ∃ i : I, ∀ x : W, H.Inc x e → rank x = i

/-- If every rank fibre is strictly smaller than the host, the local
countable-colourability hypothesis supplies one natural-number colouring for
all edges that are internal to a single rank fibre. -/
theorem countablyColorableOn_sameRankEdge_of_locallyCountablyChromaticBelow
    {I : Type u} (H : TripleSystem W D) (rank : W → I)
    (hlocal : H.LocallyCountablyChromaticBelow)
    (hfiber : ∀ i : I,
      Cardinal.mk {x : W // rank x = i} < Cardinal.mk W) :
    H.CountablyColorableOn (sameRankEdge H rank) := by
  classical
  let fiber : I → Set W := fun i => {x | rank x = i}
  have fiberEquiv (i : I) : fiber i ≃ {x : W // rank x = i} :=
    Equiv.subtypeEquivRight fun x => by simp [fiber]
  have hsmall (i : I) : Cardinal.mk (fiber i) < Cardinal.mk W := by
    calc
      Cardinal.mk (fiber i) = Cardinal.mk {x : W // rank x = i} :=
        Cardinal.mk_congr (fiberEquiv i)
      _ < Cardinal.mk W := hfiber i
  have hfiberColor (i : I) :
      ∃ c : fiber i → CountableColor.{u},
        (H.vertexRestriction (fiber i)).IsProperColoring c :=
    (H.vertexRestriction (fiber i)).exists_natColoring_of_chromaticCardinal_le_aleph0
      (hlocal (fiber i) (hsmall i))
  let inner : ∀ i : I, fiber i → CountableColor.{u} :=
    fun i => Classical.choose (hfiberColor i)
  have hinner (i : I) :
      (H.vertexRestriction (fiber i)).IsProperColoring (inner i) :=
    Classical.choose_spec (hfiberColor i)
  let c : W → ℕ := fun x => (inner (rank x) ⟨x, rfl⟩).down
  refine ⟨c, ?_⟩
  intro e he
  rcases he with ⟨i, hi⟩
  let d : H.RestrictedEdge (fiber i) := ⟨e, fun x hx => hi x hx⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hinner i d
  refine ⟨x.1, hx, y.1, hy, ?_⟩
  have hcx : c x.1 = (inner i x).down := by
    clear hx
    rcases x with ⟨x, hxmem⟩
    change rank x = i at hxmem
    cases hxmem
    rfl
  have hcy : c y.1 = (inner i y).down := by
    clear hy
    rcases y with ⟨y, hymem⟩
    change rank y = i at hymem
    cases hymem
    rfl
  rw [hcx, hcy]
  intro hEq
  exact hxy (ULift.down_injective hEq)

/-- A finite closure layering automatically provides the strict-small-fibre
hypothesis needed for same-rank edge colouring. -/
theorem countablyColorableOn_sameRankEdge_of_finiteClosureLayering
    {r : ℕ} {Φ : {s : Finset W // s.card = r} → Finset W}
    {I : Type u} [LinearOrder I] (H : TripleSystem W D)
    (L : FiniteClosureLayering r Φ I)
    (hlocal : H.LocallyCountablyChromaticBelow) :
    H.CountablyColorableOn (sameRankEdge H L.rank) :=
  countablyColorableOn_sameRankEdge_of_locallyCountablyChromaticBelow H L.rank
    hlocal L.fiber_lt

end TripleSystem

end Erdos593
