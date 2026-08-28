import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspQuotient

/-!
# A compact fundamental-cell presentation of the actual central cusp fibre

Restricting the actual honeycomb collapse to compact phases over the
central closed hexagon is still surjective: the genuine deck action
reduces every planar representative to that hexagon and adjusts its
compact phase. The fibre relation is the original lattice-and-stabilizer
relation, including all edge and vertex identifications.

At an admissible cusp radius the map is proper, closed, and a quotient
map for the inherited topology on the actual central fibre. This is a
geometric presentation for subsequent singular-homology arguments, not
an assumed cell-complex or homology identification.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

/-- Compact phases over the literal central dual hexagon. -/
abbrev FundamentalCell := CompactFibreTorus × baseCell

instance fundamentalCell_compactSpace : CompactSpace FundamentalCell := by
  let : CompactSpace baseCell := isCompact_iff_compactSpace.mp baseCell_isCompact
  infer_instance

/-- Inclusion into the already constructed actual phase-plane presentation. -/
def fundamentalCellInclusion (p : FundamentalCell) : PhasePlane := (p.1, (p.2 : Plane))

theorem fundamentalCellInclusion_continuous : Continuous fundamentalCellInclusion :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual central cusp map restricted to one compact phase hexagon. -/
def fundamentalCellMap : FundamentalCell → QuotientCentralFibre C ε :=
  honeycombCollapseMap C ε hε ∘ fundamentalCellInclusion

@[simp] theorem fundamentalCellMap_apply (p : FundamentalCell) :
    fundamentalCellMap C ε hε p = honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := rfl

theorem fundamentalCellMap_continuous : Continuous (fundamentalCellMap C ε hε) :=
  (honeycombCollapseMap_continuous C ε hε).comp fundamentalCellInclusion_continuous

/-- The full honeycomb collapse is invariant under the genuine deck map,
with its nontrivial compact-phase factor. -/
theorem honeycombCollapseMap_deck_invariant (v : Lattice) (p : PhasePlane) :
    honeycombCollapseMap C ε hε (honeycombDeckMap (C 0) v p) =
      honeycombCollapseMap C ε hε p := by
  apply (honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨v, rfl, ?_⟩
  simp [honeycombDeckMap]

/-- Every point of the actual central quotient has a representative in
the compact phase hexagon, with the deck phase explicitly adjusted. -/
theorem fundamentalCellMap_surjective : Function.Surjective (fundamentalCellMap C ε hε) := by
  intro q
  obtain ⟨p, hp⟩ := honeycombCollapseMap_surjective C ε hε q
  obtain ⟨v, hv⟩ := exists_mem_cell p.2
  let y : baseCell := ⟨p.2 - latticePoint v, hv⟩
  refine ⟨(deckFibrePhase (C 0) (cuspVector v) * p.1, y), ?_⟩
  change honeycombCollapseMap C ε hε
    (deckFibrePhase (C 0) (cuspVector v) * p.1, p.2 - latticePoint v) = q
  simpa only [honeycombDeckMap, cuspVector_cuspVector, latticePoint_neg,
    sub_eq_add_neg] using
    (honeycombCollapseMap_deck_invariant C ε hε (cuspVector v) p).trans hp

/-- Exact fibres, with no additional equivalence closure or omitted
boundary identifications. -/
theorem fundamentalCellMap_eq_iff (p q : FundamentalCell) :
    fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q ↔
      ∃ v : Lattice, (p.2 : Plane) = (q.2 : Plane) + latticePoint (cuspVector v) ∧
        p.1⁻¹ * (deckFibrePhase (C 0) v * q.1) ∈
          MulAction.stabilizer CompactFibreTorus
            ((honeycombHomeomorph (C 0) (p.2 : Plane)).1 : Space) :=
  honeycombCollapseMap_eq_iff C ε hε
    (fundamentalCellInclusion p) (fundamentalCellInclusion q)

include hε in
/-- Compactness follows for the literal central fibre from the compact
surjective presentation, without a Hausdorff or small-drift hypothesis. -/
theorem quotientCentralFibre_compactSpace : CompactSpace (QuotientCentralFibre C ε) := by
  constructor
  rw [← Set.range_eq_univ.mpr (fundamentalCellMap_surjective C ε hε)]
  exact isCompact_range (fundamentalCellMap_continuous C ε hε)

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

/-- At an actual admissible radius the compact fundamental-cell map is proper. -/
theorem fundamentalCellMap_isProperMap : IsProperMap (fundamentalCellMap C ε hε) := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (fundamentalCellMap_continuous C ε hε).isProperMap

theorem fundamentalCellMap_isClosedMap : IsClosedMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).isClosedMap

/-- The quotient topology is the inherited topology on the original
central cusp fibre, not one assigned to a replacement model. -/
theorem fundamentalCellMap_isQuotientMap : IsQuotientMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isClosedMap C ε hε hε1 hC hR).isQuotientMap
    (fundamentalCellMap_continuous C ε hε) (fundamentalCellMap_surjective C ε hε)

end Wikipedia.HopfProblem.CuspCentralHomology
