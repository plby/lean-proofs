import ErdosProblems.Erdos118.Negative
import ErdosProblems.Erdos118.PentagramDensity
import ErdosProblems.Erdos118.PentagramFiveClique

/-! The explicit negative-five relation, transported by the proved order
isomorphism. The red alternative is a copy with the full ordinal order type. -/

open Cardinal Ordinal

namespace Erdos118

/-- Larson's sharper blue coloring on the canonical ordinal carrier. -/
noncomputable def counterexampleBlueFive : SimpleGraph lambda.ToType :=
  Pentagram.graph.comap sequenceModelIso

theorem counterexampleBlueFive_cliqueFree_five : counterexampleBlueFive.CliqueFree 5 := by
  apply cliqueFree_comap Pentagram.graph _ sequenceModelIso.toEquiv.toEmbedding
  exact (cliqueFree_iff_no_cardinal_clique Pentagram.graph 5).mpr
    Pentagram.graph_no_five

/-- Every order-embedded copy of the full ordinal contains a blue edge. -/
theorem counterexampleBlueFive_meets_full_copy
    (e : lambda.ToType ↪o lambda.ToType) :
    ∃ a b, a ≠ b ∧ counterexampleBlueFive.Adj (e a) (e b) := by
  let f := e.trans sequenceModelIso.toOrderEmbedding
  have htype : typeLT (Set.range f) = (ω : Ordinal.{0}) ^ (ω ^ (2 : ℕ)) := by
    rw [type_range, Ordinal.type_toType, lambda_eq_natural_inner_power]
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ :=
    Pentagram.exists_edge_of_full_type (Set.range f) htype
  refine ⟨a, b, ?_, hab⟩
  intro h
  exact hab.ne (congrArg f h)

/-- The requested sharper finite conclusion fails at five. -/
theorem negative_five : ¬ Partition lambda lambda 5 := by
  exact (not_partition_iff lambda lambda 5).mpr
    ⟨counterexampleBlueFive, counterexampleBlueFive_cliqueFree_five,
      counterexampleBlueFive_meets_full_copy⟩

end Erdos118
