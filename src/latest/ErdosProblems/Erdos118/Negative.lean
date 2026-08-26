import ErdosProblems.Erdos118.Ordinal
import ErdosProblems.Erdos118.Imported591.ExactDensity

/-!
# A concrete negative finite conclusion for Erdős Problem 118

The blue graph is the explicit interlacing graph on literal good sequences,
transported through an order isomorphism onto `lambda.ToType`. It contains
no six-clique and meets every order-embedded copy of `lambda`.
The positive relation and the sharper negative relation at five are not
assumed or asserted by this module.
-/

open Cardinal Ordinal

namespace Erdos118

/-- Identify the canonical ordinal carrier with the literal sequence model. -/
noncomputable def sequenceModelIso : lambda.ToType ≃o Negative.Exact.G := by
  apply OrderIso.ofRelIsoLT
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [Ordinal.type_toType, Negative.Exact.type_G, lambda_eq_natural_inner_power]

/-- The concrete blue coloring; its complement is the red coloring. -/
noncomputable def counterexampleBlue : SimpleGraph lambda.ToType :=
  Negative.Exact.graph.comap sequenceModelIso

theorem counterexampleBlue_cliqueFree_six : counterexampleBlue.CliqueFree 6 := by
  apply cliqueFree_comap Negative.Exact.graph _ sequenceModelIso.toEquiv.toEmbedding
  exact (cliqueFree_iff_no_cardinal_clique Negative.Exact.graph 6).mpr
    Negative.Exact.graph_no_six

/-- Every full ordinal copy contains a blue edge, with order preserved. -/
theorem counterexampleBlue_meets_full_copy
    (e : lambda.ToType ↪o lambda.ToType) :
    ∃ a b, a ≠ b ∧ counterexampleBlue.Adj (e a) (e b) := by
  let f := e.trans sequenceModelIso.toOrderEmbedding
  have htype : typeLT (Set.range f) = (ω : Ordinal.{0}) ^ (ω ^ (2 : ℕ)) := by
    rw [type_range, Ordinal.type_toType, lambda_eq_natural_inner_power]
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ :=
    Negative.Exact.exists_edge_of_full_type (Set.range f) htype
  refine ⟨a, b, ?_, hab⟩
  intro h
  exact hab.ne (congrArg f h)

/-- The finite conclusion of the proposed implication fails at six. -/
theorem negative_six : ¬ Partition lambda lambda 6 := by
  exact (not_partition_iff lambda lambda 6).mpr
    ⟨counterexampleBlue, counterexampleBlue_cliqueFree_six,
      counterexampleBlue_meets_full_copy⟩

end Erdos118
