import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenDescent

/-!
# A terminating actual collared surgery path kills positive-half H3

Strong induction uses the finite positive-half third-homology cardinality.
Each nonterminal state admits an actual one- or two-surgery path whose
endpoint has finite closed H3 and a strictly smaller cardinality. These
finite paths concatenate. The intermediate free state is retained and
is never assigned a finite homology invariant.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

theorem exists_cleared (S : CollaredSevenState B) [Finite (SingularHomology S.Space 3)] :
    ∃ U : CollaredSevenState B, S.Reachable U ∧ Finite (SingularHomology U.Space 3) ∧
      Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3) := by
  have aux : ∀ n : ℕ, ∀ Z : CollaredSevenState B,
      Finite (SingularHomology Z.Space 3) → Z.thirdCard = n →
      ∃ U : CollaredSevenState B, Z.Reachable U ∧ Finite (SingularHomology U.Space 3) ∧
        Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Z hF hcard
      let : Finite (SingularHomology Z.Space 3) := hF
      rcases Z.reducing_path_or_zero with ⟨V, hZV, hFV, hlt⟩ | hzero
      · obtain ⟨U, hVU, hFU, hU⟩ := ih V.thirdCard (hlt.trans_eq hcard) V hFV rfl
        exact ⟨U, hZV.trans hVU, hFU, hU⟩
      · exact ⟨Z, Relation.ReflTransGen.refl, hF, hzero⟩
  exact aux S.thirdCard S inferInstance rfl

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
