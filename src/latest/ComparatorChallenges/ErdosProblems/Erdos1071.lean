import Mathlib.Data.Set.Countable

attribute [local instance] Classical.propDecidable

noncomputable abbrev Erdos1071.Point :
    Type
  := by
  sorry

noncomputable def Erdos1071.IsMaximalDisjointCollection :
    Set.{0} (Set.{0} Erdos1071.Point) → Set.{0} Erdos1071.Point → Prop
  := by
  sorry

noncomputable def Erdos1071.UnitSquare :
    Set.{0} Erdos1071.Point
  := by
  sorry

theorem Erdos1071.Corollary_3 :
    @Exists.{1} (Set.{0} (Set.{0} Erdos1071.Point)) fun (S : Set.{0} (Set.{0} Erdos1071.Point)) ↦
      And (Erdos1071.IsMaximalDisjointCollection S Erdos1071.UnitSquare)
        (And (@Set.Countable.{0} (Set.{0} Erdos1071.Point) S)
          (@Set.Infinite.{0} (Set.{0} Erdos1071.Point) S))
  := by
  sorry

noncomputable abbrev Erdos1071b.Point :
    Type
  := by
  sorry

noncomputable def Erdos1071b.UnitSquare :
    Set.{0} Erdos1071b.Point
  := by
  sorry

noncomputable def Erdos1071b.IsMaximalDisjointCollection :
    Set.{0} (Set.{0} Erdos1071b.Point) → Set.{0} Erdos1071b.Point → Prop
  := by
  sorry

theorem Erdos1071b.erdos_1071b :
    @Exists.{1} (Set.{0} (Set.{0} Erdos1071b.Point)) fun (S : Set.{0} (Set.{0} Erdos1071b.Point)) ↦
      And (Erdos1071b.IsMaximalDisjointCollection S Erdos1071b.UnitSquare)
        (@Set.Finite.{0} (Set.{0} Erdos1071b.Point) S)
  := by
  sorry
