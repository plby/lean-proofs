import ErdosProblems.Erdos591.K4Core

open Set

namespace Erdos591.Positive.TriangleCore

open Erdos591.Schipperus.K4Core

universe u v w

variable {Y : Type u} [LinearOrder Y] [Nontrivial Y]
variable {V : Type v} [LinearOrder V]

/-- In a triangle-free blue graph, points with a small red neighborhood
in one fixed indivisible reservoir form a red clique.  No hypothesis
excluding a red copy of the reservoir is needed. -/
theorem bad_isClique (hindY : FinitelyIndivisible Y)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (htri : blue.CliqueFree 3) (T : Set V) (hT : Large Y T) :
    red.IsClique {x | ¬ Large Y {z | z ∈ T ∧ red.Adj x z}} := by
  classical
  intro x hx y hy hxy
  rw [hcompl.eq_compl]
  refine ⟨hxy, ?_⟩
  intro hblue
  let Rx : Set V := {z | z ∈ T ∧ red.Adj x z}
  let Ry : Set V := {z | z ∈ T ∧ red.Adj y z}
  have h₁ : Large Y (T \ (Rx ∪ Ry)) :=
    Large.diff_union_of_not_large hindY hT hx hy
  have h₂ : Large Y ((T \ (Rx ∪ Ry)) \ {x}) :=
    Large.diff_of_not_large hindY h₁ (singleton_not_large x)
  have h₃ : Large Y (((T \ (Rx ∪ Ry)) \ {x}) \ {y}) :=
    Large.diff_of_not_large hindY h₂ (singleton_not_large y)
  obtain ⟨z, hz⟩ := h₃.nonempty
  have hzT : z ∈ T := hz.1.1.1
  have hxz : x ≠ z := by
    intro heq
    exact hz.1.2 (by simp [heq])
  have hyz : y ≠ z := by
    intro heq
    exact hz.2 (by simp [heq])
  have hRx : ¬ red.Adj x z := fun h ↦ hz.1.1.2 (Or.inl ⟨hzT, h⟩)
  have hRy : ¬ red.Adj y z := fun h ↦ hz.1.1.2 (Or.inr ⟨hzT, h⟩)
  have hxzblue : blue.Adj x z := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hxz, hRx⟩
  have hyzblue : blue.Adj y z := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hyz, hRy⟩
  exact htri {x, y, z}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hblue, hxzblue, hyzblue⟩)

variable {X : Type w} [LinearOrder X]

/-- The same red-clique conclusion for failure at an indivisible index
scale.  Reservoirs may overlap and their type need not equal that of the
index order. -/
theorem indexed_bad_isClique
    {D : Type*} [LinearOrder D] [Nonempty D]
    (hindY : FinitelyIndivisible Y) (hindD : FinitelyIndivisible D)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (htri : blue.CliqueFree 3)
    (T : D → Set V) (hT : ∀ d, Large Y (T d)) :
    red.IsClique {x | ¬ Large D
      {d | Large Y {z | z ∈ T d ∧ red.Adj x z}}} := by
  intro x hx y hy hxy
  let M : V → Set D := fun v ↦
    {d | Large Y {z | z ∈ T d ∧ red.Adj v z}}
  have hD : Large D ((Set.univ : Set D) \ (M x ∪ M y)) :=
    Large.diff_union_of_not_large hindD Large.univ hx hy
  obtain ⟨d, hd⟩ := hD.nonempty
  have hx' : ¬ Large Y {z | z ∈ T d ∧ red.Adj x z} :=
    fun h ↦ hd.2 (Or.inl h)
  have hy' : ¬ Large Y {z | z ∈ T d ∧ red.Adj y z} :=
    fun h ↦ hd.2 (Or.inr h)
  exact bad_isClique hindY red blue hcompl htri (T d) (hT d) hx' hy' hxy

/-- A bad set is small at the globally excluded red scale, even when the
reservoir has a different order type. -/
theorem bad_not_large (hindY : FinitelyIndivisible Y)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (htri : blue.CliqueFree 3)
    (hnoRed : ¬ ∃ S : Set V, red.IsClique S ∧ Large X S)
    (T : Set V) (hT : Large Y T) :
    ¬ Large X {x | ¬ Large Y {z | z ∈ T ∧ red.Adj x z}} := by
  intro hbad
  exact hnoRed ⟨_, bad_isClique hindY red blue hcompl htri T hT, hbad⟩

/-- Preserve finitely many reservoir types while selecting from a full
candidate set.  This does not assert selection from a smaller prescribed
reservoir. -/
theorem large_preserving_finset [Nonempty X] {I : Type*} [DecidableEq I]
    (hindX : FinitelyIndivisible X) (hindY : FinitelyIndivisible Y)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (htri : blue.CliqueFree 3)
    (hnoRed : ¬ ∃ S : Set V, red.IsClique S ∧ Large X S)
    (A : Set V) (hA : Large X A)
    (T : I → Set V) (F : Finset I)
    (hT : ∀ i ∈ F, Large Y (T i)) :
    Large X {x | x ∈ A ∧ ∀ i ∈ F,
      Large Y {z | z ∈ T i ∧ red.Adj x z}} := by
  apply large_all_finset hindX A hA
    (fun i x ↦ Large Y {z | z ∈ T i ∧ red.Adj x z}) F
  intro i hi hbad
  apply bad_not_large hindY red blue hcompl htri hnoRed (T i) (hT i hi)
  exact hbad.mono (fun _ hx ↦ hx.2)

end Erdos591.Positive.TriangleCore

#print axioms Erdos591.Positive.TriangleCore.large_preserving_finset
#print axioms Erdos591.Positive.TriangleCore.indexed_bad_isClique
