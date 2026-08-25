import StackExchange.Puzzling139335.TripleContact

/-! # A three-spoke nonplanarity criterion with arbitrary support regions -/

open Set

namespace Puzzling139335

/-- Three support regions cannot share three points if their disjoint open
parts admit three mutually disjoint spokes to those points.  The supports
need not be bounded: the square exterior is one intended application. -/
theorem no_three_common_points_of_disjoint_spokes
    (S U : Fin 3 → Set Plane) (hUS : ∀ i, U i ⊆ S i)
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (S j))
    (b : Fin 3 → Plane) (hb : ∀ i j, b j ∈ S i) (hinj : Function.Injective b)
    (hspokes : ∀ i, ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∈ U i ∧ (∀ j, Schoenflies.IsArcBetween (A j) x (b j)) ∧
      (∀ j, A j \ {b j} ⊆ U i) ∧ ∀ j k, j ≠ k → A j ∩ A k = {x}) : False := by
  classical
  choose x A hx hAarc hAint hAmeet using hspokes
  have hAsub (i j : Fin 3) : A i j ⊆ S i := by
    intro z hz
    by_cases hzb : z = b j
    · exact hzb ▸ hb i j
    · exact hUS i (hAint i j ⟨hz, hzb⟩)
  have hK : _root_.Graph.IsArcK33 x b A := by
    refine ⟨hAarc, ?_, hinj, ?_, ?_⟩
    · intro i k hik
      by_contra hine
      exact Set.disjoint_left.mp (hdis i k hine) (hx i)
        (hUS k (by simpa only [hik] using hx k))
    · intro i j hij
      obtain ⟨k, hki⟩ := exists_ne i
      exact Set.disjoint_left.mp (hdis i k hki.symm) (hx i) (hij ▸ hb k j)
    · intro i j k l hne z hz
      by_cases hik : i = k
      · subst k
        have hjl : j ≠ l := fun h => hne (Prod.ext rfl h)
        have hzx : z = x i := mem_singleton_iff.mp (hAmeet i j l hjl ▸ hz)
        subst z
        simp
      · have hzbj : z = b j := by
          by_contra hzne
          exact Set.disjoint_left.mp (hdis i k hik) (hAint i j ⟨hz.1, hzne⟩)
            (hAsub k l hz.2)
        have hzbl : z = b l := by
          by_contra hzne
          exact Set.disjoint_left.mp (hdis k i (Ne.symm hik)) (hAint k l ⟨hz.2, hzne⟩)
            (hAsub i j hz.1)
        exact ⟨Or.inr hzbj, Or.inr hzbl⟩
  exact hK.elim

end Puzzling139335
