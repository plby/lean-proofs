/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos136

def Is45Coloring {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  ∀ v : Fin 4 ↪ Fin n,
    5 ≤ (Finset.univ.image (C.pullback v)).card

def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), Is45Coloring C

theorem colorable_nonempty (n : ℕ) : ∃ k, Colorable n k := by
  let E : Type := (⊤ : SimpleGraph (Fin n)).edgeSet
  let C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (Fintype.card E)) :=
    fun e ↦ Fintype.equivFin E e
  refine ⟨Fintype.card E, C, ?_⟩
  intro v
  let vg : (⊤ : SimpleGraph (Fin 4)) ↪g (⊤ : SimpleGraph (Fin n)) :=
    ⟨v, by simp⟩
  have hpull : Function.Injective (C.pullback v) := by
    intro e e' heq
    apply vg.mapEdgeSet.injective
    apply (Fintype.equivFin E).injective
    exact heq
  rw [Finset.card_image_of_injective _ hpull]
  rw [SimpleGraph.edgeSet_univ_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [Nat.choose]

open scoped Classical in
noncomputable def erdos136Fun (n : ℕ) : ℕ :=
  Nat.find (colorable_nonempty n)

/-- Erdős Problem 136: the minimum number of colours in a colouring of the
edges of `K_n` for which every `K_4` receives at least five colours has
normalized limit `5 / 6`. -/
theorem erdos_136 :
    Tendsto (fun n : ℕ ↦ (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  sorry

end Erdos136
