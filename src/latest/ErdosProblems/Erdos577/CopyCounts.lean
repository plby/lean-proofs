import ErdosProblems.Erdos577.FiniteExchange

/-! Positive score information survives injective graph copies. -/

namespace Erdos577

open Finset Function
open scoped BigOperators

variable {V W : Type*} [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma degreeIn_image_le (f : G.Copy H) (v : V) (s : Finset V) :
    degreeIn G v s ≤ degreeIn H (f v) (s.image f) := by
  have hinj : Injective (f : V → W) := f.injective
  have hs : (s.filter (G.Adj v)).image f ⊆ (s.image f).filter (H.Adj (f v)) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_image.mpr ⟨u, (mem_filter.mp hu).1, rfl⟩,
      f.toHom.map_rel' (mem_filter.mp hu).2⟩
  have hc := card_le_card hs
  rwa [card_image_of_injective _ hinj] at hc

lemma contacts_image_self_le (f : G.Copy H) (s : Finset V) :
    contacts G s s ≤ contacts H (s.image f) (s.image f) := by
  have hinj : Injective (f : V → W) := f.injective
  rw [contacts_image_left H _ _ hinj]
  exact sum_le_sum fun v _ ↦ degreeIn_image_le f v s

lemma edgeCount_image_le (f : G.Copy H) (s : Finset V) :
    edgeCount G s ≤ edgeCount H (s.image f) := by
  have h := contacts_image_self_le f s
  rw [contacts_self_eq_twice_edgeCount, contacts_self_eq_twice_edgeCount] at h
  omega

end Erdos577
