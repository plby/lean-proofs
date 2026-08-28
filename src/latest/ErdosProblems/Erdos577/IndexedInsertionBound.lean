import ErdosProblems.Erdos577.NeighborPairPigeonhole
import ErdosProblems.Erdos577.LocalPathPartition

/-! Five contacts and forbidden endpoint-pair insertions rule out a universal replacement row. -/

namespace Erdos577

open Finset

variable {I V : Type*} [DecidableEq I] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma contacts_image_erase_add (e : I ↪ V) (s : Finset I) (u : I) (hu : u ∈ s)
    (a : Finset V) : contacts G ((s.erase u).image e) a + degreeIn G (e u) a =
      contacts G (s.image e) a := by
  rw [contacts_image_left G _ e e.injective, contacts_image_left G _ e e.injective]
  exact sum_erase_add _ _ hu

lemma no_universal_of_index_pairs {a : Finset V} (ha : QuadOn G a)
    (e : I ↪ V) (s : Finset I) (u : I)
    (hfive : 5 ≤ contacts G ((s.erase u).image e) a)
    (hno : ∀ v ∈ s.erase u, ∀ w ∈ s.erase u, v ≠ w →
      ¬CommonReplacement G (e v) (e w) (e u) a) :
    ¬∀ z ∈ a, QuadOn G (insert (e u) (a.erase z)) := by
  intro hrep
  obtain ⟨z, hz, v, hv, w, hw, hvw, hvz, hwz⟩ :=
    exists_common_pair_of_contacts (G := G) ((s.erase u).image e) a (by rw [ha.card]; omega)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
  exact hno i hi j hj (fun hh ↦ hvw (congrArg e hh)) ⟨z, hz, hvz, hwz, hrep z hz⟩

end Erdos577
