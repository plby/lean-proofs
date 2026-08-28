import ErdosProblems.Erdos577.WeightedFourteenUpper
import ErdosProblems.Erdos577.WeightedNineteenPaths

/-! The actual weighted inside bound27 and the resulting outside threshold17 in pattern (14). -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def weight (p : Paw G) (q : Quadrilateral G) (a : Finset V) : ℕ :=
  2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a + contacts G p.triangle a

lemma weight_eq (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : weight p q a =
    contacts G ((weightSet false).image (PawEncoding.labeling p q hd)) a +
      contacts G ((weightSet true).image (PawEncoding.labeling p q hd)) a := by
  let e := PawEncoding.labeling p q hd
  have ht : p.triangle = ({1, 2, 3} : Finset (Fin 8)).image e := by
    simp only [image_insert, image_singleton]
    rfl
  unfold weight
  rw [ht, contacts_image_left G _ e e.injective,
    contacts_image_left G _ (PawEncoding.labeling p q hd) (PawEncoding.labeling p q hd).injective,
    contacts_image_left G _ (PawEncoding.labeling p q hd) (PawEncoding.labeling p q hd).injective]
  norm_num [weightSet]
  change 2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a +
    (degreeIn G p.center a + (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a)) =
      degreeIn G p.leaf a + (degreeIn G (q 1) a +
        (degreeIn G p.center a + degreeIn G (p.vertices 2) a)) +
      (degreeIn G p.leaf a + (degreeIn G (q 1) a +
        (degreeIn G (q 3) a + degreeIn G (p.vertices 3) a)))
  omega

lemma inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3)) :
    weight p q (p.support ∪ q.support) ≤ 27 := by
  let e := PawEncoding.labeling p q hd
  have hl (second : Bool) := contacts_image_le_of_adj G upperGraph e e.injective
    (weightSet second) univ (fun i _ j _ ↦ adj_upper p q hd h hleaf hcenter i j)
  have he := Nat.add_le_add (hl false) (hl true)
  rw [inside_weight, PawEncoding.labeling_image] at he
  rw [weight_eq p q hd]
  exact he

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 17 ≤ weight p q a := by
  let e := PawEncoding.labeling p q hd
  have hinside := inside_bound p q hd h (c.paw_nonadjacent hcard hn p hp)
    (center_absent p q hd h (by rw [hp, hq]; exact c.no_local_factor hcard hn hb))
  rw [weight_eq p q hd, hp, hq] at hinside
  change contacts G ((weightSet false).image e) (c.remainder ∪ b) +
    contacts G ((weightSet true).image e) (c.remainder ∪ b) ≤ 27 at hinside
  obtain ⟨a, ha, hab, hh⟩ := c.exists_paired_heavy_outside_core hcard hdeg hb
    ((weightSet false).image e) ((weightSet true).image e)
    (by rw [card_image_of_injective _ e.injective, weightSet_card])
    (by rw [card_image_of_injective _ e.injective, weightSet_card]) (by omega)
  exact ⟨a, ha, hab, by rw [weight_eq p q hd]; exact hh⟩

end Erdos577.WeightedFourteen
