import ErdosProblems.Erdos633b.OrderedLocalRelations
import ErdosProblems.Erdos633b.OrderedSmallColumn
import ErdosProblems.Erdos633b.IsoscelesTileNecessity

/-! The explicit finite local-relation reduction for any actual hypothetical
counterexample. The 25 remaining relations are not asserted to admit tilings. -/

namespace Erdos633b

def orderedNonrightRelationTriples : Finset (ℤ × ℤ × ℤ) :=
  orderedRelationTriples.erase (2, 2, 1)

def OrderedNonrightLocalRelation (α β : ℝ) : Prop :=
  ∃ t ∈ orderedNonrightRelationTriples,
    (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi

theorem orderedNonrightRelationTriples_card : orderedNonrightRelationTriples.card = 25 := by
  decide

theorem nonright_relation_of_local_relation (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (hne : γ ≠ Real.pi / 2) (h : OrderedLocalRelation α β) :
    OrderedNonrightLocalRelation α β := by
  obtain ⟨t, ht, he⟩ := h
  refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, he⟩
  intro htup
  rw [htup] at he
  norm_num at he
  exact hne (by linarith)

namespace Tiling

theorem ordered_local_relation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    OrderedLocalRelation (d.tile.angle 0) (d.tile.angle 1) := by
  obtain ⟨p, q, r, k, hpk, _, _, hr, hkp, hkb, he⟩ :=
    d.exists_bounded_ordered_nonreptiling_relation h01 h12 hγ hscalene hrep
  exact ordered_relation_of_local_deficit _ _ _ (d.tile.angle_pos 0) h01 h12
    d.tile.angle_sum hγ p q r k hpk hr hkp hkb he

theorem counterexample_ordered_relations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e : Equiv.Perm (Fin 3),
      let S : Triangle := d.tile.reindex e
      S.angle 0 < S.angle 1 ∧ S.angle 1 < S.angle 2 ∧
        S.angle 2 ≤ 2 * Real.pi / 3 ∧ S.angle 2 ≠ Real.pi / 2 ∧
        (∀ i, IsRational (S.angle i / Real.pi)) ∧
        OrderedNonrightLocalRelation (S.angle 0) (S.angle 1) := by
  have hinj := d.tile_angles_injective_of_counterexample hnot
  have hscalene : Function.Injective T.angle := by
    by_contra h
    exact hnot (eightCases_of_not_injective_angles T h)
  obtain ⟨e, h01, h12⟩ := three_values_ordered d.tile.angle
  have hs01 : d.tile.angle (e 0) < d.tile.angle (e 1) := by
    apply lt_of_le_of_ne h01
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (e.injective (hinj h))
  have hs12 : d.tile.angle (e 1) < d.tile.angle (e 2) := by
    apply lt_of_le_of_ne h12
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (e.injective (hinj h))
  let d' := d.reindexTile e.symm
  have h01' : d'.tile.angle 0 < d'.tile.angle 1 := by
    change Triangle.angle (d.tile.reindex e.symm) 0 < Triangle.angle (d.tile.reindex e.symm) 1
    simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hs01
  have h12' : d'.tile.angle 1 < d'.tile.angle 2 := by
    change Triangle.angle (d.tile.reindex e.symm) 1 < Triangle.angle (d.tile.reindex e.symm) 2
    simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hs12
  have hγ := d'.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hne := d'.tile_angle_ne_pi_half_of_counterexample hn hnot 2
  have hrat := (d'.rational_angles_of_counterexample hn hnot).1
  have hrep : ¬ ReptilingAngles d'.tile T := fun h => hnot (d'.reptiling_necessary hn h)
  have hrel := d'.ordered_local_relation h01' h12' hγ hscalene hrep
  exact ⟨e.symm, h01', h12', hγ, hne, hrat,
    nonright_relation_of_local_relation _ _ _ d'.tile.angle_sum hne hrel⟩

end Tiling
end Erdos633b
