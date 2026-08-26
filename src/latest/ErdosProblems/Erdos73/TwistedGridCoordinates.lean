import ErdosProblems.Erdos73.Foundations

/-! Coordinate edges of the canonical twisted square grid. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def twistedCoordinateAdj {n : ℕ} (u v : Fin n × Fin n) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val)) ∨
  ((u.1.val + 1 = n ∧ v.1.val = 0 ∨ v.1.val + 1 = n ∧ u.1.val = 0) ∧
    u.2.val + v.2.val + 1 = n)

def twistedCoordinateGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj u v := u ≠ v ∧ twistedCoordinateAdj u v
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with ⟨hr, hc⟩ | ⟨hc, hr⟩ | ⟨hr, hc⟩
    · exact Or.inl ⟨hr.symm, hc.symm⟩
    · exact Or.inr (Or.inl ⟨hc.symm, hr.symm⟩)
    · exact Or.inr (Or.inr ⟨hr.symm, by omega⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cycleGraph_adj_coordinates {n : ℕ} {i j : Fin n}
    (h : (SimpleGraph.cycleGraph n).Adj i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n) := by
  rw [SimpleGraph.cycleGraph_adj'] at h
  have hsub (a b : Fin n) (hab : (a - b).val = 1) :
      a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val + 1 = n) := by
    have ha := a.isLt
    have hb := b.isLt
    by_cases hba : b ≤ a
    · rw [Fin.sub_val_of_le hba] at hab
      omega
    · have hh : n - b.val + a.val < n := by omega
      rw [Fin.val_sub, Nat.mod_eq_of_lt hh] at hab
      omega
  rcases h with h | h
  · have hh := hsub i j h
    omega
  · have hh := hsub j i h
    omega

theorem twistedLVertex_adj_of_succ {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n)
    (i j : Fin (twistedLCycleLength c)) (hij : i.val + 1 = j.val) :
    (twistedCoordinateGraph n).Adj (twistedLVertex c r i) (twistedLVertex c r j) := by
  refine ⟨fun he => ?_, ?_⟩
  · have he' := congrArg Fin.val (twistedLVertex_injective c r he)
    omega
  · have hc := c.property
    have hr := r.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hs := twistedLeft_add_span c
    have hz := twistedLeft_lt_right c
    dsimp only [twistedCoordinateAdj, twistedLVertex]
    split_ifs <;> simp only [Fin.ext_iff, Fin.val_mk, true_and]
    all_goals omega

theorem twistedLVertex_adj_of_wrap {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n)
    (i j : Fin (twistedLCycleLength c)) (hi : i.val = 0)
    (hj : j.val + 1 = twistedLCycleLength c) :
    (twistedCoordinateGraph n).Adj (twistedLVertex c r i) (twistedLVertex c r j) := by
  refine ⟨fun he => ?_, ?_⟩
  · have he' := congrArg Fin.val (twistedLVertex_injective c r he)
    have hh := twistedLCycleLength_three_le c
    omega
  · have hc := c.property
    have hr := r.isLt
    have hs := twistedLeft_add_span c
    have hz := twistedLeft_lt_right c
    change j.val + 1 = n + twistedLSpan c at hj
    have hi' : i.val ≤ r.val := by omega
    have hj' : ¬j.val ≤ r.val := by omega
    dsimp only [twistedCoordinateAdj]
    rw [twistedLVertex, dif_pos hi', twistedLVertex, dif_neg hj']
    split <;> simp only [Fin.mk.injEq, Fin.val_mk]
    all_goals dsimp only [twistedRightColumn] at *
    all_goals omega

theorem twistedLVertex_preserves_adj {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n)
    {i j : Fin (twistedLCycleLength c)}
    (h : (SimpleGraph.cycleGraph (twistedLCycleLength c)).Adj i j) :
    (twistedCoordinateGraph n).Adj (twistedLVertex c r i) (twistedLVertex c r j) := by
  rcases cycleGraph_adj_coordinates h with hij | hji | ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact twistedLVertex_adj_of_succ c r i j hij
  · exact (twistedLVertex_adj_of_succ c r j i hji).symm
  · exact twistedLVertex_adj_of_wrap c r i j hi hj
  · exact (twistedLVertex_adj_of_wrap c r j i hj hi).symm

theorem twistedCoordinateGraph_reflection {n : ℕ} {u v : Fin n × Fin n}
    (h : (twistedCoordinateGraph n).Adj u v) :
    (twistedCoordinateGraph n).Adj (twistedGridReflection n u) (twistedGridReflection n v) := by
  refine ⟨fun he => h.1 ((twistedGridReflection n).injective he), ?_⟩
  have hu := u.2.isLt
  have hv := v.2.isLt
  dsimp only [twistedCoordinateAdj, twistedGridReflection_apply] at *
  simp only [Fin.rev_inj, Fin.val_rev]
  rcases h.2 with ⟨hr, hc⟩ | ⟨hc, hr⟩ | ⟨hr, hc⟩
  · exact Or.inl ⟨hr, by omega⟩
  · exact Or.inr (Or.inl ⟨hc, hr⟩)
  · exact Or.inr (Or.inr ⟨hr, by omega⟩)

theorem twistedGridGraph_le_coordinateGraph (n : ℕ) :
    twistedGridGraph n ≤ twistedCoordinateGraph n := by
  apply iSup_le
  rintro ⟨c, r, reflected⟩
  rw [twistedMappedCycleGraph, SimpleGraph.map_le_iff_le_comap]
  intro i j hij
  change (twistedCoordinateGraph n).Adj
    (twistedCycleEmbedding c r reflected i) (twistedCycleEmbedding c r reflected j)
  cases reflected with
  | false => exact twistedLVertex_preserves_adj c r hij
  | true => exact twistedCoordinateGraph_reflection (twistedLVertex_preserves_adj c r hij)

end
end Erdos73
