import ErdosProblems.Erdos73.PairedPorts
import ErdosProblems.Erdos73.UCombPortRegions

/-! Row and boundary-rank orders of the concatenated endpoints of crossing handles. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {N c r L : ℕ}

theorem crossing_sources_before_targets (s t : Fin N → ℕ)
    (hrow : ∀ i, s i < t i)
    (hcross : ∀ i j, i < j → s i < s j ∧ s j < t i ∧ t i < t j) :
    ∀ i j, s i < t j := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hh := hcross i j hij
    omega
  · exact hrow i
  · exact (hcross j i hji).2.1

theorem sameSide_paired_rows_strictMono
    (s t : Fin N → ElementaryWallVertex c r)
    (hrow : ∀ i, (s i).val.1.val < (t i).val.1.val)
    (hcross : ∀ i j, i < j → (s i).val.1.val < (s j).val.1.val ∧
      (s j).val.1.val < (t i).val.1.val ∧ (t i).val.1.val < (t j).val.1.val) :
    StrictMono (fun i => (pairedPorts s t i).val.1.val) := by
  rw [pairedPorts_map (fun w : ElementaryWallVertex c r => w.val.1.val) s t]
  exact pairedPorts_strictMono _ _ (fun _ _ hij => (hcross _ _ hij).1)
    (fun _ _ hij => (hcross _ _ hij).2.2) (crossing_sources_before_targets _ _ hrow hcross)

def throughPortSides : Fin (2 * N) → Bool := pairedPorts (fun _ => true) (fun _ => false)

theorem through_paired_rank_eq (s t : Fin N → ElementaryWallVertex c r) :
    twoSidePortRank (pairedPorts s t) throughPortSides L =
      pairedPorts (fun i => (s i).val.1.val)
        (fun i => 2 * uCombBase L (2 * N) - (t i).val.1.val) := by
  funext i
  rcases pairedPorts_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [twoSidePortRank, throughPortSides, pairedPorts_first, ite_true]
  · simp only [twoSidePortRank, throughPortSides, pairedPorts_second,
      Bool.false_eq_true, if_false]

theorem through_paired_rank_strictMono (s t : Fin N → ElementaryWallVertex c r)
    (hs : StrictMono (fun i => (s i).val.1.val))
    (ht : StrictAnti (fun i => (t i).val.1.val))
    (hsL : ∀ i, (s i).val.1.val ≤ L) (htL : ∀ i, (t i).val.1.val ≤ L) :
    StrictMono (twoSidePortRank (pairedPorts s t) throughPortSides L) := by
  rw [through_paired_rank_eq]
  apply pairedPorts_strictMono _ _ hs
  · intro i j hij
    have hh := ht hij
    have hi := htL i
    dsimp only at hh hi
    dsimp only [uCombBase]
    omega
  · intro i j
    have hi := hsL i
    have hj := htL j
    dsimp only [uCombBase]
    omega

end
end Erdos73
