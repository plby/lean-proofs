import ErdosProblems.Erdos556.CycleCopyChords
import ErdosProblems.Erdos556.TwoParityCycle

/-! Same-parity vertices of a minimal even cycle have the opposite colour. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

theorem not_middle_even_chord {V : Type*} {G : SimpleGraph V} (t a : ℕ)
    [NeZero (2 * t)] (ha : 2 ≤ a) (hat : a + 2 ≤ t) (f : (cycleGraph (2 * t)).Copy G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ) :
    ¬ G.Adj (f 0) (f (↑(2 * a) : Fin (2 * t))) := by
  intro h
  have hfirst := complement_cross_chord_of_cycle_copy f (2 * a) (by omega) (by omega) hno h
  let g := reverseCycleCopy f
  have hneg : -(↑(2 * (t - a)) : Fin (2 * t)) = (↑(2 * a) : Fin (2 * t)) :=
    fin_neg_cast_of_add_eq _ _ (by omega)
  have hrev : G.Adj (g 0) (g (↑(2 * (t - a)) : Fin (2 * t))) := by
    simpa only [g, reverseCycleCopy_apply, neg_zero, hneg] using h
  have hsecond := complement_cross_chord_of_cycle_copy g (2 * (t - a)) (by omega) (by omega) hno hrev
  change Gᶜ.Adj (f (-(2 : Fin (2 * t))))
    (f (-(↑(2 * (t - a) + 1) : Fin (2 * t)))) at hsecond
  have hneg2 : -(2 : Fin (2 * t)) = (↑(2 * t - 2) : Fin (2 * t)) :=
    fin_neg_cast_of_add_eq 2 (2 * t - 2) (by omega)
  have hneg' : -(↑(2 * (t - a) + 1) : Fin (2 * t)) = (↑(2 * a - 1) : Fin (2 * t)) :=
    fin_neg_cast_of_add_eq _ _ (by omega)
  rw [hneg2, hneg'] at hsecond
  have h2 := complement_short_chords_of_cycle_copy (by omega : 4 ≤ 2 * t) f hno
  exact hnoc ((cycleGraph_isContained_iff (by omega : 2 < 2 * t - 1)).mpr
    (exists_odd_cycle_from_parity_chords t a ha hat f f.injective h2 hfirst hsecond))

theorem complement_even_chord_at_zero {V : Type*} {G : SimpleGraph V} (t a : ℕ)
    [NeZero (2 * t)] (ht : 4 ≤ t) (ha : 1 ≤ a) (hat : a < t)
    (f : (cycleGraph (2 * t)).Copy G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ) :
    Gᶜ.Adj (f 0) (f (↑(2 * a) : Fin (2 * t))) := by
  by_cases ha1 : a = 1
  · subst a
    have h := complement_short_chords_of_cycle_copy (by omega : 4 ≤ 2 * t) f hno 0
    simpa only [zero_add, Nat.mul_one, Nat.cast_ofNat] using h
  by_cases hlast : a + 1 = t
  · have h := complement_short_chords_of_cycle_copy (by omega : 4 ≤ 2 * t) f hno
      (↑(2 * a) : Fin (2 * t))
    have he : (↑(2 * a) : Fin (2 * t)) + 2 = 0 := by
      change (↑(2 * a) : Fin (2 * t)) + (↑(2 : ℕ) : Fin (2 * t)) = 0
      rw [← Nat.cast_add, show 2 * a + 2 = 2 * t by omega, Fin.natCast_self]
    rw [he] at h
    exact h.symm
  rw [compl_adj]
  refine ⟨?_, not_middle_even_chord t a (by omega) (by omega) f hno hnoc⟩
  intro he
  have hi := congrArg Fin.val (f.injective he)
  change 0 = (2 * a) % (2 * t) at hi
  rw [Nat.mod_eq_of_lt (by omega : 2 * a < 2 * t)] at hi
  omega

theorem complement_even_chords_of_cycle_copy {V : Type*} {G : SimpleGraph V} (t a : ℕ)
    [NeZero (2 * t)] (ht : 4 ≤ t) (ha : 1 ≤ a) (hat : a < t)
    (f : (cycleGraph (2 * t)).Copy G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ)
    (i : Fin (2 * t)) : Gᶜ.Adj (f i) (f (i + (↑(2 * a) : Fin (2 * t)))) := by
  simpa only [rotateCycleCopy_apply, add_zero] using
    complement_even_chord_at_zero t a ht ha hat (rotateCycleCopy f i) hno hnoc

theorem complement_adj_of_same_parity {V : Type*} {G : SimpleGraph V} (t : ℕ)
    [NeZero (2 * t)] (ht : 4 ≤ t) (f : (cycleGraph (2 * t)).Copy G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ)
    (i j : Fin (2 * t)) (hne : i ≠ j) (hpar : i.val % 2 = j.val % 2) : Gᶜ.Adj (f i) (f j) := by
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  wlog hij : i.val < j.val generalizing i j
  · exact (this j i hne.symm hpar.symm hneval.symm (by omega)).symm
  let a := (j.val - i.val) / 2
  have hdiff : i.val + 2 * a = j.val := by dsimp only [a]; omega
  have ha : 1 ≤ a := by omega
  have hat : a < t := by have hj := j.isLt; omega
  have he : i + (↑(2 * a) : Fin (2 * t)) = j := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_natCast,
      Nat.mod_eq_of_lt (show 2 * a < 2 * t by omega), hdiff, Nat.mod_eq_of_lt j.isLt]
  have h := complement_even_chords_of_cycle_copy t a ht ha hat f hno hnoc i
  simpa only [he] using h

#print axioms complement_adj_of_same_parity

end Erdos556
