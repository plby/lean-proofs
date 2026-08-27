/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNaturalResidueSieve

/-! # The zero-extended initial residue sieve on a literal integer interval -/

namespace Erdos4b.FGKMT

noncomputable section

def zeroExtendedResidue (S P : Finset ℕ) (b : ResidueAssignment S) (r : ResidueAssignment P)
    (p : ℕ) : ℕ :=
  if h : p ∈ S then (b ⟨p, h⟩).val else if h : p ∈ P then (r ⟨p, h⟩).val else 0

theorem zeroExtendedResidue_small (S P : Finset ℕ) (b : ResidueAssignment S)
    (r : ResidueAssignment P) (p : S) : zeroExtendedResidue S P b r p.val = (b p).val := by
  rw [zeroExtendedResidue, dif_pos p.property]

theorem zeroExtendedResidue_large (S P : Finset ℕ) (b : ResidueAssignment S)
    (r : ResidueAssignment P) (hSP : Disjoint S P) (p : P) :
    zeroExtendedResidue S P b r p.val = (r p).val := by
  have hpS : p.val ∉ S := fun h => Finset.disjoint_left.mp hSP h p.property
  rw [zeroExtendedResidue, dif_neg hpS, dif_pos p.property]

theorem zeroExtendedResidue_zero (S P : Finset ℕ) (b : ResidueAssignment S)
    (r : ResidueAssignment P) {p : ℕ} (hpS : p ∉ S) (hpP : p ∉ P) :
    zeroExtendedResidue S P b r p = 0 := by
  rw [zeroExtendedResidue, dif_neg hpS, dif_neg hpP]

open scoped Classical in
def initialResidueSurvivors (x Y : ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  (Finset.Ioc x Y).filter fun n => ∀ p ∈ Nat.primesLE x, ¬n ≡ r p [MOD p]

theorem mem_initialResidueSurvivors (x Y : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    n ∈ initialResidueSurvivors x Y r ↔
      x < n ∧ n ≤ Y ∧ ∀ p ∈ Nat.primesLE x, ¬n ≡ r p [MOD p] := by
  simp only [initialResidueSurvivors, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

theorem initialResidueSurvivors_subset (x Y : ℕ) (r : ℕ → ℕ) :
    initialResidueSurvivors x Y r ⊆ Finset.Ioc x Y := by
  classical
  exact Finset.filter_subset _ _

theorem initialResidueSurvivors_not_dvd {x Y n p : ℕ} {r : ℕ → ℕ}
    (hn : n ∈ initialResidueSurvivors x Y r) (hp : p.Prime) (hpx : p ≤ x)
    (hr : r p = 0) : ¬p ∣ n := by
  intro hpn
  have hnot := (mem_initialResidueSurvivors x Y r n).mp hn |>.2.2 p
    (Nat.mem_primesLE.mpr ⟨hpx, hp⟩)
  apply hnot
  rw [hr, Nat.ModEq, Nat.mod_eq_zero_of_dvd hpn, Nat.zero_mod]

theorem initialResidueSurvivors_avoids {x Y n : ℕ} {r : ℕ → ℕ}
    (hn : n ∈ initialResidueSurvivors x Y r) (S : Finset ℕ) (b : ResidueAssignment S)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ x) (hr : ∀ p : S, r p.val = (b p).val) :
    residueAssignmentAvoids S {(n : ℤ)} b := by
  rw [residueAssignmentAvoids_nat_singleton_iff]
  intro p heq
  have hnot := (mem_initialResidueSurvivors x Y r n).mp hn |>.2.2 p.val
    (Nat.mem_primesLE.mpr ⟨(hS p.val p.property).2, (hS p.val p.property).1⟩)
  apply hnot
  rw [Nat.ModEq, hr p, Nat.mod_eq_of_lt (b p).isLt]
  exact heq

end

end Erdos4b.FGKMT
