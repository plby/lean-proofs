/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Realizing ordered digit frames as covering sets of congruence moduli.
Informal source: Section 5 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridFrame
import ErdosProblems.Erdos1189.PrimeGrid
import ErdosProblems.Erdos1189.Core

namespace Erdos1189

open Finset

abbrev PrimeSlot (N : ℕ) := Grid.Slot (@coordinateSize N)

/-- CRT realizes a vector with exactly the tag's own digit nonzero. -/
noncomputable def frameResidue (N : ℕ) (s : PrimeSlot N) : ℕ :=
  Classical.choose (digitPoint_surjective N (Grid.spikePoint coordinateSize_pos s))

lemma digitPoint_frameResidue (N : ℕ) (s : PrimeSlot N) :
    digitPoint N (frameResidue N s) = Grid.spikePoint coordinateSize_pos s :=
  Classical.choose_spec (digitPoint_surjective N (Grid.spikePoint coordinateSize_pos s))

def frameModuli {N : ℕ} (m : PrimeSlot N → ℕ) : Finset ℕ := univ.image m

lemma mem_frameModuli {N d : ℕ} {m : PrimeSlot N → ℕ} :
    d ∈ frameModuli m ↔ ∃ s, m s = d := by simp [frameModuli]

lemma frameBox_ordered {N : ℕ} (m : PrimeSlot N → ℕ) (rank : PrimeCoordinate N → ℕ)
    (horder : ∀ s i, (i.2 : ℕ) < (m s).factorization i.1 →
      i = s.1 ∨ rank i < rank s.1) :
    Grid.IsOrderedTagFamily (fun s => congruenceBox N (m s) (frameResidue N s)) rank := by
  intro s i v hv
  by_cases hi : (i.2 : ℕ) < (m s).factorization i.1
  · have hv' : digitPoint N (frameResidue N s) i = v := by
      simpa [congruenceBox, hi] using hv
    rw [digitPoint_frameResidue] at hv'
    rcases horder s i hi with his | hlt
    · refine Or.inl ⟨his, ?_⟩
      subst i
      have hh := congrArg Fin.val hv'
      simpa only [Grid.spikePoint_self, Grid.slotValue] using hh.symm
    · refine Or.inr ⟨hlt, ?_⟩
      have his : i ≠ s.1 := by intro heq; rw [heq] at hlt; exact (lt_irrefl _ hlt)
      exact (congrArg Fin.val hv').symm.trans (Grid.spikePoint_other coordinateSize_pos s his)
  · simp [congruenceBox, hi] at hv

lemma digitPoint_eq_zero_iff {N n : ℕ} (hN : N ≠ 0) :
    digitPoint N n = Grid.zeroPoint coordinateSize_pos ↔ n ≡ 0 [MOD N] := by
  have hz : digitPoint N 0 = Grid.zeroPoint coordinateSize_pos := by
    funext i
    apply Fin.ext
    simp [digitPoint, digit, Grid.zeroPoint]
  rw [← contains_congruenceBox_iff (d := N) hN dvd_rfl]
  constructor
  · intro heq i v hv
    have hi : (i.2 : ℕ) < N.factorization i.1 := i.2.isLt
    have hv' : digitPoint N 0 i = v := by simpa [congruenceBox, hi] using hv
    rw [heq, ← hz]
    exact hv'
  · intro h
    rw [← hz]
    funext i
    exact h i (digitPoint N 0 i) (by simp [congruenceBox, i.2.isLt])

/-- Any nontrivial divisor may serve as the zero center, provided its modulus
is distinct from every tag modulus. -/
theorem digit_frame_covers {N P : ℕ} (hN : N ≠ 0) (hP : 1 < P) (hPN : P ∣ N)
    (m : PrimeSlot N → ℕ) (rank : PrimeCoordinate N → ℕ)
    (hm : ∀ s, 1 < m s) (hdiv : ∀ s, m s ∣ N) (hinj : Function.Injective m)
    (hcenter : P ∉ frameModuli m)
    (horder : ∀ s i, (i.2 : ℕ) < (m s).factorization i.1 →
      i = s.1 ∨ rank i < rank s.1) :
    IsCoveringSet (insert P (frameModuli m)) := by
  classical
  let a : ℕ → ℤ := Function.update
    (Function.extend m (fun s => (frameResidue N s : ℤ)) (fun _ => 0)) P 0
  have ha : ∀ s, a (m s) = frameResidue N s := by
    intro s
    have hs : m s ≠ P := fun heq => hcenter (mem_frameModuli.mpr ⟨s, heq⟩)
    simp only [a, Function.update_of_ne hs, hinj.extend_apply]
  refine ⟨?_, a, ?_⟩
  · intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact hP
    · obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
      exact hm s
  · apply (covers_iff_finite_period (Nat.pos_of_ne_zero hN) ?_).mpr
    · intro x
      by_cases hx : ∃ i, (digitPoint N x i : ℕ) ≠ 0
      · obtain ⟨s, hs⟩ := (frameBox_ordered m rank horder).covers_nonzero hx
        refine ⟨m s, mem_insert_of_mem (mem_frameModuli.mpr ⟨s, rfl⟩), ?_⟩
        rw [ha]
        exact Int.natCast_modEq_iff.mpr ((contains_congruenceBox_iff hN (hdiv s)).mp hs)
      · have heq : digitPoint N x = Grid.zeroPoint coordinateSize_pos := by
          funext i
          apply Fin.ext
          change (digitPoint N x i : ℕ) = 0
          exact not_not.mp (fun hi => hx ⟨i, hi⟩)
        refine ⟨P, mem_insert_self _ _, ?_⟩
        have hmod := ((digitPoint_eq_zero_iff hN).mp heq).of_dvd hPN
        simpa [a] using Int.natCast_modEq_iff.mpr hmod
    · intro d hd
      rcases mem_insert.mp hd with rfl | hd
      · exact hPN
      · obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
        exact hdiv s

end Erdos1189
