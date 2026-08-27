import ErdosProblems.Erdos4.TiltedBlocks
import ErdosProblems.Erdos4.TiltedLabelLaw

/-! A block size chosen from the actual target count gives uniform partition-size bounds. -/

namespace Erdos4.Tilted

def blockSize (x : ℕ) (C : Finset ℕ) : ℕ := C.card / x + 1

theorem blockSize_pos (x : ℕ) (C : Finset ℕ) : 0 < blockSize x C := by
  exact Nat.succ_pos _

theorem blockSize_cast_le (x : ℕ) (C : Finset ℕ) :
    (blockSize x C : ℝ) ≤ (C.card : ℝ) / x + 1 := by
  simp only [blockSize, Nat.cast_add, Nat.cast_one]
  exact add_le_add (Nat.cast_div_le (α := ℝ)) le_rfl

theorem blockSize_mul_le {x : ℕ} (_hx : 0 < x) (C : Finset ℕ) (hC : x ≤ C.card) :
    x * blockSize x C ≤ 2 * C.card := by
  have hh := Nat.div_mul_le_self C.card x
  unfold blockSize
  nlinarith

theorem card_lt_mul_blockSize {x : ℕ} (hx : 0 < x) (C : Finset ℕ) :
    C.card < x * blockSize x C := by
  have hh := Nat.mod_add_div C.card x
  have hr := Nat.mod_lt C.card hx
  unfold blockSize
  nlinarith

theorem exists_balanced_fiber_partition {x p : ℕ} (hx : 0 < x) (hp : p.Prime)
    (C : Finset ℕ) (hC : x ≤ C.card) :
    ∃ P : Finpartition C,
      (∀ E ∈ P.parts, E.card ≤ blockSize x C) ∧
      (∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) ∧
      x ≤ 2 * P.parts.card ∧ P.parts.card ≤ x + p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hsize, hfiber, hlo, hhi⟩ := exists_all_fiber_partition C
    (fun n : ℕ => (n : ZMod p)) (blockSize_pos x C)
  have hhi' : P.parts.card * blockSize x C ≤ C.card + p * blockSize x C := by
    simpa only [ZMod.card] using hhi
  have hK := blockSize_pos x C
  have hKmul := blockSize_mul_le hx C hC
  have hClt := card_lt_mul_blockSize hx C
  refine ⟨P, hsize, hfiber, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem partition_count_pos {x : ℕ} (hx : 0 < x) {C : Finset ℕ} (P : Finpartition C)
    (hP : x ≤ 2 * P.parts.card) : 0 < P.parts.card := by omega

theorem inverse_partition_count_le {x : ℕ} (hx : 0 < x) {C : Finset ℕ} (P : Finpartition C)
    (hP : x ≤ 2 * P.parts.card) : 1 / (P.parts.card : ℝ) ≤ 2 / x := by
  have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hPR : (0 : ℝ) < P.parts.card := Nat.cast_pos.mpr (partition_count_pos hx P hP)
  apply (div_le_div_iff₀ hPR hxR).mpr
  have hh : (x : ℝ) ≤ 2 * (P.parts.card : ℝ) := by exact_mod_cast hP
  simpa only [one_mul] using hh

end Erdos4.Tilted
