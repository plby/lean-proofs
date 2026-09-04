import Mathlib
import ErdosProblems.Erdos336.BlockScaleSmallDoubling
import ErdosProblems.Erdos336.ConditionalRankDenseEndgame

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite theorem reduced to one explicit high-power structure statement
-/

namespace Erdos336

/-- Remaining structural input, isolated exactly: every primitive
zero-containing high power in a finite cyclic group with strict doubling below
`9/4` has the rank-or-dense certificate used by F-067. -/
def HasHighPowerRankDenseStructure : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
    ∀ (C : Set (ZMod N)) (t : ℕ),
      15 ≤ t → 0 ∈ C →
      (∃ q : ℕ, ExactPower C q = Set.univ) →
      4 * (ExactPower C (2 * t)).ncard <
        9 * (ExactPower C t).ncard →
      RankDenseCertificate C t

/-- Conditional sharp finite theorem on one explicit block. -/
theorem cyclicWeakStrongBoundNE_of_structure_block
    (hstruct : HasHighPowerRankDenseStructure)
    {h K : ℕ} (hh : 15 ≤ h) (hK : 0 < K)
    (hblock : h + 1 < 128 ^ K) :
    CyclicWeakStrongBoundNE h
      (2 ^ 26 * (h * 64 ^ K) + extensionRankOneCost h) := by
  intro N hN B hBne hweak hexact
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨i, hi, hiscale, hdoub⟩ :=
    exists_small_doubling_before_block_scale hb hweak hK hblock
  let C : Set (ZMod N) := ShiftToZero B b
  let t : ℕ := 2 ^ i * h
  let T : ℕ := h * 64 ^ K
  have ht : 0 < t := by dsimp [t]; positivity
  have ht15 : 15 ≤ t := by
    dsimp [t]
    calc
      15 ≤ h := hh
      _ ≤ 2 ^ i * h := by
        exact Nat.le_mul_of_pos_left h (by positivity)
  have htT : t ≤ T := by
    dsimp [t, T]
    have hiweak : 2 ^ i ≤ 2 ^ (i + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hipow : 2 ^ i ≤ 64 ^ K := le_trans hiweak hiscale
    nlinarith [Nat.zero_le h]
  have hzeroC : 0 ∈ C := zero_mem_shiftToZero hb
  obtain ⟨q, hq⟩ := hexact
  have hqC : ∀ y : ZMod N, GroupRepExactly C q y :=
    (all_exact_shift_iff q).mp hq
  have hprimitiveC : ∃ q : ℕ, ExactPower C q = Set.univ := by
    refine ⟨q, ?_⟩
    ext y
    simp only [Set.mem_univ, iff_true]
    exact hqC y
  have hdoub' : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard := by
    simpa [C, t, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hdoub
  have hcert : RankDenseCertificate C t :=
    hstruct N hN C t ht15 hzeroC hprimitiveC hdoub'
  simpa [T] using exact_cover_of_rankDenseCertificate
    hb ht htT hweak ⟨q, hq⟩ hcert

/-- The corresponding conditional cyclic removal bound follows through the
correct nonempty normalization. -/
theorem cyclicRemovalBound_of_structure_block
    (hstruct : HasHighPowerRankDenseStructure)
    {h K : ℕ} (hh : 15 ≤ h) (hK : 0 < K)
    (hblock : h + 1 < 128 ^ K) :
    CyclicRemovalBound h
      (2 ^ 26 * (h * 64 ^ K) + extensionRankOneCost h) :=
  cyclicRemovalBound_of_weakStrongBoundNE
    (cyclicWeakStrongBoundNE_of_structure_block hstruct hh hK hblock)

end Erdos336
