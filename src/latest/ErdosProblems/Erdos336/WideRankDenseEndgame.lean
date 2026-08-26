import ErdosProblems.Erdos336.ConditionalRankDenseEndgame
import ErdosProblems.Erdos336.WideDenseSaturation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def WideRankDenseCertificate (C : Set G) (t : ℕ) : Prop :=
  let S := ExactPower C t
  Fintype.card G < (30000000 * Nat.factorial 36) * S.ncard ∨
  ∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
    ∃ (α : ZMod m) (L V : ℕ),
      15 ≤ L ∧
      (∀ x ∈ S, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) ∧
      (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
      4 * L * V < 5 * S.ncard ∧
      ∃ (α₀ : ZMod m) (L₀ : ℕ) (p q : G),
        0 < L₀ ∧ L₀ ≤ L ∧
        (∀ x ∈ C, ∃ k : ℕ, k ≤ L₀ ∧ π x = α₀ + (k : ZMod m)) ∧
        p ∈ C ∧ q ∈ C ∧ π q = π p + (L₀ : ZMod m)

/-- A rank-or-dense certificate for a positive primitive high power gives a
uniform exact bound after padding in the zero-containing translate. -/
theorem exact_cover_of_wideRankDenseCertificate
    {B : Set G} {b : G} (hb : b ∈ B)
    {h t T : ℕ} (ht : 0 < t) (htT : t ≤ T)
    (hweak : ∀ y : G, GroupRepAtMost B h y)
    (hexact : ∃ q : ℕ, ∀ y : G, GroupRepExactly B q y)
    (hcert : WideRankDenseCertificate (ShiftToZero B b) t) :
    ∀ y : G,
      GroupRepExactly B (2 ^ 280 * T + extensionRankOneCost h) y := by
  let C : Set G := ShiftToZero B b
  have hzeroC : 0 ∈ C := zero_mem_shiftToZero hb
  obtain ⟨q, hq⟩ := hexact
  have hqC : ∀ y : G, GroupRepExactly C q y :=
    (all_exact_shift_iff q).mp hq
  have hprimitiveC : ∃ q : ℕ, ExactPower C q = Set.univ := by
    refine ⟨q, ?_⟩
    ext y
    simp only [Set.mem_univ, iff_true]
    exact hqC y
  let M : ℕ := 2 ^ 280 * T + extensionRankOneCost h
  have htarget : ∀ y : G, GroupRepExactly C M y := by
    rcases hcert with hdense | hrank
    · obtain ⟨u, hu, huU, hfull⟩ :=
        wide_dense_highPower_saturates hzeroC hprimitiveC ht hdense
      have hqfull : ∀ y : G, GroupRepExactly C (u * t) y := by
        intro y
        change y ∈ ExactPower C (u * t)
        rw [hfull]
        trivial
      apply all_exact_mono_of_zero hzeroC
        (q := u * t) (M := M)
      · have huT : u * t ≤ 2 ^ 280 * T := Nat.mul_le_mul huU htT
        dsimp [M]
        omega
      · exact hqfull
    · have hrankB :
          ∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
            ∃ (α : ZMod m) (L V : ℕ),
              15 ≤ L ∧
              (∀ x ∈ ExactPower (ShiftToZero B b) t,
                ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) ∧
              (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
              4 * L * V < 5 * (ExactPower (ShiftToZero B b) t).ncard ∧
              ∃ (α₀ : ZMod m) (L₀ : ℕ) (p q : G),
                0 < L₀ ∧ L₀ ≤ L ∧
                (∀ x ∈ ShiftToZero B b,
                  ∃ k : ℕ, k ≤ L₀ ∧ π x = α₀ + (k : ZMod m)) ∧
                p ∈ ShiftToZero B b ∧ q ∈ ShiftToZero B b ∧
                π q = π p + (L₀ : ZMod m) := by
          simpa [C] using hrank
      have hrankFull := exact_cover_of_rank_certificate hb hweak hrankB
      have hrankC : ∀ y : G,
          GroupRepExactly C (2 * t + extensionRankOneCost h) y :=
        (all_exact_shift_iff (2 * t + extensionRankOneCost h)).mp hrankFull
      apply all_exact_mono_of_zero hzeroC
        (q := 2 * t + extensionRankOneCost h) (M := M)
      · have htwo : 2 * t ≤ 2 ^ 280 * T := by
          have htwoPow : 2 ≤ 2 ^ 280 := by
            calc
              2 = 2 ^ 1 := by simp
              _ ≤ 2 ^ 280 := Nat.pow_le_pow_right (by omega) (by omega)
          exact le_trans (Nat.mul_le_mul_left 2 htT)
            (Nat.mul_le_mul_right T htwoPow)
        dsimp [M]
        omega
      · exact hrankC
  exact (all_exact_shift_iff M).mpr htarget


end Erdos336
