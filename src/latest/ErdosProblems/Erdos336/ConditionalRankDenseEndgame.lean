import Mathlib
import ErdosProblems.Erdos336.DenseProgressionCore
import ErdosProblems.Erdos336.RankOneExtensionEndgame
import ErdosProblems.Erdos336.NonemptyFiniteRemoval

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Conditional finite endgame from a rank-or-dense small-doubling certificate
-/

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The precise output needed from the remaining cyclic small-doubling
structure theorem.  The rank alternative includes a long progression support
for the high power and an endpoint-attaining (possibly shorter) outer interval
for its root. -/
def RankDenseCertificate (C : Set G) (t : ℕ) : Prop :=
  let S := ExactPower C t
  Fintype.card G < 30000 * S.ncard ∨
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

/-- Iterating an exact-power set multiplies the exponent. -/
theorem exactPower_exactPower (A : Set G) (t k : ℕ) :
    ExactPower (ExactPower A t) k = ExactPower A (k * t) := by
  simp only [exactPower_eq_nsmul, smul_smul]

/-- A full exact power of a zero-containing set remains full at every larger
exponent. -/
theorem all_exact_mono_of_zero {A : Set G} (hzero : 0 ∈ A)
    {q M : ℕ} (hqM : q ≤ M)
    (hq : ∀ y : G, GroupRepExactly A q y) :
    ∀ y : G, GroupRepExactly A M y := by
  intro y
  exact exactPower_mono_of_zero hzero hqM (hq y)

/-- The rank alternative gives exact coverage at cost
`2t + extensionRankOneCost h`. -/
theorem exact_cover_of_rank_certificate
    {B : Set G} {b : G} (hb : b ∈ B)
    {h t : ℕ} (hweak : ∀ y : G, GroupRepAtMost B h y)
    (hrank :
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
            π q = π p + (L₀ : ZMod m)) :
    ∀ y : G,
      GroupRepExactly B (2 * t + extensionRankOneCost h) y := by
  obtain ⟨m, hm, π, hπ, α, L, V, hL, houterS, hfiber, hdense,
    α₀, L₀, p, q, hL₀, hL₀L, houterC, hp, hq, hpq⟩ := hrank
  let C : Set G := ShiftToZero B b
  let S : Set G := ExactPower C t
  let β : ZMod m := α + α + (L - L / 2 : ℕ)
  have hcoreS : ∀ s : ℕ, s ≤ L → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly S 2 y := by
    simpa [C, S, β] using dense_outer_interval_gives_full_fiber_core
      π hL houterS hfiber hdense
  let αB : ZMod m := α₀ + π b
  let βB : ZMod m := β + (2 * t) • π b
  let pB : G := p + b
  let qB : G := q + b
  have hpB : pB ∈ B := by
    simpa [pB, C, ShiftToZero] using hp
  have hqB : qB ∈ B := by
    simpa [qB, C, ShiftToZero] using hq
  have hstepB : π qB = π pB + (L₀ : ZMod m) := by
    dsimp [pB, qB]
    simp only [map_add]
    rw [hpq]
    abel
  have houterB : ∀ x ∈ B, ∃ k : ℕ, k ≤ L₀ ∧
      π x = αB + (k : ZMod m) := by
    intro x hx
    have hxC : x - b ∈ C := by simpa [C, ShiftToZero]
    obtain ⟨k, hk, hxk⟩ := houterC (x - b) hxC
    refine ⟨k, hk, ?_⟩
    dsimp [αB]
    calc
      π x = π (x - b) + π b := by rw [map_sub]; abel
      _ = (α₀ + (k : ZMod m)) + π b := by rw [hxk]
      _ = α₀ + π b + (k : ZMod m) := by abel
  have hcoreB : ∀ s : ℕ, s ≤ L → ∀ y : G,
      π y = βB + (s : ZMod m) → GroupRepExactly B (2 * t) y := by
    intro s hs y hy
    have hproj : π (y - (2 * t) • b) = β + (s : ZMod m) := by
      rw [map_sub, map_nsmul, hy]
      dsimp [βB]
      abel
    have hS := hcoreS s hs (y - (2 * t) • b) hproj
    have hC : GroupRepExactly C (2 * t) (y - (2 * t) • b) := by
      change y - (2 * t) • b ∈ ExactPower C (2 * t)
      rw [← exactPower_exactPower C t 2]
      change y - (2 * t) • b ∈ ExactPower S 2
      change y - (2 * t) • b ∈ ExactPower S 2 at hS
      simpa [Nat.mul_comm] using hS
    apply groupRepExactly_shift_iff.mpr
    simpa [C] using hC
  exact full_coverage_of_outer_interval_and_core hm π hπ hweak houterB
    hpB hqB hstepB hcoreB hL₀L hL₀

/-- A rank-or-dense certificate for a positive primitive high power gives a
uniform exact bound after padding in the zero-containing translate. -/
theorem exact_cover_of_rankDenseCertificate
    {B : Set G} {b : G} (hb : b ∈ B)
    {h t T : ℕ} (ht : 0 < t) (htT : t ≤ T)
    (hweak : ∀ y : G, GroupRepAtMost B h y)
    (hexact : ∃ q : ℕ, ∀ y : G, GroupRepExactly B q y)
    (hcert : RankDenseCertificate (ShiftToZero B b) t) :
    ∀ y : G,
      GroupRepExactly B (2 ^ 26 * T + extensionRankOneCost h) y := by
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
  let M : ℕ := 2 ^ 26 * T + extensionRankOneCost h
  have htarget : ∀ y : G, GroupRepExactly C M y := by
    rcases hcert with hdense | hrank
    · obtain ⟨u, hu, huU, hfull⟩ :=
        dense_highPower_saturates hzeroC hprimitiveC ht hdense
      have hqfull : ∀ y : G, GroupRepExactly C (u * t) y := by
        intro y
        change y ∈ ExactPower C (u * t)
        rw [hfull]
        trivial
      apply all_exact_mono_of_zero hzeroC
        (q := u * t) (M := M)
      · have huT : u * t ≤ 2 ^ 26 * T := Nat.mul_le_mul huU htT
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
      · have htwo : 2 * t ≤ 2 ^ 26 * T := by
          have htwoPow : 2 ≤ 2 ^ 26 := by norm_num
          exact le_trans (Nat.mul_le_mul_left 2 htT)
            (Nat.mul_le_mul_right T htwoPow)
        dsimp [M]
        omega
      · exact hrankC
  exact (all_exact_shift_iff M).mpr htarget

end Erdos336
