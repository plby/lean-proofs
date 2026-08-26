/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Basic

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Residue blocks for Erdős Problem 330

The stage construction repeatedly adds long intervals restricted to a finite
set of residue classes modulo a modulus `M`.
-/

namespace Erdos330

open scoped Pointwise

/--
The natural numbers in `[lo, hi]` whose residue modulo `M` belongs to `Ω`.
For `M = 0`, `ZMod M` is still a Lean type; stage lemmas should carry
separate positivity hypotheses when they need genuine modular arithmetic.
-/
def residueBlock (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) : Set ℕ :=
  {n | lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω}

/-- A residue block parameterized by its lower endpoint and length. -/
def residueBlockLen (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) : Set ℕ :=
  residueBlock M Ω lo (lo + len)

/-- Finite version of `residueBlock`, used for cardinality estimates. -/
def residueBlockFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter fun n => (n : ZMod M) ∈ Ω

/-- Finite version of `residueBlockLen`. -/
def residueBlockLenFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) : Finset ℕ :=
  residueBlockFinset M Ω lo (lo + len)

theorem mem_residueBlock {M : ℕ} {Ω : Finset (ZMod M)} {lo hi n : ℕ} :
    n ∈ residueBlock M Ω lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω := by
  rfl

theorem mem_residueBlockLen {M : ℕ} {Ω : Finset (ZMod M)} {lo len n : ℕ} :
    n ∈ residueBlockLen M Ω lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ (n : ZMod M) ∈ Ω := by
  rfl

theorem mem_residueBlockFinset {M : ℕ} {Ω : Finset (ZMod M)} {lo hi n : ℕ} :
    n ∈ residueBlockFinset M Ω lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω := by
  simp only [residueBlockFinset, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem mem_residueBlockLenFinset {M : ℕ} {Ω : Finset (ZMod M)} {lo len n : ℕ} :
    n ∈ residueBlockLenFinset M Ω lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ (n : ZMod M) ∈ Ω := by
  simp only [residueBlockLenFinset, mem_residueBlockFinset]

theorem mem_residueBlockFinset_singleton {M : ℕ} [NeZero M] {ρ : ZMod M}
    {lo hi n : ℕ} :
    n ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) lo hi ↔
      lo ≤ n ∧ n ≤ hi ∧ n ≡ ρ.val [MOD M] := by
  rw [mem_residueBlockFinset]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hlo, hhi, heq⟩
    have hcast : (n : ZMod M) = (ρ.val : ZMod M) := by
      simpa [ZMod.natCast_zmod_val ρ] using heq
    exact ⟨hlo, hhi, (ZMod.natCast_eq_natCast_iff n ρ.val M).mp hcast⟩
  · rintro ⟨hlo, hhi, hmod⟩
    have hcast : (n : ZMod M) = (ρ.val : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff n ρ.val M).mpr hmod
    exact ⟨hlo, hhi, by simpa [ZMod.natCast_zmod_val ρ] using hcast⟩

theorem mem_residueBlockLenFinset_singleton {M : ℕ} [NeZero M] {ρ : ZMod M}
    {lo len n : ℕ} :
    n ∈ residueBlockLenFinset M ({ρ} : Finset (ZMod M)) lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ n ≡ ρ.val [MOD M] := by
  simp only [residueBlockLenFinset, mem_residueBlockFinset_singleton]

theorem coe_residueBlockFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) :
    (residueBlockFinset M Ω lo hi : Set ℕ) = residueBlock M Ω lo hi := by
  ext n
  simp [mem_residueBlockFinset, residueBlock]

theorem coe_residueBlockLenFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) :
    (residueBlockLenFinset M Ω lo len : Set ℕ) = residueBlockLen M Ω lo len := by
  ext n
  simp [mem_residueBlockLenFinset, residueBlockLen, residueBlock]

theorem residueBlock_subset_Icc {M : ℕ} {Ω : Finset (ZMod M)} {lo hi : ℕ} :
    residueBlock M Ω lo hi ⊆ Set.Icc lo hi := by
  intro n hn
  exact ⟨hn.1, hn.2.1⟩

theorem residueBlockLen_subset_Icc {M : ℕ} {Ω : Finset (ZMod M)} {lo len : ℕ} :
    residueBlockLen M Ω lo len ⊆ Set.Icc lo (lo + len) :=
  residueBlock_subset_Icc

theorem residueBlock_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo hi : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlock M Ω lo hi ⊆ residueBlock M Ω' lo hi := by
  intro n hn
  exact ⟨hn.1, hn.2.1, hΩ hn.2.2⟩

theorem residueBlockLen_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo len : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockLen M Ω lo len ⊆ residueBlockLen M Ω' lo len :=
  residueBlock_mono_residues hΩ

theorem residueBlockFinset_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo hi : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockFinset M Ω lo hi ⊆ residueBlockFinset M Ω' lo hi := by
  intro n hn
  rw [mem_residueBlockFinset] at hn ⊢
  exact ⟨hn.1, hn.2.1, hΩ hn.2.2⟩

theorem residueBlockLenFinset_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo len : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockLenFinset M Ω lo len ⊆ residueBlockLenFinset M Ω' lo len :=
  residueBlockFinset_mono_residues hΩ

theorem residueBlockFinset_card_le_interval (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) :
    (residueBlockFinset M Ω lo hi).card ≤ (Finset.Icc lo hi).card := by
  exact Finset.card_filter_le _ _

theorem residueBlockLenFinset_card_le_interval (M : ℕ) (Ω : Finset (ZMod M))
    (lo len : ℕ) :
    (residueBlockLenFinset M Ω lo len).card ≤ (Finset.Icc lo (lo + len)).card :=
  residueBlockFinset_card_le_interval M Ω lo (lo + len)

theorem residueBlockLenFinset_card_lower (M : ℕ) [NeZero M]
    (Ω : Finset (ZMod M)) (lo len : ℕ) :
    Ω.card * (len / M) ≤ (residueBlockLenFinset M Ω lo len).card := by
  classical
  let source : Finset (ZMod M × ℕ) := Ω.product (Finset.range (len / M))
  let rep : ZMod M → ℕ := fun ρ => (ρ - (lo : ZMod M)).val
  let f : ZMod M × ℕ → ℕ := fun zq => lo + zq.2 * M + rep zq.1
  have hmaps : Set.MapsTo f (source : Set (ZMod M × ℕ))
      (residueBlockLenFinset M Ω lo len : Set ℕ) := by
    intro zq hzq
    rcases zq with ⟨ρ, q⟩
    have hzq_mem : ρ ∈ Ω ∧ q ∈ Finset.range (len / M) := by
      simpa [source] using hzq
    change f (ρ, q) ∈ residueBlockLenFinset M Ω lo len
    rw [mem_residueBlockLenFinset]
    have hrep_lt : rep ρ < M := ZMod.val_lt (ρ - (lo : ZMod M))
    have hq_lt : q < len / M := by simpa using hzq_mem.2
    have hq_succ_mul : q * M + M ≤ len := by
      have hq_succ : q + 1 ≤ len / M := Nat.succ_le_iff.mpr hq_lt
      have hmul := (Nat.mul_le_mul_right M hq_succ).trans (Nat.div_mul_le_self len M)
      rwa [Nat.succ_mul] at hmul
    have hres : ((lo + q * M + rep ρ : ℕ) : ZMod M) = ρ := by
      dsimp [rep]
      calc
        ((lo + q * M + (ρ - (lo : ZMod M)).val : ℕ) : ZMod M)
            = (lo : ZMod M) + (q * M : ℕ) +
                ((ρ - (lo : ZMod M)).val : ZMod M) := by
              simp [Nat.cast_add]
        _ = (lo : ZMod M) + 0 + (ρ - (lo : ZMod M)) := by
              rw [ZMod.natCast_zmod_val]
              simp
        _ = ρ := by abel
    refine ⟨by dsimp [f]; omega, ?_, ?_⟩
    · dsimp [f]
      omega
    · simpa [f, hres] using hzq_mem.1
  have hinj : Set.InjOn f (source : Set (ZMod M × ℕ)) := by
    intro zq _hzq zq' _hzq' hff
    rcases zq with ⟨ρ, q⟩
    rcases zq' with ⟨ρ', q'⟩
    have hresρ : ((lo + q * M + rep ρ : ℕ) : ZMod M) = ρ := by
      dsimp [rep]
      calc
        ((lo + q * M + (ρ - (lo : ZMod M)).val : ℕ) : ZMod M)
            = (lo : ZMod M) + (q * M : ℕ) +
                ((ρ - (lo : ZMod M)).val : ZMod M) := by
              simp [Nat.cast_add]
        _ = (lo : ZMod M) + 0 + (ρ - (lo : ZMod M)) := by
              rw [ZMod.natCast_zmod_val]
              simp
        _ = ρ := by abel
    have hresρ' : ((lo + q' * M + rep ρ' : ℕ) : ZMod M) = ρ' := by
      dsimp [rep]
      calc
        ((lo + q' * M + (ρ' - (lo : ZMod M)).val : ℕ) : ZMod M)
            = (lo : ZMod M) + (q' * M : ℕ) +
                ((ρ' - (lo : ZMod M)).val : ZMod M) := by
              simp [Nat.cast_add]
        _ = (lo : ZMod M) + 0 + (ρ' - (lo : ZMod M)) := by
              rw [ZMod.natCast_zmod_val]
              simp
        _ = ρ' := by abel
    have hρeq : ρ = ρ' := by
      rw [← hresρ, ← hresρ']
      exact congrArg (fun n : ℕ => (n : ZMod M)) hff
    subst ρ'
    have hnat : q * M + rep ρ = q' * M + rep ρ := by
      dsimp [f] at hff
      omega
    have hmul : q * M = q' * M := by omega
    have hq : q = q' := Nat.mul_right_cancel (NeZero.pos M) hmul
    subst q'
    rfl
  calc
    Ω.card * (len / M) = source.card := by simp [source]
    _ ≤ (residueBlockLenFinset M Ω lo len).card :=
      Finset.card_le_card_of_injOn f hmaps hinj

theorem residueBlockFinset_eq_len_of_le {M : ℕ} {Ω : Finset (ZMod M)} {lo hi : ℕ}
    (hlohi : lo ≤ hi) :
    residueBlockFinset M Ω lo hi = residueBlockLenFinset M Ω lo (hi - lo) := by
  ext n
  rw [mem_residueBlockFinset, mem_residueBlockLenFinset]
  constructor <;> intro h
  · exact ⟨h.1, by omega, h.2.2⟩
  · exact ⟨h.1, by omega, h.2.2⟩

theorem residueBlockFinset_card_lower_of_le (M : ℕ) [NeZero M]
    (Ω : Finset (ZMod M)) {lo hi : ℕ} (hlohi : lo ≤ hi) :
    Ω.card * ((hi - lo) / M) ≤ (residueBlockFinset M Ω lo hi).card := by
  rw [residueBlockFinset_eq_len_of_le hlohi]
  exact residueBlockLenFinset_card_lower M Ω lo (hi - lo)

lemma exists_natCast_eq_zmod_in_Icc_len (M lo : ℕ) [NeZero M] (ρ : ZMod M) :
    ∃ x : ℕ, lo ≤ x ∧ x ≤ lo + M ∧ (x : ZMod M) = ρ := by
  let δ : ZMod M := ρ - (lo : ZMod M)
  refine ⟨lo + δ.val, by omega, ?_, ?_⟩
  · have hδ : δ.val < M := ZMod.val_lt δ
    omega
  · calc
      ((lo + δ.val : ℕ) : ZMod M) = (lo : ZMod M) + (δ.val : ZMod M) := by
        exact Nat.cast_add lo δ.val
      _ = (lo : ZMod M) + δ := by rw [ZMod.natCast_zmod_val]
      _ = ρ := by simp [δ]

theorem exists_residueBlock_pair_of_middle {M N L n : ℕ} [NeZero M]
    {Ω Θ : Finset (ZMod M)}
    (hML : M ≤ L) (hnlo : 2 * N + M ≤ n) (hnhi : n ≤ 2 * N + 2 * L - M)
    (hres : (n : ZMod M) ∈ (Ω : Set (ZMod M)) + (Θ : Set (ZMod M))) :
    ∃ x ∈ residueBlockFinset M Ω N (N + L),
      ∃ y ∈ residueBlockFinset M Θ N (N + L), x + y = n := by
  rcases hres with ⟨ω, hω, θ, hθ, hsum⟩
  let Jlo := max N (n - (N + L))
  have hJloN : N ≤ Jlo := le_max_left _ _
  have hJloLow : n - (N + L) ≤ Jlo := le_max_right _ _
  have hJhi_interval : Jlo + M ≤ N + L := by
    dsimp [Jlo]
    omega
  have hJhi_sub : Jlo + M ≤ n - N := by
    dsimp [Jlo]
    omega
  obtain ⟨x, hxlo, hxhi, hxω⟩ := exists_natCast_eq_zmod_in_Icc_len M Jlo ω
  have hxN : N ≤ x := hJloN.trans hxlo
  have hxNL : x ≤ N + L := hxhi.trans hJhi_interval
  have hxle_n_sub : x ≤ n - N := hxhi.trans hJhi_sub
  have hxle_n : x ≤ n := by omega
  let y := n - x
  have hyN : N ≤ y := by
    dsimp [y]
    omega
  have hyNL : y ≤ N + L := by
    dsimp [y]
    have hlow : n - (N + L) ≤ x := hJloLow.trans hxlo
    omega
  have hyθ : (y : ZMod M) = θ := by
    dsimp [y]
    calc
      ((n - x : ℕ) : ZMod M) = (n : ZMod M) - (x : ZMod M) := by
        exact Nat.cast_sub hxle_n
      _ = (ω + θ) - ω := by rw [← hsum, hxω]
      _ = θ := by abel
  have hxBlock : x ∈ residueBlockFinset M Ω N (N + L) := by
    rw [mem_residueBlockFinset]
    exact ⟨hxN, hxNL, by simpa [hxω] using hω⟩
  have hyBlock : y ∈ residueBlockFinset M Θ N (N + L) := by
    rw [mem_residueBlockFinset]
    exact ⟨hyN, hyNL, by simpa [hyθ] using hθ⟩
  refine ⟨x, hxBlock, y, hyBlock, ?_⟩
  dsimp [y]
  omega

theorem residueBlockFinset_middle_mem_twoFold_union {M N L n : ℕ} [NeZero M]
    {Ω Θ : Finset (ZMod M)}
    (hML : M ≤ L) (hnlo : 2 * N + M ≤ n) (hnhi : n ≤ 2 * N + 2 * L - M)
    (hres : (n : ZMod M) ∈ (Ω : Set (ZMod M)) + (Θ : Set (ZMod M))) :
    n ∈ twoFoldFinset
      (residueBlockFinset M Ω N (N + L) ∪ residueBlockFinset M Θ N (N + L)) := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    exists_residueBlock_pair_of_middle (M := M) (N := N) (L := L) (n := n)
      hML hnlo hnhi hres
  exact ⟨x, Finset.mem_union.mpr (Or.inl hx), y, Finset.mem_union.mpr (Or.inr hy), hxy⟩

theorem residueBlockFinset_middle_mem_twoFold_self {M N L n : ℕ} [NeZero M]
    {Ω : Finset (ZMod M)}
    (hML : M ≤ L) (hnlo : 2 * N + M ≤ n) (hnhi : n ≤ 2 * N + 2 * L - M)
    (hres : (n : ZMod M) ∈ (Ω : Set (ZMod M)) + (Ω : Set (ZMod M))) :
    n ∈ twoFoldFinset (residueBlockFinset M Ω N (N + L)) := by
  simpa using
    (residueBlockFinset_middle_mem_twoFold_union (M := M) (N := N) (L := L)
      (n := n) (Ω := Ω) (Θ := Ω) hML hnlo hnhi hres)

end Erdos330
