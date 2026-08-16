/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Wikipedia.SzemeredisTheorem.FormalConjectures139
import Wikipedia.SzemeredisTheorem.UpperDensity

open scoped Topology

namespace SzemeredisTheorem

private theorem finitarySzemeredi_of_cyclic_count {k : ℕ} (hk : 1 < k) :
    FinitarySzemeredi k := by
  intro δ hδ
  let K : ℕ := max 2 k
  have hKtwo : 2 ≤ K := le_max_left 2 k
  have hkK : k ≤ K := le_max_right 2 k
  obtain ⟨c, hc, huniform⟩ :=
    Wikipedia.SzemeredisTheorem.szemeredi K hKtwo (by positivity : 0 < δ / 8)
  obtain ⟨m : ℕ, hm : 1 / c < m⟩ := exists_nat_gt (1 / c)
  refine ⟨max 1 m, by simp, ?_⟩
  intro N hN A hA hdense
  have hNpos : 0 < N := (le_max_left 1 m).trans hN
  let M : ℕ := 4 * (N + 1)
  letI : NeZero M := ⟨by dsimp [M]; omega⟩
  have hNM : N + 1 ≤ M := by
    dsimp [M]
    omega
  let S : Finset (ZMod M) :=
    Wikipedia.SzemeredisTheorem.cyclicPrefix (A : Set ℕ) N M
  have hprefix : Wikipedia.SzemeredisTheorem.naturalPrefix (A : Set ℕ) N = A := by
    ext x
    simp only [Wikipedia.SzemeredisTheorem.naturalPrefix, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hx
      have hxI := hA hx
      simp only [Finset.mem_Icc] at hxI
      exact ⟨by omega, hx⟩
  have hmean : δ / 8 ≤
      Wikipedia.SzemeredisTheorem.mean
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by
    rw [show S = Wikipedia.SzemeredisTheorem.cyclicPrefix (A : Set ℕ) N M from rfl,
      Wikipedia.SzemeredisTheorem.mean_cyclicPrefix (A := (A : Set ℕ)) hNM,
      Wikipedia.SzemeredisTheorem.prefixDensity_eq_card, hprefix]
    have hratio : (((N + 1 : ℕ) : ℝ) / (M : ℕ)) = 1 / 4 := by
      dsimp [M]
      push_cast
      field_simp
    rw [hratio]
    have htwo : N + 1 ≤ 2 * N := by omega
    have hscale : (δ / 2) * (N + 1 : ℕ) ≤ δ * (N : ℝ) := by
      calc
        (δ / 2) * (N + 1 : ℕ) ≤ (δ / 2) * (2 * N : ℕ) := by
          gcongr
        _ = δ * (N : ℝ) := by push_cast; ring
    have hdense' : δ / 2 ≤ (A.card : ℝ) / (N + 1 : ℕ) := by
      have hden : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      exact (le_div_iff₀ hden).2 (hscale.trans hdense)
    nlinarith
  have hcyclic :
      c ≤ Wikipedia.SzemeredisTheorem.cyclicAPCount K M
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) :=
    huniform M S hmean
  have hf0 : ∀ x : ZMod M,
      0 ≤ Wikipedia.SzemeredisTheorem.finsetIndicator S x := by
    intro x
    unfold Wikipedia.SzemeredisTheorem.finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod M,
      Wikipedia.SzemeredisTheorem.finsetIndicator S x ≤ 1 := by
    intro x
    unfold Wikipedia.SzemeredisTheorem.finsetIndicator
    split <;> norm_num
  have hmean_one : Wikipedia.SzemeredisTheorem.mean
      (Wikipedia.SzemeredisTheorem.finsetIndicator S) ≤ 1 :=
    Wikipedia.SzemeredisTheorem.mean_le_of_le_const hf1
  have hm_real : 1 / c < (N : ℝ) :=
    hm.trans_le (by exact_mod_cast ((le_max_right 1 m).trans hN))
  have hone_N : 1 < (M : ℝ) * c := by
    have hone : 1 < (N : ℝ) * c := (div_lt_iff₀ hc).mp hm_real
    have hNM' : (N : ℝ) ≤ M := by
      exact_mod_cast (show N ≤ M by dsimp [M]; omega)
    exact hone.trans_le (mul_le_mul_of_nonneg_right hNM' hc.le)
  have hoffdiag :
      0 < Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass K M
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by
    apply Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass_pos_of_count
      (by omega) hf0 hf1
    calc
      1 ^ (K - 1) * Wikipedia.SzemeredisTheorem.mean
          (Wikipedia.SzemeredisTheorem.finsetIndicator S) =
          Wikipedia.SzemeredisTheorem.mean
            (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by simp
      _ ≤ 1 := hmean_one
      _ < (M : ℝ) * c := hone_N
      _ ≤ (M : ℝ) * Wikipedia.SzemeredisTheorem.cyclicAPCount K M
          (Wikipedia.SzemeredisTheorem.finsetIndicator S) :=
        mul_le_mul_of_nonneg_left hcyclic (by positivity)
  obtain ⟨a, d, hd, hpositive⟩ :=
    Wikipedia.SzemeredisTheorem.exists_cyclicAP_of_offDiagMass_pos hf0 hoffdiag
  have htermS : ∀ j : ℕ, j < K → a + (j : ZMod M) * d ∈ S := by
    intro j hj
    let jf : Fin K := ⟨j, hj⟩
    have hp := hpositive jf
    have hmem : Wikipedia.SzemeredisTheorem.cyclicAPTerm a d jf ∈ S := by
      by_contra hnot
      rw [Wikipedia.SzemeredisTheorem.finsetIndicator_of_not_mem hnot] at hp
      linarith
    simpa [Wikipedia.SzemeredisTheorem.cyclicAPTerm, jf] using hmem
  have htermData : ∀ j : ℕ, j < K →
      Wikipedia.SzemeredisTheorem.cyclicAPVal a d j < N + 1 ∧
        Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ∈ (A : Set ℕ) := by
    intro j hj
    have hmem := htermS j hj
    simpa [S, Wikipedia.SzemeredisTheorem.cyclicPrefix,
      Wikipedia.SzemeredisTheorem.cyclicAPVal] using hmem
  have hinterval : ∀ j : ℕ, j < K →
      (0 : ℤ) ≤ Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ∧
        Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ≤ (N : ℤ) := by
    intro j hj
    have hmem := htermData j hj
    constructor
    · positivity
    · exact_mod_cast (Nat.lt_succ_iff.mp hmem.1)
  have hwidth : 2 * ((N : ℤ) - 0) < (M : ℤ) := by
    dsimp [M]
    push_cast
    omega
  obtain ⟨x, step, hstep, hprogression⟩ :=
    Wikipedia.SzemeredisTheorem.exists_naturalAP_of_cyclicAPVal_shortInterval
      a d hd hKtwo 0 N hinterval hwidth
      (fun j hj => (htermData j hj).2)
  exact not_isAPOfLengthFree_of_parameters hk hstep
    (fun j hj => by simpa [Nat.mul_comm] using hprogression j (hj.trans_le hkK))

theorem szemeredis_theorem (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) :=
  tendsto_maxCard_div_of_finitarySzemeredi
    (finitarySzemeredi_of_cyclic_count hk)

end SzemeredisTheorem
