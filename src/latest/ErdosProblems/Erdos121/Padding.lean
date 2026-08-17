import ErdosProblems.Erdos121.DenseFive

/-! # Padding a square-product tuple by the pair `m, 4m` -/

open Filter
open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

abbrev PairCandidate (N : ℕ) := ↥(Finset.Icc 1 (N / 4))

lemma card_pairCandidate (N : ℕ) :
    Fintype.card (PairCandidate N) = N / 4 := by
  rw [Fintype.card_coe]
  simp

lemma exists_mul_four_pair_of_small_complement {N : ℕ} (hN : 64 ≤ N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hcomp : (((Finset.Icc 1 N \ A).card : ℕ) : ℝ) <
      (1 / 64 : ℝ) * N) :
    ∃ m : ℕ, m ∈ A ∧ 4 * m ∈ A ∧ m ≠ 4 * m := by
  classical
  let V := Finset.Icc 1 N
  let C := V \ A
  by_contra hnone
  have hfail : ∀ m : PairCandidate N,
      m.1 ∉ A ∨ 4 * m.1 ∉ A := by
    intro m
    by_contra h
    push Not at h
    exact hnone ⟨m.1, h.1, h.2, by
      have hm := (Finset.mem_Icc.mp m.2).1
      omega⟩
  let f : PairCandidate N → (↥C × Bool) := fun m =>
    if hm : m.1 ∈ A then
      (⟨4 * m.1, Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by
          have hm1 := (Finset.mem_Icc.mp m.2).1
          omega, by
          have hm4 := (Finset.mem_Icc.mp m.2).2
          omega⟩, (hfail m).resolve_left (by simpa using hm)⟩⟩, true)
    else
      (⟨m.1, Finset.mem_sdiff.mpr ⟨by
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp m.2).1,
            (Finset.mem_Icc.mp m.2).2.trans (Nat.div_le_self N 4)⟩,
          hm⟩⟩, false)
  have hinj : Function.Injective f := by
    intro m m' heq
    by_cases hm : m.1 ∈ A <;> by_cases hm' : m'.1 ∈ A
    · have hv := congrArg (fun z => z.1.1) heq
      simp only [f, dif_pos hm, dif_pos hm'] at hv
      apply Subtype.ext
      change 4 * m.1 = 4 * m'.1 at hv
      omega
    · have hb := congrArg Prod.snd heq
      simp [f, hm, hm'] at hb
    · have hb := congrArg Prod.snd heq
      simp [f, hm, hm'] at hb
    · have hv := congrArg (fun z => z.1.1) heq
      simp only [f, dif_neg hm, dif_neg hm'] at hv
      apply Subtype.ext
      exact hv
  have hcard := Fintype.card_le_of_injective f hinj
  have hcardBound : N / 4 ≤ 2 * C.card := by
    simpa [card_pairCandidate, Fintype.card_prod, C, Nat.mul_comm] using hcard
  have hcompNat : 64 * C.card < N := by
    have hcomp' : (C.card : ℝ) < (1 / 64 : ℝ) * N := by
      simpa [C, V] using hcomp
    exact_mod_cast (show (64 : ℝ) * C.card < N by nlinarith)
  omega

/-- Any fixed positive density gap for `k` propagates to `k+2`. -/
theorem denseSquareTupleBound_add_two {k : ℕ} {c : ℝ} (hc : 0 < c)
    (h : DenseSquareTupleBound k c) :
    ∃ c' : ℝ, 0 < c' ∧ DenseSquareTupleBound (k + 2) c' := by
  let c' : ℝ := min (c / 2) (1 / 64)
  have hc' : 0 < c' := lt_min (div_pos hc (by norm_num)) (by norm_num)
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (4 / c)
  refine ⟨c', hc', ?_⟩
  filter_upwards [h, eventually_ge_atTop (max 64 M)] with N hbase hN
  intro A hA hlarge
  let V := Finset.Icc 1 N
  have hVcard : V.card = N := by simp [V]
  have hcomp : (((V \ A).card : ℕ) : ℝ) < (1 / 64 : ℝ) * N := by
    have hdiff : ((V \ A).card : ℝ) = (N : ℝ) - A.card := by
      rw [Finset.cast_card_sdiff hA, hVcard]
    have hc'le : c' ≤ (1 / 64 : ℝ) := min_le_right _ _
    rw [hdiff]
    nlinarith
  obtain ⟨m, hmA, h4mA, hmne⟩ :=
    exists_mul_four_pair_of_small_complement
      ((le_max_left 64 M).trans hN) hA (by simpa [V] using hcomp)
  let P : Finset ℕ := {m, 4 * m}
  let A' := A \ P
  have hPcard : P.card = 2 := by simp [P, hmne]
  have hPsub : P ⊆ A := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmA
    · exact h4mA
  have hA'card : ((A'.card : ℕ) : ℝ) = A.card - 2 := by
    rw [show A' = A \ P from rfl, Finset.cast_card_sdiff hPsub, hPcard]
    norm_num
  have hc'le : c' ≤ c / 2 := min_le_left _ _
  have hNc : (4 : ℝ) < c * N := by
    have hMN : M ≤ N := (le_max_right 64 M).trans hN
    have hMreal : 4 / c < (M : ℝ) := hM
    have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hcne : c ≠ 0 := ne_of_gt hc
    apply (div_lt_iff₀ hc).mp at hMreal
    nlinarith
  have hlarge' : (1 - c) * (N : ℝ) < A'.card := by
    rw [hA'card]
    nlinarith
  have hA'sub : A' ⊆ Finset.Icc 1 N :=
    (Finset.sdiff_subset).trans hA
  obtain ⟨S, hSA', hScard, hSsq⟩ := hbase A' hA'sub hlarge'
  let T := S ∪ P
  refine ⟨T, ?_, ?_, ?_⟩
  · exact Finset.union_subset (hSA'.trans Finset.sdiff_subset) hPsub
  · have hdisj : Disjoint S P := by
      exact Finset.disjoint_left.mpr fun x hxS hxP =>
        (Finset.mem_sdiff.mp (hSA' hxS)).2 hxP
    rw [show T = S ∪ P from rfl,
      Finset.card_union_of_disjoint hdisj, hScard, hPcard]
  · have hdisj : Disjoint S P := by
      exact Finset.disjoint_left.mpr fun x hxS hxP =>
        (Finset.mem_sdiff.mp (hSA' hxS)).2 hxP
    have hPprod : P.prod id = (2 * m) ^ 2 := by
      simp [P, hmne]
      ring
    rw [HasSquareProduct, show T = S ∪ P from rfl,
      Finset.prod_union hdisj, hPprod]
    exact hSsq.mul ⟨2 * m, by simp [pow_two]⟩

end

end Erdos121
