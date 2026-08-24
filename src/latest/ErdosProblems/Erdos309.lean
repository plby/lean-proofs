/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 309.
https://www.erdosproblems.com/forum/thread/309

Informal authors:
- Hisashi Yokota
- Ernest S. Croot III
- Thomas Bloom

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos309.md
-/
/-
This file formalizes the negative resolution of Erdős Problem 309.

Informal authors:
- Hisashi Yokota
- Ernest S. Croot III
- Thomas Bloom (the unit-fraction extraction theorem used here)

Formal author:
- OpenAI Codex

The mathematical proof and its correspondence with this development are
documented in `tex/309.tex`.
-/

import UnitFractions.ErdosProblems
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Filter Real
open scoped BigOperators Topology

namespace Erdos309

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A natural number is representable using distinct denominators from
`{1, ..., N}`.  The reciprocal sum is computed exactly in `ℚ`. -/
def IsRepresentable (N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (m : ℚ)

/-- The finite set of represented integers.  Every reciprocal sum is
nonnegative and at most `N`, so `range (N + 1)` is an exact search range. -/
def representableIntegers (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (IsRepresentable N)

/-- The number of integers representable by distinct unit fractions with
denominators at most `N`. -/
def F (N : ℕ) : ℕ := (representableIntegers N).card

@[simp] lemma mem_representableIntegers {N m : ℕ} :
    m ∈ representableIntegers N ↔ m ≤ N ∧ IsRepresentable N m := by
  simp [representableIntegers]

/-- A family of pairwise-disjoint unit-sum blocks contained in `A`. -/
def IsUnitPacking (A : Finset ℕ) (P : Finset (Finset ℕ)) : Prop :=
  (P : Set (Finset ℕ)).PairwiseDisjoint id ∧
    ∀ B ∈ P, B ⊆ A ∧ UnitFractions.rec_sum B = 1

/-- The finite search space of all unit packings in `A`. -/
def packingCandidates (A : Finset ℕ) : Finset (Finset (Finset ℕ)) :=
  A.powerset.powerset.filter (IsUnitPacking A)

/-- The largest possible number of pairwise-disjoint unit-sum blocks in `A`. -/
def packingNumber (A : Finset ℕ) : ℕ :=
  (packingCandidates A).sup Finset.card

lemma empty_isUnitPacking (A : Finset ℕ) : IsUnitPacking A ∅ := by
  simp [IsUnitPacking]

lemma packingCandidates_nonempty (A : Finset ℕ) : (packingCandidates A).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [packingCandidates, empty_isUnitPacking]

lemma mem_packingCandidates {A : Finset ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking A P) : P ∈ packingCandidates A := by
  rw [packingCandidates, Finset.mem_filter]
  refine ⟨?_, hP⟩
  rw [Finset.mem_powerset]
  intro B hB
  rw [Finset.mem_powerset]
  exact (hP.2 B hB).1

lemma exists_maximal_packing (A : Finset ℕ) :
    ∃ P : Finset (Finset ℕ), IsUnitPacking A P ∧ P.card = packingNumber A := by
  obtain ⟨P, hPmem, hPsup⟩ :=
    Finset.exists_mem_eq_sup (packingCandidates A) (packingCandidates_nonempty A) Finset.card
  refine ⟨P, (Finset.mem_filter.mp hPmem).2, ?_⟩
  exact hPsup.symm

lemma card_le_packingNumber {A : Finset ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking A P) : P.card ≤ packingNumber A := by
  exact Finset.le_sup (f := Finset.card) (mem_packingCandidates hP)

lemma packing_biUnion_subset {A : Finset ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking A P) : P.biUnion id ⊆ A := by
  intro x hx
  obtain ⟨B, hBP, hxB⟩ := Finset.mem_biUnion.mp hx
  exact (hP.2 B hBP).1 hxB

lemma packing_biUnion_rec_sum {A : Finset ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking A P) :
    UnitFractions.rec_sum (P.biUnion id) = (P.card : ℚ) := by
  rw [UnitFractions.rec_sum_bUnion_disjoint hP.1]
  calc
    ∑ B ∈ P, UnitFractions.rec_sum B = ∑ _B ∈ P, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro B hBP
      exact (hP.2 B hBP).2
    _ = (P.card : ℚ) := by simp

lemma packing_mass_identity {A : Finset ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking A P) :
    UnitFractions.rec_sum A =
      (P.card : ℚ) + UnitFractions.rec_sum (A \ P.biUnion id) := by
  let U := P.biUnion id
  have hUA : U ⊆ A := packing_biUnion_subset hP
  have hdisj : Disjoint U (A \ U) := Finset.disjoint_sdiff
  calc
    UnitFractions.rec_sum A = UnitFractions.rec_sum (U ∪ (A \ U)) := by
      rw [Finset.union_sdiff_of_subset hUA]
    _ = UnitFractions.rec_sum U + UnitFractions.rec_sum (A \ U) :=
      UnitFractions.rec_sum_disjoint hdisj
    _ = (P.card : ℚ) + UnitFractions.rec_sum (A \ U) := by
      rw [packing_biUnion_rec_sum hP]

lemma unitBlock_not_mem_of_subset_remainder {A S : Finset ℕ}
    {P : Finset (Finset ℕ)} (hS : S ⊆ A \ P.biUnion id)
    (hSsum : UnitFractions.rec_sum S = 1) : S ∉ P := by
  have hSne : S.Nonempty :=
    UnitFractions.nonempty_of_rec_sum_recip (d := 1) (by omega) (by simpa using hSsum)
  intro hSP
  obtain ⟨x, hxS⟩ := hSne
  have hxU : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨S, hSP, hxS⟩
  exact (Finset.mem_sdiff.mp (hS hxS)).2 hxU

lemma insert_unitBlock_isUnitPacking {A S : Finset ℕ}
    {P : Finset (Finset ℕ)} (hP : IsUnitPacking A P)
    (hS : S ⊆ A \ P.biUnion id) (hSsum : UnitFractions.rec_sum S = 1) :
    IsUnitPacking A (insert S P) := by
  have hSnot : S ∉ P := unitBlock_not_mem_of_subset_remainder hS hSsum
  have hdisj : ∀ B ∈ (P : Set (Finset ℕ)), Disjoint S B := by
    intro B hBP
    rw [Finset.disjoint_left]
    intro x hxS hxB
    have hxrem := Finset.mem_sdiff.mp (hS hxS)
    exact hxrem.2 (Finset.mem_biUnion.mpr ⟨B, hBP, hxB⟩)
  refine ⟨by simpa using hP.1.insert_of_notMem hSnot hdisj, ?_⟩
  intro B hB
  rw [Finset.mem_insert] at hB
  rcases hB with rfl | hBP
  · exact ⟨hS.trans Finset.sdiff_subset, hSsum⟩
  · exact hP.2 B hBP

/-- Maximality plus the extraction property forces the unused reciprocal mass
below the extraction threshold. -/
lemma maximal_remainder_rec_sum_le {N : ℕ} {δ : ℝ}
    {P : Finset (Finset ℕ)} (hP : IsUnitPacking (Finset.Icc 1 N) P)
    (hPmax : P.card = packingNumber (Finset.Icc 1 N))
    (hextract : ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N →
      δ * Real.log (N : ℝ) < (UnitFractions.rec_sum B : ℝ) →
        ∃ S ⊆ B, UnitFractions.rec_sum S = 1) :
    (UnitFractions.rec_sum (Finset.Icc 1 N \ P.biUnion id) : ℝ) ≤
      δ * Real.log (N : ℝ) := by
  by_contra hmass
  rw [not_le] at hmass
  obtain ⟨S, hSrem, hSsum⟩ :=
    hextract (Finset.Icc 1 N \ P.biUnion id) Finset.sdiff_subset hmass
  have hPacking := insert_unitBlock_isUnitPacking hP hSrem hSsum
  have hcard := card_le_packingNumber hPacking
  have hSnot := unitBlock_not_mem_of_subset_remainder hSrem hSsum
  rw [Finset.card_insert_of_notMem hSnot, ← hPmax] at hcard
  omega

lemma isRepresentable_le {N m : ℕ} (hm : IsRepresentable N m) : m ≤ N := by
  obtain ⟨A, hAN, hsum⟩ := hm
  have hmass : UnitFractions.rec_sum A ≤ (A.card : ℚ) := by
    rw [UnitFractions.rec_sum]
    calc
      ∑ n ∈ A, (1 : ℚ) / n ≤ ∑ _n ∈ A, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro n hnA
        have hn1 : (1 : ℚ) ≤ n := by
          exact_mod_cast (Finset.mem_Icc.mp (hAN hnA)).1
        exact (div_le_one (by positivity : (0 : ℚ) < n)).2 hn1
      _ = (A.card : ℚ) := by simp
  have hmcardQ : (m : ℚ) ≤ (A.card : ℚ) := by simpa [hsum] using hmass
  have hmcard : m ≤ A.card := by exact_mod_cast hmcardQ
  exact hmcard.trans (by simpa using Finset.card_le_card hAN)

lemma isRepresentable_of_le_packing_card {N j : ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking (Finset.Icc 1 N) P) (hj : j ≤ P.card) :
    IsRepresentable N j := by
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hj
  have hQpair : (Q : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro B hBQ C hCQ hBC
    exact hP.1 (hQP hBQ) (hQP hCQ) hBC
  refine ⟨Q.biUnion id, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hBQ, hxB⟩ := Finset.mem_biUnion.mp hx
    exact (hP.2 B (hQP hBQ)).1 hxB
  · rw [UnitFractions.rec_sum_bUnion_disjoint hQpair]
    calc
      ∑ B ∈ Q, UnitFractions.rec_sum B = ∑ _B ∈ Q, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro B hBQ
        exact (hP.2 B (hQP hBQ)).2
      _ = (j : ℚ) := by simp [hQcard]

lemma packing_card_add_one_le_F {N : ℕ} {P : Finset (Finset ℕ)}
    (hP : IsUnitPacking (Finset.Icc 1 N) P) : P.card + 1 ≤ F N := by
  have hsub : Finset.range (P.card + 1) ⊆ representableIntegers N := by
    intro j hj
    have hjcard : j ≤ P.card := by simpa using hj
    have hjrep := isRepresentable_of_le_packing_card hP hjcard
    exact mem_representableIntegers.2 ⟨isRepresentable_le hjrep, hjrep⟩
  simpa [F] using Finset.card_le_card hsub

/-- The natural-valued predicate counts exactly the represented integers:
nonnegativity lets us pass from an arbitrary integer to its natural value. -/
lemma integer_representable_iff {N : ℕ} {z : ℤ} :
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        UnitFractions.rec_sum A = (z : ℚ)) ↔
      ∃ m : ℕ, z = (m : ℤ) ∧ IsRepresentable N m := by
  constructor
  · rintro ⟨A, hAN, hsum⟩
    have hzQ : (0 : ℚ) ≤ (z : ℚ) := by
      rw [← hsum]
      exact UnitFractions.rec_sum_nonneg
    have hz : 0 ≤ z := by exact_mod_cast hzQ
    have hzNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    refine ⟨z.toNat, ?_, A, hAN, ?_⟩
    · exact hzNat.symm
    · exact hsum.trans (by exact_mod_cast hzNat.symm)
  · rintro ⟨m, rfl, A, hAN, hsum⟩
    exact ⟨A, hAN, by simpa using hsum⟩

lemma rec_sum_Icc_one (N : ℕ) :
    UnitFractions.rec_sum (Finset.Icc 1 N) = harmonic N := by
  rw [UnitFractions.rec_sum, harmonic_eq_sum_Icc]
  simp [one_div]

lemma represented_le_harmonic {N m : ℕ} (hm : IsRepresentable N m) :
    (m : ℚ) ≤ harmonic N := by
  obtain ⟨A, hAN, hsum⟩ := hm
  rw [← rec_sum_Icc_one N, ← hsum]
  exact UnitFractions.rec_sum_mono hAN

lemma representableIntegers_subset_harmonicFloor (N : ℕ) :
    representableIntegers N ⊆
      Finset.range (⌊((harmonic N : ℚ) : ℝ)⌋₊ + 1) := by
  intro m hm
  rw [Finset.mem_range, Nat.lt_add_one_iff]
  apply Nat.le_floor
  exact_mod_cast represented_le_harmonic (mem_representableIntegers.mp hm).2

lemma harmonic_nonneg_real (N : ℕ) : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  positivity

/-- The elementary counting upper bound `F(N) ≤ H_N + 1`. -/
lemma F_le_harmonic_add_one (N : ℕ) :
    (F N : ℝ) ≤ ((harmonic N : ℚ) : ℝ) + 1 := by
  have hcard := Finset.card_le_card (representableIntegers_subset_harmonicFloor N)
  have hcard' : F N ≤ ⌊((harmonic N : ℚ) : ℝ)⌋₊ + 1 := by
    simpa [F] using hcard
  have hfloor := Nat.floor_le (harmonic_nonneg_real N)
  calc
    (F N : ℝ) ≤ (⌊((harmonic N : ℚ) : ℝ)⌋₊ + 1 : ℕ) := by
      exact_mod_cast hcard'
    _ = (⌊((harmonic N : ℚ) : ℝ)⌋₊ : ℝ) + 1 := by norm_num
    _ ≤ ((harmonic N : ℚ) : ℝ) + 1 := by linarith

lemma F_le_log_add_two (N : ℕ) :
    (F N : ℝ) ≤ Real.log (N : ℝ) + 2 := by
  calc
    (F N : ℝ) ≤ ((harmonic N : ℚ) : ℝ) + 1 := F_le_harmonic_add_one N
    _ ≤ (1 + Real.log (N : ℝ)) + 1 := by
      gcongr
      exact harmonic_le_one_add_log N
    _ = Real.log (N : ℝ) + 2 := by ring

lemma packingNumber_add_one_le_F (N : ℕ) :
    packingNumber (Finset.Icc 1 N) + 1 ≤ F N := by
  obtain ⟨P, hP, hPcard⟩ := exists_maximal_packing (Finset.Icc 1 N)
  simpa [hPcard] using packing_card_add_one_le_F hP

/-- The extraction theorem gives a maximal packing whose block count has all
but an arbitrarily small proportion of the harmonic mass. -/
lemma eventually_harmonic_sub_le_packingNumber (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((harmonic N : ℚ) : ℝ) - δ * Real.log (N : ℝ) ≤
        (packingNumber (Finset.Icc 1 N) : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := UnitFractions.erdos47 δ hδ
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨P, hP, hPcard⟩ := exists_maximal_packing (Finset.Icc 1 N)
  have hrem := maximal_remainder_rec_sum_le hP hPcard (hN₀ N hN)
  have hmassQ := packing_mass_identity hP
  have hmassR := congrArg (fun q : ℚ ↦ (q : ℝ)) hmassQ
  simp only [Rat.cast_add, Rat.cast_natCast] at hmassR
  rw [rec_sum_Icc_one] at hmassR
  rw [← hPcard]
  linarith

lemma eventually_one_sub_mul_log_le_F (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (1 - δ) * Real.log (N : ℝ) ≤ (F N : ℝ) := by
  filter_upwards [eventually_harmonic_sub_le_packingNumber δ hδ,
      eventually_ge_atTop (1 : ℕ)] with N hpack hN
  have hlogH : Real.log (N : ℝ) ≤ ((harmonic N : ℚ) : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < N by omega)
        · exact_mod_cast Nat.le_succ N
      _ ≤ ((harmonic N : ℚ) : ℝ) := log_add_one_le_harmonic N
  have hPF := packingNumber_add_one_le_F N
  have hPFreal : (packingNumber (Finset.Icc 1 N) : ℝ) + 1 ≤ (F N : ℝ) := by
    exact_mod_cast hPF
  linarith

lemma tendsto_two_div_log :
    Tendsto (fun N : ℕ ↦ (2 : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    tendsto_log_coe_at_top.inv_tendsto_atTop.const_mul (2 : ℝ)

/-- Yokota's sharp first-order resolution: the number of represented integers
is asymptotic to `log N`. -/
theorem erdos_309_asymptotic :
    Tendsto (fun N : ℕ ↦ (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let δ : ℝ := (1 - a) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    filter_upwards [eventually_one_sub_mul_log_le_F δ hδ,
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hF hlog
    calc
      a < 1 - δ := by dsimp [δ]; linarith
      _ ≤ (F N : ℝ) / Real.log (N : ℝ) := (le_div_iff₀ hlog).2 hF
  · intro b hb
    have hsmall : ∀ᶠ N : ℕ in atTop,
        (2 : ℝ) / Real.log (N : ℝ) < b - 1 :=
      (tendsto_order.1 tendsto_two_div_log).2 (b - 1) (sub_pos.mpr hb)
    filter_upwards [hsmall,
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hsmallN hlog
    calc
      (F N : ℝ) / Real.log (N : ℝ) ≤
          (Real.log (N : ℝ) + 2) / Real.log (N : ℝ) :=
        (div_le_div_iff_of_pos_right hlog).2 (F_le_log_add_two N)
      _ = 1 + 2 / Real.log (N : ℝ) := by field_simp
      _ < b := by linarith

/-- The answer to the question in Problem 309 is negative: `F(N)` is not
little-oh of `log N`. -/
theorem erdos_309_not_littleO :
    ¬ ((fun N : ℕ ↦ (F N : ℝ)) =o[atTop]
        (fun N : ℕ ↦ Real.log (N : ℝ))) := by
  intro hsmall
  have hzero := hsmall.tendsto_div_nhds_zero
  have hne : (0 : ℝ) = 1 := tendsto_nhds_unique hzero erdos_309_asymptotic
  norm_num at hne

/-- Erdős Problem 309, with both the sharp asymptotic and the requested
negative answer bundled as the final theorem. -/
theorem not_erdos_309 :
    Tendsto (fun N : ℕ ↦ (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) ∧
      ¬ ((fun N : ℕ ↦ (F N : ℝ)) =o[atTop]
          (fun N : ℕ ↦ Real.log (N : ℝ))) :=
  ⟨erdos_309_asymptotic, erdos_309_not_littleO⟩

#print axioms Erdos309.not_erdos_309

end

end Erdos309

alias _root_.Erdos309.erdos_309 := _root_.Erdos309.not_erdos_309
