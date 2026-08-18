import ErdosProblems.Erdos140.BohrSmoothingMeasure
import ErdosProblems.Erdos140.RelativeChangDefinitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Additive.Randomisation

/-!
# Dissociation relative to a spectrum

This file records the elementary ``dissociated modulo a set'' selection
which is used in Sanders' relative form of Chang's lemma, together with the
corresponding approximate Riesz-product randomisation estimate.
-/

noncomputable section

open Finset Real
open scoped BigOperators ComplexConjugate

namespace Erdos140.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- A finite family is dissociated modulo `S` if no nonempty signed sum of
distinct members, with signs in `{-1, 1}`, belongs to `S`.

The two disjoint finsets are respectively the positive and negative parts of
the signed sum. -/
def AddDissociatedMod (S Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ t u : Finset (AddChar G ℂ), t ⊆ Delta → u ⊆ Delta →
    Disjoint t u → (t ∪ u).Nonempty →
      (∑ psi ∈ t, psi) - ∑ psi ∈ u, psi ∉ S

theorem addDissociatedMod_empty (S : Finset (AddChar G ℂ)) :
    AddDissociatedMod S ∅ := by
  intro t u ht hu htu hne
  simp only [Finset.subset_empty] at ht hu
  subst t
  subst u
  simpa using hne

theorem AddDissociatedMod.mono {S : Finset (AddChar G ℂ)}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : AddDissociatedMod S Delta) (hsub : Gamma ⊆ Delta) :
    AddDissociatedMod S Gamma := by
  intro t u ht hu
  exact h t u (ht.trans hsub) (hu.trans hsub)

/-- Maximal dissociation modulo a negation-invariant set gives a signed-span
cover. -/
theorem exists_maximal_addDissociatedMod
    (S T : Finset (AddChar G ℂ))
    (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  classical
  let candidates := T.powerset.filter (AddDissociatedMod S)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, addDissociatedMod_empty]
  obtain ⟨Delta, hDelta_mem, hDelta_max⟩ := candidates.exists_maximal hcandidates
  have hDelta := Finset.mem_filter.mp hDelta_mem
  refine ⟨Delta, Finset.mem_powerset.mp hDelta.1, hDelta.2, ?_⟩
  intro psi hpsiT
  by_cases hpsiDelta : psi ∈ Delta
  · exact ⟨psi, Finset.subset_addSpan hpsiDelta, 0, hzero, by simp⟩
  · have hinsert_subset : insert psi Delta ⊆ T :=
      Finset.insert_subset hpsiT (Finset.mem_powerset.mp hDelta.1)
    have hnot : ¬ AddDissociatedMod S (insert psi Delta) := by
      intro hins
      have hinsert_mem : insert psi Delta ∈ candidates := by
        simp [candidates, hinsert_subset, hins]
      have hsub := hDelta_max hinsert_mem (Finset.subset_insert psi Delta)
      exact hpsiDelta (hsub (Finset.mem_insert_self psi Delta))
    rw [AddDissociatedMod] at hnot
    push_neg at hnot
    obtain ⟨t, u, ht, hu, htu, hne, hsumS⟩ := hnot
    have hpsi_tu : psi ∈ t ∪ u := by
      by_contra hpsi
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_left u ha))
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_right t ha))
      exact hDelta.2 t u htDelta huDelta htu hne hsumS
    rw [Finset.mem_union] at hpsi_tu
    rcases hpsi_tu with hpsi_t | hpsi_u
    · have hpsi_not_u : psi ∉ u := fun h ↦ Finset.disjoint_left.mp htu hpsi_t h
      have htErase : t.erase psi ⊆ Delta := by
        intro a ha
        have ha' := ht (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_u (h ▸ ha))
      let z := (∑ a ∈ u, a) - ∑ a ∈ t.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan huDelta htErase
      refine ⟨z, hz, (∑ a ∈ t, a) - ∑ a ∈ u, a, hsumS, ?_⟩
      dsimp [z]
      rw [← Finset.sum_erase_add _ _ hpsi_t]
      abel
    · have hpsi_not_t : psi ∉ t := fun h ↦ Finset.disjoint_left.mp htu h hpsi_u
      have huErase : u.erase psi ⊆ Delta := by
        intro a ha
        have ha' := hu (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_t (h ▸ ha))
      let z := (∑ a ∈ t, a) - ∑ a ∈ u.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan htDelta huErase
      let s := -((∑ a ∈ t, a) - ∑ a ∈ u, a)
      have hs : s ∈ S := hS _ hsumS
      refine ⟨z, hz, s, hs, ?_⟩
      dsimp [z, s]
      rw [← Finset.sum_erase_add _ _ hpsi_u]
      abel

/-- A capped dimension estimate for all small dissociated subsets applies to
the maximal modulo-dissociated set. -/
theorem exists_maximal_addDissociatedMod_card_le
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma : Finset (AddChar G ℂ), Gamma ⊆ T →
      AddDissociatedMod S Gamma → Gamma.card ≤ k →
        (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  obtain ⟨Delta, hDeltaT, hDelta, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hS
  have hcard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaReal : (Gamma.card : ℝ) ≤ D :=
      hdim Gamma (hGammaDelta.trans hDeltaT) (hDelta.mono hGammaDelta)
        (by omega)
    have hkD : (k : ℝ) ≤ D := by simpa [hGammaCard] using hGammaReal
    exact (not_le_of_gt hDk) hkD
  exact ⟨Delta, hDeltaT, hDelta, hdim Delta hDeltaT hDelta hcard, hcover⟩

private def signedFrequency (t u : Finset (AddChar G ℂ)) : AddChar G ℂ :=
  (∑ psi ∈ u, psi) - ∑ psi ∈ t \ u, psi

private def signedCoefficient (v : AddChar G ℂ → ℂ)
    (t u : Finset (AddChar G ℂ)) : ℂ :=
  ((∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)) /
    (2 : ℂ) ^ t.card

private lemma rieszProduct_eq_signedExpansion
    (Delta : Finset (AddChar G ℂ)) (v : AddChar G ℂ → ℂ) (x : G) :
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
  calc
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
        ∏ psi ∈ Delta,
          (((v psi * psi x) + conj (v psi * psi x)) / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro psi hpsi
      rw [add_comm, ← Complex.re_eq_add_conj]
      push_cast
      rfl
    _ = ∑ t ∈ Delta.powerset,
        ∏ psi ∈ t, ((v psi * psi x) + conj (v psi * psi x)) / 2 := by
      rw [Finset.prod_add]
      simp
    _ = ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      rw [Finset.prod_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [signedCoefficient, signedFrequency]
      simp only [AddChar.sum_apply, AddChar.sub_apply,
        AddChar.map_neg_eq_conj]
      simp only [Finset.prod_const]
      simp_rw [map_mul, Finset.prod_mul_distrib]
      rw [map_prod]
      ring

private lemma weightedRiesz_eq_signedExpansion
    (w : G → ℝ) (Delta : Finset (AddChar G ℂ))
    (v : AddChar G ℂ → ℂ) :
    ((∑ x : G, w x *
        ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u *
          Erdos140.massCoeff w (signedFrequency t u) := by
  simp_rw [Complex.ofReal_prod]
  simp_rw [rieszProduct_eq_signedExpansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos140.massCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private lemma signedFrequency_not_mem
    {S Delta t u : Finset (AddChar G ℂ)}
    (hDelta : AddDissociatedMod S Delta)
    (ht : t ⊆ Delta) (ht0 : t.Nonempty) (hu : u ⊆ t) :
    signedFrequency t u ∉ S := by
  apply hDelta u (t \ u)
  · exact hu.trans ht
  · exact Finset.sdiff_subset.trans ht
  · rw [Finset.disjoint_left]
    intro psi hpsiu hpsitu
    exact (Finset.mem_sdiff.mp hpsitu).2 hpsiu
  · simpa [Finset.union_sdiff_of_subset hu] using ht0

private lemma norm_signedCoefficient_le
    {v : AddChar G ℂ → ℂ} {t u : Finset (AddChar G ℂ)}
    (hu : u ⊆ t) (hv : ∀ psi ∈ t, ‖v psi‖ ≤ 1) :
    ‖signedCoefficient v t u‖ ≤ ((2 : ℝ) ^ t.card)⁻¹ := by
  have hvu : ‖∏ psi ∈ u, v psi‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ hv psi (hu hpsi))
  have hvtu : ‖∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ by
        rw [RCLike.norm_conj]
        exact hv psi (Finset.sdiff_subset hpsi))
  have hnum :
      ‖(∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hvu hvtu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [signedCoefficient, norm_div]
  calc
    _ ≤ 1 / ‖(2 : ℂ) ^ t.card‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = ((2 : ℝ) ^ t.card)⁻¹ := by
      rw [norm_pow]
      norm_num

/-- Approximate weighted randomisation for a family dissociated modulo `S`.
The empty Fourier term contributes the mass of `w`; every other signed
frequency lies outside `S`. -/
theorem AddDissociatedMod.weighted_riesz_randomisation_le
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ}
    (hDelta : AddDissociatedMod S Delta)
    (_hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (v : AddChar G ℂ → ℂ) (hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1) :
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
      1 + q * (2 : ℝ) ^ Delta.card := by
  classical
  let F : Finset (AddChar G ℂ) → ℂ := fun t ↦
    ∑ u ∈ t.powerset, signedCoefficient v t u *
      Erdos140.massCoeff w (signedFrequency t u)
  let E : ℂ := ∑ t ∈ Delta.powerset.erase ∅, F t
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ Delta.powerset := by simp
  have hw1c : ∑ x : G, (w x : ℂ) = 1 := by exact_mod_cast hw1
  have hFempty : F ∅ = 1 := by
    simp [F, signedCoefficient, signedFrequency, Erdos140.massCoeff, hw1c]
  have hexp :
      ((∑ x : G, w x *
          ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) = 1 + E := by
    rw [weightedRiesz_eq_signedExpansion]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [hFempty, E, F]
    ring
  have hinner (t : Finset (AddChar G ℂ))
      (ht : t ∈ Delta.powerset.erase ∅) : ‖F t‖ ≤ q := by
    have htDelta : t ⊆ Delta := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have ht0 : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    calc
      ‖F t‖ ≤ ∑ u ∈ t.powerset,
          ‖signedCoefficient v t u *
            Erdos140.massCoeff w (signedFrequency t u)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _u ∈ t.powerset, ((2 : ℝ) ^ t.card)⁻¹ * q := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_signedCoefficient_le (Finset.mem_powerset.mp hu)
            (fun psi hpsi ↦ hv psi (htDelta hpsi))
        · exact hq _ (signedFrequency_not_mem hDelta htDelta ht0
            (Finset.mem_powerset.mp hu))
        · exact norm_nonneg _
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
      _ = q := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul]
  have hEnorm : ‖E‖ ≤ q * (2 : ℝ) ^ Delta.card := by
    calc
      ‖E‖ ≤ ∑ t ∈ Delta.powerset.erase ∅, ‖F t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Delta.powerset.erase ∅, q := by
        exact Finset.sum_le_sum fun t ht ↦ hinner t ht
      _ ≤ ∑ _t ∈ Delta.powerset, q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ hq0)
      _ = q * (2 : ℝ) ^ Delta.card := by
        simp [Finset.card_powerset]
        ring
  let R : ℝ :=
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re)
  have hexpR : (R : ℂ) = 1 + E := by
    calc
      (R : ℂ) = ∑ x : G, (w x : ℂ) *
          (↑(∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) := by
        dsimp [R]
        push_cast
        rfl
      _ = 1 + E := hexp
  have hre : R = 1 + E.re := by
    have := congrArg Complex.re hexpR
    simpa using this
  change R ≤ 1 + q * (2 : ℝ) ^ Delta.card
  calc
    R = 1 + E.re := hre
    _ ≤ 1 + ‖E‖ := add_le_add (le_refl 1) (Complex.re_le_norm E)
    _ ≤ 1 + q * (2 : ℝ) ^ Delta.card := add_le_add (le_refl 1) hEnorm

/-- A small spectral tail turns dissociation modulo `S` into Sanders'
weighted dissociativity. -/
theorem AddDissociatedMod.isWeightedDissociated
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hqk : q * (2 : ℝ) ^ k ≤ 1) :
    IsWeightedDissociated w 1 Delta := by
  intro v hv
  have hpowNat : 2 ^ Delta.card ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hpow : (2 : ℝ) ^ Delta.card ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hpowNat
  have htail : q * (2 : ℝ) ^ Delta.card ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hq0).trans hqk
  calc
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
        1 + q * (2 : ℝ) ^ Delta.card :=
      hDelta.weighted_riesz_randomisation_le hw0 hw1 hq0 hq v hv
    _ ≤ 2 := by linarith
    _ ≤ exp 1 := Real.exp_one_gt_two.le

/-- Convenient `4^{-k}` specialization of
`AddDissociatedMod.isWeightedDissociated`. -/
theorem AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hq_quarter : q ≤ (1 / 4 : ℝ) ^ k) :
    IsWeightedDissociated w 1 Delta := by
  apply hDelta.isWeightedDissociated hw0 hw1 hq0 hq hcard
  calc
    q * (2 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hq_quarter (pow_nonneg (by norm_num) _)
    _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; congr 1 <;> norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-! ## The ordinary large spectrum is symmetric -/

theorem zero_mem_chang_largeSpectrum_half (A : Finset G) :
    (0 : AddChar G ℂ) ∈ Erdos140.Chang.largeSpectrum A (1 / 2 : ℝ) := by
  rw [Erdos140.Chang.mem_largeSpectrum]
  simp [Erdos140.Chang.spectrumSum]
  have hcard : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le A.card
  nlinarith

theorem neg_mem_chang_largeSpectrum {A : Finset G} {eta : ℝ}
    {psi : AddChar G ℂ}
    (hpsi : psi ∈ Erdos140.Chang.largeSpectrum A eta) :
    -psi ∈ Erdos140.Chang.largeSpectrum A eta := by
  rw [Erdos140.Chang.mem_largeSpectrum] at hpsi ⊢
  have hsum : Erdos140.Chang.spectrumSum A (-psi) =
      conj (Erdos140.Chang.spectrumSum A psi) := by
    unfold Erdos140.Chang.spectrumSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [AddChar.neg_apply, AddChar.map_neg_eq_conj]
  rw [hsum, RCLike.norm_conj]
  exact hpsi

end Erdos140.RelativeChangSanders
