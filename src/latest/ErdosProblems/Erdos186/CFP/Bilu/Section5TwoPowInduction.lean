/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonInduction
import ErdosProblems.Erdos186.CFP.Bilu.Section5TwoPowEpsilonCalc

/-!
# Bilu Section 5.2: the source-correct `2^n` induction

This is the quantitative induction in Freiman's `2^n` theorem.  The Cube
Lemma is invoked with doubling parameter `2 ^ n`; consequently its central
cube contribution is used exactly, without the lossy replacement by `2 * n`.
-/

namespace Erdos186.CFP.Bilu.Section5TwoPowInduction

open Set Module Submodule
open Section7FreimanMap Section5TwoN Section5CubeGeometry Section5CubeLemma
  Section5OutsideCells Section5FullCube Section5EpsilonCalc
  Section5TwoPowEpsilonCalc Section5EpsilonInduction
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The Cube-Lemma denominator at the source coefficient `2 ^ n`. -/
def twoPowCubeDenominator (n : ℕ) : ℕ :=
  cubeLemmaConstant n (2 ^ n)

/-- The corresponding dimension-only Cube-Lemma density. -/
def twoPowCubeDensity (n : ℕ) : ℝ :=
  1 / (twoPowCubeDenominator n : ℝ)

theorem twoPowCubeDenominator_pos {n : ℕ} (hn : 0 < n) :
    0 < twoPowCubeDenominator n := by
  unfold twoPowCubeDenominator cubeLemmaConstant
  exact Nat.mul_pos (Nat.pow_pos (by omega))
    (tubeCubeConstant_pos n ((2 ^ n) * (2 ^ n)))

theorem twoPowCubeDensity_pos {n : ℕ} (hn : 0 < n) :
    0 < twoPowCubeDensity n := by
  unfold twoPowCubeDensity
  positivity [twoPowCubeDenominator_pos hn]

theorem twoPowCubeDensity_le_one {n : ℕ} (hn : 0 < n) :
    twoPowCubeDensity n ≤ 1 := by
  unfold twoPowCubeDensity
  have hD : (1 : ℝ) ≤ twoPowCubeDenominator n := by
    exact_mod_cast twoPowCubeDenominator_pos hn
  rw [div_le_one]
  · exact hD
  · exact_mod_cast twoPowCubeDenominator_pos hn

theorem twoPowCubeDenominator_mul_density {n : ℕ} (hn : 0 < n) :
    (twoPowCubeDenominator n : ℝ) * twoPowCubeDensity n = 1 := by
  unfold twoPowCubeDensity
  field_simp [show (twoPowCubeDenominator n : ℝ) ≠ 0 by
    exact_mod_cast (twoPowCubeDenominator_pos hn).ne']

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- A source-coefficient Cube-Lemma slice contains the stated fraction. -/
theorem twoPowCubeDensity_mul_card_le_of_card_le {n : ℕ} (hn : 0 < n)
    {S T : Finset V}
    (hcard : S.card ≤ twoPowCubeDenominator n * T.card) :
    twoPowCubeDensity n * S.card ≤ T.card := by
  have hcardR : (S.card : ℝ) ≤
      (twoPowCubeDenominator n : ℝ) * T.card := by
    exact_mod_cast hcard
  have hDpos : (0 : ℝ) < twoPowCubeDenominator n := by
    exact_mod_cast twoPowCubeDenominator_pos hn
  unfold twoPowCubeDensity
  rw [show 1 / (twoPowCubeDenominator n : ℝ) * S.card =
      (S.card : ℝ) / twoPowCubeDenominator n by ring]
  apply (div_le_iff₀ hDpos).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcardR

/-- The boundary cost is still `2n`; below the same cutoff it leaves half of
the source-coefficient Cube-Lemma density in the interior. -/
theorem half_twoPowCubeDensity_mul_card_lt_interior
    {n : ℕ} (hn : 0 < n) (S : Finset V) (hS : S.Nonempty)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (T : Finset V) (hTS : T ⊆ S)
    (hTclosed : ∀ x ∈ T, x ∈ affineCubeClosed e center)
    (hTcard : S.card ≤ twoPowCubeDenominator n * T.card)
    {delta : ℝ}
    (hdelta : delta < twoPowCubeDensity n / (4 * n))
    (hsparse : HyperplaneSparse n delta S) :
    twoPowCubeDensity n / 2 * S.card <
      (affineCubeInteriorPart S e center).card := by
  let closed := affineCubeClosedPart S e center
  let interior := affineCubeInteriorPart S e center
  let boundary := affineCubeBoundaryPart S e center
  have hTclosedPart : T ⊆ closed := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hTS hx, hTclosed x hx⟩
  have hdSleT : twoPowCubeDensity n * S.card ≤ (T.card : ℝ) :=
    twoPowCubeDensity_mul_card_le_of_card_le hn hTcard
  have hTleClosed : (T.card : ℝ) ≤ closed.card := by
    exact_mod_cast Finset.card_le_card hTclosedPart
  have hclosedLe : (closed.card : ℝ) ≤ interior.card + boundary.card := by
    exact_mod_cast card_affineCubeClosedPart_le S e center
  have hboundary := boundary_card_lt hn S e center hsparse
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdensPos := twoPowCubeDensity_pos hn
  have hboundarySmall : (boundary.card : ℝ) <
      twoPowCubeDensity n / 2 * S.card := by
    calc
      (boundary.card : ℝ) < 2 * (n : ℝ) * delta * S.card := hboundary
      _ < twoPowCubeDensity n / 2 * S.card := by
        apply mul_lt_mul_of_pos_right _ (by
          exact_mod_cast (Finset.card_pos.mpr hS))
        calc
          2 * (n : ℝ) * delta <
              2 * (n : ℝ) * (twoPowCubeDensity n / (4 * n)) := by gcongr
          _ = twoPowCubeDensity n / 2 := by field_simp; ring
  linarith

/-- Quantitative contrapositive of the genuine `2^n` theorem. -/
theorem pairSumset_card_twoPow_lower_bound
    {n : ℕ} (hn : 0 < n) (hfinrank : finrank ℝ V = n)
    (S : Finset V) (hS : S.Nonempty) (delta : ℝ) (hdelta : 0 < delta)
    (hsparse : HyperplaneSparse n delta S) :
    (((2 ^ n : ℕ) : ℝ) -
        twoPowNEpsilon n (twoPowCubeDensity n) delta) * S.card ≤
      ((pairSumset S).card : ℝ) := by
  let P : ℕ → Prop := fun N ↦
    ∀ T : Finset V, T.card = N → T.Nonempty →
      ∀ rho : ℝ, 0 < rho → HyperplaneSparse n rho T →
        (((2 ^ n : ℕ) : ℝ) -
            twoPowNEpsilon n (twoPowCubeDensity n) rho) * T.card ≤
          ((pairSumset T).card : ℝ)
  have hP : ∀ N, P N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        dsimp [P]
        intro T hTN hT rho hrho hsparseT
        subst N
        have hd0 := twoPowCubeDensity_pos hn
        have hd1 := twoPowCubeDensity_le_one hn
        by_cases hcutoff : twoPowCubeDensity n / (4 * n) ≤ rho
        · have heps := two_pow_le_twoPowNEpsilon_of_cutoff_le
            hn hd0 hcutoff
          have hpair0 : (0 : ℝ) ≤ (pairSumset T).card := by positivity
          have hT0 : (0 : ℝ) ≤ T.card := by positivity
          nlinarith
        · have hrhoSmall : rho < twoPowCubeDensity n / (4 * n) :=
            lt_of_not_ge hcutoff
          by_cases hlarge : (2 ^ n) * T.card < (pairSumset T).card
          · have hlargeR :
                ((2 ^ n : ℕ) : ℝ) * T.card <
                  ((pairSumset T).card : ℝ) := by
              exact_mod_cast hlarge
            have hepsPos := twoPowNEpsilon_pos hn hd0 hrho
            have hT0 : (0 : ℝ) ≤ T.card := by positivity
            nlinarith
          · have hdouble :
                (pairSumset T).card ≤ (2 ^ n) * T.card := by omega
            rcases exists_affineSlice_or_fullCube hn T hT hfinrank
                hdouble with hslice | hfull
            · obtain ⟨W⟩ := hslice
              have hsliceFilter : W.slice ⊆
                  T.filter fun x ↦ x ∈ W.plane := by
                intro x hx
                exact Finset.mem_filter.mpr
                  ⟨W.slice_subset hx, W.slice_mem_plane x hx⟩
              have hsliceCard : (W.slice.card : ℝ) ≤
                  (T.filter fun x ↦ x ∈ W.plane).card := by
                exact_mod_cast Finset.card_le_card hsliceFilter
              have hsliceSparse : (W.slice.card : ℝ) < rho * T.card :=
                hsliceCard.trans_lt (hsparseT W.plane W.dimension_lt)
              have hcardR : (T.card : ℝ) ≤
                  (twoPowCubeDenominator n : ℝ) * W.slice.card := by
                exact_mod_cast W.card_le
              have hDpos : (0 : ℝ) < twoPowCubeDenominator n := by
                exact_mod_cast twoPowCubeDenominator_pos hn
              have hDdelta : (twoPowCubeDenominator n : ℝ) * rho < 1 := by
                calc
                  (twoPowCubeDenominator n : ℝ) * rho <
                      (twoPowCubeDenominator n : ℝ) *
                        (twoPowCubeDensity n / (4 * n)) :=
                    mul_lt_mul_of_pos_left hrhoSmall hDpos
                  _ = 1 / (4 * (n : ℝ)) := by
                    rw [show (twoPowCubeDenominator n : ℝ) *
                        (twoPowCubeDensity n / (4 * n)) =
                        ((twoPowCubeDenominator n : ℝ) *
                          twoPowCubeDensity n) / (4 * n) by ring,
                      twoPowCubeDenominator_mul_density hn]
                  _ ≤ 1 := by
                    rw [div_le_one]
                    · exact_mod_cast (show 1 ≤ 4 * n by omega)
                    · positivity
              have hTpos : (0 : ℝ) < T.card := by
                exact_mod_cast Finset.card_pos.mpr hT
              nlinarith
            · obtain ⟨W⟩ := hfull
              let I := affineCubeInteriorPart T W.coordinates W.center
              let cells := outsideCellIndices n
              let A : (Fin n → Fin 3) → Finset V :=
                fun alpha ↦ cubeCell T W.coordinates W.center alpha
              let eta : (Fin n → Fin 3) → ℝ :=
                fun alpha ↦ (A alpha).card / T.card
              have hIlarge : twoPowCubeDensity n / 2 * T.card < I.card :=
                half_twoPowCubeDensity_mul_card_lt_interior hn T hT
                  W.coordinates W.center W.slice W.slice_subset
                  W.slice_mem_closed W.card_le hrhoSmall hsparseT
              have hIpos : 0 < I.card := by
                have hdhalf : 0 < twoPowCubeDensity n / 2 := by positivity
                have hTposR : (0 : ℝ) < T.card := by
                  exact_mod_cast Finset.card_pos.mpr hT
                have : (0 : ℝ) < I.card :=
                  lt_of_lt_of_le (mul_pos hdhalf hTposR) hIlarge.le
                exact_mod_cast this
              have hpartitionNat :
                  I.card + ∑ alpha ∈ cells, (A alpha).card = T.card := by
                exact card_interiorPart_add_sum_outsideCells
                  T W.coordinates W.center
              have hpartition :
                  (I.card : ℝ) +
                      ∑ alpha ∈ cells, ((A alpha).card : ℝ) = T.card := by
                exact_mod_cast hpartitionNat
              have hTposR : (0 : ℝ) < T.card := by
                exact_mod_cast Finset.card_pos.mpr hT
              have hetaNonneg : ∀ alpha ∈ cells, 0 ≤ eta alpha := by
                intro alpha _halpha
                unfold eta
                positivity
              have hetaSum :
                  ∑ alpha ∈ cells, eta alpha =
                    1 - (I.card : ℝ) / T.card := by
                unfold eta
                simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
                field_simp
                nlinarith
              have hetaSumLe :
                  ∑ alpha ∈ cells, eta alpha ≤
                    1 - twoPowCubeDensity n / 2 := by
                rw [hetaSum]
                have hdiv : twoPowCubeDensity n / 2 <
                    (I.card : ℝ) / T.card := by
                  exact (lt_div_iff₀ hTposR).2 (by
                    simpa [mul_assoc] using hIlarge)
                linarith
              have hcellsCard : cells.card ≤ cellCount n := by
                simp [cells, cellCount]
              have herror := sum_twoPowNEpsilon_div_mul_lt_of_nonneg
                cells eta hn hd0 hd1 hrho hetaNonneg hcellsCard hetaSumLe
              have hcellLower : ∀ alpha ∈ cells,
                  (((2 ^ n : ℕ) : ℝ) -
                      twoPowNEpsilon n (twoPowCubeDensity n)
                        (rho / eta alpha)) * (A alpha).card ≤
                    ((pairSumset (A alpha)).card : ℝ) := by
                intro alpha halpha
                by_cases hA : (A alpha).Nonempty
                · have hAleSum : (A alpha).card ≤
                      ∑ beta ∈ cells, (A beta).card := by
                    exact Finset.single_le_sum
                      (fun beta _ ↦ Nat.zero_le (A beta).card) halpha
                  have hAlt : (A alpha).card < T.card := by omega
                  have hetaPos : 0 < eta alpha := by
                    unfold eta
                    exact div_pos (by
                      exact_mod_cast Finset.card_pos.mpr hA) hTposR
                  have hrhoCell : 0 < rho / eta alpha := div_pos hrho hetaPos
                  have hAS : A alpha ⊆ T := by
                    intro x hx
                    exact (mem_cubeCell.mp hx).1
                  have hsparseA :
                      HyperplaneSparse n (rho / eta alpha) (A alpha) := by
                    intro plane hplane
                    have hfilter :
                        (A alpha).filter (fun x ↦ x ∈ plane) ⊆
                          T.filter fun x ↦ x ∈ plane := by
                      intro x hx
                      have hx' := Finset.mem_filter.mp hx
                      exact Finset.mem_filter.mpr ⟨hAS hx'.1, hx'.2⟩
                    have hle :
                        (((A alpha).filter fun x ↦ x ∈ plane).card : ℝ) ≤
                          ((T.filter fun x ↦ x ∈ plane).card : ℝ) := by
                      exact_mod_cast Finset.card_le_card hfilter
                    have hglobal := hsparseT plane hplane
                    have hscale :
                        (rho / eta alpha) * (A alpha).card = rho * T.card := by
                      unfold eta
                      field_simp
                    rw [hscale]
                    exact hle.trans_lt hglobal
                  exact ih (A alpha).card hAlt (A alpha) rfl hA
                    (rho / eta alpha) hrhoCell hsparseA
                · have hAempty := Finset.not_nonempty_iff_eq_empty.mp hA
                  simp [hAempty]
              have houtsideLower :
                  ∑ alpha ∈ cells,
                      (((2 ^ n : ℕ) : ℝ) -
                        twoPowNEpsilon n (twoPowCubeDensity n)
                          (rho / eta alpha)) * (A alpha).card ≤
                    ∑ alpha ∈ cells,
                      ((pairSumset (A alpha)).card : ℝ) := by
                exact Finset.sum_le_sum fun alpha halpha ↦
                  hcellLower alpha halpha
              have hmasterNat := interior_and_outside_pairSum_card_le
                T I W.coordinates W.center (by
                  intro x hx
                  exact (Finset.mem_filter.mp hx).1) (by
                  intro x hx
                  exact (Finset.mem_filter.mp hx).2) W.vertex_mem
              have hmaster :
                  ((I.card * 2 ^ n : ℕ) : ℝ) +
                      ∑ alpha ∈ cells,
                        ((pairSumset (A alpha)).card : ℝ) ≤
                    ((pairSumset T).card : ℝ) := by
                exact_mod_cast hmasterNat
              have hcentral :
                  ((2 ^ n : ℕ) : ℝ) * I.card =
                    ((I.card * 2 ^ n : ℕ) : ℝ) := by
                norm_num [mul_comm]
              have herrorScaled :
                  ∑ alpha ∈ cells,
                      twoPowNEpsilon n (twoPowCubeDensity n)
                        (rho / eta alpha) * (A alpha).card <
                    twoPowNEpsilon n (twoPowCubeDensity n) rho * T.card := by
                have hmul := mul_lt_mul_of_pos_right herror hTposR
                calc
                  ∑ alpha ∈ cells,
                      twoPowNEpsilon n (twoPowCubeDensity n)
                        (rho / eta alpha) * (A alpha).card =
                      (∑ alpha ∈ cells,
                        twoPowNEpsilon n (twoPowCubeDensity n)
                          (rho / eta alpha) * eta alpha) * T.card := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro alpha _halpha
                    have hetaMul : eta alpha * (T.card : ℝ) =
                        (A alpha).card := by
                      unfold eta
                      field_simp
                    rw [mul_assoc, hetaMul]
                  _ < twoPowNEpsilon n (twoPowCubeDensity n) rho * T.card :=
                    hmul
              have hsourceEq :
                  ((2 ^ n : ℕ) : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (((2 ^ n : ℕ) : ℝ) -
                          twoPowNEpsilon n (twoPowCubeDensity n)
                            (rho / eta alpha)) * (A alpha).card =
                    ((2 ^ n : ℕ) : ℝ) * T.card -
                      ∑ alpha ∈ cells,
                        twoPowNEpsilon n (twoPowCubeDensity n)
                          (rho / eta alpha) * (A alpha).card := by
                simp_rw [sub_mul, Finset.sum_sub_distrib]
                rw [← Finset.mul_sum]
                nlinarith
              have hsourceStrict :
                  (((2 ^ n : ℕ) : ℝ) -
                      twoPowNEpsilon n (twoPowCubeDensity n) rho) * T.card <
                    ((2 ^ n : ℕ) : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (((2 ^ n : ℕ) : ℝ) -
                          twoPowNEpsilon n (twoPowCubeDensity n)
                            (rho / eta alpha)) * (A alpha).card := by
                rw [hsourceEq]
                nlinarith
              have hsourceLe :
                  ((2 ^ n : ℕ) : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (((2 ^ n : ℕ) : ℝ) -
                          twoPowNEpsilon n (twoPowCubeDensity n)
                            (rho / eta alpha)) * (A alpha).card ≤
                    ((I.card * 2 ^ n : ℕ) : ℝ) +
                      ∑ alpha ∈ cells,
                        ((pairSumset (A alpha)).card : ℝ) := by
                rw [hcentral]
                exact add_le_add le_rfl houtsideLower
              exact (hsourceStrict.trans_le (hsourceLe.trans hmaster)).le
  exact hP S.card S rfl hS delta hdelta hsparse

end

end Erdos186.CFP.Bilu.Section5TwoPowInduction

#print axioms
  Erdos186.CFP.Bilu.Section5TwoPowInduction.pairSumset_card_twoPow_lower_bound
