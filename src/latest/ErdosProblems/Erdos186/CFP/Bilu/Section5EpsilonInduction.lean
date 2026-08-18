/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonCalc
import ErdosProblems.Erdos186.CFP.Bilu.Section5Theorem56

/-!
# Bilu Section 5.2: the quantitative epsilon induction

This file combines the full-dimensional output of the Cube Lemma with the
outside-cell disjointness inequality and the density-error calculus.  The
result is Freiman's Theorem 5.1, and in particular the exact
`TwoNTheoremStatement` consumed by Theorem 5.6.
-/

namespace Erdos186.CFP.Bilu.Section5EpsilonInduction

open Set Module Submodule
open Section7FreimanMap Section5TwoN Section5CubeGeometry Section5CubeLemma
  Section5OutsideCells Section5FullCube Section5EpsilonCalc
  Section5Theorem56
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The reciprocal-density denominator supplied by the Cube Lemma at
doubling constant `2n`. -/
def cubeDenominator (n : ℕ) : ℕ :=
  cubeLemmaConstant n (2 * n)

/-- The proportion of the set captured by the Cube Lemma. -/
def cubeDensity (n : ℕ) : ℝ :=
  1 / (cubeDenominator n : ℝ)

theorem tubeCubeConstant_pos (r tau : ℕ) :
    0 < tubeCubeConstant r tau := by
  cases r with
  | zero => simp
  | succ r =>
      cases r with
      | zero => simp
      | succ r => simp [tubeCubeConstant]

theorem cubeDenominator_pos {n : ℕ} (hn : 0 < n) :
    0 < cubeDenominator n := by
  unfold cubeDenominator cubeLemmaConstant
  exact Nat.mul_pos (by omega) (tubeCubeConstant_pos n (2 * n * (2 * n)))

theorem cubeDensity_pos {n : ℕ} (hn : 0 < n) :
    0 < cubeDensity n := by
  unfold cubeDensity
  positivity [cubeDenominator_pos hn]

theorem cubeDensity_le_one {n : ℕ} (hn : 0 < n) :
    cubeDensity n ≤ 1 := by
  unfold cubeDensity
  have hD : (1 : ℝ) ≤ cubeDenominator n := by
    exact_mod_cast cubeDenominator_pos hn
  rw [div_le_one]
  · exact hD
  · exact_mod_cast cubeDenominator_pos hn

theorem cubeDenominator_mul_cubeDensity {n : ℕ} (hn : 0 < n) :
    (cubeDenominator n : ℝ) * cubeDensity n = 1 := by
  unfold cubeDensity
  field_simp [show (cubeDenominator n : ℝ) ≠ 0 by
    exact_mod_cast (cubeDenominator_pos hn).ne']

/-- Elementary inequality `2n ≤ 2^n` for positive `n`. -/
theorem two_mul_le_two_pow {n : ℕ} (hn : 0 < n) :
    2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have ih' := ih hnpos
        have htwo : 2 ≤ 2 ^ n := by
          exact (show 2 = 2 ^ 1 by norm_num) ▸
            pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) (by omega : 1 ≤ n)
        rw [pow_succ]
        omega

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- Real-cardinality form of the hypothesis that no proper affine plane
captures the requested `delta` fraction. -/
def HyperplaneSparse (n : ℕ) (delta : ℝ) (S : Finset V) : Prop :=
  ∀ plane : AffineSubspace ℝ V,
    finrank ℝ plane.direction < n →
      ((S.filter fun x ↦ x ∈ plane).card : ℝ) < delta * S.card

/-- Under hyperplane sparsity, the boundary of a full affine cube has fewer
than `2n * delta * |S|` points. -/
theorem boundary_card_lt {n : ℕ} (hn : 0 < n)
    (S : Finset V) (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    {delta : ℝ} (hsparse : HyperplaneSparse n delta S) :
    ((affineCubeBoundaryPart S e center).card : ℝ) <
      2 * (n : ℝ) * delta * S.card := by
  let faces : Finset (Fin n × Fin 2) := Finset.univ
  have hsubset := affineCubeBoundaryPart_subset_biUnion_faces S e center
  have hcardNat :
      (affineCubeBoundaryPart S e center).card ≤
        ∑ p ∈ faces, (affineCubeFacePart S e center p).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcardReal :
      ((affineCubeBoundaryPart S e center).card : ℝ) ≤
        ∑ p ∈ faces, ((affineCubeFacePart S e center p).card : ℝ) := by
    exact_mod_cast hcardNat
  have hfaces : faces.Nonempty := by
    refine ⟨(⟨0, hn⟩, 0), Finset.mem_univ _⟩
  have hsumlt :
      (∑ p ∈ faces, ((affineCubeFacePart S e center p).card : ℝ)) <
        ∑ _p ∈ faces, delta * S.card := by
    apply Finset.sum_lt_sum_of_nonempty hfaces
    intro p _hp
    exact hsparse (affineCubeFacePlane e center p.1
      (if p.2 = 0 then -1 else 1))
      (finrank_direction_affineCubeFacePlane_lt e center p.1
        (if p.2 = 0 then -1 else 1))
  refine hcardReal.trans_lt (hsumlt.trans_eq ?_)
  simp [faces]
  ring

/-- A Cube-Lemma slice has at least the reciprocal-denominator fraction of
the original set. -/
theorem cubeDensity_mul_card_le_of_card_le {n : ℕ} (hn : 0 < n)
    {S T : Finset V}
    (hcard : S.card ≤ cubeDenominator n * T.card) :
    cubeDensity n * S.card ≤ T.card := by
  have hcardR : (S.card : ℝ) ≤
      (cubeDenominator n : ℝ) * T.card := by exact_mod_cast hcard
  have hDpos : (0 : ℝ) < cubeDenominator n := by
    exact_mod_cast cubeDenominator_pos hn
  unfold cubeDensity
  rw [show 1 / (cubeDenominator n : ℝ) * S.card =
      (S.card : ℝ) / cubeDenominator n by ring]
  apply (div_le_iff₀ hDpos).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcardR

/-- The closed Cube-Lemma slice and hyperplane sparsity leave at least
`d/2` of the set in the cube interior. -/
theorem half_cubeDensity_mul_card_lt_interior
    {n : ℕ} (hn : 0 < n) (S : Finset V) (hS : S.Nonempty)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] V) (center : V)
    (T : Finset V) (hTS : T ⊆ S)
    (hTclosed : ∀ x ∈ T, x ∈ affineCubeClosed e center)
    (hTcard : S.card ≤ cubeDenominator n * T.card)
    {delta : ℝ}
    (hdelta : delta < cubeDensity n / (4 * n))
    (hsparse : HyperplaneSparse n delta S) :
    cubeDensity n / 2 * S.card <
      (affineCubeInteriorPart S e center).card := by
  let closed := affineCubeClosedPart S e center
  let interior := affineCubeInteriorPart S e center
  let boundary := affineCubeBoundaryPart S e center
  have hTclosedPart : T ⊆ closed := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hTS hx, hTclosed x hx⟩
  have hdSleT : cubeDensity n * S.card ≤ (T.card : ℝ) :=
    cubeDensity_mul_card_le_of_card_le hn hTcard
  have hTleClosed : (T.card : ℝ) ≤ closed.card := by
    exact_mod_cast Finset.card_le_card hTclosedPart
  have hclosedLe : (closed.card : ℝ) ≤ interior.card + boundary.card := by
    exact_mod_cast card_affineCubeClosedPart_le S e center
  have hboundary := boundary_card_lt hn S e center hsparse
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdensPos := cubeDensity_pos hn
  have hboundarySmall : (boundary.card : ℝ) <
      cubeDensity n / 2 * S.card := by
    calc
      (boundary.card : ℝ) < 2 * (n : ℝ) * delta * S.card := hboundary
      _ < cubeDensity n / 2 * S.card := by
        apply mul_lt_mul_of_pos_right _ (by
          exact_mod_cast (Finset.card_pos.mpr hS))
        calc
          2 * (n : ℝ) * delta <
              2 * (n : ℝ) * (cubeDensity n / (4 * n)) := by gcongr
          _ = cubeDensity n / 2 := by field_simp; ring
  linarith

/-- Quantitative contrapositive of Theorem 5.1: if every proper affine
plane is `delta`-sparse, then the doubling constant is at least
`2n - epsilon(delta)`. -/
theorem pairSumset_card_lower_bound
    {n : ℕ} (hn : 0 < n) (hfinrank : finrank ℝ V = n)
    (S : Finset V) (hS : S.Nonempty) (delta : ℝ) (hdelta : 0 < delta)
    (hsparse : HyperplaneSparse n delta S) :
    (2 * (n : ℝ) - twoNEpsilon n (cubeDensity n) delta) * S.card ≤
      ((pairSumset S).card : ℝ) := by
  let P : ℕ → Prop := fun N ↦
    ∀ T : Finset V, T.card = N → T.Nonempty →
      ∀ rho : ℝ, 0 < rho → HyperplaneSparse n rho T →
        (2 * (n : ℝ) - twoNEpsilon n (cubeDensity n) rho) * T.card ≤
          ((pairSumset T).card : ℝ)
  have hP : ∀ N, P N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        dsimp [P]
        intro T hTN hT rho hrho hsparseT
        subst N
        have hd0 := cubeDensity_pos hn
        have hd1 := cubeDensity_le_one hn
        by_cases hcutoff : cubeDensity n / (4 * n) ≤ rho
        · have heps := two_mul_le_twoNEpsilon_of_cutoff_le hn hd0 hcutoff
          have hpair0 : (0 : ℝ) ≤ (pairSumset T).card := by positivity
          have hT0 : (0 : ℝ) ≤ T.card := by positivity
          nlinarith
        · have hrhoSmall : rho < cubeDensity n / (4 * n) :=
            lt_of_not_ge hcutoff
          by_cases hlarge : 2 * n * T.card < (pairSumset T).card
          · have hlargeR :
                2 * (n : ℝ) * T.card < ((pairSumset T).card : ℝ) := by
              exact_mod_cast hlarge
            have hepsPos := twoNEpsilon_pos hn hd0 hrho
            have hT0 : (0 : ℝ) ≤ T.card := by positivity
            nlinarith
          · have hdouble :
                (pairSumset T).card ≤ (2 * n) * T.card := by omega
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
                  (cubeDenominator n : ℝ) * W.slice.card := by
                exact_mod_cast W.card_le
              have hDpos : (0 : ℝ) < cubeDenominator n := by
                exact_mod_cast cubeDenominator_pos hn
              have hDdelta : (cubeDenominator n : ℝ) * rho < 1 := by
                calc
                  (cubeDenominator n : ℝ) * rho <
                      (cubeDenominator n : ℝ) *
                        (cubeDensity n / (4 * n)) :=
                    mul_lt_mul_of_pos_left hrhoSmall hDpos
                  _ = 1 / (4 * (n : ℝ)) := by
                    rw [show (cubeDenominator n : ℝ) *
                        (cubeDensity n / (4 * n)) =
                        ((cubeDenominator n : ℝ) * cubeDensity n) /
                          (4 * n) by ring,
                      cubeDenominator_mul_cubeDensity hn]
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
              have hIlarge : cubeDensity n / 2 * T.card < I.card :=
                half_cubeDensity_mul_card_lt_interior hn T hT
                  W.coordinates W.center W.slice W.slice_subset
                  W.slice_mem_closed W.card_le hrhoSmall hsparseT
              have hIpos : 0 < I.card := by
                have hdhalf : 0 < cubeDensity n / 2 := by positivity
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
                  ∑ alpha ∈ cells, eta alpha ≤ 1 - cubeDensity n / 2 := by
                rw [hetaSum]
                have hdiv : cubeDensity n / 2 < (I.card : ℝ) / T.card := by
                  exact (lt_div_iff₀ hTposR).2 (by
                    simpa [mul_assoc] using hIlarge)
                linarith
              have hcellsCard : cells.card ≤ cellCount n := by
                simp [cells, cellCount]
              have herror := sum_twoNEpsilon_div_mul_lt_of_nonneg
                cells eta hn hd0 hd1 hrho hetaNonneg hcellsCard hetaSumLe
              have hcellLower : ∀ alpha ∈ cells,
                  (2 * (n : ℝ) -
                      twoNEpsilon n (cubeDensity n) (rho / eta alpha)) *
                      (A alpha).card ≤ ((pairSumset (A alpha)).card : ℝ) := by
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
                      (2 * (n : ℝ) -
                        twoNEpsilon n (cubeDensity n) (rho / eta alpha)) *
                        (A alpha).card ≤
                    ∑ alpha ∈ cells,
                      ((pairSumset (A alpha)).card : ℝ) := by
                exact Finset.sum_le_sum fun alpha halpha ↦
                  hcellLower alpha halpha
              have hcentral :
                  2 * (n : ℝ) * I.card ≤ (I.card * 2 ^ n : ℕ) := by
                have hcentralNat :=
                  Nat.mul_le_mul_left I.card (two_mul_le_two_pow hn)
                exact_mod_cast (by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using hcentralNat)
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
              have herrorScaled :
                  ∑ alpha ∈ cells,
                      twoNEpsilon n (cubeDensity n) (rho / eta alpha) *
                        (A alpha).card <
                    twoNEpsilon n (cubeDensity n) rho * T.card := by
                have hmul := mul_lt_mul_of_pos_right herror hTposR
                calc
                  ∑ alpha ∈ cells,
                      twoNEpsilon n (cubeDensity n) (rho / eta alpha) *
                        (A alpha).card =
                      (∑ alpha ∈ cells,
                        twoNEpsilon n (cubeDensity n) (rho / eta alpha) *
                          eta alpha) * T.card := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro alpha _halpha
                    have hetaMul : eta alpha * (T.card : ℝ) =
                        (A alpha).card := by
                      unfold eta
                      field_simp
                    rw [mul_assoc, hetaMul]
                  _ < twoNEpsilon n (cubeDensity n) rho * T.card := hmul
              have hsourceEq :
                  2 * (n : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (2 * (n : ℝ) -
                          twoNEpsilon n (cubeDensity n) (rho / eta alpha)) *
                          (A alpha).card =
                    2 * (n : ℝ) * T.card -
                      ∑ alpha ∈ cells,
                        twoNEpsilon n (cubeDensity n) (rho / eta alpha) *
                          (A alpha).card := by
                simp_rw [sub_mul, Finset.sum_sub_distrib]
                rw [← Finset.mul_sum]
                nlinarith
              have hsourceStrict :
                  (2 * (n : ℝ) -
                      twoNEpsilon n (cubeDensity n) rho) * T.card <
                    2 * (n : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (2 * (n : ℝ) -
                          twoNEpsilon n (cubeDensity n) (rho / eta alpha)) *
                          (A alpha).card := by
                rw [hsourceEq]
                nlinarith
              have hsourceLe :
                  2 * (n : ℝ) * I.card +
                      ∑ alpha ∈ cells,
                        (2 * (n : ℝ) -
                          twoNEpsilon n (cubeDensity n) (rho / eta alpha)) *
                          (A alpha).card ≤
                    ((I.card * 2 ^ n : ℕ) : ℝ) +
                      ∑ alpha ∈ cells,
                        ((pairSumset (A alpha)).card : ℝ) :=
                add_le_add hcentral houtsideLower
              exact (hsourceStrict.trans_le (hsourceLe.trans hmaster)).le
  exact hP S.card S rfl hS delta hdelta hsparse

/-- A fixed positive density at which the quantitative error is exactly
one.  This is the specialization needed by `RankTwoNStatement`. -/
def theoremDensity (n : ℕ) : ℝ :=
  cubeDensity n / (4 * (n : ℝ)) *
    (1 / (2 * (n : ℝ))) ^ (epsilonExponent n (cubeDensity n))⁻¹

theorem theoremDensity_pos {n : ℕ} (hn : 0 < n) :
    0 < theoremDensity n := by
  unfold theoremDensity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := cubeDensity_pos hn
  have hx : 0 < (1 / (2 * (n : ℝ)) : ℝ) := by positivity
  positivity

theorem twoNEpsilon_theoremDensity {n : ℕ} (hn : 0 < n) :
    twoNEpsilon n (cubeDensity n) (theoremDensity n) = 1 := by
  let d := cubeDensity n
  let nu := epsilonExponent n d
  let x : ℝ := 1 / (2 * (n : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < d := cubeDensity_pos hn
  have hnu : 0 < nu := epsilonExponent_pos hn hd
  have hx : 0 < x := by unfold x; positivity
  have hbase :
      4 * (n : ℝ) * theoremDensity n / cubeDensity n = x ^ nu⁻¹ := by
    have hdCube : cubeDensity n ≠ 0 := (cubeDensity_pos hn).ne'
    dsimp [x, nu, d]
    unfold theoremDensity
    field_simp [hdCube]
  unfold twoNEpsilon
  rw [hbase]
  rw [← Real.rpow_mul hx.le]
  rw [inv_mul_cancel₀ hnu.ne', Real.rpow_one]
  unfold x
  field_simp

/-- Real-density form of Freiman's Theorem 5.1 at epsilon one. -/
theorem exists_dense_hyperplane
    {n : ℕ} (hn : 0 < n) (hfinrank : finrank ℝ V = n)
    (S : Finset V) (hS : S.Nonempty)
    (hdouble : (pairSumset S).card < (2 * n - 1) * S.card) :
    ∃ plane : AffineSubspace ℝ V,
      finrank ℝ plane.direction < n ∧
        theoremDensity n * S.card ≤
          ((S.filter fun x ↦ x ∈ plane).card : ℝ) := by
  by_contra hnone
  have hsparse : HyperplaneSparse n (theoremDensity n) S := by
    intro plane hplane
    have hnot : ¬ theoremDensity n * S.card ≤
        ((S.filter fun x ↦ x ∈ plane).card : ℝ) := by
      intro hdense
      apply hnone
      exact ⟨plane, hplane, hdense⟩
    exact lt_of_not_ge hnot
  have hlower := pairSumset_card_lower_bound hn hfinrank S hS
    (theoremDensity n) (theoremDensity_pos hn) hsparse
  rw [twoNEpsilon_theoremDensity hn] at hlower
  have hdoubleR : ((pairSumset S).card : ℝ) <
      ((2 * n - 1) * S.card : ℕ) := by exact_mod_cast hdouble
  have hcoef : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    norm_num
  rw [Nat.cast_mul, hcoef] at hdoubleR
  linarith

/-- Freiman's Theorem 5.1 in the exact division-free form required by the
rest of the Bilu/CFP chain. -/
theorem twoNTheoremStatement : TwoNTheoremStatement.{u} := by
  intro n hn
  let delta := theoremDensity n
  have hdelta : 0 < delta := theoremDensity_pos hn
  obtain ⟨proportionConstant, hconstant⟩ :=
    exists_nat_gt (1 / delta)
  refine ⟨proportionConstant, ?_⟩
  intro W _ _ _ _ hfinrank S hS hdouble
  obtain ⟨plane, hdim, hdense⟩ :=
    exists_dense_hyperplane hn hfinrank S hS hdouble
  let slice := S.filter fun x ↦ x ∈ plane
  have hslice0 : (0 : ℝ) ≤ slice.card := by positivity
  have hrealCard : (S.card : ℝ) ≤
      (proportionConstant : ℝ) * slice.card := by
    have hinvpos : 0 < (1 / delta : ℝ) := by positivity
    calc
      (S.card : ℝ) = (1 / delta) * (delta * S.card) := by
        field_simp
      _ ≤ (1 / delta) * slice.card :=
        mul_le_mul_of_nonneg_left hdense hinvpos.le
      _ ≤ (proportionConstant : ℝ) * slice.card :=
        mul_le_mul_of_nonneg_right hconstant.le hslice0
  refine ⟨{
    plane := plane
    dimension_lt := hdim
    slice := slice
    slice_subset := Finset.filter_subset _ _
    slice_mem_plane := ?_
    card_le := ?_ }⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact_mod_cast hrealCard

/-- Unconditional form of Bilu's generalized Theorem 5.6, obtained by
feeding Theorem 5.1 into the already-verified generic-projection bridge. -/
theorem exists_constant_affineSlice (rank : ℕ) (hrank : 0 < rank) :
    ∃ proportionConstant : ℕ,
      ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
        [FiniteDimensional ℝ W] [DecidableEq W],
        rank ≤ finrank ℝ W →
        ∀ S : Finset W, S.Nonempty →
          (pairSumset S).card < (2 * rank - 1) * S.card →
          Nonempty (AffineSliceWitness rank proportionConstant S) :=
  exists_constant_affineSlice_of_twoNTheorem
    twoNTheoremStatement rank hrank

end

end Erdos186.CFP.Bilu.Section5EpsilonInduction

#print axioms Erdos186.CFP.Bilu.Section5EpsilonInduction.boundary_card_lt
#print axioms Erdos186.CFP.Bilu.Section5EpsilonInduction.half_cubeDensity_mul_card_lt_interior
#print axioms Erdos186.CFP.Bilu.Section5EpsilonInduction.pairSumset_card_lower_bound
#print axioms Erdos186.CFP.Bilu.Section5EpsilonInduction.twoNTheoremStatement
#print axioms Erdos186.CFP.Bilu.Section5EpsilonInduction.exists_constant_affineSlice
