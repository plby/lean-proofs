/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos874.Foundations

/-!
# Erdős 874: the exact final inequality

This file contains the integral endgame in Deshouillers--Freiman's proof.
The preceding structural and local-density arguments produce a positive
progression difference `q`, a parity error `θ ∈ {0,1}`, and the master
inequality displayed below.  We prove, without division or truncated natural
subtraction, that it implies the sharp bound `(K + 1)² ≤ 4N + 1`.

All polynomial calculations are made in `ℤ`; a final lemma transports the
result back to natural cardinalities.
-/

namespace Erdos874

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma restrictedSumset_mono_exactUpper
    {r : ℕ} {A B : Finset ℤ} (hAB : A ⊆ B) :
    restrictedSumset r A ⊆ restrictedSumset r B := by
  intro z hz
  obtain ⟨C, hCA, hCr, rfl⟩ := mem_restrictedSumset.mp hz
  exact mem_restrictedSumset.mpr ⟨C, hCA.trans hAB, hCr, rfl⟩

/-! ## Fixed translates and the density pigeonhole -/

/-- A block of progression terms, kept local to the exact endgame so this
module does not depend on any particular formulation of the local-density
theorem. -/
def endgameProgressionBlock (z q : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image fun i : ℕ => z + q * (i : ℤ)

lemma endgameProgressionBlock_card {z q : ℤ} (hq : q ≠ 0) (n : ℕ) :
    (endgameProgressionBlock z q n).card = n := by
  have hinj : Function.Injective (fun i : ℕ => z + q * (i : ℤ)) := by
    intro i j hij
    have hmul : q * (i : ℤ) = q * (j : ℤ) := by linarith
    have hcast : (i : ℤ) = (j : ℤ) := mul_left_cancel₀ hq hmul
    exact_mod_cast hcast
  unfold endgameProgressionBlock
  exact (Finset.card_image_of_injective (Finset.range n) hinj).trans
    (Finset.card_range n)

/-- Adjoining one fixed set of summands translates a restricted-sum layer.
The disjointness hypothesis is what ensures that the union still consists of
distinct elements. -/
theorem fixed_subset_sum_add_mem_restrictedSumset
    {A V B : Finset ℤ} {r : ℕ} {z : ℤ}
    (hVA : V ⊆ A) (hBA : B ⊆ A) (hBV : Disjoint B V)
    (hz : z ∈ restrictedSumset r V) :
    (∑ x ∈ B, x) + z ∈ restrictedSumset (B.card + r) A := by
  obtain ⟨C, hCV, hCr, hCsum⟩ := mem_restrictedSumset.mp hz
  have hBC : Disjoint B C := hBV.mono_right hCV
  apply mem_restrictedSumset.mpr
  refine ⟨B ∪ C, Finset.union_subset hBA (hCV.trans hVA), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hBC, hCr]
  · rw [Finset.sum_union hBC, hCsum]

/-- The original layer and a layer translated by a fixed disjoint subset are
disjoint whenever their total numbers of summands differ.  This is the exact
admissibility input in both DF99 pigeonhole arguments. -/
theorem restrictedSumset_disjoint_fixed_translate
    {A V B : Finset ℤ} {r s : ℕ}
    (hA : IsAdmissible A)
    (hVA : V ⊆ A) (hBA : B ⊆ A) (hBV : Disjoint B V)
    (hr : 0 < r) (hrs : r ≠ B.card + s) (hBs : 0 < B.card + s) :
    Disjoint (restrictedSumset r V)
      ((restrictedSumset s V).image fun z => (∑ x ∈ B, x) + z) := by
  rw [Finset.disjoint_left]
  intro z hzr hzt
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzt
  have hleft : w + ∑ x ∈ B, x ∈ restrictedSumset r A := by
    simpa [add_comm] using restrictedSumset_mono_exactUpper hVA hzr
  have hright : w + ∑ x ∈ B, x ∈ restrictedSumset (B.card + s) A := by
    simpa [add_comm] using
      fixed_subset_sum_add_mem_restrictedSumset hVA hBA hBV hw
  exact (Finset.disjoint_left.mp (hA hr hBs hrs)) hleft hright

/-- Two subsets occupying strict majorities of the same finite block must
intersect. -/
theorem not_disjoint_of_majorities_on_block
    {B X Y : Finset ℤ} {R : ℕ}
    (hcard : B.card ≤ 2 * R + 1)
    (hX : R + 1 ≤ (B ∩ X).card)
    (hY : R + 1 ≤ (B ∩ Y).card) :
    ¬ Disjoint X Y := by
  intro hXY
  have hd : Disjoint (B ∩ X) (B ∩ Y) :=
    hXY.mono Finset.inter_subset_right Finset.inter_subset_right
  have hunion : (B ∩ X) ∪ (B ∩ Y) ⊆ B := by
    exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hd] at hle
  omega

/-- Pigeonhole on an actual block of `2R+1` progression terms. -/
theorem not_disjoint_of_progression_majorities
    {z q : ℤ} {X Y : Finset ℤ} {R : ℕ}
    (hq : q ≠ 0)
    (hX : R + 1 ≤ ((endgameProgressionBlock z q (2 * R + 1)) ∩ X).card)
    (hY : R + 1 ≤ ((endgameProgressionBlock z q (2 * R + 1)) ∩ Y).card) :
    ¬ Disjoint X Y := by
  apply not_disjoint_of_majorities_on_block
      (B := endgameProgressionBlock z q (2 * R + 1))
      (X := X) (Y := Y) (R := R)
  · rw [endgameProgressionBlock_card hq]
  · exact hX
  · exact hY

/-! ## The parity parameter -/

/-- The remainder left after removing `q` and the largest even number from
`T`.  In the application, `T = K - 2u` and `sigma T q` is the number of
central elements used in the first restricted-sum layer. -/
def sigma (T q : ℕ) : ℕ := (T - q) / 2

/-- The parity parameter in the Deshouillers--Freiman endgame. -/
def theta (T q : ℕ) : ℕ := T - (2 * sigma T q + q)

theorem theta_eq_mod_two (T q : ℕ) (hqT : q ≤ T) :
    theta T q = (T - q) % 2 := by
  simp only [theta, sigma]
  omega

theorem theta_eq_zero_or_one (T q : ℕ) (hqT : q ≤ T) :
    theta T q = 0 ∨ theta T q = 1 := by
  rw [theta_eq_mod_two T q hqT]
  omega

theorem two_sigma_add_q_add_theta (T q : ℕ) (hqT : q ≤ T) :
    2 * sigma T q + q + theta T q = T := by
  simp only [theta, sigma]
  omega

/-! ## Ordered progression bookkeeping -/

/-- `QSeparated a K q` says that the first `K` entries of `a` are separated
by at least `q` times their index distance.  An increasing enumeration of
distinct integers all congruent modulo a positive `q` has this property. -/
def QSeparated (a : ℕ → ℤ) (K q : ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < j → j < K →
    a i + (q : ℤ) * ((j : ℤ) - (i : ℤ)) ≤ a j

/-- It is enough to check the gap `q` on adjacent entries. -/
theorem qSeparated_of_adjacent {a : ℕ → ℤ} {K q : ℕ}
    (hadj : ∀ i : ℕ, i + 1 < K → a i + q ≤ a (i + 1)) :
    QSeparated a K q := by
  intro i j hij hjK
  have hwalk : ∀ d : ℕ, i + d < K →
      a i + (q : ℤ) * (d : ℤ) ≤ a (i + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro hidK
        calc
          a i + (q : ℤ) * ((d + 1 : ℕ) : ℤ) =
              (a i + (q : ℤ) * (d : ℤ)) + q := by
                push_cast
                ring
          _ ≤ a (i + d) + q := by
            have hd := ih (by omega)
            linarith
          _ ≤ a (i + (d + 1)) := by
            simpa [Nat.add_assoc] using hadj (i + d) (by omega)
  have hijEq : i + (j - i) = j := by omega
  have h := hwalk (j - i) (by omega)
  rw [hijEq] at h
  have hcast : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
    rw [Nat.cast_sub (by omega)]
  simpa [hcast] using h

/-- The paired endpoint difference for the first `K` terms, using `L` terms
from either end. -/
def pairedEndpointSpread (a : ℕ → ℤ) (K L : ℕ) : ℤ :=
  ∑ i ∈ Finset.range L, (a (K - 1 - i) - a i)

private theorem sum_symmetric_index_gaps (K L : ℕ) :
    (∑ i ∈ Finset.range L,
        ((K : ℤ) - 2 * (i : ℤ) - 1)) =
      (L : ℤ) * ((K : ℤ) - (L : ℤ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The paired-endpoint estimate used in the DF99 cancellation:

`∑_{i=1}^L (a_{K-i+1}-a_i) ≥ q L (K-L)`.

The statement uses zero-based indexing. -/
theorem pairedEndpointSpread_lower {a : ℕ → ℤ} {K L q : ℕ}
    (hL : 2 * L ≤ K) (hsep : QSeparated a K q) :
    (q : ℤ) * (L : ℤ) * ((K : ℤ) - (L : ℤ)) ≤
      pairedEndpointSpread a K L := by
  have hpoint : ∀ i ∈ Finset.range L,
      (q : ℤ) * ((K : ℤ) - 2 * (i : ℤ) - 1) ≤
        a (K - 1 - i) - a i := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hij : i < K - 1 - i := by omega
    have hjK : K - 1 - i < K := by omega
    have h := hsep hij hjK
    have hcast : ((K - 1 - i : ℕ) : ℤ) = (K : ℤ) - 1 - (i : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast] at h
    linarith
  calc
    (q : ℤ) * (L : ℤ) * ((K : ℤ) - (L : ℤ)) =
        ∑ i ∈ Finset.range L,
          (q : ℤ) * ((K : ℤ) - 2 * (i : ℤ) - 1) := by
            rw [← Finset.mul_sum]
            rw [sum_symmetric_index_gaps]
            ring
    _ ≤ ∑ i ∈ Finset.range L, (a (K - 1 - i) - a i) :=
      Finset.sum_le_sum hpoint
    _ = pairedEndpointSpread a K L := rfl

/-! ## Algebraic endgame -/

/-- The exact master inequality obtained from the two local-density
pigeonhole arguments in the 1999 proof. -/
def MasterInequality (N K q θ : ℤ) : Prop :=
  K ^ 2 - (q + θ) ^ 2 ≤
    4 * N - 2 * K * q + 2 * q * (1 - θ) - 4

/-- The density/pigeonhole and endpoint estimates, with the factor `2`
cleared.  Here `L = u + σ`, `K = 2L + q + θ`, and the right side is the
paper's endpoint estimate

`Nq - q²(K-L) + q²(q+1)/2 - q`.

Keeping this intermediate inequality separate makes the final cancellation
independent of any convention for integer division. -/
def ClearedDensityEstimate (N K L q : ℤ) : Prop :=
  2 * q * L * (K - L) ≤
    2 * N * q - 2 * q ^ 2 * (K - L) + q ^ 2 * (q + 1) - 2 * q

/-- The first local-density separation.  `α` is the sum of the first `q`
elements and `spread = M(σ)-m(σ)`.  Notice the `2R+1`. -/
def FirstPigeonholeBound (α spread : ℤ) (R : ℕ) (q : ℤ) : Prop :=
  spread - (2 * (R : ℤ) + 1) * q ≤ α

/-- The second local-density separation after rearranging endpoint sums.
Here `P` is the paired endpoint sum and `U` is the sum of the `q` unpaired
middle terms.  The correction term is **`2R-1`**, as in DF99 pp. 146--147;
using `2R+1` here loses the sharp theorem. -/
def SecondPigeonholeBound (P U : ℤ) (R : ℕ) (q : ℤ) : Prop :=
  P ≤ U + (2 * (R : ℤ) - 1) * q

/-- The extra central-span gain in the paired endpoint sum.  The first `u`
outer pairs cross all `R` missing progression steps, contributing `uRq` in
addition to the baseline `qL(K-L)`. -/
def OuterPairBound (K L q P : ℤ) (u R : ℕ) : Prop :=
  q * L * (K - L) + (u : ℤ) * (R : ℤ) * q ≤ P

/-- The elementary ambient endpoint estimate for the `q` unpaired middle
terms.  The factor `2` clears the triangular-number denominator. -/
def MiddleEndpointBound (N K L q U : ℤ) : Prop :=
  2 * U ≤
    2 * N * q - 2 * q ^ 2 * (K - L) + q ^ 2 * (q + 1)

/-- The central-span gain, the corrected second pigeonhole bound, and the
middle endpoint estimate together give the cleared density estimate. -/
theorem cleared_density_estimate_of_pigeonhole_bounds
    {N K L q P U : ℤ} {u R : ℕ}
    (hq : 0 ≤ q) (hu : 2 ≤ u)
    (hpaired : OuterPairBound K L q P u R)
    (hsecond : SecondPigeonholeBound P U R q)
    (hmiddle : MiddleEndpointBound N K L q U) :
    ClearedDensityEstimate N K L q := by
  dsimp [OuterPairBound] at hpaired
  dsimp [SecondPigeonholeBound] at hsecond
  dsimp [MiddleEndpointBound] at hmiddle
  dsimp [ClearedDensityEstimate]
  have hu' : (2 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hR : 0 ≤ (R : ℤ) := by omega
  have hgain : 0 ≤ ((u : ℤ) - 2) * (R : ℤ) * q :=
    mul_nonneg (mul_nonneg (by omega) hR) hq
  nlinarith

/-- Clearing the density estimate gives the master inequality (3.17). -/
theorem master_of_cleared_density_estimate {N K L q θ : ℤ}
    (hq : 1 ≤ q) (hK : K = 2 * L + q + θ)
    (hdensity : ClearedDensityEstimate N K L q) :
    MasterInequality N K q θ := by
  dsimp [ClearedDensityEstimate] at hdensity
  dsimp [MasterInequality]
  have hfactor :
      q * ((K ^ 2 - (q + θ) ^ 2) -
        (4 * N - 2 * K * q + 2 * q * (1 - θ) - 4)) ≤ 0 := by
    calc
      q * ((K ^ 2 - (q + θ) ^ 2) -
          (4 * N - 2 * K * q + 2 * q * (1 - θ) - 4)) =
          2 * ((2 * q * L * (K - L)) -
            (2 * N * q - 2 * q ^ 2 * (K - L) +
              q ^ 2 * (q + 1) - 2 * q)) := by
              rw [hK]
              ring
      _ ≤ 0 := by linarith
  have hqpos : 0 < q := by omega
  have := nonpos_of_mul_nonpos_right hfactor hqpos
  linarith

/-- When the parity error is zero, the master inequality gives the slightly
stronger estimate `(K+1)² ≤ 4N`.

The eventual side condition `q+3 ≤ 2K` makes the correction term
`(q-1)(q+3-2K)` nonpositive.
-/
theorem even_final_bound {N K q : ℤ}
    (hq : 1 ≤ q) (hsize : q + 3 ≤ 2 * K)
    (hmaster : MasterInequality N K q 0) :
    (K + 1) ^ 2 ≤ 4 * N := by
  have hnonpos : (q - 1) * (q + 3 - 2 * K) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  dsimp [MasterInequality] at hmaster
  nlinarith

/-- When the parity error is one, the master inequality gives exactly the
required estimate `(K+1)² ≤ 4N+1`. -/
theorem odd_final_bound {N K q : ℤ}
    (hq : 1 ≤ q) (hsize : q + 3 ≤ 2 * K)
    (hmaster : MasterInequality N K q 1) :
    (K + 1) ^ 2 ≤ 4 * N + 1 := by
  have hnonpos : (q - 1) * (q + 3 - 2 * K) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  dsimp [MasterInequality] at hmaster
  nlinarith

/-- Deshouillers--Freiman's parity split, in a form directly usable after the
combinatorial construction of `q` and `θ`. -/
theorem exact_upper_of_master {N K q θ : ℤ}
    (hq : 1 ≤ q) (hsize : q + 3 ≤ 2 * K)
    (hθ : θ = 0 ∨ θ = 1)
    (hmaster : MasterInequality N K q θ) :
    (K + 1) ^ 2 ≤ 4 * N + 1 := by
  rcases hθ with rfl | rfl
  · have h := even_final_bound hq hsize hmaster
    omega
  · exact odd_final_bound hq hsize hmaster

/-- Combined finite endgame, starting from the cleared output of the two
local-density applications. -/
theorem exact_upper_of_cleared_density_estimate {N K L q θ : ℤ}
    (hq : 1 ≤ q) (hsize : q + 3 ≤ 2 * K)
    (hθ : θ = 0 ∨ θ = 1)
    (hK : K = 2 * L + q + θ)
    (hdensity : ClearedDensityEstimate N K L q) :
    (K + 1) ^ 2 ≤ 4 * N + 1 :=
  exact_upper_of_master hq hsize hθ
    (master_of_cleared_density_estimate hq hK hdensity)

/-- Natural-number wrapper for the exact upper-bound endgame.  The hypothesis
is stated after casting to `ℤ`, so no information is lost to truncated
subtraction. -/
theorem nat_exact_upper_of_master {N K q θ : ℕ}
    (hq : 1 ≤ q) (hsize : q + 3 ≤ 2 * K)
    (hθ : θ = 0 ∨ θ = 1)
    (hmaster : MasterInequality (N : ℤ) (K : ℤ) (q : ℤ) (θ : ℤ)) :
    (K + 1) ^ 2 ≤ 4 * N + 1 := by
  have h := exact_upper_of_master
    (N := (N : ℤ)) (K := (K : ℤ)) (q := (q : ℤ)) (θ := (θ : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hsize)
    (by rcases hθ with rfl | rfl <;> simp) hmaster
  exact_mod_cast h

/-! ## Connection to the finite extremal problem -/

/-- The exact finite output required from the central-span and local-density
parts of the proof.  This definition packages only their concrete witnesses
and the explicit inequality they establish; it contains no occurrence of the
desired upper bound. -/
def HasDensityEndgame (N : ℕ) (A : Finset ℤ) : Prop :=
  ∃ L q θ : ℕ,
    1 ≤ q ∧ q + 3 ≤ 2 * A.card ∧ (θ = 0 ∨ θ = 1) ∧
      (A.card : ℤ) = 2 * (L : ℤ) + (q : ℤ) + (θ : ℤ) ∧
      ClearedDensityEstimate (N : ℤ) (A.card : ℤ) (L : ℤ) (q : ℤ)

/-- The DF99 density endgame implies the sharp finite cardinality bound. -/
theorem card_sq_le_of_density_endgame {N : ℕ} {A : Finset ℤ}
    (h : HasDensityEndgame N A) :
    (A.card + 1) ^ 2 ≤ 4 * N + 1 := by
  obtain ⟨L, q, θ, hq, hsize, hθ, hK, hdensity⟩ := h
  have hfinal := exact_upper_of_cleared_density_estimate
    (N := (N : ℤ)) (K := (A.card : ℤ)) (L := (L : ℤ))
    (q := (q : ℤ)) (θ := (θ : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hsize)
    (by rcases hθ with rfl | rfl <;> simp) hK hdensity
  exact_mod_cast hfinal

/-- Applying the finite endgame to a maximizing admissible set bounds `k N`.
This is the precise seam used by the public eventual theorem. -/
theorem k_sq_le_of_all_density_endgames {N : ℕ}
    (hendgame : ∀ A : Finset ℤ, IsBoundedAdmissible N A →
      HasDensityEndgame N A) :
    (k N + 1) ^ 2 ≤ 4 * N + 1 := by
  obtain ⟨A, hA, hcard⟩ := exists_boundedAdmissible_card_eq_k N
  simpa [← hcard] using card_sq_le_of_density_endgame (hendgame A hA)

/-- It suffices to construct the density endgame for cardinality maximizers.
This is the connector used in the eventual theorem: empty and small
admissible sets need not satisfy the large-set structural conclusions. -/
theorem k_sq_le_of_maximizers_density_endgame {N : ℕ}
    (hendgame : ∀ A : Finset ℤ, IsBoundedAdmissible N A →
      A.card = k N → HasDensityEndgame N A) :
    (k N + 1) ^ 2 ≤ 4 * N + 1 := by
  obtain ⟨A, hA, hcard⟩ := exists_boundedAdmissible_card_eq_k N
  simpa [← hcard] using card_sq_le_of_density_endgame (hendgame A hA hcard)

end

end Erdos874
