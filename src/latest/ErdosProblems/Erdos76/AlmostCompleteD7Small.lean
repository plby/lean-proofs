/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostCompleteD7Parameters
import ErdosProblems.Erdos76.FractionalHallTransport

/-!
# The small-universal-set branch of case D7

This module implements the fractional Hall redistribution used when the set
of universal vertices has size at most `n-8`.  The resulting flows are the
edge-capacity deductions in the weighted vertex-deletion packings.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The right capacity at a nonuniversal vertex in the D7 Hall graph. -/
def d7HallCapacity (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  (Gᶜ.degree (u : A) - 1 - sigma u : ℕ)

/-- The source mass attached to a nonuniversal vertex. -/
def d7HallBetaSource (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  ((universalVertices G).card : ℝ) * P.betaIncident u

/-- The unrestricted source mass in the D7 Hall graph. -/
def d7HallAlphaSource (G : SimpleGraph A) (P : D7SeparatedParameters G) : ℝ :=
  ((universalVertices G).card : ℝ) / 2 * P.alphaMass

lemma d7HallCapacity_nonneg (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) : 0 ≤ d7HallCapacity G sigma u := by
  unfold d7HallCapacity
  positivity

lemma d7HallBetaSource_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (u : ↑(nonUniversalVertices G)) :
    0 ≤ d7HallBetaSource G P u := by
  exact mul_nonneg (Nat.cast_nonneg _) (P.betaIncident_nonneg u)

lemma d7HallAlphaSource_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (hm : 1 ≤ (universalVertices G).card) :
    0 ≤ d7HallAlphaSource G P := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (P.alphaMass_nonneg hm)

lemma sum_d7HallCapacity {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 8 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G a u)
    (hsupport : ∀ u ∉ nonUniversalVertices G, sigma u = 0)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a) :
    (∑ u : ↑(nonUniversalVertices G), d7HallCapacity G sigma u) =
      (n + (universalVertices G).card - 8 : ℕ) := by
  have hpoint : ∀ u : ↑(nonUniversalVertices G),
      d7HallCapacity G sigma u =
        (Gᶜ.degree (u : A) : ℝ) - 1 - sigma u := by
    intro u
    unfold d7HallCapacity
    have hpos : 0 < Gᶜ.degree (u : A) := mem_nonUniversalVertices.mp u.property
    have hs : sigma u ≤ Gᶜ.degree (u : A) - 1 :=
      (hsigma u).trans (Nat.min_le_right _ _)
    rw [Nat.cast_sub hs,
      Nat.cast_sub (by omega : 1 ≤ Gᶜ.degree (u : A)), Nat.cast_one]
  rw [Finset.sum_congr rfl fun u _ ↦ hpoint u,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdegrees : (∑ u : ↑(nonUniversalVertices G),
      (Gᶜ.degree (u : A) : ℝ)) = 2 * (n - 4 + a : ℕ) := by
    norm_cast
    calc
      (∑ u : ↑(nonUniversalVertices G), Gᶜ.degree (u : A)) =
          ∑ u ∈ nonUniversalVertices G, Gᶜ.degree u :=
        (Finset.sum_subtype (nonUniversalVertices G) (fun _ ↦ Iff.rfl)
          (fun u : A ↦ Gᶜ.degree u)).symm
      _ = 2 * (n - 4 + a) := by
        simpa only [hexact] using sum_nonUniversalVertices_compl_degree G
  have hsigmaSubtype : (∑ u : ↑(nonUniversalVertices G), (sigma u : ℝ)) =
      (2 * a : ℕ) := by
    norm_cast
    calc
      (∑ u : ↑(nonUniversalVertices G), sigma (u : A)) =
          ∑ u ∈ nonUniversalVertices G, sigma u :=
        (Finset.sum_subtype (nonUniversalVertices G) (fun _ ↦ Iff.rfl)
          sigma).symm
      _ = 2 * a := hsum
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  rw [hcard] at hparts
  simp only [hdegrees, hsigmaSubtype, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one]
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = n := by exact_mod_cast hparts
  norm_num only [Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_add,
    Nat.cast_sub (by omega : 8 ≤ n + (universalVertices G).card)]
  linarith

lemma sum_d7HallBetaSource (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    (∑ u, d7HallBetaSource G P u) =
      2 * ((universalVertices G).card : ℝ) * P.betaMass := by
  unfold d7HallBetaSource
  rw [← Finset.mul_sum, P.sum_betaIncident_eq_two_betaMass]
  ring

lemma d7Hall_totalSource_le_two_mul (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (hm : 4 ≤ (universalVertices G).card) :
    (∑ u, d7HallBetaSource G P u) + d7HallAlphaSource G P ≤
      2 * ((universalVertices G).card : ℝ) := by
  rw [sum_d7HallBetaSource]
  unfold d7HallAlphaSource
  have halpha0 := P.alphaMass_nonneg (by omega)
  have hbeta0 := P.betaMass_nonneg
  have halphaBeta : P.alphaMass + P.betaMass ≤ 1 := by
    have hgamma := P.gammaTerm_nonneg (by omega)
    have hnorm :
        ((((universalVertices G).card : ℝ) - 1) *
            (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma +
          P.alphaMass + P.betaMass = 1 := by
      simpa only [D7SeparatedParameters.alphaMass,
        D7SeparatedParameters.betaMass] using P.normalization
    linarith
  have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma d7HallBetaSource_le_m (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    d7HallBetaSource G P u ≤ ((universalVertices G).card : ℝ) := by
  unfold d7HallBetaSource
  have hinc := (P.betaIncident_le_betaMass u).trans
    (P.betaMass_le_one (by omega))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hinc
      (show 0 ≤ ((universalVertices G).card : ℝ) from Nat.cast_nonneg _)

lemma d7HallCapacity_le_degree_sub_one
    (G : SimpleGraph A) (sigma : A → ℕ)
    (u : ↑(nonUniversalVertices G)) :
    d7HallCapacity G sigma u ≤ (Gᶜ.degree (u : A) - 1 : ℕ) := by
  unfold d7HallCapacity
  exact_mod_cast Nat.sub_le _ _

/-- The singleton Hall bound: after deleting the forbidden column `u`, at
least `m` units of right capacity remain. -/
lemma d7HallCapacity_erase_ge_m {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G a u)
    (hsupport : ∀ u ∉ nonUniversalVertices G, sigma u = 0)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a)
    (u : ↑(nonUniversalVertices G)) :
    ((universalVertices G).card : ℝ) ≤
      (∑ v, d7HallCapacity G sigma v) - d7HallCapacity G sigma u := by
  rw [sum_d7HallCapacity hcard (by omega) G hexact sigma hsigma hsupport hsum]
  have hcap := d7HallCapacity_le_degree_sub_one G sigma u
  have hdegree := hnoD5 (u : A)
  have hnat : (universalVertices G).card +
      (Gᶜ.degree (u : A) - 1) ≤
        n + (universalVertices G).card - 8 := by
    omega
  have hnatR : ((universalVertices G).card : ℝ) +
      (Gᶜ.degree (u : A) - 1 : ℕ) ≤
        (n + (universalVertices G).card - 8 : ℕ) := by
    exact_mod_cast hnat
  linarith

/-- The exact D7 fractional-Hall output. -/
structure D7HallRedistribution (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ) where
  betaFlow : ↑(nonUniversalVertices G) → ↑(nonUniversalVertices G) → ℝ
  alphaFlow : ↑(nonUniversalVertices G) → ℝ
  beta_nonneg : ∀ u v, 0 ≤ betaFlow u v
  alpha_nonneg : ∀ u, 0 ≤ alphaFlow u
  beta_source_sum : ∀ v, ∑ u, betaFlow u v = d7HallBetaSource G P v
  alpha_sum : ∑ u, alphaFlow u = d7HallAlphaSource G P
  diagonal_zero : ∀ u, betaFlow u u = 0
  target_le : ∀ u,
    (∑ v, betaFlow u v) + alphaFlow u ≤ d7HallCapacity G sigma u

/-- Claim 5.4's fractional matching in the `m ≤ n-8` branch. -/
theorem exists_d7HallRedistribution {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hsmall : (universalVertices G).card ≤ n - 8)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (P : D7SeparatedParameters G)
    (sigma : A → ℕ)
    (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G a u)
    (hsupport : ∀ u ∉ nonUniversalVertices G, sigma u = 0)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a) :
    ∃ R : D7HallRedistribution G P sigma, True := by
  let d : Option ↑(nonUniversalVertices G) → ℝ := fun src ↦
    match src with
    | none => d7HallAlphaSource G P
    | some u => d7HallBetaSource G P u
  let c : ↑(nonUniversalVertices G) → ℝ := d7HallCapacity G sigma
  have hd : ∀ src, 0 ≤ d src := by
    intro src
    rcases src with _ | u
    · exact d7HallAlphaSource_nonneg G P (by omega)
    · exact d7HallBetaSource_nonneg G P u
  have hc : ∀ u, 0 ≤ c u := d7HallCapacity_nonneg G sigma
  have htotalR : (∑ src, d src) ≤ ∑ u, c u := by
    rw [Fintype.sum_option]
    change d7HallAlphaSource G P + (∑ u, d7HallBetaSource G P u) ≤ _
    rw [sum_d7HallCapacity hcard (by omega) G hexact sigma hsigma hsupport hsum]
    have hsource := d7Hall_totalSource_le_two_mul G P hm
    have hsmallR : 2 * ((universalVertices G).card : ℝ) ≤
        (n + (universalVertices G).card - 8 : ℕ) := by
      exact_mod_cast (by omega : 2 * (universalVertices G).card ≤
        n + (universalVertices G).card - 8)
    linarith
  have hsingleR : ∀ u, d (some u) ≤ (∑ v, c v) - c u := by
    intro u
    exact (d7HallBetaSource_le_m G P hm u).trans
      (d7HallCapacity_erase_ge_m hcard hn ha G hexact hm hnoD5 sigma
        hsigma hsupport hsum u)
  obtain ⟨μ, hμ0, hrow, hdiag, hcol⟩ :=
    exists_offDiagonalTransport_real d c hd hc htotalR hsingleR
  let R : D7HallRedistribution G P sigma :=
    { betaFlow := fun u v ↦ μ (some v) u
      alphaFlow := fun u ↦ μ none u
      beta_nonneg := fun u v ↦ hμ0 (some v) u
      alpha_nonneg := fun u ↦ hμ0 none u
      beta_source_sum := fun v ↦ by simpa [d] using hrow (some v)
      alpha_sum := by simpa [d] using hrow none
      diagonal_zero := fun u ↦ hdiag u
      target_le := fun u ↦ by
        simpa [c, Fintype.sum_option, add_comm] using hcol u }
  exact ⟨R, trivial⟩

/-! ## Hall deductions on a deleted graph -/

private lemma mem_nonUniversalVertices_of_not_mem_universalVertices
    (G : SimpleGraph A) {v : A} (hv : v ∉ universalVertices G) :
    v ∈ nonUniversalVertices G := by
  apply mem_nonUniversalVertices.mpr
  apply Nat.pos_of_ne_zero
  intro hz
  exact hv (mem_universalVertices.mpr hz)

/-- The amount removed from an edge of `G-u` by the Hall redistribution
targeted at `u`.  Mixed edges share the corresponding `beta` target evenly
among the `m` universal endpoints; universal edges share `alpha` evenly
among the `choose m 2` universal pairs. -/
def d7SmallHallDeduction (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G)) :
    Sym2 (↑(d7DeletedFinset (u : A))) → ℝ :=
  Sym2.lift ⟨fun x y ↦
    if hx : (x : A) ∈ universalVertices G then
      if hy : (y : A) ∈ universalVertices G then
        R.alphaFlow u / (((universalVertices G).card.choose 2 : ℕ) : ℝ)
      else
        R.betaFlow u ⟨(y : A),
          mem_nonUniversalVertices_of_not_mem_universalVertices G hy⟩ /
            ((universalVertices G).card : ℝ)
    else if hy : (y : A) ∈ universalVertices G then
      R.betaFlow u ⟨(x : A),
        mem_nonUniversalVertices_of_not_mem_universalVertices G hx⟩ /
          ((universalVertices G).card : ℝ)
    else 0,
    by
      intro x y
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp [hx, hy]⟩

lemma d7SmallHallDeduction_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) :
    0 ≤ d7SmallHallDeduction G P sigma R u e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      unfold d7SmallHallDeduction
      simp only [Sym2.lift_mk]
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp only [hx, hy, dite_true, dite_false]
      · exact div_nonneg (R.alpha_nonneg u) (Nat.cast_nonneg _)
      · exact div_nonneg (R.beta_nonneg u _) (Nat.cast_nonneg _)
      · exact div_nonneg (R.beta_nonneg u _) (Nat.cast_nonneg _)
      · exact le_rfl

lemma D7HallRedistribution.betaFlow_le_m (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u v : ↑(nonUniversalVertices G)) :
    R.betaFlow u v ≤ ((universalVertices G).card : ℝ) := by
  have hle : R.betaFlow u v ≤ ∑ x, R.betaFlow x v := by
    apply Finset.single_le_sum (fun x _ ↦ R.beta_nonneg x v)
    exact Finset.mem_univ u
  rw [R.beta_source_sum v] at hle
  exact hle.trans (d7HallBetaSource_le_m G P hm v)

lemma D7HallRedistribution.alphaFlow_le_choose_two (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    R.alphaFlow u ≤ (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
  have hle : R.alphaFlow u ≤ ∑ x, R.alphaFlow x := by
    apply Finset.single_le_sum (fun x _ ↦ R.alpha_nonneg x)
    exact Finset.mem_univ u
  rw [R.alpha_sum] at hle
  have halpha : P.alphaMass ≤ 1 := P.alphaMass_le_one (by omega)
  have hm0 : 0 ≤ ((universalVertices G).card : ℝ) := Nat.cast_nonneg _
  have hsource : d7HallAlphaSource G P ≤
      ((universalVertices G).card : ℝ) / 2 := by
    unfold d7HallAlphaSource
    nlinarith [P.alphaMass_nonneg (by omega)]
  have hchoose : ((universalVertices G).card : ℝ) / 2 ≤
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
    rw [Nat.cast_choose_two]
    have hmR : (4 : ℝ) ≤ ((universalVertices G).card : ℝ) := by
      exact_mod_cast hm
    nlinarith
  exact hle.trans (hsource.trans hchoose)

lemma d7SmallHallDeduction_le_one (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) :
    d7SmallHallDeduction G P sigma R u e ≤ 1 := by
  have hmR : (0 : ℝ) < ((universalVertices G).card : ℝ) := by
    positivity
  have hchooseR : (0 : ℝ) <
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ (universalVertices G).card)
  induction e using Sym2.inductionOn with
  | hf x y =>
      unfold d7SmallHallDeduction
      simp only [Sym2.lift_mk]
      by_cases hx : (x : A) ∈ universalVertices G <;>
        by_cases hy : (y : A) ∈ universalVertices G <;>
        simp only [hx, hy, dite_true, dite_false]
      · exact (div_le_one hchooseR).mpr
          (D7HallRedistribution.alphaFlow_le_choose_two G P sigma R hm u)
      · exact (div_le_one hmR).mpr
          (D7HallRedistribution.betaFlow_le_m G P sigma R hm u _)
      · exact (div_le_one hmR).mpr
          (D7HallRedistribution.betaFlow_le_m G P sigma R hm u _)
      · norm_num

/-- The complete-graph capacity used for the weighted induction on `G-u`.
Nonedges of `G-u` have capacity zero. -/
def d7SmallDeletedCapacity (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) : ℝ :=
  if e ∈ (d7DeletedGraph G (u : A)).edgeFinset then
    1 - d7SmallHallDeduction G P sigma R u e
  else 0

lemma d7SmallDeletedCapacity_isEdgeCapacity (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    IsEdgeCapacity (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) := by
  constructor
  · intro e _heTop
    by_cases he : e ∈ (d7DeletedGraph G (u : A)).edgeFinset
    · rw [d7SmallDeletedCapacity, if_pos he]
      exact ⟨sub_nonneg.mpr (d7SmallHallDeduction_le_one G P sigma R hm u e),
        by linarith [d7SmallHallDeduction_nonneg G P sigma R hm u e]⟩
    · simp [d7SmallDeletedCapacity, he]
  · intro e heTop
    have hdiag : e.IsDiag := by
      induction e using Sym2.inductionOn with
      | hf x y =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.top_adj, Sym2.mk_isDiag_iff] at heTop ⊢
          exact not_ne_iff.mp heTop
    rw [d7SmallDeletedCapacity, if_neg]
    intro he
    exact (d7DeletedGraph G (u : A)).not_isDiag_of_mem_edgeFinset he hdiag

lemma d7SmallDeletedCapacity_support (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G)) (e : Sym2 (↑(d7DeletedFinset (u : A))))
    (he : e ∉ (d7DeletedGraph G (u : A)).edgeSet) :
    d7SmallDeletedCapacity G P sigma R u e = 0 := by
  rw [d7SmallDeletedCapacity, if_neg]
  simpa only [SimpleGraph.mem_edgeFinset] using he

/-- A universal vertex, regarded as a vertex of the graph obtained by
deleting the nonuniversal vertex `u`. -/
def d7SmallUniversalDeletedEmbedding (G : SimpleGraph A)
    (u : ↑(nonUniversalVertices G)) :
    ↑(universalVertices G) ↪ ↑(d7DeletedFinset (u : A)) where
  toFun z := d7DeletedVertex (u : A) (z : A) (by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property))
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun q : ↑(d7DeletedFinset (u : A)) ↦ (q : A)) h

@[simp] lemma d7SmallUniversalDeletedEmbedding_val (G : SimpleGraph A)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    (d7SmallUniversalDeletedEmbedding G u z : A) = (z : A) := rfl

/-- A nonuniversal vertex distinct from the deleted vertex, regarded in the
deleted subtype. -/
def d7SmallNonUniversalDeletedVertex (G : SimpleGraph A)
    (u v : ↑(nonUniversalVertices G)) (hvu : v ≠ u) :
    ↑(d7DeletedFinset (u : A)) :=
  d7DeletedVertex (u : A) (v : A) (by
    intro h
    exact hvu (Subtype.ext h))

@[simp] lemma d7SmallNonUniversalDeletedVertex_val (G : SimpleGraph A)
    (u v : ↑(nonUniversalVertices G)) (hvu : v ≠ u) :
    (d7SmallNonUniversalDeletedVertex G u v hvu : A) = (v : A) := rfl

/-- The Hall deduction written as an explicit sum of delta masses on the
mixed and universal edges of the deleted complete graph. -/
def d7SmallHallDeductionExpanded (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) : ℝ :=
  (∑ v : ↑(nonUniversalVertices G),
    if hvu : v ≠ u then
      ∑ z : ↑(universalVertices G),
        if e = s(d7SmallNonUniversalDeletedVertex G u v hvu,
            d7SmallUniversalDeletedEmbedding G u z) then
          R.betaFlow u v / ((universalVertices G).card : ℝ)
        else 0
    else 0) +
  ∑ q : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset),
    if e = (d7SmallUniversalDeletedEmbedding G u).sym2Map q then
      R.alphaFlow u /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ)
    else 0

private lemma sum_top_edgeFinset_ite_eq {B : Type} [Fintype B]
    [DecidableEq B] (e₀ : Sym2 B) (he₀ : ¬e₀.IsDiag) (r : ℝ) :
    ∑ e ∈ (⊤ : SimpleGraph B).edgeFinset,
      (if e = e₀ then r else 0) = r := by
  calc
    (∑ e ∈ (⊤ : SimpleGraph B).edgeFinset,
        (if e = e₀ then r else 0)) = (if e₀ = e₀ then r else 0) := by
      apply Finset.sum_eq_single e₀
      · intro b _hb hne
        rw [if_neg hne]
      · intro he
        exfalso
        apply he
        induction e₀ using Sym2.inductionOn with
        | hf x y =>
            simp only [Sym2.mk_isDiag_iff] at he₀
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.top_adj]
            exact he₀
    _ = r := by rw [if_pos rfl]

lemma sum_d7SmallHallDeductionExpanded (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
      d7SmallHallDeductionExpanded G P sigma R u e) =
      (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u := by
  have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by
    positivity
  have hchooseR :
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.choose_pos (by omega : 2 ≤ (universalVertices G).card)))
  unfold d7SmallHallDeductionExpanded
  rw [Finset.sum_add_distrib]
  have hmixed :
      (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        ∑ v : ↑(nonUniversalVertices G),
          if hvu : v ≠ u then
            ∑ z : ↑(universalVertices G),
              if e = s(d7SmallNonUniversalDeletedVertex G u v hvu,
                  d7SmallUniversalDeletedEmbedding G u z) then
                R.betaFlow u v / ((universalVertices G).card : ℝ)
              else 0
          else 0) =
        ∑ v : ↑(nonUniversalVertices G), R.betaFlow u v := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro v
    by_cases hvu : v ≠ u
    · simp only [dif_pos hvu]
      rw [Finset.sum_comm]
      calc
        (∑ z : ↑(universalVertices G),
            ∑ e ∈ (⊤ : SimpleGraph
              (↑(d7DeletedFinset (u : A)))).edgeFinset,
              if e = s(d7SmallNonUniversalDeletedVertex G u v hvu,
                  d7SmallUniversalDeletedEmbedding G u z) then
                R.betaFlow u v / ((universalVertices G).card : ℝ)
              else 0) =
            ∑ _z : ↑(universalVertices G),
              R.betaFlow u v / ((universalVertices G).card : ℝ) := by
          apply Fintype.sum_congr
          intro z
          apply sum_top_edgeFinset_ite_eq
          simp only [Sym2.mk_isDiag_iff]
          intro h
          have hval := congrArg
            (fun x : ↑(d7DeletedFinset (u : A)) ↦ (x : A)) h
          exact nonUniversalVertex_not_mem_universalVertices G v.property
            (hval ▸ z.property)
        _ = R.betaFlow u v := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
            nsmul_eq_mul]
          field_simp
    · have hvuEq : v = u := not_ne_iff.mp hvu
      subst v
      rw [R.diagonal_zero]
      apply Finset.sum_eq_zero
      intro e he
      rw [dif_neg (by simp)]
  rw [hmixed]
  congr 1
  rw [Finset.sum_comm]
  calc
    (∑ q : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset),
        ∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          if e = (d7SmallUniversalDeletedEmbedding G u).sym2Map q then
            R.alphaFlow u /
              (((universalVertices G).card.choose 2 : ℕ) : ℝ)
          else 0) =
        ∑ _q : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset),
          R.alphaFlow u /
            (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
      apply Fintype.sum_congr
      intro q
      apply sum_top_edgeFinset_ite_eq
      exact (Sym2.isDiag_map (d7SmallUniversalDeletedEmbedding G u).injective).not.mpr
        ((⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset
          q.property)
    _ = R.alphaFlow u := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
        nsmul_eq_mul]
      field_simp

private lemma d7SmallMixedEdge_injective (G : SimpleGraph A)
    (u v v' : ↑(nonUniversalVertices G)) (hvu : v ≠ u) (hv'u : v' ≠ u)
    (z z' : ↑(universalVertices G))
    (h : s(d7SmallNonUniversalDeletedVertex G u v hvu,
          d7SmallUniversalDeletedEmbedding G u z) =
        s(d7SmallNonUniversalDeletedVertex G u v' hv'u,
          d7SmallUniversalDeletedEmbedding G u z')) :
    v = v' ∧ z = z' := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · constructor
    · apply Subtype.ext
      exact congrArg
        (fun x : ↑(d7DeletedFinset (u : A)) ↦ (x : A)) h.1
    · apply Subtype.ext
      exact congrArg
        (fun x : ↑(d7DeletedFinset (u : A)) ↦ (x : A)) h.2
  · exfalso
    have hval := congrArg
      (fun x : ↑(d7DeletedFinset (u : A)) ↦ (x : A)) h.1
    exact nonUniversalVertex_not_mem_universalVertices G v.property
      (hval ▸ z'.property)

private lemma d7SmallMixedEdge_ne_universalEdge (G : SimpleGraph A)
    (u v : ↑(nonUniversalVertices G)) (hvu : v ≠ u)
    (z : ↑(universalVertices G))
    (q : Sym2 (↑(universalVertices G))) :
    s(d7SmallNonUniversalDeletedVertex G u v hvu,
        d7SmallUniversalDeletedEmbedding G u z) ≠
      (d7SmallUniversalDeletedEmbedding G u).sym2Map q := by
  induction q using Sym2.inductionOn with
  | hf x y =>
      change s(d7SmallNonUniversalDeletedVertex G u v hvu,
          d7SmallUniversalDeletedEmbedding G u z) ≠
        s(d7SmallUniversalDeletedEmbedding G u x,
          d7SmallUniversalDeletedEmbedding G u y)
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · have hval := congrArg
          (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.1
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (hval ▸ x.property)
      · have hval := congrArg
          (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.1
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (hval ▸ y.property)

private lemma d7SmallNonUniversalEdge_ne_mixedEdge (G : SimpleGraph A)
    (u v w v' : ↑(nonUniversalVertices G))
    (hvu : v ≠ u) (hwu : w ≠ u) (hv'u : v' ≠ u)
    (z : ↑(universalVertices G)) :
    s(d7SmallNonUniversalDeletedVertex G u v hvu,
        d7SmallNonUniversalDeletedVertex G u w hwu) ≠
      s(d7SmallNonUniversalDeletedVertex G u v' hv'u,
        d7SmallUniversalDeletedEmbedding G u z) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hval := congrArg
      (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.2
    exact nonUniversalVertex_not_mem_universalVertices G w.property
      (hval ▸ z.property)
  · have hval := congrArg
      (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.1
    exact nonUniversalVertex_not_mem_universalVertices G v.property
      (hval ▸ z.property)

private lemma d7SmallNonUniversalEdge_ne_universalEdge (G : SimpleGraph A)
    (u v w : ↑(nonUniversalVertices G)) (hvu : v ≠ u) (hwu : w ≠ u)
    (q : Sym2 (↑(universalVertices G))) :
    s(d7SmallNonUniversalDeletedVertex G u v hvu,
        d7SmallNonUniversalDeletedVertex G u w hwu) ≠
      (d7SmallUniversalDeletedEmbedding G u).sym2Map q := by
  induction q using Sym2.inductionOn with
  | hf x y =>
      change s(d7SmallNonUniversalDeletedVertex G u v hvu,
          d7SmallNonUniversalDeletedVertex G u w hwu) ≠
        s(d7SmallUniversalDeletedEmbedding G u x,
          d7SmallUniversalDeletedEmbedding G u y)
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · have hval := congrArg
          (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.1
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (hval ▸ x.property)
      · have hval := congrArg
          (fun a : ↑(d7DeletedFinset (u : A)) ↦ (a : A)) h.1
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (hval ▸ y.property)

private lemma d7SmallHallDeductionExpanded_mixed (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u v : ↑(nonUniversalVertices G)) (hvu : v ≠ u)
    (z : ↑(universalVertices G)) :
    d7SmallHallDeductionExpanded G P sigma R u
      s(d7SmallNonUniversalDeletedVertex G u v hvu,
        d7SmallUniversalDeletedEmbedding G u z) =
      R.betaFlow u v / ((universalVertices G).card : ℝ) := by
  unfold d7SmallHallDeductionExpanded
  have hmixed :
      (∑ v' : ↑(nonUniversalVertices G),
        if hv'u : v' ≠ u then
          ∑ z' : ↑(universalVertices G),
            if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                  d7SmallUniversalDeletedEmbedding G u z) =
                s(d7SmallNonUniversalDeletedVertex G u v' hv'u,
                  d7SmallUniversalDeletedEmbedding G u z') then
              R.betaFlow u v' / ((universalVertices G).card : ℝ)
            else 0
        else 0) =
      R.betaFlow u v / ((universalVertices G).card : ℝ) := by
    calc
      (∑ v' : ↑(nonUniversalVertices G),
          if hv'u : v' ≠ u then
            ∑ z' : ↑(universalVertices G),
              if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z) =
                  s(d7SmallNonUniversalDeletedVertex G u v' hv'u,
                    d7SmallUniversalDeletedEmbedding G u z') then
                R.betaFlow u v' / ((universalVertices G).card : ℝ)
              else 0
          else 0) =
          (if hvv : v ≠ u then
            ∑ z' : ↑(universalVertices G),
              if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z) =
                  s(d7SmallNonUniversalDeletedVertex G u v hvv,
                    d7SmallUniversalDeletedEmbedding G u z') then
                R.betaFlow u v / ((universalVertices G).card : ℝ)
              else 0
          else 0) := by
            apply Fintype.sum_eq_single v
            intro v' hv'
            by_cases hv'u : v' ≠ u
            · simp only [dif_pos hv'u]
              apply Fintype.sum_eq_zero
              intro z'
              rw [if_neg]
              intro h
              exact hv' (d7SmallMixedEdge_injective G u v v'
                hvu hv'u z z' h).1.symm
            · rw [dif_neg hv'u]
      _ = R.betaFlow u v / ((universalVertices G).card : ℝ) := by
        rw [dif_pos hvu]
        calc
          (∑ z' : ↑(universalVertices G),
              if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z) =
                  s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z') then
                R.betaFlow u v / ((universalVertices G).card : ℝ)
              else 0) =
              (if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z) =
                  s(d7SmallNonUniversalDeletedVertex G u v hvu,
                    d7SmallUniversalDeletedEmbedding G u z) then
                R.betaFlow u v / ((universalVertices G).card : ℝ)
              else 0) := by
                apply Fintype.sum_eq_single z
                intro z' hz'
                rw [if_neg]
                intro h
                exact hz' (d7SmallMixedEdge_injective G u v v
                  hvu hvu z z' h).2.symm
          _ = R.betaFlow u v / ((universalVertices G).card : ℝ) := by
            rw [if_pos rfl]
  rw [hmixed]
  have huniversal :
      (∑ q : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset),
        if s(d7SmallNonUniversalDeletedVertex G u v hvu,
              d7SmallUniversalDeletedEmbedding G u z) =
            (d7SmallUniversalDeletedEmbedding G u).sym2Map q then
          R.alphaFlow u /
            (((universalVertices G).card.choose 2 : ℕ) : ℝ)
        else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro q
    rw [if_neg]
    exact d7SmallMixedEdge_ne_universalEdge G u v hvu z q
  rw [huniversal, add_zero]

private lemma d7SmallHallDeductionExpanded_universal (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G))
    (q : Sym2 (↑(universalVertices G)))
    (hq : q ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    d7SmallHallDeductionExpanded G P sigma R u
      ((d7SmallUniversalDeletedEmbedding G u).sym2Map q) =
      R.alphaFlow u /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
  unfold d7SmallHallDeductionExpanded
  have hmixed :
      (∑ v : ↑(nonUniversalVertices G),
        if hvu : v ≠ u then
          ∑ z : ↑(universalVertices G),
            if (d7SmallUniversalDeletedEmbedding G u).sym2Map q =
                s(d7SmallNonUniversalDeletedVertex G u v hvu,
                  d7SmallUniversalDeletedEmbedding G u z) then
              R.betaFlow u v / ((universalVertices G).card : ℝ)
            else 0
        else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro v
    by_cases hvu : v ≠ u
    · simp only [dif_pos hvu]
      apply Fintype.sum_eq_zero
      intro z
      rw [if_neg]
      exact (d7SmallMixedEdge_ne_universalEdge G u v hvu z q).symm
    · rw [dif_neg hvu]
  rw [hmixed, zero_add]
  let q' : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) := ⟨q, hq⟩
  calc
    (∑ r : ↑((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset),
        if (d7SmallUniversalDeletedEmbedding G u).sym2Map q =
            (d7SmallUniversalDeletedEmbedding G u).sym2Map r then
          R.alphaFlow u /
            (((universalVertices G).card.choose 2 : ℕ) : ℝ)
        else 0) =
        (if (d7SmallUniversalDeletedEmbedding G u).sym2Map q =
            (d7SmallUniversalDeletedEmbedding G u).sym2Map q' then
          R.alphaFlow u /
            (((universalVertices G).card.choose 2 : ℕ) : ℝ)
        else 0) := by
      apply Fintype.sum_eq_single q'
      intro r hr
      rw [if_neg]
      intro heq
      apply hr
      apply Subtype.ext
      exact ((d7SmallUniversalDeletedEmbedding G u).sym2Map.injective heq).symm
    _ = R.alphaFlow u /
          (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
      rw [if_pos]
      rfl

private lemma d7SmallHallDeductionExpanded_nonUniversal (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u v w : ↑(nonUniversalVertices G)) (hvu : v ≠ u) (hwu : w ≠ u) :
    d7SmallHallDeductionExpanded G P sigma R u
      s(d7SmallNonUniversalDeletedVertex G u v hvu,
        d7SmallNonUniversalDeletedVertex G u w hwu) = 0 := by
  unfold d7SmallHallDeductionExpanded
  have hmixed :
      (∑ v' : ↑(nonUniversalVertices G),
        if hv'u : v' ≠ u then
          ∑ z : ↑(universalVertices G),
            if s(d7SmallNonUniversalDeletedVertex G u v hvu,
                  d7SmallNonUniversalDeletedVertex G u w hwu) =
                s(d7SmallNonUniversalDeletedVertex G u v' hv'u,
                  d7SmallUniversalDeletedEmbedding G u z) then
              R.betaFlow u v' / ((universalVertices G).card : ℝ)
            else 0
        else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro v'
    by_cases hv'u : v' ≠ u
    · simp only [dif_pos hv'u]
      apply Fintype.sum_eq_zero
      intro z
      rw [if_neg]
      exact d7SmallNonUniversalEdge_ne_mixedEdge G u v w v'
        hvu hwu hv'u z
    · rw [dif_neg hv'u]
  rw [hmixed]
  rw [zero_add]
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  exact d7SmallNonUniversalEdge_ne_universalEdge G u v w hvu hwu q

lemma d7SmallHallDeductionExpanded_eq (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G))
    (e : Sym2 (↑(d7DeletedFinset (u : A)))) (heND : ¬e.IsDiag) :
    d7SmallHallDeductionExpanded G P sigma R u e =
      d7SmallHallDeduction G P sigma R u e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      simp only [Sym2.mk_isDiag_iff] at heND
      by_cases hx : (x : A) ∈ universalVertices G
      · let zx : ↑(universalVertices G) := ⟨(x : A), hx⟩
        by_cases hy : (y : A) ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨(y : A), hy⟩
          have hzxy : zx ≠ zy := by
            intro h
            apply heND
            apply Subtype.ext
            exact congrArg (fun z : ↑(universalVertices G) ↦ (z : A)) h
          have hq : s(zx, zy) ∈
              (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset := by
            simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.top_adj] using hzxy
          have hedge : s(x, y) =
              (d7SmallUniversalDeletedEmbedding G u).sym2Map s(zx, zy) := by
            change s(x, y) =
              s(d7SmallUniversalDeletedEmbedding G u zx,
                d7SmallUniversalDeletedEmbedding G u zy)
            congr 1 <;> apply Subtype.ext <;> rfl
          rw [hedge,
            d7SmallHallDeductionExpanded_universal G P sigma R u s(zx, zy) hq]
          change R.alphaFlow u /
              (((universalVertices G).card.choose 2 : ℕ) : ℝ) =
            d7SmallHallDeduction G P sigma R u
              s(d7SmallUniversalDeletedEmbedding G u zx,
                d7SmallUniversalDeletedEmbedding G u zy)
          unfold d7SmallHallDeduction
          simp only [Sym2.lift_mk]
          have hzx : (d7SmallUniversalDeletedEmbedding G u zx : A) ∈
              universalVertices G := by simpa using zx.property
          have hzy : (d7SmallUniversalDeletedEmbedding G u zy : A) ∈
              universalVertices G := by simpa using zy.property
          rw [dif_pos hzx, dif_pos hzy]
        · let vy : ↑(nonUniversalVertices G) :=
            ⟨(y : A),
              mem_nonUniversalVertices_of_not_mem_universalVertices G hy⟩
          have hyuA : (y : A) ≠ (u : A) := by
            simpa only [d7DeletedFinset, Finset.mem_erase,
              Finset.mem_univ, and_true] using y.property
          have hvu : vy ≠ u := by
            intro h
            exact hyuA (congrArg Subtype.val h)
          have hedge : s(x, y) =
              s(d7SmallNonUniversalDeletedVertex G u vy hvu,
                d7SmallUniversalDeletedEmbedding G u zx) := by
            rw [Sym2.eq_swap]
            congr 1 <;> apply Subtype.ext <;> rfl
          rw [hedge,
            d7SmallHallDeductionExpanded_mixed G P sigma R u vy hvu zx]
          unfold d7SmallHallDeduction
          simp only [Sym2.lift_mk]
          have hvy : (d7SmallNonUniversalDeletedVertex G u vy hvu : A) ∉
              universalVertices G := by
            simpa using nonUniversalVertex_not_mem_universalVertices G vy.property
          have hzx : (d7SmallUniversalDeletedEmbedding G u zx : A) ∈
              universalVertices G := by simpa using zx.property
          rw [dif_neg hvy, dif_pos hzx]
          congr 2
      · let vx : ↑(nonUniversalVertices G) :=
          ⟨(x : A),
            mem_nonUniversalVertices_of_not_mem_universalVertices G hx⟩
        have hxuA : (x : A) ≠ (u : A) := by
          simpa only [d7DeletedFinset, Finset.mem_erase,
            Finset.mem_univ, and_true] using x.property
        have hvu : vx ≠ u := by
          intro h
          exact hxuA (congrArg Subtype.val h)
        by_cases hy : (y : A) ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨(y : A), hy⟩
          have hedge : s(x, y) =
              s(d7SmallNonUniversalDeletedVertex G u vx hvu,
                d7SmallUniversalDeletedEmbedding G u zy) := by
            congr 1 <;> apply Subtype.ext <;> rfl
          rw [hedge,
            d7SmallHallDeductionExpanded_mixed G P sigma R u vx hvu zy]
          unfold d7SmallHallDeduction
          simp only [Sym2.lift_mk]
          have hvx : (d7SmallNonUniversalDeletedVertex G u vx hvu : A) ∉
              universalVertices G := by
            simpa using nonUniversalVertex_not_mem_universalVertices G vx.property
          have hzy : (d7SmallUniversalDeletedEmbedding G u zy : A) ∈
              universalVertices G := by simpa using zy.property
          rw [dif_neg hvx, dif_pos hzy]
          congr 2
        · let vy : ↑(nonUniversalVertices G) :=
            ⟨(y : A),
              mem_nonUniversalVertices_of_not_mem_universalVertices G hy⟩
          have hyuA : (y : A) ≠ (u : A) := by
            simpa only [d7DeletedFinset, Finset.mem_erase,
              Finset.mem_univ, and_true] using y.property
          have hwu : vy ≠ u := by
            intro h
            exact hyuA (congrArg Subtype.val h)
          have hedge : s(x, y) =
              s(d7SmallNonUniversalDeletedVertex G u vx hvu,
                d7SmallNonUniversalDeletedVertex G u vy hwu) := by
            congr 1 <;> apply Subtype.ext <;> rfl
          rw [hedge,
            d7SmallHallDeductionExpanded_nonUniversal G P sigma R u
              vx vy hvu hwu]
          unfold d7SmallHallDeduction
          simp only [Sym2.lift_mk]
          have hvx : (d7SmallNonUniversalDeletedVertex G u vx hvu : A) ∉
              universalVertices G := by
            simpa using nonUniversalVertex_not_mem_universalVertices G vx.property
          have hvy : (d7SmallNonUniversalDeletedVertex G u vy hwu : A) ∉
              universalVertices G := by
            simpa using nonUniversalVertex_not_mem_universalVertices G vy.property
          rw [dif_neg hvx, dif_neg hvy]

lemma sum_d7SmallHallDeduction (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
      d7SmallHallDeduction G P sigma R u e) =
      (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u := by
  rw [← sum_d7SmallHallDeductionExpanded G P sigma R hm u]
  apply Finset.sum_congr rfl
  intro e he
  exact (d7SmallHallDeductionExpanded_eq G P sigma R u e
    ((⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).not_isDiag_of_mem_edgeFinset he)).symm

private lemma filter_topEdgeFinset_graph_eq {B : Type} [Fintype B]
    [DecidableEq B] (H : SimpleGraph B) :
    (⊤ : SimpleGraph B).edgeFinset.filter (fun e ↦ e ∈ H.edgeFinset) =
      H.edgeFinset := by
  apply Finset.Subset.antisymm
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he
    apply Finset.mem_filter.mpr
    exact ⟨SimpleGraph.edgeFinset_mono le_top he, he⟩

private lemma filter_topEdgeFinset_not_graph_eq {B : Type} [Fintype B]
    [DecidableEq B] (H : SimpleGraph B) :
    (⊤ : SimpleGraph B).edgeFinset.filter (fun e ↦ e ∉ H.edgeFinset) =
      Hᶜ.edgeFinset := by
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf x y => simp [SimpleGraph.compl_adj]

lemma capacityMissingWeight_d7SmallDeletedCapacity (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d7SmallDeletedCapacity G P sigma R u) =
      (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
        ∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
          d7SmallHallDeduction G P sigma R u e := by
  let H := d7DeletedGraph G (u : A)
  let E := (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset
  unfold capacityMissingWeight
  rw [← Finset.sum_filter_add_sum_filter_not E
    (fun e ↦ e ∈ H.edgeFinset)]
  change
    (∑ e ∈ E.filter (fun e ↦ e ∈ H.edgeFinset),
        (1 - d7SmallDeletedCapacity G P sigma R u e)) +
      (∑ e ∈ E.filter (fun e ↦ e ∉ H.edgeFinset),
        (1 - d7SmallDeletedCapacity G P sigma R u e)) = _
  rw [show E.filter (fun e ↦ e ∈ H.edgeFinset) = H.edgeFinset by
        simpa only [E] using filter_topEdgeFinset_graph_eq H,
      show E.filter (fun e ↦ e ∉ H.edgeFinset) = Hᶜ.edgeFinset by
        simpa only [E] using filter_topEdgeFinset_not_graph_eq H]
  have hedge :
      (∑ e ∈ H.edgeFinset,
        (1 - d7SmallDeletedCapacity G P sigma R u e)) =
        ∑ e ∈ H.edgeFinset, d7SmallHallDeduction G P sigma R u e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [d7SmallDeletedCapacity, if_pos]
    · ring
    · simpa only [H] using he
  have hnonedge :
      (∑ e ∈ Hᶜ.edgeFinset,
        (1 - d7SmallDeletedCapacity G P sigma R u e)) =
        (Hᶜ.edgeFinset.card : ℝ) := by
    calc
      (∑ e ∈ Hᶜ.edgeFinset,
          (1 - d7SmallDeletedCapacity G P sigma R u e)) =
          ∑ _e ∈ Hᶜ.edgeFinset, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [d7SmallDeletedCapacity, if_neg]
            · ring
            · intro heH
              induction e using Sym2.inductionOn with
              | hf x y =>
                  simp only [SimpleGraph.mem_edgeFinset,
                    SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at he
                  exact he.2 (SimpleGraph.mem_edgeFinset.mp heH)
      _ = (Hᶜ.edgeFinset.card : ℝ) := by simp
  rw [hedge, hnonedge]
  change _ + (Hᶜ.edgeFinset.card : ℝ) =
    (Hᶜ.edgeFinset.card : ℝ) + _
  exact add_comm _ _

lemma capacityMissingWeight_d7SmallDeletedCapacity_le (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d7SmallDeletedCapacity G P sigma R u) ≤
      (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
        d7HallCapacity G sigma u := by
  rw [capacityMissingWeight_d7SmallDeletedCapacity]
  refine add_le_add_right (α := ℝ) ?_ _
  calc
    (∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
        d7SmallHallDeduction G P sigma R u e) ≤
        ∑ e ∈ (⊤ : SimpleGraph
          (↑(d7DeletedFinset (u : A)))).edgeFinset,
          d7SmallHallDeduction G P sigma R u e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact SimpleGraph.edgeFinset_mono le_top
      · intro e _heTop _heNot
        exact d7SmallHallDeduction_nonneg G P sigma R hm u e
    _ = (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
          R.alphaFlow u := sum_d7SmallHallDeduction G P sigma R hm u
    _ ≤ d7HallCapacity G sigma u := R.target_le u

lemma capacityMissingWeight_d7SmallDeletedCapacity_inductionBound
    {n a : ℕ} (hcard : Fintype.card A = n) (hn : 14 ≤ n)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (hsigma : ∀ v, sigma v ≤ d7ResidualAllowance G a v)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    capacityMissingWeight (d7SmallDeletedCapacity G P sigma R u) ≤
      ((n - 1) - 4 + (a - sigma u) : ℕ) := by
  have hdegreePos : 0 < Gᶜ.degree (u : A) :=
    mem_nonUniversalVertices.mp u.property
  have hsigmaA : sigma u ≤ a :=
    (hsigma u).trans (Nat.min_le_left _ _)
  have hsigmaDegree : sigma u + 1 ≤ Gᶜ.degree (u : A) := by
    have h := (hsigma u).trans (Nat.min_le_right _ _)
    omega
  have hmissingExact : missingEdgeCount (d7DeletedGraph G (u : A)) =
      missingEdgeCount G - Gᶜ.degree (u : A) := by
    change missingEdgeCount
      (G.induce (↑((Finset.univ : Finset A).erase (u : A)) : Set A)) = _
    exact missingEdgeCount_induce_univ_erase G (u : A)
  have hdegreeLe : Gᶜ.degree (u : A) ≤ missingEdgeCount G := by
    simpa only [missingEdgeCount, Nat.card_eq_fintype_card,
      SimpleGraph.card_edgeSet] using
      (Gᶜ.degree_le_card_edgeFinset (v := (u : A)))
  have hnat : missingEdgeCount (d7DeletedGraph G (u : A)) +
      (Gᶜ.degree (u : A) - 1 - sigma u) =
        (n - 1) - 4 + (a - sigma u) := by
    rw [hmissingExact, hexact]
    omega
  calc
    capacityMissingWeight (d7SmallDeletedCapacity G P sigma R u) ≤
        (missingEdgeCount (d7DeletedGraph G (u : A)) : ℝ) +
          d7HallCapacity G sigma u :=
      capacityMissingWeight_d7SmallDeletedCapacity_le G P sigma R hm u
    _ = ((n - 1) - 4 + (a - sigma u) : ℕ) := by
      unfold d7HallCapacity
      exact_mod_cast hnat

/-- The weighted reduction on a nonuniversal vertex deletion, supported on
the actual deleted graph.  This is the packing to which the explicit Hall
capacity deductions will later be restored by the correction. -/
theorem exists_d7SmallSupportedWeightedPacking {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (hsigma : ∀ v, sigma v ≤ d7ResidualAllowance G a v)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hstrong : AlmostCompleteStrongAt (n - 1))
    (u : ↑(nonUniversalVertices G)) :
    ∃ w : Finset (↑(d7DeletedFinset (u : A))) → ℝ,
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d7SmallDeletedCapacity G P sigma R u) w ∧
      IsCapacityPacking (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
        (d7SmallDeletedCapacity G P sigma R u) w ∧
      capacityUncoveredWeight
          (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d7SmallDeletedCapacity G P sigma R u) w ≤
        ((a - sigma u : ℕ) : ℝ) ∧
      IsHalfBounded (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) w := by
  have horder : Fintype.card (↑(d7DeletedFinset (u : A))) = n - 1 := by
    unfold d7DeletedFinset
    rw [card_univ_erase, hcard]
  have hdefect : a - sigma u ≤ 4 := by omega
  obtain ⟨w, hw, hunc, hhalf⟩ := weightedPacking_of_strongAt
    hstrong horder hdefect (d7SmallDeletedCapacity G P sigma R u)
      (d7SmallDeletedCapacity_isEdgeCapacity G P sigma R hm u)
      (capacityMissingWeight_d7SmallDeletedCapacity_inductionBound
        hcard hn G hexact P sigma hsigma R hm u)
  let H := d7DeletedGraph G (u : A)
  let v := zeroExtendTriangleWeight H w
  have hsupport : ∀ e, e ∉ H.edgeSet →
      d7SmallDeletedCapacity G P sigma R u e = 0 := by
    intro e he
    exact d7SmallDeletedCapacity_support G P sigma R u e (by
      simpa only [H] using he)
  have hvTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) v := by
    constructor
    · intro t htTop
      dsimp only [v]
      by_cases htH : t ∈ H.cliqueFinset 3
      · rw [zeroExtendTriangleWeight_of_mem htH]
        exact hw.1 t htTop
      · rw [zeroExtendTriangleWeight_of_not_mem htH]
    · intro e heTop
      dsimp only [v]
      rw [fractionalEdgeLoad_zeroExtend_eq_of_capacity_support hw hsupport]
      exact hw.2 e heTop
  refine ⟨v, hw.zeroExtend_support hsupport, hvTop, ?_, ?_⟩
  · rw [show capacityUncoveredWeight
        (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d7SmallDeletedCapacity G P sigma R u) v =
        capacityUncoveredWeight
        (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d7SmallDeletedCapacity G P sigma R u) w by
      exact capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
        hw hsupport]
    exact hunc
  · intro t htTop
    dsimp only [v]
    by_cases htH : t ∈ H.cliqueFinset 3
    · rw [zeroExtendTriangleWeight_of_mem htH]
      exact hhalf t htTop
    · rw [zeroExtendTriangleWeight_of_not_mem htH]
      norm_num

/-! ## Aggregate loads of the Hall-adjusted deletion packings -/

private lemma d7SmallLiftedWeight_nonUniversal_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (d v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (x : A)) ≤
      if d = v ∨ d = x then 0 else 1 := by
  by_cases hd : d = v ∨ d = x
  · rw [if_pos hd]
    rcases hd with hdv | hdx
    · subst d
      exact le_of_eq (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
        G (v : A) (x : A) (w v))
    · subst d
      simpa only [Sym2.eq_swap] using le_of_eq
        (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (x : A) (v : A) (w x))
  · rw [if_neg hd]
    have hvd : (v : A) ≠ (d : A) := by
      intro h
      exact hd (Or.inl (Subtype.ext h.symm))
    have hxd : (x : A) ≠ (d : A) := by
      intro h
      exact hd (Or.inr (Subtype.ext h.symm))
    rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
      (v : A) (x : A) (w d) hvd hxd]
    have heDel : s(d7DeletedVertex (d : A) (v : A) hvd,
        d7DeletedVertex (d : A) (x : A) hxd) ∈
        (d7DeletedGraph G (d : A)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change G.Adj (v : A) (x : A)
      exact SimpleGraph.mem_edgeFinset.mp he
    calc
      fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) _ ≤
          d7SmallDeletedCapacity G P sigma R d _ := (hw d).2 _ heDel
      _ ≤ 1 := by
        rw [d7SmallDeletedCapacity, if_pos heDel]
        exact sub_le_self 1 (d7SmallHallDeduction_nonneg G P sigma R hm d _)

lemma sum_d7SmallLiftedWeight_nonUniversal_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (x : A))) ≤
      ((nonUniversalVertices G).card : ℝ) - 2 := by
  calc
    (∑ d : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
          s((v : A), (x : A))) ≤
        ∑ d : ↑(nonUniversalVertices G),
          if d = v ∨ d = x then 0 else 1 := by
      apply Finset.sum_le_sum
      intro d _
      exact d7SmallLiftedWeight_nonUniversal_le G P sigma R hm w hw
        d v x hvx he
    _ = ((nonUniversalVertices G).card : ℝ) - 2 := by
      rw [sum_ite_eq_zero_else_two v x hvx]
      simp only [Fintype.card_coe]
      ring

private lemma d7SmallLiftedWeight_mixed_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (d v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (z : A)) ≤
      if d = v then 0 else
        1 - R.betaFlow d v / ((universalVertices G).card : ℝ) := by
  by_cases hd : d = v
  · subst d
    rw [if_pos rfl]
    exact le_of_eq (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
      G (v : A) (z : A) (w v))
  · rw [if_neg hd]
    have hvd : (v : A) ≠ (d : A) := by
      intro h
      exact hd (Subtype.ext h.symm)
    have hzd : (z : A) ≠ (d : A) := by
      intro h
      exact nonUniversalVertex_not_mem_universalVertices G d.property
        (h ▸ z.property)
    rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
      (v : A) (z : A) (w d) hvd hzd]
    let e : Sym2 (↑(d7DeletedFinset (d : A))) :=
      s(d7DeletedVertex (d : A) (v : A) hvd,
        d7DeletedVertex (d : A) (z : A) hzd)
    have he : e ∈ (d7DeletedGraph G (d : A)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change G.Adj (v : A) (z : A)
      exact (adj_of_mem_universalVertices G z.property (by
        intro h
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (h ▸ z.property))).symm
    calc
      fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) e ≤
          d7SmallDeletedCapacity G P sigma R d e := (hw d).2 e he
      _ = 1 - R.betaFlow d v /
          ((universalVertices G).card : ℝ) := by
        rw [d7SmallDeletedCapacity, if_pos he]
        unfold d7SmallHallDeduction
        simp only [e, Sym2.lift_mk]
        have hvNZ : (d7DeletedVertex (d : A) (v : A) hvd : A) ∉
            universalVertices G := by
          simpa using nonUniversalVertex_not_mem_universalVertices G v.property
        have hzZ : (d7DeletedVertex (d : A) (z : A) hzd : A) ∈
            universalVertices G := by simpa using z.property
        rw [dif_neg hvNZ, dif_pos hzZ]
        congr 2

lemma sum_d7SmallLiftedWeight_mixed_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((v : A), (z : A))) ≤
      ((nonUniversalVertices G).card : ℝ) - 1 - P.betaIncident v := by
  have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by positivity
  calc
    (∑ d : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
          s((v : A), (z : A))) ≤
        ∑ d : ↑(nonUniversalVertices G),
          if d = v then 0 else
            1 - R.betaFlow d v /
              ((universalVertices G).card : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact d7SmallLiftedWeight_mixed_le G P sigma R w hw d v z
    _ = ((nonUniversalVertices G).card : ℝ) - 1 - P.betaIncident v := by
      have hpoint : ∀ d : ↑(nonUniversalVertices G),
          (if d = v then 0 else
            1 - R.betaFlow d v /
              ((universalVertices G).card : ℝ)) =
          (if d = v then 0 else 1) -
            R.betaFlow d v / ((universalVertices G).card : ℝ) := by
        intro d
        by_cases hd : d = v
        · subst d
          simp [R.diagonal_zero]
        · simp [hd]
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib, sum_ite_eq_zero_else,
        ← Finset.sum_div, R.beta_source_sum]
      unfold d7HallBetaSource
      simp only [Fintype.card_coe]
      field_simp

private lemma d7SmallLiftedWeight_universal_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (d : ↑(nonUniversalVertices G)) (x y : ↑(universalVertices G))
    (hxy : x ≠ y) :
    fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((x : A), (y : A)) ≤
      1 - R.alphaFlow d /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
  have hxd : (x : A) ≠ (d : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G d.property
      (h ▸ x.property)
  have hyd : (y : A) ≠ (d : A) := by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G d.property
      (h ▸ y.property)
  rw [fractionalEdgeLoad_d7LiftedWeight_of_ne G (d : A)
    (x : A) (y : A) (w d) hxd hyd]
  let e : Sym2 (↑(d7DeletedFinset (d : A))) :=
    s(d7DeletedVertex (d : A) (x : A) hxd,
      d7DeletedVertex (d : A) (y : A) hyd)
  have he : e ∈ (d7DeletedGraph G (d : A)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change G.Adj (x : A) (y : A)
    exact adj_of_mem_universalVertices G x.property
      (fun h ↦ hxy (Subtype.ext h))
  calc
    fractionalEdgeLoad (d7DeletedGraph G (d : A)) (w d) e ≤
        d7SmallDeletedCapacity G P sigma R d e := (hw d).2 e he
    _ = 1 - R.alphaFlow d /
        (((universalVertices G).card.choose 2 : ℕ) : ℝ) := by
      rw [d7SmallDeletedCapacity, if_pos he]
      unfold d7SmallHallDeduction
      simp only [e, Sym2.lift_mk]
      have hxZ : (d7DeletedVertex (d : A) (x : A) hxd : A) ∈
          universalVertices G := by simpa using x.property
      have hyZ : (d7DeletedVertex (d : A) (y : A) hyd : A) ∈
          universalVertices G := by simpa using y.property
      rw [dif_pos hxZ, dif_pos hyZ]

lemma sum_d7SmallLiftedWeight_universal_le
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ d : ↑(nonUniversalVertices G),
      fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
        s((x : A), (y : A))) ≤
      ((nonUniversalVertices G).card : ℝ) -
        ∑ v : ↑(nonUniversalVertices G), P.alpha v := by
  have hchooseR :
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.choose_pos (by omega : 2 ≤ (universalVertices G).card)))
  calc
    (∑ d : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (d : A) (w d))
          s((x : A), (y : A))) ≤
        ∑ d : ↑(nonUniversalVertices G),
          (1 - R.alphaFlow d /
            (((universalVertices G).card.choose 2 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact d7SmallLiftedWeight_universal_le G P sigma R w hw d x y hxy
    _ = ((nonUniversalVertices G).card : ℝ) -
          ∑ v : ↑(nonUniversalVertices G), P.alpha v := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_one, ← Finset.sum_div, R.alpha_sum]
      unfold d7HallAlphaSource D7SeparatedParameters.alphaMass
      rw [Nat.cast_choose_two]
      have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by positivity
      have hm1R : ((universalVertices G).card : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
          exact_mod_cast (by omega : 1 < (universalVertices G).card)
        linarith
      field_simp

/-! ## The explicit small-branch correction -/

/-- The `UZZ` part of the correction in the small-universal-set branch.
Unlike the large-branch correction, its coefficient at `u` is the original
separated parameter `alpha u`. -/
def d7SmallUZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ ∑ u : ↑(nonUniversalVertices G),
    weightedAttachedEdgeWeight (universalVertices G) (u : A)
      ((⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset)
      (fun _ ↦ P.alpha u) t

lemma d7SmallUZZCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7SmallUZZCorrection G P t := by
  intro t ht
  unfold d7SmallUZZCorrection
  exact Finset.sum_nonneg fun u _ ↦
    weightedAttachedEdgeWeight_nonneg
      (fun _ _ ↦ P.alpha_nonneg u) t ht

lemma fractionalEdgeLoad_d7SmallUZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7SmallUZZCorrection G P) p =
      ∑ u : ↑(nonUniversalVertices G),
        ∑ e : ↑((⊤ : SimpleGraph
          (↑(universalVertices G))).edgeFinset),
          if p ∈ (attachedEdgeTriangle (universalVertices G) (u : A) e).sym2
          then P.alpha u else 0 := by
  unfold d7SmallUZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact fractionalEdgeLoad_weightedAttachedEdgeWeight
    (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩) p

lemma fractionalEdgeLoad_d7SmallUZZCorrection_induced
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d7SmallUZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  unfold d7SmallUZZCorrection
  rw [fractionalEdgeLoad_sum]
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  apply Fintype.sum_congr
  intro u
  rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_induced
    (G := G)
    (nonUniversalVertex_not_mem_universalVertices G u.property)
    (fun f hf ↦
      (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
    (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨f, hf⟩)
    heND,
    if_pos he]

lemma fractionalEdgeLoad_d7SmallUZZCorrection_mixed
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7SmallUZZCorrection G P) s((u : A), (z : A)) =
      (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  unfold d7SmallUZZCorrection
  rw [fractionalEdgeLoad_sum]
  rw [Fintype.sum_eq_single u]
  · rw [fractionalEdgeLoad_weightedAttachedEdgeWeight_star
      (G := G) (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨f, hf⟩) z]
    have hm : 1 ≤ (universalVertices G).card :=
      Finset.one_le_card.mpr ⟨z, z.property⟩
    rw [Finset.sum_const, card_top_edgeFinset_filter_mem]
    simp only [nsmul_eq_mul]
    rw [Fintype.card_coe, Nat.cast_sub hm, Nat.cast_one]
  · intro u' hu'
    rw [fractionalEdgeLoad_weightedAttachedEdgeWeight
      (fun f hf ↦ d7UZZTriangle_mem_cliqueFinset G u' ⟨f, hf⟩)]
    apply Fintype.sum_eq_zero
    intro e
    rw [if_neg]
    exact starEdge_not_mem_attachedEdgeTriangle_of_ne_attachment
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (nonUniversalVertex_not_mem_universalVertices G u'.property)
      (fun h ↦ hu' (Subtype.ext h.symm)) z e

lemma fractionalEdgeLoad_d7SmallUZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d7SmallUZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [Sym2.mk_isDiag_iff] at heND
      rw [fractionalEdgeLoad_d7SmallUZZCorrection]
      apply Fintype.sum_eq_zero
      intro x
      apply Fintype.sum_eq_zero
      intro f
      rw [if_neg]
      exact outsidePair_not_mem_attachedEdgeTriangle
        (nonUniversalVertex_not_mem_universalVertices G u.property)
        (nonUniversalVertex_not_mem_universalVertices G v.property)
        (fun h ↦ heND (Subtype.ext h)) f

/-- The `ZZZ` part of the correction in the small-universal-set branch,
with the original separated parameter `gamma`. -/
def d7SmallZZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ ∑ q : ↑((universalVertices G).powersetCard 3),
    singleTriangleWeight q P.gamma t

lemma d7SmallZZZCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7SmallZZZCorrection G P t := by
  intro t _
  unfold d7SmallZZZCorrection singleTriangleWeight
  exact Finset.sum_nonneg fun q _ ↦ by
    split_ifs
    · exact P.gamma_nonneg
    · exact le_rfl

lemma fractionalEdgeLoad_d7SmallZZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7SmallZZZCorrection G P) p =
      ∑ q : ↑((universalVertices G).powersetCard 3),
        if p ∈ (q : Finset A).sym2 then P.gamma else 0 := by
  unfold d7SmallZZZCorrection
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact fractionalEdgeLoad_singleTriangle
    (d7ZZZTriangle_mem_cliqueFinset G q) P.gamma p

lemma fractionalEdgeLoad_d7SmallZZZCorrection_induced
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G))) (heND : ¬e.IsDiag) :
    fractionalEdgeLoad G (d7SmallZZZCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  rw [fractionalEdgeLoad_d7SmallZZZCorrection]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        if (inducedEmbedding (universalVertices G)).sym2Map e ∈
          (q : Finset A).sym2 then P.gamma else 0) =
        ∑ q ∈ (universalVertices G).powersetCard 3,
          if (inducedEmbedding (universalVertices G)).sym2Map e ∈ q.sym2
          then P.gamma else 0 :=
      (Finset.sum_subtype ((universalVertices G).powersetCard 3)
        (fun _ ↦ Iff.rfl)
        (fun q ↦ if (inducedEmbedding
          (universalVertices G)).sym2Map e ∈ q.sym2
          then P.gamma else 0)).symm
    _ = ∑ q ∈ ((universalVertices G).powersetCard 3).filter
          (fun q ↦ (inducedEmbedding
            (universalVertices G)).sym2Map e ∈ q.sym2), P.gamma := by
      rw [Finset.sum_filter]
    _ = (((universalVertices G).card : ℝ) - 2) * P.gamma := by
      rw [Finset.sum_const,
        card_universal_triangles_through_induced_edge G e heND]
      simp only [nsmul_eq_mul]
      have hm : 2 ≤ (universalVertices G).card := by
        have hcard := Sym2.card_toFinset_of_not_isDiag e heND
        have hle := Finset.card_le_card (Finset.subset_univ e.toFinset)
        rw [hcard] at hle
        simpa only [Finset.card_univ, Fintype.card_coe] using hle
      rw [Nat.cast_sub hm, Nat.cast_ofNat]

lemma fractionalEdgeLoad_d7SmallZZZCorrection_nonUniversal_left
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (x : A) :
    fractionalEdgeLoad G (d7SmallZZZCorrection G P) s((u : A), x) = 0 := by
  rw [fractionalEdgeLoad_d7SmallZZZCorrection]
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  have hqsub := (Finset.mem_powersetCard.mp q.property).1
  have huq : (u : A) ∉ (q : Finset A) := by
    intro hu
    exact nonUniversalVertex_not_mem_universalVertices G u.property (hqsub hu)
  simpa only [Finset.mk_mem_sym2_iff, not_and_or] using
    (Or.inl huq : (u : A) ∉ (q : Finset A) ∨ x ∉ (q : Finset A))

lemma fractionalEdgeLoad_d7SmallZZZCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    fractionalEdgeLoad G (d7SmallZZZCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      exact fractionalEdgeLoad_d7SmallZZZCorrection_nonUniversal_left G P u v

/-- The complete explicit correction in the small-universal-set branch. -/
def d7SmallCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ d7UUZCorrection G P t + d7SmallUZZCorrection G P t +
    d7SmallZZZCorrection G P t

lemma d7SmallCorrection_nonneg (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ d7SmallCorrection G P t := by
  intro t ht
  exact add_nonneg (add_nonneg (d7UUZCorrection_nonneg G P t ht)
    (d7SmallUZZCorrection_nonneg G P t ht))
    (d7SmallZZZCorrection_nonneg G P t ht)

lemma fractionalEdgeLoad_d7SmallCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (p : Sym2 A) :
    fractionalEdgeLoad G (d7SmallCorrection G P) p =
      fractionalEdgeLoad G (d7UUZCorrection G P) p +
        fractionalEdgeLoad G (d7SmallUZZCorrection G P) p +
        fractionalEdgeLoad G (d7SmallZZZCorrection G P) p := by
  unfold d7SmallCorrection
  rw [fractionalEdgeLoad_add, fractionalEdgeLoad_add]

lemma fractionalEdgeLoad_d7SmallCorrection_nonUniversal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7SmallCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) * P.beta e := by
  rw [fractionalEdgeLoad_d7SmallCorrection,
    fractionalEdgeLoad_d7UUZCorrection_induced G P e he,
    fractionalEdgeLoad_d7SmallUZZCorrection_nonUniversal G P e
      ((G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset he),
    fractionalEdgeLoad_d7SmallZZZCorrection_nonUniversal G P e]
  ring

lemma fractionalEdgeLoad_d7SmallCorrection_mixed
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7SmallCorrection G P) s((u : A), (z : A)) =
      P.betaIncident u +
        (((universalVertices G).card : ℝ) - 1) * P.alpha u := by
  rw [fractionalEdgeLoad_d7SmallCorrection]
  have hUUZ := fractionalEdgeLoad_d7UUZCorrection_mixed G P z u
  rw [Sym2.eq_swap] at hUUZ
  rw [hUUZ, fractionalEdgeLoad_d7SmallUZZCorrection_mixed G P u z,
    fractionalEdgeLoad_d7SmallZZZCorrection_nonUniversal_left G P u z]
  ring

lemma fractionalEdgeLoad_d7SmallCorrection_universal
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (e : Sym2 (↑(universalVertices G)))
    (he : e ∈ (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset) :
    fractionalEdgeLoad G (d7SmallCorrection G P)
        ((inducedEmbedding (universalVertices G)).sym2Map e) =
      (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
        (((universalVertices G).card : ℝ) - 2) * P.gamma := by
  have heND : ¬e.IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset he
  rw [fractionalEdgeLoad_d7SmallCorrection,
    fractionalEdgeLoad_d7UUZCorrection_universal G P e heND,
    fractionalEdgeLoad_d7SmallUZZCorrection_induced G P e he,
    fractionalEdgeLoad_d7SmallZZZCorrection_induced G P e heND]
  ring

/-! ## The corrected average over all vertex deletions -/

/-- The small-`m` D7 numerator consists of the Hall-adjusted packings on
nonuniversal deletions, the coherent packings on universal deletions, and
the explicit `UUZ/UZZ/ZZZ` correction. -/
def d7SmallAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ) : Finset A → ℝ :=
  fun t ↦ (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
    ((∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) t) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) t) +
      d7SmallCorrection G P t)

lemma fractionalEdgeLoad_d7SmallAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ) (e : Sym2 A) :
    fractionalEdgeLoad G (d7SmallAverageWeight G z₀ w₀ P w) e =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
          (∑ z : ↑(universalVertices G),
            fractionalEdgeLoad G
              (d7LiftedWeight (z : A)
                (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) e) +
          fractionalEdgeLoad G (d7SmallCorrection G P) e) := by
  unfold d7SmallAverageWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_add,
    fractionalEdgeLoad_add, fractionalEdgeLoad_sum,
    fractionalEdgeLoad_sum]

private lemma d7SmallUniversalNumerator_nonUniversal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e)) +
      fractionalEdgeLoad G (d7SmallCorrection G P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) ≤
      ((universalVertices G).card : ℝ) := by
  rw [fractionalEdgeLoad_d7SmallCorrection_nonUniversal G P e he,
    ← fractionalEdgeLoad_d7LargeCorrection_nonUniversal G P e he,
    d7LargeCorrection_numerator_nonUniversal G z₀ w₀ P hreal e he]
  exact sub_le_self _ (Finset.sum_nonneg fun z _ ↦
    d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _)

private lemma d7SmallUniversalNumerator_mixed_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((u : A), (y : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((u : A), (y : A)) ≤
      ((universalVertices G).card : ℝ) - 1 + P.betaIncident u := by
  have hlarge := d7LargeCorrection_numerator_mixed G z₀ w₀ P hreal hm u y
  rw [fractionalEdgeLoad_d7LargeCorrection_mixed G P hm u y] at hlarge
  rw [fractionalEdgeLoad_d7SmallCorrection_mixed G P u y]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d7MixedRemainingResidual G z₀ w₀ u y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d7MixedRemainingResidual
    split
    · exact le_rfl
    · exact d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _
  linarith

private lemma d7SmallUniversalNumerator_universal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((x : A), (y : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((x : A), (y : A)) ≤
      ((universalVertices G).card : ℝ) - 2 +
        ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  have hlarge := d7LargeCorrection_numerator_universal
    G z₀ w₀ P hreal hm x y hxy
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have hlargeCorr := fractionalEdgeLoad_d7LargeCorrection_universal_simplified
    G P hm e he
  have hsmallCorr := fractionalEdgeLoad_d7SmallCorrection_universal G P e he
  change fractionalEdgeLoad G (d7LargeCorrection G P)
      s((x : A), (y : A)) =
        2 + (((universalVertices G).card : ℝ) - 2) * P.gamma at hlargeCorr
  change fractionalEdgeLoad G (d7SmallCorrection G P)
      s((x : A), (y : A)) =
        (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
          (((universalVertices G).card : ℝ) - 2) * P.gamma at hsmallCorr
  rw [hlargeCorr] at hlarge
  rw [hsmallCorr]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d7UniversalRemainingResidual G z₀ w₀ x y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d7UniversalRemainingResidual
    split
    · exact le_rfl
    · exact d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _
  linarith

lemma d7SmallAverageWeight_numerator_nonUniversal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (v x : ↑(nonUniversalVertices G)) (hvx : v ≠ x)
    (he : s(v, x) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((v : A), (x : A))) +
      (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((v : A), (x : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((v : A), (x : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d7SmallLiftedWeight_nonUniversal_le
    G P sigma R hm w hw v x hvx he
  let e : Sym2 (↑(nonUniversalVertices G)) := s(v, x)
  have hZ := d7SmallUniversalNumerator_nonUniversal_le
    G z₀ w₀ P hreal hwPacking hwOne e (by simpa only [e] using he)
  change (∑ z : ↑(universalVertices G),
      fractionalEdgeLoad G
        (d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
        s((v : A), (x : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((v : A), (x : A)) ≤
        ((universalVertices G).card : ℝ) at hZ
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hU2 : 2 ≤ (nonUniversalVertices G).card := by
    have hpair : ({v, x} : Finset (↑(nonUniversalVertices G))).card = 2 := by
      simp [hvx]
    have hle := Finset.card_le_card
      (Finset.subset_univ ({v, x} : Finset (↑(nonUniversalVertices G))))
    simpa only [hpair, Finset.card_univ, Fintype.card_coe] using hle
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

lemma d7SmallAverageWeight_numerator_mixed_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (v : ↑(nonUniversalVertices G)) (z : ↑(universalVertices G)) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((v : A), (z : A))) +
      (∑ y : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (y : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ y))
          s((v : A), (z : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((v : A), (z : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d7SmallLiftedWeight_mixed_le
    G P sigma R hm w hw v z
  have hZ := d7SmallUniversalNumerator_mixed_le
    G z₀ w₀ P hreal hm hwPacking hwOne v z
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

lemma d7SmallAverageWeight_numerator_universal_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u))
          s((x : A), (y : A))) +
      (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((x : A), (y : A))) +
      fractionalEdgeLoad G (d7SmallCorrection G P) s((x : A), (y : A)) ≤
      ((Fintype.card A - 2 : ℕ) : ℝ) := by
  have hU := sum_d7SmallLiftedWeight_universal_le
    G P sigma R hm w hw x y hxy
  have hZ := d7SmallUniversalNumerator_universal_le
    G z₀ w₀ P hreal hm hwPacking hwOne x y hxy
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hA2 : 2 ≤ Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub hA2, Nat.cast_ofNat]
  linarith

private lemma d7SmallAverageWeight_edgeLoad_le_one_of_numerator
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hcard : 2 < Fintype.card A) (e : Sym2 A)
    (hnum :
      (∑ u : ↑(nonUniversalVertices G),
          fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
        (∑ z : ↑(universalVertices G),
          fractionalEdgeLoad G
            (d7LiftedWeight (z : A)
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) e) +
        fractionalEdgeLoad G (d7SmallCorrection G P) e ≤
          ((Fintype.card A - 2 : ℕ) : ℝ)) :
    fractionalEdgeLoad G (d7SmallAverageWeight G z₀ w₀ P w) e ≤ 1 := by
  rw [fractionalEdgeLoad_d7SmallAverageWeight]
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  calc
    d⁻¹ * ((∑ u : ↑(nonUniversalVertices G),
        fractionalEdgeLoad G (d7LiftedWeight (u : A) (w u)) e) +
      (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) e) +
      fractionalEdgeLoad G (d7SmallCorrection G P) e) ≤ d⁻¹ * d :=
        mul_le_mul_of_nonneg_left (by simpa only [d] using hnum)
          (inv_nonneg.mpr hd.le)
    _ = 1 := by field_simp

lemma d7SmallAverageWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hw : ∀ u : ↑(nonUniversalVertices G),
      IsCapacityPacking (d7DeletedGraph G (u : A))
        (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) :
    IsFractionalPacking G (d7SmallAverageWeight G z₀ w₀ P w) := by
  have hcard : 2 < Fintype.card A := by
    have hparts := card_nonUniversalVertices_add_card_universalVertices G
    omega
  have hwFractional : ∀ u : ↑(nonUniversalVertices G),
      IsFractionalPacking (d7DeletedGraph G (u : A)) (w u) := by
    intro u
    refine ⟨(hw u).1, ?_⟩
    intro e he
    calc
      fractionalEdgeLoad (d7DeletedGraph G (u : A)) (w u) e ≤
          d7SmallDeletedCapacity G P sigma R u e := (hw u).2 e he
      _ ≤ 1 := by
        rw [d7SmallDeletedCapacity, if_pos he]
        exact sub_le_self 1 (d7SmallHallDeduction_nonneg G P sigma R hm u e)
  constructor
  · intro t ht
    unfold d7SmallAverageWeight
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact add_nonneg (add_nonneg
      (Finset.sum_nonneg fun u _ ↦ (hwFractional u).extendInduced.nonneg_on ht)
      (Finset.sum_nonneg fun z _ ↦ (hwPacking z).extendInduced.nonneg_on ht))
      (d7SmallCorrection_nonneg G P t ht)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := by
        have hnd := G.not_isDiag_of_mem_edgeFinset he
        simpa only [Sym2.mk_isDiag_iff] using hnd
      have nonUniversal_of_not_universal : ∀ {v : A},
          v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
        intro v hv
        apply mem_nonUniversalVertices.mpr
        have hvne : Gᶜ.degree v ≠ 0 := by
          intro hz
          exact hv (mem_universalVertices.mpr hz)
        exact Nat.pos_of_ne_zero hvne
      apply d7SmallAverageWeight_edgeLoad_le_one_of_numerator
        G z₀ w₀ P w hcard
      by_cases hxZ : x ∈ universalVertices G
      · let zx : ↑(universalVertices G) := ⟨x, hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          have hzxy : zx ≠ zy := fun h ↦ hxy (congrArg Subtype.val h)
          exact d7SmallAverageWeight_numerator_universal_le G z₀ w₀ P hreal
            hm sigma R w hw hwPacking hwOne zx zy hzxy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          rw [show s(x, y) = s(y, x) from Sym2.eq_swap]
          exact d7SmallAverageWeight_numerator_mixed_le G z₀ w₀ P hreal
            hm sigma R w hw hwPacking hwOne uy zx
      · let ux : ↑(nonUniversalVertices G) :=
          ⟨x, nonUniversal_of_not_universal hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          exact d7SmallAverageWeight_numerator_mixed_le G z₀ w₀ P hreal
            hm sigma R w hw hwPacking hwOne ux zy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          have huxy : ux ≠ uy := fun h ↦ hxy (congrArg Subtype.val h)
          have heU : s(ux, uy) ∈ (G.induce
              (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            change G.Adj x y
            exact SimpleGraph.mem_edgeFinset.mp he
          exact d7SmallAverageWeight_numerator_nonUniversal_le
            G z₀ w₀ P hreal hm sigma R w hw hwPacking hwOne ux uy huxy heU

/-! ## Global size and residual cancellation -/

lemma fractionalSize_d7SmallUZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7SmallUZZCorrection G P) =
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
  unfold fractionalSize d7SmallUZZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (universalVertices G) (u : A)
            (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
            (fun _ ↦ P.alpha u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          (((universalVertices G).card.choose 2 : ℕ) : ℝ) * P.alpha u := by
      apply Fintype.sum_congr
      intro u
      change fractionalSize G
        (weightedAttachedEdgeWeight (universalVertices G) (u : A)
          (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
          (fun _ ↦ P.alpha u)) = _
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩),
        Finset.sum_const, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp only [Fintype.card_coe, nsmul_eq_mul]
    _ = (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
      rw [Finset.mul_sum]

lemma fractionalSize_d7SmallZZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7SmallZZZCorrection G P) =
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) * P.gamma := by
  unfold fractionalSize d7SmallZZZCorrection singleTriangleWeight
  rw [Finset.sum_comm]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        ∑ t ∈ G.cliqueFinset 3,
          if t = (q : Finset A) then P.gamma else 0) =
        ∑ _q : ↑((universalVertices G).powersetCard 3), P.gamma := by
      apply Fintype.sum_congr
      intro q
      rw [Finset.sum_eq_single (q : Finset A)]
      · simp
      · intro t _ hne
        rw [if_neg hne]
      · intro hnot
        exact (hnot (d7ZZZTriangle_mem_cliqueFinset G q)).elim
    _ = (((universalVertices G).card.choose 3 : ℕ) : ℝ) * P.gamma := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, Finset.card_powersetCard]

lemma fractionalSize_d7SmallCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7SmallCorrection G P) =
      ((universalVertices G).card : ℝ) * P.betaMass +
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.alpha u +
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) * P.gamma := by
  unfold fractionalSize d7SmallCorrection
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (fractionalSize_d7UUZCorrection G P)
      (fractionalSize_d7SmallUZZCorrection G P))
    (fractionalSize_d7SmallZZZCorrection G P)

lemma three_mul_fractionalSize_d7SmallCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    3 * fractionalSize G (d7SmallCorrection G P) =
      ((universalVertices G).card : ℝ) +
        2 * ((universalVertices G).card : ℝ) * P.betaMass +
        ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
  rw [fractionalSize_d7SmallCorrection, Nat.cast_choose_two,
    cast_choose_three_d7]
  let m : ℝ := ((universalVertices G).card : ℝ)
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have halpha : alpha = (m - 1) *
      ∑ u : ↑(nonUniversalVertices G), P.alpha u := by
    rfl
  have hnorm : ((m - 1) * (m - 2) / 2) * P.gamma + alpha + beta = 1 := by
    simpa only [m, alpha, beta, D7SeparatedParameters.alphaMass,
      D7SeparatedParameters.betaMass] using P.normalization
  change 3 * (m * beta + (m * (m - 1) / 2) *
      (∑ u : ↑(nonUniversalVertices G), P.alpha u) +
      (m * (m - 1) * (m - 2) / 6) * P.gamma) =
    m + 2 * m * beta + m / 2 * alpha
  rw [halpha] at hnorm ⊢
  have hscaled := congrArg (fun x : ℝ ↦ m * x) hnorm
  ring_nf at hscaled ⊢
  linarith

lemma fractionalSize_d7SmallAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ) :
    fractionalSize G (d7SmallAverageWeight G z₀ w₀ P w) =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalSize (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalSize (d7DeletedGraph G (z : A))
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) +
          fractionalSize G (d7SmallCorrection G P)) := by
  have hnonUniversal :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ u : ↑(nonUniversalVertices G),
          d7LiftedWeight (u : A) (w u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          fractionalSize (d7DeletedGraph G (u : A)) (w u) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro u
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (u : A)) (w u)
  have huniversal :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ z : ↑(universalVertices G),
          d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z) t) =
        ∑ z : ↑(universalVertices G),
          fractionalSize (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro z
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
  unfold fractionalSize d7SmallAverageWeight
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hnonUniversal, huniversal]
  rfl

lemma sum_d7HallRedistribution_outflow (G : SimpleGraph A)
    (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma) :
    (∑ u : ↑(nonUniversalVertices G),
      ((∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u)) =
      2 * ((universalVertices G).card : ℝ) * P.betaMass +
        ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [R.beta_source_sum]
  rw [R.alpha_sum]
  unfold d7HallBetaSource d7HallAlphaSource
  rw [← Finset.mul_sum, P.sum_betaIncident_eq_two_betaMass]
  ring

private lemma sum_nonUniversal_add_sum_universal
    (G : SimpleGraph A) (f : A → ℝ) :
    (∑ u : ↑(nonUniversalVertices G), f u) +
        (∑ z : ↑(universalVertices G), f z) =
      ∑ x : A, f x := by
  have hdisj : Disjoint (nonUniversalVertices G) (universalVertices G) := by
    rw [Finset.disjoint_left]
    intro u hu hz
    rw [mem_nonUniversalVertices] at hu
    rw [mem_universalVertices] at hz
    omega
  have hunion : nonUniversalVertices G ∪ universalVertices G = Finset.univ := by
    ext u
    simp only [Finset.mem_union, mem_nonUniversalVertices,
      mem_universalVertices, Finset.mem_univ, iff_true]
    omega
  rw [← Finset.sum_subtype (nonUniversalVertices G) (fun _ ↦ Iff.rfl) f,
    ← Finset.sum_subtype (universalVertices G) (fun _ ↦ Iff.rfl) f,
    ← Finset.sum_union hdisj, hunion]

lemma sum_d7DeletedGraph_edgeSet_card (G : SimpleGraph A)
    (hcard : 2 ≤ Fintype.card A) :
    (∑ u : ↑(nonUniversalVertices G),
        (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) +
      (∑ z : ↑(universalVertices G),
        (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) =
      ((Fintype.card A - 2 : ℕ) : ℝ) * (Nat.card G.edgeSet : ℝ) := by
  calc
    (∑ u : ↑(nonUniversalVertices G),
        (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) +
      (∑ z : ↑(universalVertices G),
        (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) =
        ∑ x : A, (Nat.card (d7DeletedGraph G x).edgeSet : ℝ) :=
      sum_nonUniversal_add_sum_universal G
        (fun x ↦ (Nat.card (d7DeletedGraph G x).edgeSet : ℝ))
    _ = ((Fintype.card A - 2 : ℕ) : ℝ) *
        (Nat.card G.edgeSet : ℝ) := by
      have hpoint : ∀ x : A,
          (Nat.card (d7DeletedGraph G x).edgeSet : ℝ) + (G.degree x : ℝ) =
            (Nat.card G.edgeSet : ℝ) := by
        intro x
        exact_mod_cast (card_edgeSet_induce_univ_erase_add_degree G x).symm
      have hsum := congrArg (fun q : ℝ ↦ q)
        (show (∑ x : A,
          ((Nat.card (d7DeletedGraph G x).edgeSet : ℝ) + (G.degree x : ℝ))) =
            ∑ _x : A, (Nat.card G.edgeSet : ℝ) by
          apply Fintype.sum_congr
          exact hpoint)
      rw [Finset.sum_add_distrib] at hsum
      have hdegrees : (∑ x : A, (G.degree x : ℝ)) =
          2 * (Nat.card G.edgeSet : ℝ) := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      rw [hdegrees] at hsum
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat] at hsum
      rw [Nat.cast_sub hcard, Nat.cast_ofNat]
      linarith

lemma fractionalUncoveredWeight_d7SmallAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hcard : 2 < Fintype.card A) :
    fractionalUncoveredWeight G (d7SmallAverageWeight G z₀ w₀ P w) =
      (((Fintype.card A - 2 : ℕ) : ℝ)⁻¹) *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (z : A))
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) -
          3 * fractionalSize G (d7SmallCorrection G P)) := by
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  have hedge := sum_d7DeletedGraph_edgeSet_card G (by omega)
  have hedgeD :
      (∑ u : ↑(nonUniversalVertices G),
          (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) +
        (∑ z : ↑(universalVertices G),
          (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) =
        d * (Nat.card G.edgeSet : ℝ) := by
    simpa only [d] using hedge
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d7SmallAverageWeight]
  simp_rw [fractionalUncoveredWeight_eq_card_sub_general]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change (Nat.card G.edgeSet : ℝ) -
      3 * (d⁻¹ *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalSize (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalSize (d7DeletedGraph G (z : A))
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) +
          fractionalSize G (d7SmallCorrection G P))) =
      d⁻¹ *
        (((∑ u : ↑(nonUniversalVertices G),
              (Nat.card (d7DeletedGraph G (u : A)).edgeSet : ℝ)) -
            3 * (∑ u : ↑(nonUniversalVertices G),
              fractionalSize (d7DeletedGraph G (u : A)) (w u))) +
          ((∑ z : ↑(universalVertices G),
              (Nat.card (d7DeletedGraph G (z : A)).edgeSet : ℝ)) -
            3 * (∑ z : ↑(universalVertices G),
              fractionalSize (d7DeletedGraph G (z : A))
                (d7CoherentUniversalDeletedWeight G z₀ w₀ z))) -
          3 * fractionalSize G (d7SmallCorrection G P))
  field_simp [ne_of_gt hd]
  linarith [hedgeD]

lemma fractionalUncoveredWeight_d7SmallDeleted_eq
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G))
    (w : Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) w) :
    fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w =
      capacityUncoveredWeight
          (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
          (d7SmallDeletedCapacity G P sigma R u) w +
        ∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
          d7SmallHallDeduction G P sigma R u e := by
  letI : DecidableRel
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).Adj := Classical.decRel _
  let H := d7DeletedGraph G (u : A)
  let c := d7SmallDeletedCapacity G P sigma R u
  have hcSupport : ∀ e, e ∉ H.edgeSet → c e = 0 := by
    intro e he
    exact d7SmallDeletedCapacity_support G P sigma R u e (by
      simpa only [H, SimpleGraph.mem_edgeSet] using he)
  have hIndicatorPacking : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w := by
    refine ⟨hwTop.1, ?_⟩
    intro e heTop
    change fractionalEdgeLoad (⊤ : SimpleGraph _) w e ≤
      (if e ∈ H.edgeFinset then 1 else 0)
    by_cases heH : e ∈ H.edgeFinset
    · rw [if_pos heH]
      calc
        fractionalEdgeLoad (⊤ : SimpleGraph _) w e ≤ c e := hwTop.2 e heTop
        _ ≤ 1 := by
          dsimp only [c]
          rw [d7SmallDeletedCapacity, if_pos heH]
          exact sub_le_self 1
            (d7SmallHallDeduction_nonneg G P sigma R hm u e)
    · rw [if_neg heH]
      have hc0 : c e = 0 := hcSupport e (by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heH)
      exact (hwTop.2 e heTop).trans_eq hc0
  have hIndicatorSupport : ∀ e, e ∉ H.edgeSet →
      (if e ∈ H.edgeFinset then (1 : ℝ) else 0) = 0 := by
    intro e he
    rw [if_neg]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
  have hindicator : fractionalUncoveredWeight H w =
      capacityUncoveredWeight (⊤ : SimpleGraph _)
        (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w := by
    calc
      fractionalUncoveredWeight H w =
          capacityUncoveredWeight (⊤ : SimpleGraph _)
            (fun e ↦ if e ∈ H.edgeFinset then 1 else 0)
            (zeroExtendTriangleWeight H w) :=
        (capacityUncoveredWeight_indicator_zeroExtend H w).symm
      _ = capacityUncoveredWeight (⊤ : SimpleGraph _)
            (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w :=
        capacityUncoveredWeight_zeroExtend_eq_of_capacity_support
          hIndicatorPacking hIndicatorSupport
  rw [show fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w =
      capacityUncoveredWeight (⊤ : SimpleGraph _)
        (fun e ↦ if e ∈ H.edgeFinset then 1 else 0) w by
      simpa only [H] using hindicator]
  unfold capacityUncoveredWeight
  have hsub : H.edgeFinset ⊆
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hfilter : ((⊤ : SimpleGraph
      (↑(d7DeletedFinset (u : A)))).edgeFinset.filter
        (fun e ↦ e ∈ H.edgeFinset)) = H.edgeFinset := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hsub h, h⟩
  calc
    (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        ((if e ∈ H.edgeFinset then 1 else 0) -
          fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) =
      ∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        ((c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e) +
          if e ∈ H.edgeFinset then
            d7SmallHallDeduction G P sigma R u e else 0) := by
      apply Finset.sum_congr rfl
      intro e heTop
      by_cases heH : e ∈ H.edgeFinset
      · simp only [if_pos heH]
        dsimp only [c]
        rw [d7SmallDeletedCapacity, if_pos heH]
        ring
      · simp only [if_neg heH]
        have hc0 : c e = 0 := hcSupport e (by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heH)
        rw [hc0]
        ring
    _ = (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
          (c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) +
        ∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
          if e ∈ H.edgeFinset then
            d7SmallHallDeduction G P sigma R u e else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
          (c e - fractionalEdgeLoad (⊤ : SimpleGraph _) w e)) +
        ∑ e ∈ H.edgeFinset, d7SmallHallDeduction G P sigma R u e := by
      congr 1
      rw [← Finset.sum_filter, hfilter]

lemma fractionalUncoveredWeight_d7SmallDeleted_le {a : ℕ}
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G))
    (w : Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) w)
    (hunc : capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) w ≤
        ((a - sigma u : ℕ) : ℝ)) :
    fractionalUncoveredWeight (d7DeletedGraph G (u : A)) w ≤
      ((a - sigma u : ℕ) : ℝ) +
        (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
        R.alphaFlow u := by
  rw [fractionalUncoveredWeight_d7SmallDeleted_eq G P sigma R hm u w hwTop]
  have hsum : (∑ e ∈ (d7DeletedGraph G (u : A)).edgeFinset,
      d7SmallHallDeduction G P sigma R u e) ≤
      ∑ e ∈ (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))).edgeFinset,
        d7SmallHallDeduction G P sigma R u e := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact SimpleGraph.edgeFinset_mono le_top
    · intro e _heTop _heNot
      exact d7SmallHallDeduction_nonneg G P sigma R hm u e
  rw [sum_d7SmallHallDeduction G P sigma R hm u] at hsum
  linarith

lemma sum_fractionalUncoveredWeight_d7SmallDeleted_le {a : ℕ}
    (G : SimpleGraph A) (P : D7SeparatedParameters G) (sigma : A → ℕ)
    (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hsigma : ∀ u, sigma u ≤ a)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u) ≤
        ((a - sigma u : ℕ) : ℝ)) :
    (∑ u : ↑(nonUniversalVertices G),
      fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) ≤
      ((nonUniversalVertices G).card : ℝ) * (a : ℝ) - 2 * (a : ℝ) +
        2 * ((universalVertices G).card : ℝ) * P.betaMass +
        ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
  calc
    (∑ u : ↑(nonUniversalVertices G),
        fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) ≤
      ∑ u : ↑(nonUniversalVertices G),
        (((a - sigma u : ℕ) : ℝ) +
          (∑ v : ↑(nonUniversalVertices G), R.betaFlow u v) +
          R.alphaFlow u) := by
      apply Finset.sum_le_sum
      intro u _
      exact fractionalUncoveredWeight_d7SmallDeleted_le
        G P sigma R hm u (w u) (hwTop u) (hunc u)
    _ = ((nonUniversalVertices G).card : ℝ) * (a : ℝ) - 2 * (a : ℝ) +
        2 * ((universalVertices G).card : ℝ) * P.betaMass +
        ((universalVertices G).card : ℝ) / 2 * P.alphaMass := by
      have hsigmaSubtype :
          (∑ u : ↑(nonUniversalVertices G), (sigma u : ℝ)) =
            (2 * a : ℕ) := by
        norm_cast
        calc
          (∑ u : ↑(nonUniversalVertices G), sigma (u : A)) =
              ∑ u ∈ nonUniversalVertices G, sigma u :=
            (Finset.sum_subtype (nonUniversalVertices G)
              (fun _ ↦ Iff.rfl) sigma).symm
          _ = 2 * a := hsum
      have hpoint : ∀ u : ↑(nonUniversalVertices G),
          (((a - sigma u : ℕ) : ℝ)) = (a : ℝ) - sigma u := by
        intro u
        rw [Nat.cast_sub (hsigma u)]
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      conv_lhs => rw [add_assoc]
      rw [← Finset.sum_add_distrib,
        sum_d7HallRedistribution_outflow G P sigma R]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_one, hsigmaSubtype, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma sum_fractionalUncoveredWeight_d7CoherentUniversalDeletedWeight_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    {a : ℝ}
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ a + 1) :
    (∑ z : ↑(universalVertices G),
        fractionalUncoveredWeight (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) ≤
      ((universalVertices G).card : ℝ) * (a + 1) := by
  simp_rw [fractionalUncoveredWeight_d7CoherentUniversalDeletedWeight
    G z₀ w₀]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hwUpper (Nat.cast_nonneg _)

lemma fractionalUncoveredWeight_d7SmallAverageWeight_le {a : ℕ}
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (hm : 4 ≤ (universalVertices G).card)
    (hsigma : ∀ u, sigma u ≤ a)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u) ≤
        ((a - sigma u : ℕ) : ℝ))
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ (a : ℝ) + 1) :
    fractionalUncoveredWeight G (d7SmallAverageWeight G z₀ w₀ P w) ≤
      (a : ℝ) := by
  have hU := sum_fractionalUncoveredWeight_d7SmallDeleted_le
    G P sigma R hm hsigma hsum w hwTop hunc
  have hZ :=
    sum_fractionalUncoveredWeight_d7CoherentUniversalDeletedWeight_le
      G z₀ w₀ hwUpper
  have hcorrection := three_mul_fractionalSize_d7SmallCorrection G P hm
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hmle : (universalVertices G).card ≤ Fintype.card A :=
    Finset.card_le_card (Finset.subset_univ (universalVertices G))
  have hcard : 2 < Fintype.card A := by omega
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  have hnum :
      ((∑ u : ↑(nonUniversalVertices G),
          fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) +
        (∑ z : ↑(universalVertices G),
          fractionalUncoveredWeight (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) -
        3 * fractionalSize G (d7SmallCorrection G P)) ≤
      (((Fintype.card A - 2 : ℕ) : ℝ) * (a : ℝ)) := by
    rw [hcorrection]
    rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
    nlinarith
  rw [fractionalUncoveredWeight_d7SmallAverageWeight G z₀ w₀ P w hcard]
  let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Nat.sub_pos_of_lt hcard)
  calc
    d⁻¹ *
        ((∑ u : ↑(nonUniversalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (u : A)) (w u)) +
          (∑ z : ↑(universalVertices G),
            fractionalUncoveredWeight (d7DeletedGraph G (z : A))
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) -
          3 * fractionalSize G (d7SmallCorrection G P)) ≤
      d⁻¹ * (d * (a : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [d] using hnum)
          (inv_nonneg.mpr hd.le)
    _ = (a : ℝ) := by field_simp [ne_of_gt hd]

lemma D7SeparatedParameters.alpha_le_half
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    P.alpha u ≤ 1 / 2 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hmR : 4 ≤ m := by
    dsimp only [m]
    exact_mod_cast hm
  have halphaSingle : P.alpha u ≤
      ∑ v : ↑(nonUniversalVertices G), P.alpha v := by
    apply Finset.single_le_sum
    · intro v _
      exact P.alpha_nonneg v
    · exact Finset.mem_univ u
  have hfactor : 0 ≤ m - 1 := by linarith
  have hscaled : (m - 1) * P.alpha u ≤ P.alphaMass := by
    unfold D7SeparatedParameters.alphaMass
    change (m - 1) * P.alpha u ≤
      (m - 1) * ∑ v : ↑(nonUniversalVertices G), P.alpha v
    exact mul_le_mul_of_nonneg_left halphaSingle hfactor
  have hmass : P.alphaMass ≤ 1 := P.alphaMass_le_one (by omega)
  have halpha0 := P.alpha_nonneg u
  nlinarith

lemma D7SeparatedParameters.gamma_le_half
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    P.gamma ≤ 1 / 2 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hmR : 4 ≤ m := by
    dsimp only [m]
    exact_mod_cast hm
  have halpha := P.alphaMass_nonneg (by omega)
  have hbeta := P.betaMass_nonneg
  have hnorm : ((m - 1) * (m - 2) / 2) * P.gamma +
      P.alphaMass + P.betaMass = 1 := by
    simpa only [m, D7SeparatedParameters.alphaMass,
      D7SeparatedParameters.betaMass] using P.normalization
  have hterm : ((m - 1) * (m - 2) / 2) * P.gamma ≤ 1 := by
    linarith
  have hgamma0 := P.gamma_nonneg
  have hfactor : 3 ≤ (m - 1) * (m - 2) / 2 := by nlinarith
  have hscaled : 3 * P.gamma ≤
      ((m - 1) * (m - 2) / 2) * P.gamma :=
    mul_le_mul_of_nonneg_right hfactor hgamma0
  linarith

private lemma d7SmallUZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d7SmallUZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d7SmallUZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro f
  rw [if_neg]
  intro hEq
  have hfND : ¬(f : Sym2 (↑(universalVertices G))).IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset
      f.property
  have hmapSub : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆
        ({(z : A), (u : A), (v : A)} : Finset A) := by
    intro x hx
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr hx
  have hmapSingleton : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆ ({(z : A)} : Finset A) := by
    intro x hx
    have hxTarget := hmapSub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTarget ⊢
    rcases hxTarget with hxz | hxu | hxv
    · exact hxz
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (u : A) at hxu
      rw [hxu]
      exact u.property
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (v : A) at hxv
      rw [hxv]
      exact v.property
  have hcardMap : ((f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ hfND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

private lemma d7SmallZZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d7SmallZZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d7SmallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d7SmallCorrection_apply_UUZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d7SmallCorrection G P {(z : A), (u : A), (v : A)} = P.beta s(u, v) := by
  unfold d7SmallCorrection
  rw [d7UUZCorrection_apply G P u v huv z he,
    d7SmallUZZCorrection_apply_UUZ_eq_zero G P u v z,
    d7SmallZZZCorrection_apply_UUZ_eq_zero G P u v z]
  ring

private lemma d7SmallUZZCorrection_apply
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d7SmallUZZCorrection G P {(u : A), (x : A), (y : A)} = P.alpha u := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have htriangle : attachedEdgeTriangle (universalVertices G) (u : A) e =
      ({(u : A), (x : A), (y : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d7SmallUZZCorrection
  rw [Fintype.sum_eq_single u]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦
        (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro u' hu'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hu'
    apply Subtype.ext
    have humem : (u' : A) ∈ ({(u : A), (x : A), (y : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem
    rcases humem with h | h | h
    · exact h
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ x.property)).elim
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ y.property)).elim

private lemma d7SmallZZZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d7SmallZZZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d7SmallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d7SmallCorrection_apply_UZZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d7SmallCorrection G P {(u : A), (x : A), (y : A)} = P.alpha u := by
  unfold d7SmallCorrection
  rw [d7UUZCorrection_apply_UZZ_eq_zero G P u x y,
    d7SmallUZZCorrection_apply G P u x y hxy,
    d7SmallZZZCorrection_apply_UZZ_eq_zero G P u x y]
  ring

private lemma d7SmallUZZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d7SmallUZZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d7SmallUZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have huTarget : (u : A) ∈
      ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at huTarget
  rcases huTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ x.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)).elim

private lemma d7SmallZZZCorrection_apply
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d7SmallZZZCorrection G P {(x : A), (y : A), (z : A)} = P.gamma := by
  have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
  have hxzA : (x : A) ≠ (z : A) := fun h ↦ hxz (Subtype.ext h)
  have hyzA : (y : A) ≠ (z : A) := fun h ↦ hyz (Subtype.ext h)
  let q0 : Finset A := {(x : A), (y : A), (z : A)}
  have hqsub : q0 ⊆ universalVertices G := by
    intro a ha
    simp only [q0, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
  have hqcard : q0.card = 3 := by
    simp [q0, hxyA, hxzA, hyzA]
  let q : ↑((universalVertices G).powersetCard 3) :=
    ⟨q0, Finset.mem_powersetCard.mpr ⟨hqsub, hqcard⟩⟩
  unfold d7SmallZZZCorrection singleTriangleWeight
  rw [Fintype.sum_eq_single q]
  · dsimp only [q, q0]
    rw [if_pos rfl]
  · intro q' hne
    rw [if_neg]
    intro hEq
    apply hne
    apply Subtype.ext
    exact hEq.symm

lemma d7SmallCorrection_apply_ZZZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d7SmallCorrection G P {(x : A), (y : A), (z : A)} = P.gamma := by
  unfold d7SmallCorrection
  rw [d7UUZCorrection_apply_ZZZ_eq_zero G P x y z,
    d7SmallUZZCorrection_apply_ZZZ_eq_zero G P x y z,
    d7SmallZZZCorrection_apply G P x y z hxy hxz hyz]
  ring

private lemma d7SmallUZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7SmallUZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7SmallUZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty (e : Sym2 (↑(universalVertices G))))
  have hzMap : (z : A) ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzMap
  rcases hzMap with h | h | h
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ u.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ v.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ w.property)).elim

private lemma d7SmallZZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7SmallZZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7SmallZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have hqne : (q : Finset A) ≠ ∅ := by
    intro hzero
    have hcard := (Finset.mem_powersetCard.mp q.property).2
    rw [hzero, Finset.card_empty] at hcard
    omega
  obtain ⟨z, hzq⟩ := Finset.nonempty_iff_ne_empty.mpr hqne
  have hzTarget : z ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    exact hzq
  have hzZ := (Finset.mem_powersetCard.mp q.property).1 hzq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (h ▸ hzZ)).elim

lemma d7SmallCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7SmallCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7SmallCorrection
  rw [d7UUZCorrection_apply_UUU_eq_zero G P u v w,
    d7SmallUZZCorrection_apply_UUU_eq_zero G P u v w,
    d7SmallZZZCorrection_apply_UUU_eq_zero G P u v w]
  ring

lemma d7LiftedWeight_eq_zero_of_mem_vertex
    (z : A) (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    {t : Finset A} (hz : z ∈ t) :
    d7LiftedWeight z w t = 0 := by
  apply extendInducedWeight_eq_zero
  intro hsub
  have hzdel := hsub hz
  simp [d7DeletedFinset] at hzdel

lemma d7LiftedWeight_le_half_of_top
    (G : SimpleGraph A) (z : A)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (A := A) z))) w)
    {t : Finset A} (ht : t ∈ G.cliqueFinset 3) :
    d7LiftedWeight z w t ≤ 1 / 2 := by
  unfold d7LiftedWeight
  by_cases hsub : t ⊆ d7DeletedFinset z
  · let q : Finset (↑(d7DeletedFinset (A := A) z)) :=
      restrictToInduced (d7DeletedFinset z) t hsub
    have hmap : q.map (inducedEmbedding (d7DeletedFinset z)) = t := by
      simpa only [q, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    rw [extendInducedWeight, dif_pos hsub]
    apply hw q
    have htcard := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    rw [← hmap, Finset.card_map] at htcard
    have htopNC : (⊤ : SimpleGraph
        (↑(d7DeletedFinset (A := A) z))).IsNClique 3 q := by
      refine ⟨?_, htcard⟩
      intro x _ y _ hxy
      exact hxy
    simpa only [SimpleGraph.cliqueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using htopNC
  · rw [extendInducedWeight_eq_zero hsub]
    norm_num

lemma sum_le_one_zero {B : Type} [Fintype B] [DecidableEq B]
    (f : B → ℝ) (x : B) (hx : f x ≤ 0)
    (hrest : ∀ y, y ≠ x → f y ≤ 1 / 2) :
    (∑ y : B, f y) ≤ ((Fintype.card B : ℝ) - 1) * (1 / 2) := by
  calc
    (∑ y : B, f y) ≤
        ∑ y : B, if y = x then 0 else 1 / 2 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y = x
      · subst y
        rw [if_pos rfl]
        exact hx
      · rw [if_neg hy]
        exact hrest y hy
    _ = ((Fintype.card B : ℝ) - 1) * (1 / 2) := by
      rw [Finset.sum_ite]
      simp only [Finset.filter_eq', Finset.mem_univ, if_true,
        Finset.sum_const_zero, zero_add]
      rw [show (Finset.univ : Finset B).filter (fun y ↦ y ≠ x) =
          Finset.univ \ {x} by ext y; simp]
      rw [Finset.sum_const, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp only [Finset.card_univ, Finset.card_singleton, nsmul_eq_mul]
      have hxcard : 1 ≤ Fintype.card B := Fintype.card_pos_iff.mpr ⟨x⟩
      rw [Nat.cast_sub hxcard, Nat.cast_one]

lemma sum_d7SmallNonUniversalDeleted_UUU_le
    (G : SimpleGraph A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (u v x : ↑(nonUniversalVertices G))
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (ht : ({(u : A), (v : A), (x : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ y : ↑(nonUniversalVertices G),
        d7LiftedWeight (y : A) (w y) {(u : A), (v : A), (x : A)}) ≤
      (((nonUniversalVertices G).card : ℝ) - 3) * (1 / 2) := by
  let f : ↑(nonUniversalVertices G) → ℝ := fun y ↦
    d7LiftedWeight (y : A) (w y) {(u : A), (v : A), (x : A)}
  have hfu : f u ≤ 0 := by
    rw [show f u = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (u : A) (w u) (by simp)]
  have hfv : f v ≤ 0 := by
    rw [show f v = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (v : A) (w v) (by simp)]
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (x : A) (w x) (by simp)]
  have hrest : ∀ y, y ≠ u → y ≠ v → y ≠ x → f y ≤ 1 / 2 := by
    intro y _ _ _
    exact d7LiftedWeight_le_half_of_top G (y : A) (hwHalf y) ht
  have hsum := sum_le_three_zero f u v x huv hux hvx hfu hfv hfx hrest
  simpa only [f, Fintype.card_coe] using hsum

lemma sum_d7SmallNonUniversalDeleted_UUZ_le
    (G : SimpleGraph A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ x : ↑(nonUniversalVertices G),
        d7LiftedWeight (x : A) (w x) {(z : A), (u : A), (v : A)}) ≤
      (((nonUniversalVertices G).card : ℝ) - 2) * (1 / 2) := by
  let f : ↑(nonUniversalVertices G) → ℝ := fun x ↦
    d7LiftedWeight (x : A) (w x) {(z : A), (u : A), (v : A)}
  have hfu : f u ≤ 0 := by
    rw [show f u = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (u : A) (w u) (by simp)]
  have hfv : f v ≤ 0 := by
    rw [show f v = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (v : A) (w v) (by simp)]
  have hrest : ∀ x, x ≠ u → x ≠ v → f x ≤ 1 / 2 := by
    intro x _ _
    exact d7LiftedWeight_le_half_of_top G (x : A) (hwHalf x) ht
  have hsum := sum_le_two_exception f u v huv 0 0 (1 / 2) hfu hfv hrest
  simpa only [f, Fintype.card_coe, zero_add] using hsum

lemma sum_d7SmallNonUniversalDeleted_UZZ_le
    (G : SimpleGraph A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (u : ↑(nonUniversalVertices G)) (x y : ↑(universalVertices G))
    (ht : ({(u : A), (x : A), (y : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ v : ↑(nonUniversalVertices G),
        d7LiftedWeight (v : A) (w v) {(u : A), (x : A), (y : A)}) ≤
      (((nonUniversalVertices G).card : ℝ) - 1) * (1 / 2) := by
  let f : ↑(nonUniversalVertices G) → ℝ := fun v ↦
    d7LiftedWeight (v : A) (w v) {(u : A), (x : A), (y : A)}
  have hfu : f u ≤ 0 := by
    rw [show f u = 0 by
      exact d7LiftedWeight_eq_zero_of_mem_vertex (u : A) (w u) (by simp)]
  have hrest : ∀ v, v ≠ u → f v ≤ 1 / 2 := by
    intro v _
    exact d7LiftedWeight_le_half_of_top G (v : A) (hwHalf v) ht
  have hsum := sum_le_one_zero f u hfu hrest
  simpa only [f, Fintype.card_coe] using hsum

lemma sum_d7SmallNonUniversalDeleted_ZZZ_le
    (G : SimpleGraph A)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hwHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (x y z : ↑(universalVertices G))
    (ht : ({(x : A), (y : A), (z : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {(x : A), (y : A), (z : A)}) ≤
      ((nonUniversalVertices G).card : ℝ) * (1 / 2) := by
  calc
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {(x : A), (y : A), (z : A)}) ≤
      ∑ _u : ↑(nonUniversalVertices G), (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        exact d7LiftedWeight_le_half_of_top G (u : A) (hwHalf u) ht
    _ = ((nonUniversalVertices G).card : ℝ) * (1 / 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]

lemma d7SmallAverageWeight_UUU_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u v x : ↑(nonUniversalVertices G))
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (ht : ({(u : A), (v : A), (x : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ y : ↑(nonUniversalVertices G),
        d7LiftedWeight (y : A) (w y) {(u : A), (v : A), (x : A)}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
          {(u : A), (v : A), (x : A)}) +
      d7SmallCorrection G P {(u : A), (v : A), (x : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UUU_le G w hwTop
    u v x huv hux hvx ht
  have hZ : (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        {(u : A), (v : A), (x : A)}) ≤
      ((universalVertices G).card : ℝ) * (1 / 2) := by
    calc
      _ ≤ ∑ _z : ↑(universalVertices G), (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        exact d7LiftedWeight_le_half G z (hwHalf z) ht
      _ = ((universalVertices G).card : ℝ) * (1 / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nsmul_eq_mul]
  rw [d7SmallCorrection_apply_UUU_eq_zero G P u v x, add_zero]
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d7SmallAverageWeight_UUZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ x : ↑(nonUniversalVertices G),
        d7LiftedWeight (x : A) (w x) {(z : A), (u : A), (v : A)}) +
      (∑ y : ↑(universalVertices G),
        d7LiftedWeight (y : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ y)
          {(z : A), (u : A), (v : A)}) +
      d7SmallCorrection G P {(z : A), (u : A), (v : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UUZ_le G w hwTop u v huv z ht
  have hZ := d7LargeAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal hm
    hwPacking hwHalf hwOne u v huv z he ht
  rw [d7LargeCorrection_apply_UUZ G P u v huv z he,
    ← d7SmallCorrection_apply_UUZ G P u v huv z he] at hZ
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d7SmallAverageWeight_UZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y)
    (ht : ({(u : A), (x : A), (y : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ v : ↑(nonUniversalVertices G),
        d7LiftedWeight (v : A) (w v) {(u : A), (x : A), (y : A)}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
          {(u : A), (x : A), (y : A)}) +
      d7SmallCorrection G P {(u : A), (x : A), (y : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_UZZ_le G w hwTop u x y ht
  let f : ↑(universalVertices G) → ℝ := fun z ↦
    d7LiftedWeight (z : A)
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      {(u : A), (x : A), (y : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hrest : ∀ z, z ≠ x → z ≠ y → f z ≤ 1 / 2 := by
    intro z _ _
    exact d7LiftedWeight_le_half G z (hwHalf z) ht
  have hZ := sum_le_two_exception f x y hxy 0 0 (1 / 2) hfx hfy hrest
  simp only [f, Fintype.card_coe, zero_add] at hZ
  rw [d7SmallCorrection_apply_UZZ G P u x y hxy]
  have halpha := P.alpha_le_half hm u
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

lemma d7SmallAverageWeight_ZZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : ({(x : A), (y : A), (z : A)} : Finset A) ∈ G.cliqueFinset 3) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {(x : A), (y : A), (z : A)}) +
      (∑ q : ↑(universalVertices G),
        d7LiftedWeight (q : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ q)
          {(x : A), (y : A), (z : A)}) +
      d7SmallCorrection G P {(x : A), (y : A), (z : A)} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have hU := sum_d7SmallNonUniversalDeleted_ZZZ_le G w hwTop x y z ht
  let f : ↑(universalVertices G) → ℝ := fun q ↦
    d7LiftedWeight (q : A)
      (d7CoherentUniversalDeletedWeight G z₀ w₀ q)
      {(x : A), (y : A), (z : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hrest : ∀ q, q ≠ x → q ≠ y → q ≠ z → f q ≤ 1 / 2 := by
    intro q _ _ _
    exact d7LiftedWeight_le_half G q (hwHalf q) ht
  have hZ := sum_le_three_zero f x y z hxy hxz hyz hfx hfy hfz hrest
  simp only [f, Fintype.card_coe] at hZ
  rw [d7SmallCorrection_apply_ZZZ G P x y z hxy hxz hyz]
  have hgamma := P.gamma_le_half hm
  have hparts := card_nonUniversalVertices_add_card_universalVertices G
  have hpartsR : ((nonUniversalVertices G).card : ℝ) +
      ((universalVertices G).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hparts
  rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card A), Nat.cast_ofNat]
  linarith

private lemma d7SmallAverageWeight_numerator_le_of_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∈ universalVertices G) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {a, b, c}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
      d7SmallCorrection G P {a, b, c} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let za : ↑(universalVertices G) := ⟨a, haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d7SmallAverageWeight_ZZZ_numerator_le G z₀ w₀ P w hn hm
        hwTop hwHalf za zb zc hzab hzac hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hset : ({(uc : A), (za : A), (zb : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [uc, za, zb, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(uc : A), (za : A), (zb : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7SmallAverageWeight_UZZ_numerator_le G z₀ w₀ P w
        hn hm hwTop hwHalf uc za zb hzab htri'
      rw [hset] at hnum
      exact hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hset : ({(ub : A), (za : A), (zc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [ub, za, zc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(ub : A), (za : A), (zc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7SmallAverageWeight_UZZ_numerator_le G z₀ w₀ P w
        hn hm hwTop hwHalf ub za zc hzac htri'
      rw [hset] at hnum
      exact hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      have he : s(ub, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj b c
        exact hadj.2.2
      exact d7SmallAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal w
        hn hm hwTop hwPacking hwHalf hwOne ub uc hubc za he ht

private lemma d7SmallAverageWeight_numerator_le_of_not_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∉ universalVertices G) :
    (∑ u : ↑(nonUniversalVertices G),
        d7LiftedWeight (u : A) (w u) {a, b, c}) +
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
      d7SmallCorrection G P {a, b, c} ≤
        (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let ua : ↑(nonUniversalVertices G) :=
    ⟨a, nonUniversal_of_not_universal haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d7SmallAverageWeight_UZZ_numerator_le G z₀ w₀ P w hn hm
        hwTop hwHalf ua zb zc hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have he : s(ua, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a c
        exact hadj.2.1
      have hset : ({(zb : A), (ua : A), (uc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [zb, ua, uc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zb : A), (ua : A), (uc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7SmallAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal w
        hn hm hwTop hwPacking hwHalf hwOne ua uc huac zb he htri'
      rw [hset] at hnum
      exact hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have he : s(ua, ub) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a b
        exact hadj.1
      have hset : ({(zc : A), (ua : A), (ub : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [zc, ua, ub, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zc : A), (ua : A), (ub : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7SmallAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal w
        hn hm hwTop hwPacking hwHalf hwOne ua ub huab zc he htri'
      rw [hset] at hnum
      exact hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d7SmallAverageWeight_UUU_numerator_le G z₀ w₀ P w hn
        hwTop hwHalf ua ub uc huab huac hubc ht

/-- The Hall-adjusted deletion family and the small correction preserve the
pointwise one-half bound after normalization by `|V|-2`. -/
lemma d7SmallAverageWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) :
    IsHalfBounded G (d7SmallAverageWeight G z₀ w₀ P w) := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp
    (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have finish :
      (∑ u : ↑(nonUniversalVertices G),
          d7LiftedWeight (u : A) (w u) {a, b, c}) +
        (∑ z : ↑(universalVertices G),
          d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
        d7SmallCorrection G P {a, b, c} ≤
          (((Fintype.card A - 2 : ℕ) : ℝ)) / 2 →
      d7SmallAverageWeight G z₀ w₀ P w {a, b, c} ≤ 1 / 2 := by
    intro hnum
    unfold d7SmallAverageWeight
    let d : ℝ := ((Fintype.card A - 2 : ℕ) : ℝ)
    have hd : 0 < d := by
      dsimp only [d]
      exact_mod_cast (Nat.sub_pos_of_lt (by omega : 2 < Fintype.card A))
    calc
      d⁻¹ * ((∑ u : ↑(nonUniversalVertices G),
            d7LiftedWeight (u : A) (w u) {a, b, c}) +
          (∑ z : ↑(universalVertices G),
            d7LiftedWeight (z : A)
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
          d7SmallCorrection G P {a, b, c}) ≤
        d⁻¹ * (d / 2) :=
          mul_le_mul_of_nonneg_left (by simpa only [d] using hnum)
            (inv_nonneg.mpr hd.le)
      _ = 1 / 2 := by field_simp [ne_of_gt hd]
  by_cases haZ : a ∈ universalVertices G
  · apply finish
    exact d7SmallAverageWeight_numerator_le_of_mem_universal_left
      G z₀ w₀ P hreal w hn hm hwTop hwPacking hwHalf hwOne
      hab hac hbc ht haZ
  · apply finish
    exact d7SmallAverageWeight_numerator_le_of_not_mem_universal_left
      G z₀ w₀ P hreal w hn hm hwTop hwPacking hwHalf hwOne
      hab hac hbc ht haZ

/-- The corrected small-`m` average is a strong packing once the Hall-adjusted
deletion packings and their exact budget data are supplied. -/
lemma hasStrongFractionalPacking_d7SmallAverageWeight {a : ℕ}
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (sigma : A → ℕ) (R : D7HallRedistribution G P sigma)
    (w : ∀ u : ↑(nonUniversalVertices G),
      Finset (↑(d7DeletedFinset (u : A))) → ℝ)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hsigma : ∀ u, sigma u ≤ a)
    (hsum : ∑ u ∈ nonUniversalVertices G, sigma u = 2 * a)
    (hwActual : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (d7DeletedGraph G (u : A))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hwTop : ∀ u : ↑(nonUniversalVertices G), IsCapacityPacking
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u))
    (hunc : ∀ u : ↑(nonUniversalVertices G), capacityUncoveredWeight
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
      (d7SmallDeletedCapacity G P sigma R u) (w u) ≤
        ((a - sigma u : ℕ) : ℝ))
    (hwTopHalf : ∀ u : ↑(nonUniversalVertices G), IsHalfBounded
      (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) (w u))
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ (a : ℝ) + 1) :
    HasStrongFractionalPacking G (a : ℝ) := by
  refine ⟨d7SmallAverageWeight G z₀ w₀ P w, ?_, ?_, ?_⟩
  · exact d7SmallAverageWeight_isFractionalPacking G z₀ w₀ P hreal hm
      sigma R w hwActual hwPacking hwOne
  · exact fractionalUncoveredWeight_d7SmallAverageWeight_le G z₀ w₀ P
      sigma R hm hsigma hsum w hwTop hunc hwUpper
  · exact d7SmallAverageWeight_halfBounded G z₀ w₀ P hreal w hn hm
      hwTopHalf hwPacking hwHalf hwOne

/-- The small-universal-set subcase of D7, assembled from Claim 5.3's
allocation, the fractional Hall redistribution, and the weighted induction
packings on every nonuniversal deletion. -/
theorem d7_small_universal_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hsmall : (universalVertices G).card ≤ n - 8)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  obtain ⟨sigma, hsigma, hsupport, hsum⟩ :=
    exists_d7ResidualAllocation hcard hn ha G hexact hm hnoD5
  have hsigmaA : ∀ u, sigma u ≤ a := by
    intro u
    exact (hsigma u).trans (Nat.min_le_left _ _)
  obtain ⟨z₀, w₀, hwPack₀, hwHalf₀, hwUncov₀, hsymm, _hwUnit, hfamily⟩ :=
    exists_d7CoherentUniversalDeletedWeights hcard hn ha G hexact hm
      sigma hsigma hstrong
  obtain ⟨P, hreal⟩ := exists_d7SeparatedParameters_realizing_coherent_family
    G z₀ w₀ hm hwPack₀ hwUncov₀.1 hsymm
  obtain ⟨R, _⟩ := exists_d7HallRedistribution hcard hn ha G hexact hm
    hsmall hnoD5 P sigma hsigma hsupport hsum
  have hweights : ∀ u : ↑(nonUniversalVertices G),
      ∃ w : Finset (↑(d7DeletedFinset (u : A))) → ℝ,
        IsCapacityPacking (d7DeletedGraph G (u : A))
            (d7SmallDeletedCapacity G P sigma R u) w ∧
        IsCapacityPacking (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
            (d7SmallDeletedCapacity G P sigma R u) w ∧
        capacityUncoveredWeight
            (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A))))
            (d7SmallDeletedCapacity G P sigma R u) w ≤
              ((a - sigma u : ℕ) : ℝ) ∧
        IsHalfBounded (⊤ : SimpleGraph (↑(d7DeletedFinset (u : A)))) w := by
    intro u
    exact exists_d7SmallSupportedWeightedPacking hcard hn ha G hexact P sigma
      hsigma R hm hstrong u
  choose w hwActual hwTop hunc hwTopHalf using hweights
  apply hasStrongFractionalPacking_d7SmallAverageWeight G z₀ w₀ P hreal
    sigma R w (hcard ▸ hn) hm hsigmaA hsum hwActual hwTop hunc hwTopHalf
  · intro z
    exact (hfamily z).1
  · intro z
    exact (hfamily z).2.1
  · intro z
    exact (hfamily z).2.2.1
  · have hupper := hwUncov₀.2
    norm_num [Nat.cast_add, Nat.cast_one] at hupper ⊢
    exact hupper

/-- Complete case D7: the universal-vertex set is either in the orbit-average
range or in the fractional-Hall range. -/
theorem d7_case {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (hnoD5 : ∀ u : A, 3 * Gᶜ.degree u ≤ n + a)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    HasStrongFractionalPacking G (a : ℝ) := by
  by_cases hlarge : n - 7 ≤ (universalVertices G).card
  · exact d7_large_universal_case hcard hn ha G hexact hm hlarge hstrong
  · have hsmall : (universalVertices G).card ≤ n - 8 := by omega
    exact d7_small_universal_case hcard hn ha G hexact hm hsmall hnoD5 hstrong

end

end Erdos76
