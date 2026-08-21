/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.AKSGraph

/-!
# Erdős Problem 88: asymptotic AKS prescribed-count assembly

This module supplies the asymptotic wrappers around the exact finite AKS
construction in `AKSGraph`.  In particular, it strengthens the square-root
balancedness interface there to an arbitrary positive power scale.  The AKS
application uses the specialization `theta = 1 / 5`.
-/

open Classical SimpleGraph

namespace Erdos88
namespace AKSGraph

/-- Ramsey-freeness passes to every induced set of cardinality at least
`n ^ theta`, at the cost of replacing the Ramsey constant `C` by
`C / theta`. -/
lemma ramseyFree_induce_overFin_of_rpow {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) {C theta : ℝ}
    (hC : 0 < C) (htheta : 0 < theta) (hn : 1 ≤ n)
    (hG : RamseyFree C G)
    (hS : (n : ℝ) ^ theta ≤ (S.card : ℝ)) :
    RamseyFree (C / theta)
      ((G.induce (S : Set (Fin n))).overFin (card_subtype_coe_finset S)) := by
  apply ramseyFree_induce_overFin G S hG
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpowpos : 0 < (n : ℝ) ^ theta :=
    Real.rpow_pos_of_pos hnpos theta
  have hlogMono :
      Real.logb 2 ((n : ℝ) ^ theta) ≤ Real.logb 2 (S.card : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hpowpos hS
  have hlogPow :
      Real.logb 2 ((n : ℝ) ^ theta) =
        theta * Real.logb 2 n := by
    rw [Real.logb, Real.logb, Real.log_rpow hnpos]
    ring
  rw [hlogPow] at hlogMono
  calc
    C * Real.logb 2 n =
        (C / theta) * (theta * Real.logb 2 n) := by
      field_simp [ne_of_gt htheta]
    _ ≤ (C / theta) * Real.logb 2 S.card :=
      mul_le_mul_of_nonneg_left hlogMono (div_nonneg hC.le htheta.le)

/-- A `C`-Ramsey graph is uniformly balanced on every induced vertex set
of size at least `n ^ theta`, for any fixed positive `theta`.  This is the
power-scale form needed by the AKS construction. -/
theorem ramseyFree_eventually_balanced_rpow
    (C theta : ℝ) (hC : 0 < C) (htheta : 0 < theta) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 / 12 ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, 1 ≤ n → ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
        ∀ {t : ℕ}, N ≤ t → (n : ℝ) ^ theta ≤ (t : ℝ) →
          IsBalanced G gamma t ∧ IsBalanced Gᶜ gamma t := by
  obtain ⟨a, ha, N, hDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower (C / theta)
      (div_pos hC htheta)
  let gamma : ℝ := min a (1 / 12)
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact lt_min ha (by norm_num)
  have hgammaa : gamma ≤ a := min_le_left _ _
  have hgammaSmall : gamma ≤ 1 / 12 := min_le_right _ _
  refine ⟨gamma, hgamma, hgammaSmall, N, ?_⟩
  intro n hn G hG t hNt hpower
  have hLower (H : SimpleGraph (Fin n)) (hHG : RamseyFree C H) :
      ∀ S : Finset (Fin n), t ≤ S.card →
        gamma * (S.card.choose 2 : ℝ) ≤ (edgeCount H S : ℝ) := by
    intro S htS
    let HI := (H.induce (S : Set (Fin n))).overFin
      (card_subtype_coe_finset S)
    have hNS : N ≤ S.card := hNt.trans htS
    have hpowerS : (n : ℝ) ^ theta ≤ (S.card : ℝ) := by
      exact hpower.trans (by exact_mod_cast htS)
    have hRamsey : RamseyFree (C / theta) HI :=
      ramseyFree_induce_overFin_of_rpow H S hC htheta hn hHG hpowerS
    have hDense := hDensity S.card hNS HI hRamsey
    have hEdge : FiniteES.edgeCount HI = edgeCount H S := by
      calc
        FiniteES.edgeCount HI =
            FiniteES.edgeCount (H.induce (S : Set (Fin n))) :=
          edgeCount_overFin _ (card_subtype_coe_finset S)
        _ = (H.induce (S : Set (Fin n))).edgeFinset.card := rfl
        _ = edgeCount H S := by
          symm
          simpa only [edgeCount] using
            H.card_filter_edgeFinset_toFinset_subset S
    rw [hEdge] at hDense
    have hchooseSq :
        (S.card.choose 2 : ℝ) ≤ (S.card : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow S.card 2
    calc
      gamma * (S.card.choose 2 : ℝ) ≤
          a * (S.card.choose 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hgammaa (by positivity)
      _ ≤ a * (S.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hchooseSq ha.le
      _ ≤ (edgeCount H S : ℝ) := hDense
  have hLowerG := hLower G hG
  have hLowerGc := hLower Gᶜ ((ramseyFree_compl G).2 hG)
  constructor
  · exact isBalanced_of_lower_and_compl_lower G gamma t hLowerG hLowerGc
  · apply isBalanced_of_lower_and_compl_lower Gᶜ gamma t hLowerGc
    simpa using hLowerG

/-- The exact fifth-power specialization used in the AKS small-count
argument. -/
theorem ramseyFree_eventually_balanced_fifth (C : ℝ) (hC : 0 < C) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 / 12 ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, 1 ≤ n → ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
        ∀ {t : ℕ}, N ≤ t → (n : ℝ) ^ (1 / 5 : ℝ) ≤ (t : ℝ) →
          IsBalanced G gamma t ∧ IsBalanced Gᶜ gamma t := by
  exact ramseyFree_eventually_balanced_rpow C (1 / 5 : ℝ) hC (by norm_num)

/-- The uniform quotient schedule discharges the nonlinear indexed-family
inequality in every positive AKS stage.  The remaining hypotheses are the
linear size and degree inequalities that are propagated along the reservoir
recurrence. -/
theorem exists_sizedPairExtension_of_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ}
    {t i u ell d q Q nextMin : ℕ} {Cset : Finset V}
    (hbal : IsBalanced G (6 * epsilon) t)
    (hbalc : IsBalanced Gᶜ (6 * epsilon) t)
    (hgamma0 : 0 ≤ 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q) (hu : u = 18 * Q ^ 2)
    (htu : t + u ≤ Cset.card / 2)
    (hlow : (ell : ℝ) ≤
      (6 * epsilon) * (((Cset.card / 2 : ℕ) : ℝ) - 1) - (u : ℝ))
    (hi : 1 ≤ i)
    (hq : q + (Cset.card - 1) / 2 ≤ Cset.card - u)
    (hwpos : 0 < Cset.card - u)
    (hwell : Cset.card - u ≤ Q * ell)
    (hwq : Cset.card - u ≤ 3 * q)
    (hd : d = (Cset.card - u) / u - 1)
    (hsize : max t (2 ^ i) ≤ d + 1)
    (hnext : nextMin ≤ d + 1) :
    Nonempty (SizedPairExtension G epsilon i nextMin Cset) := by
  apply exists_sizedPairExtension_of_balanced hbal hbalc hgamma0 hgamma1
      htu hlow hi
  · intro split
    have hWcard : split.W.card = Cset.card - u := by
      rw [split.W_eq, Finset.card_sdiff_of_subset split.U_sub,
        split.card_U]
    simpa [hWcard] using hq
  · exact hsize
  · intro split
    have hWcard : split.W.card = Cset.card - u := by
      rw [split.W_eq, Finset.card_sdiff_of_subset split.U_sub,
        split.card_U]
    rw [hWcard, split.card_U, hd]
    subst u
    exact pairSelection_numeric_divSchedule hwpos hQ hwell hwq
  · exact hnext

/-- If each of the two bad-triple contributions uses less than half of the
available main term, their sum satisfies the strict AKS triple-selection
inequality. -/
lemma tripleSelection_numeric_of_two_budgets
    {b w u ell q d : ℕ}
    (hfirst : 2 * ((b - 1) * w ^ 8) < u * (ell ^ 4 * q ^ 4))
    (hsecond :
      2 * (u.choose 3 * (d ^ 4 * w ^ 4)) < u * (ell ^ 4 * q ^ 4)) :
    (b - 1) * w ^ 8 + u.choose 3 * (d ^ 4 * w ^ 4) <
      u * (ell ^ 4 * q ^ 4) := by
  omega

/-- Balancedness, the oriented degree split, and two separate numerical
budgets produce the initial independent triple and its residual reservoir.
This is the finite initial-stage counterpart of
`exists_sizedPairExtension_of_ratio`. -/
theorem exists_initialTripleExtension_of_balanced_budgets
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {gamma : ℝ}
    {t b d q u ell : ℕ} {Cset : Finset V}
    (hbal : IsBalanced G gamma t)
    (hbalc : IsBalanced Gᶜ gamma t)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (htu : t + u ≤ Cset.card / 2)
    (hlow : (ell : ℝ) ≤
      gamma * (((Cset.card / 2 : ℕ) : ℝ) - 1) - (u : ℝ))
    (hgamma : 0 < gamma) (ht : 2 ≤ t) (htb : t ≤ b)
    (hlarge : (t : ℝ) ≤ gamma * ((b : ℝ) - 1))
    (hb : 0 < b)
    (hq : q + (Cset.card - 1) / 2 ≤ Cset.card - u)
    (hfirst :
      2 * ((b - 1) * (Cset.card - u) ^ 8) <
        u * (ell ^ 4 * q ^ 4))
    (hsecond :
      2 * (u.choose 3 * (d ^ 4 * (Cset.card - u) ^ 4)) <
        u * (ell ^ 4 * q ^ 4)) :
    Nonempty (InitialTripleExtension G d Cset) := by
  obtain ⟨split⟩ :=
    hbal.exists_orientedModerateSplit hbalc hgamma0 hgamma1 htu hlow
  have hWcard : split.W.card = Cset.card - u := by
    rw [split.W_eq, Finset.card_sdiff_of_subset split.U_sub,
      split.card_U]
  apply split.exists_initialTripleExtension hbal hgamma ht htb hlarge hb
  · simpa [hWcard] using hq
  · rw [hWcard, split.card_U]
    exact tripleSelection_numeric_of_two_budgets hfirst hsecond

/-- Natural-number ceiling division, kept local to the AKS schedule so its
rounding convention is explicit even when the divisor is zero. -/
def ceilingQuotient (a b : ℕ) : ℕ :=
  if a % b = 0 then a / b else a / b + 1

lemma ceilingQuotient_le_div_add_one (a b : ℕ) :
    ceilingQuotient a b ≤ a / b + 1 := by
  simp only [ceilingQuotient]
  split <;> omega

lemma le_mul_ceilingQuotient (a : ℕ) {b : ℕ} (hb : 0 < b) :
    a ≤ b * ceilingQuotient a b := by
  rw [ceilingQuotient]
  split_ifs with hmod
  · have hdecomp := Nat.div_add_mod a b
    omega
  · have hdecomp := Nat.div_add_mod a b
    have hmodPos : 0 < a % b := Nat.pos_of_ne_zero hmod
    have hmodLt : a % b < b := Nat.mod_lt a hb
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Canonical parameters for a positive AKS stage in a reservoir of size
`r`: a fixed `18 Q^2`-set is peeled off, the two degree thresholds are
rounded upward, and the next reservoir is the quotient schedule from the
pair-selection lemma. -/
def pairSelectedSize (Q : ℕ) : ℕ := 18 * Q ^ 2

def pairWorkingSize (r Q : ℕ) : ℕ := r - pairSelectedSize Q

def pairDegreeThreshold (r Q : ℕ) : ℕ :=
  ceilingQuotient (pairWorkingSize r Q) Q

def pairNonneighborThreshold (r Q : ℕ) : ℕ :=
  ceilingQuotient (pairWorkingSize r Q) 3

def pairNextThreshold (r Q : ℕ) : ℕ :=
  pairWorkingSize r Q / pairSelectedSize Q - 1

lemma ceilingNonneighborThreshold_capacity {r u : ℕ}
    (hlarge : 12 * u + 12 ≤ r) :
    ceilingQuotient (r - u) 3 + (r - 1) / 2 ≤ r - u := by
  unfold ceilingQuotient
  split_ifs <;> omega

lemma pairNonneighborThreshold_capacity {r Q : ℕ}
    (hlarge : 12 * pairSelectedSize Q + 12 ≤ r) :
    pairNonneighborThreshold r Q + (r - 1) / 2 ≤
      pairWorkingSize r Q := by
  exact ceilingNonneighborThreshold_capacity hlarge

lemma pairDegreeThreshold_le_of_large
    {gamma : ℝ} {r Q u : ℕ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ gamma * Q)
    (huge : (8 : ℝ) * (u + 3) ≤ gamma * r) :
    (ceilingQuotient (r - u) Q : ℝ) ≤
      gamma * (((r / 2 : ℕ) : ℝ) - 1) - (u : ℝ) := by
  have hceilNat := ceilingQuotient_le_div_add_one (r - u) Q
  have hceilCast :
      (ceilingQuotient (r - u) Q : ℝ) ≤
        (((r - u) / Q : ℕ) : ℝ) + 1 := by
    exact_mod_cast hceilNat
  have hdivMul := Nat.div_mul_le_self (r - u) Q
  have hdivCast :
      (((r - u) / Q : ℕ) : ℝ) * Q ≤ ((r - u : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hdivMul)
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hdiv :
      (((r - u) / Q : ℕ) : ℝ) ≤ ((r - u : ℕ) : ℝ) / Q := by
    exact (le_div_iff₀ hQreal).2 hdivCast
  have hwle : ((r - u : ℕ) : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast Nat.sub_le r u
  have hratio : (1 : ℝ) / Q ≤ gamma / 8 := by
    rw [div_le_div_iff₀ hQreal (by norm_num : (0 : ℝ) < 8)]
    simpa [mul_comm] using hgammaQ
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hdivBound : ((r - u : ℕ) : ℝ) / Q ≤ gamma * r / 8 := by
    calc
      ((r - u : ℕ) : ℝ) / Q ≤ (r : ℝ) / Q := by
        exact div_le_div_of_nonneg_right hwle hQreal.le
      _ = (r : ℝ) * (1 / Q) := by ring
      _ ≤ (r : ℝ) * (gamma / 8) :=
        mul_le_mul_of_nonneg_left hratio hr0
      _ = gamma * r / 8 := by ring
  have hdecompNat := Nat.div_add_mod r 2
  have hmodNat := Nat.mod_lt r (by norm_num : 0 < (2 : ℕ))
  have hdecomp :
      (2 : ℝ) * ((r / 2 : ℕ) : ℝ) + (r % 2 : ℕ) = r := by
    exact_mod_cast hdecompNat
  have hmod : ((r % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hmodNat
  have hhalf : (r : ℝ) / 2 - 1 ≤ ((r / 2 : ℕ) : ℝ) := by
    nlinarith
  calc
    (ceilingQuotient (r - u) Q : ℝ) ≤
        (((r - u) / Q : ℕ) : ℝ) + 1 := hceilCast
    _ ≤ ((r - u : ℕ) : ℝ) / Q + 1 := by linarith
    _ ≤ gamma * r / 8 + 1 := by linarith
    _ ≤ gamma * (((r / 2 : ℕ) : ℝ) - 1) - (u : ℝ) := by
      have huReal : (0 : ℝ) ≤ u := by positivity
      nlinarith

/-- Canonical power-scale parameters for the first (triple) AKS stage. -/
noncomputable def initialSelectedSize (r : ℕ) : ℕ :=
  Nat.floor ((r : ℝ) ^ (3 / 4 : ℝ))

noncomputable def initialWorkingSize (r : ℕ) : ℕ := r - initialSelectedSize r

noncomputable def initialFamilySize (r : ℕ) : ℕ :=
  Nat.floor ((initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ))

noncomputable def initialNextThreshold (r : ℕ) : ℕ :=
  Nat.floor ((initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ))

noncomputable def initialDegreeThreshold (r Q : ℕ) : ℕ :=
  ceilingQuotient (initialWorkingSize r) Q

noncomputable def initialNonneighborThreshold (r : ℕ) : ℕ :=
  ceilingQuotient (initialWorkingSize r) 3

/-- The rounded lower bounds `ell >= w/Q` and `q >= w/3` cost exactly
`81 Q^4` in the fourth-power triple-selection estimate. -/
lemma tripleSelection_budgets_of_scale_separation
    {w u b d ell q Q : ℕ} (hQ : 0 < Q) (hw : 0 < w)
    (hwell : w ≤ Q * ell) (hwq : w ≤ 3 * q)
    (hfirstScale : 2 * (81 * Q ^ 4) * (b - 1) < u)
    (hsecondScale :
      2 * (81 * Q ^ 4) * (u.choose 3 * (d ^ 4 * w ^ 4)) <
        u * w ^ 8) :
    2 * ((b - 1) * w ^ 8) < u * (ell ^ 4 * q ^ 4) ∧
      2 * (u.choose 3 * (d ^ 4 * w ^ 4)) <
        u * (ell ^ 4 * q ^ 4) := by
  let F : ℕ := 81 * Q ^ 4
  have hF : 0 < F := by
    dsimp only [F]
    positivity
  have hwell4 := Nat.pow_le_pow_left hwell 4
  have hwq4 := Nat.pow_le_pow_left hwq 4
  have hw8 : w ^ 8 ≤ F * (ell ^ 4 * q ^ 4) := by
    calc
      w ^ 8 = w ^ 4 * w ^ 4 := by ring
      _ ≤ (Q * ell) ^ 4 * (3 * q) ^ 4 :=
        Nat.mul_le_mul hwell4 hwq4
      _ = F * (ell ^ 4 * q ^ 4) := by
        dsimp only [F]
        ring
  have htarget :
      u * w ^ 8 ≤ (u * (ell ^ 4 * q ^ 4)) * F := by
    calc
      u * w ^ 8 ≤ u * (F * (ell ^ 4 * q ^ 4)) :=
        Nat.mul_le_mul_left u hw8
      _ = (u * (ell ^ 4 * q ^ 4)) * F := by ring
  constructor
  · have hscaled := Nat.mul_lt_mul_of_pos_right hfirstScale (pow_pos hw 8)
    have hmul :
        (2 * ((b - 1) * w ^ 8)) * F <
          (u * (ell ^ 4 * q ^ 4)) * F := by
      calc
        (2 * ((b - 1) * w ^ 8)) * F =
            (2 * F * (b - 1)) * w ^ 8 := by ring
        _ < u * w ^ 8 := hscaled
        _ ≤ (u * (ell ^ 4 * q ^ 4)) * F := htarget
    exact (Nat.mul_lt_mul_right hF).mp hmul
  · have hmul :
        (2 * (u.choose 3 * (d ^ 4 * w ^ 4))) * F <
          (u * (ell ^ 4 * q ^ 4)) * F := by
      calc
        (2 * (u.choose 3 * (d ^ 4 * w ^ 4))) * F =
            2 * F * (u.choose 3 * (d ^ 4 * w ^ 4)) := by ring
        _ < u * w ^ 8 := hsecondScale
        _ ≤ (u * (ell ^ 4 * q ^ 4)) * F := htarget
    exact (Nat.mul_lt_mul_right hF).mp hmul

/-- The two scale-separation hypotheses used above follow from a linear
family-size gap and a quadratic selected-set gap. -/
lemma tripleScaleSeparation_of_quadratic_gaps
    {w u b d Q : ℕ}
    (hfamily : 2 * (81 * Q ^ 4) * b < u)
    (hnext : d ^ 2 ≤ w)
    (hselected : 2 * (81 * Q ^ 4) * u ^ 2 < w ^ 2) :
    2 * (81 * Q ^ 4) * (b - 1) < u ∧
      2 * (81 * Q ^ 4) *
          (u.choose 3 * (d ^ 4 * w ^ 4)) < u * w ^ 8 := by
  have hu : 0 < u := by omega
  have hw : 0 < w := by
    have : 0 < w ^ 2 := lt_of_le_of_lt (Nat.zero_le _) hselected
    exact Nat.pos_of_ne_zero (fun hw => by simp [hw] at this)
  have hchoose : u.choose 3 ≤ u ^ 3 := Nat.choose_le_pow u 3
  have hnext4 : d ^ 4 ≤ w ^ 2 := by
    calc
      d ^ 4 = (d ^ 2) ^ 2 := by ring
      _ ≤ w ^ 2 := Nat.pow_le_pow_left hnext 2
  constructor
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul_left (2 * (81 * Q ^ 4)) (Nat.sub_le b 1)) hfamily
  · calc
      2 * (81 * Q ^ 4) *
          (u.choose 3 * (d ^ 4 * w ^ 4)) ≤
          2 * (81 * Q ^ 4) * (u ^ 3 * (w ^ 2 * w ^ 4)) := by
        gcongr
      _ = (2 * (81 * Q ^ 4) * u ^ 2) * (u * w ^ 6) := by ring
      _ < w ^ 2 * (u * w ^ 6) :=
        Nat.mul_lt_mul_of_pos_right hselected
          (mul_pos hu (pow_pos hw 6))
      _ = u * w ^ 8 := by ring

lemma half_le_natFloor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hlt := Nat.lt_floor_add_one x
  linarith

lemma initialSelectedSize_cast_le (r : ℕ) :
    (initialSelectedSize r : ℝ) ≤ (r : ℝ) ^ (3 / 4 : ℝ) := by
  unfold initialSelectedSize
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

lemma half_rpow_le_initialSelectedSize {r : ℕ}
    (hlarge : 2 ≤ (r : ℝ) ^ (3 / 4 : ℝ)) :
    (r : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ initialSelectedSize r := by
  unfold initialSelectedSize
  exact half_le_natFloor hlarge

lemma initialFamilySize_cast_le (r : ℕ) :
    (initialFamilySize r : ℝ) ≤
      (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) := by
  unfold initialFamilySize
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

lemma half_rpow_le_initialFamilySize {r : ℕ}
    (hlarge : 2 ≤ (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ)) :
    (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) / 2 ≤
      initialFamilySize r := by
  unfold initialFamilySize
  exact half_le_natFloor hlarge

lemma initialNextThreshold_sq_le (r : ℕ) :
    initialNextThreshold r ^ 2 ≤ initialWorkingSize r := by
  have hfloor : (initialNextThreshold r : ℝ) ≤
      (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) := by
    unfold initialNextThreshold
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  rw [← Real.sqrt_eq_rpow] at hfloor
  have hsquare := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ initialNextThreshold r) hfloor 2
  rw [Real.sq_sqrt (by positivity)] at hsquare
  exact_mod_cast hsquare

lemma half_card_le_initialWorkingSize {r : ℕ}
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ)) :
    r / 2 ≤ initialWorkingSize r := by
  have hrpos : (0 : ℝ) < r := by
    by_contra hr
    have hr0real : (r : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hr) (by positivity)
    have hr0 : r = 0 := by exact_mod_cast hr0real
    norm_num [hr0] at hquarter
  have hprod :
      (r : ℝ) ^ (3 / 4 : ℝ) * (r : ℝ) ^ (1 / 4 : ℝ) = r := by
    rw [← Real.rpow_add hrpos]
    norm_num
  have hpow : 2 * (r : ℝ) ^ (3 / 4 : ℝ) ≤ r := by
    have hmul := mul_le_mul_of_nonneg_left hquarter
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (3 / 4 : ℝ))
    rw [hprod] at hmul
    simpa [mul_comm] using hmul
  have hselected : 2 * initialSelectedSize r ≤ r := by
    exact_mod_cast (show
      2 * (initialSelectedSize r : ℝ) ≤ r by
        nlinarith [initialSelectedSize_cast_le r])
  unfold initialWorkingSize
  omega

lemma initialFamily_scale_separation
    {r Q : ℕ} (hr : 0 < r)
    (hselectedLarge : 2 ≤ (r : ℝ) ^ (3 / 4 : ℝ))
    (hgap : (4 * (81 * Q ^ 4) : ℝ) < (r : ℝ) ^ (3 / 20 : ℝ)) :
    2 * (81 * Q ^ 4) * initialFamilySize r < initialSelectedSize r := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hwle : initialWorkingSize r ≤ r := by
    unfold initialWorkingSize
    omega
  have hwleReal : (initialWorkingSize r : ℝ) ≤ r := by exact_mod_cast hwle
  have hpowMono :
      (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) ≤
        (r : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hwleReal (by norm_num)
  have hfamily : (initialFamilySize r : ℝ) ≤
      (r : ℝ) ^ (3 / 5 : ℝ) :=
    (initialFamilySize_cast_le r).trans hpowMono
  have hselected : (r : ℝ) ^ (3 / 4 : ℝ) / 2 ≤
      initialSelectedSize r :=
    half_rpow_le_initialSelectedSize hselectedLarge
  have hmul := mul_lt_mul_of_pos_right hgap
    (Real.rpow_pos_of_pos hrReal (3 / 5 : ℝ))
  have hpow :
      (r : ℝ) ^ (3 / 20 : ℝ) * (r : ℝ) ^ (3 / 5 : ℝ) =
        (r : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hrReal]
    norm_num
  rw [hpow] at hmul
  have hstrict :
      (2 * (81 * Q ^ 4) : ℝ) * (r : ℝ) ^ (3 / 5 : ℝ) <
        (r : ℝ) ^ (3 / 4 : ℝ) / 2 := by
    nlinarith
  have hreal :
      (2 * (81 * Q ^ 4) * initialFamilySize r : ℕ) <
        (initialSelectedSize r : ℝ) := by
    push_cast
    exact (mul_le_mul_of_nonneg_left hfamily
      (by positivity : (0 : ℝ) ≤ 2 * (81 * Q ^ 4))).trans_lt
        (hstrict.trans_le hselected)
  exact_mod_cast hreal

lemma initialSelected_quadratic_separation
    {r Q : ℕ} (hr : 4 ≤ r)
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ))
    (hgap : (32 * (81 * Q ^ 4) : ℝ) < (r : ℝ) ^ (1 / 2 : ℝ)) :
    2 * (81 * Q ^ 4) * initialSelectedSize r ^ 2 <
      initialWorkingSize r ^ 2 := by
  have hrPos : 0 < r := by omega
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hrPos
  have hselected := initialSelectedSize_cast_le r
  have hselectedSq : (initialSelectedSize r : ℝ) ^ 2 ≤
      (r : ℝ) ^ (3 / 2 : ℝ) := by
    have hsquare := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ initialSelectedSize r) hselected 2
    calc
      (initialSelectedSize r : ℝ) ^ 2 ≤
          ((r : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := hsquare
      _ = (r : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hrReal)]
        norm_num
  have hhalfNat := half_card_le_initialWorkingSize hquarter
  have hhalfCast : ((r / 2 : ℕ) : ℝ) ≤ initialWorkingSize r := by
    exact_mod_cast hhalfNat
  have hdecompNat := Nat.div_add_mod r 2
  have hmodNat := Nat.mod_lt r (by norm_num : 0 < (2 : ℕ))
  have hdecomp :
      (2 : ℝ) * ((r / 2 : ℕ) : ℝ) + (r % 2 : ℕ) = r := by
    exact_mod_cast hdecompNat
  have hmod : ((r % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hmodNat
  have hworking : (r : ℝ) / 4 ≤ initialWorkingSize r := by
    have hrFour : (4 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hworkingSq : (r : ℝ) ^ 2 / 16 ≤
      (initialWorkingSize r : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((initialWorkingSize r : ℝ) - (r : ℝ) / 4)]
  have hmul := mul_lt_mul_of_pos_right hgap
    (Real.rpow_pos_of_pos hrReal (3 / 2 : ℝ))
  have hpow :
      (r : ℝ) ^ (1 / 2 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) =
        (r : ℝ) ^ 2 := by
    rw [← Real.rpow_add hrReal]
    norm_num [Real.rpow_two]
  rw [hpow] at hmul
  have hstrict :
      (2 * (81 * Q ^ 4) : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) <
        (r : ℝ) ^ 2 / 16 := by
    nlinarith
  have hreal :
      (2 * (81 * Q ^ 4) * initialSelectedSize r ^ 2 : ℕ) <
        (initialWorkingSize r ^ 2 : ℕ) := by
    exact_mod_cast
      ((mul_le_mul_of_nonneg_left hselectedSq
        (by positivity : (0 : ℝ) ≤ 2 * (81 * Q ^ 4))).trans_lt
          (hstrict.trans_le hworkingSq))
  exact hreal

lemma eventually_initialPowerGaps (Q : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop,
      (4 * (81 * Q ^ 4) : ℝ) < (r : ℝ) ^ (3 / 20 : ℝ) ∧
      (32 * (81 * Q ^ 4) : ℝ) < (r : ℝ) ^ (1 / 2 : ℝ) ∧
      2 ≤ (r : ℝ) ^ (1 / 4 : ℝ) ∧
      2 ≤ (r : ℝ) ^ (3 / 4 : ℝ) ∧ 4 ≤ r := by
  have hpow (a : ℝ) (ha : 0 < a) (A : ℝ) :
      ∀ᶠ r : ℕ in Filter.atTop, A < (r : ℝ) ^ a := by
    have ht : Filter.Tendsto (fun r : ℕ ↦ (r : ℝ) ^ a)
        Filter.atTop Filter.atTop := by
      convert (tendsto_rpow_atTop ha).comp
        tendsto_natCast_atTop_atTop using 1
      funext r
      rfl
    have hge := ht.eventually (Filter.eventually_ge_atTop (A + 1))
    filter_upwards [hge] with r hr
    linarith
  filter_upwards
    [hpow (3 / 20 : ℝ) (by norm_num) (4 * (81 * Q ^ 4) : ℝ),
      hpow (1 / 2 : ℝ) (by norm_num) (32 * (81 * Q ^ 4) : ℝ),
      hpow (1 / 4 : ℝ) (by norm_num) 2,
      hpow (3 / 4 : ℝ) (by norm_num) 2,
      (Filter.eventually_ge_atTop 4 : ∀ᶠ r : ℕ in Filter.atTop, 4 ≤ r)]
      with r hfirst hsecond hquarter hselected hr
  exact ⟨hfirst, hsecond, hquarter.le, hselected.le, hr⟩

/-- For each fixed ratio parameter `Q`, all numerical budgets of the
canonical initial triple stage hold beyond one natural-number threshold. -/
theorem eventually_initialScaleSeparation (Q : ℕ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      0 < initialWorkingSize r ∧
      2 * (81 * Q ^ 4) * (initialFamilySize r - 1) <
        initialSelectedSize r ∧
      2 * (81 * Q ^ 4) *
          ((initialSelectedSize r).choose 3 *
            (initialNextThreshold r ^ 4 * initialWorkingSize r ^ 4)) <
        initialSelectedSize r * initialWorkingSize r ^ 8 := by
  have hevent := eventually_initialPowerGaps Q
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, ?_⟩
  intro r hr
  obtain ⟨hgapFamily, hgapSelected, hquarter, hselectedLarge, hr4⟩ := hN r hr
  have hhalf := half_card_le_initialWorkingSize hquarter
  have hworking : 0 < initialWorkingSize r := by omega
  have hfamily := initialFamily_scale_separation (by omega) hselectedLarge
    hgapFamily
  have hselected := initialSelected_quadratic_separation hr4 hquarter
    hgapSelected
  have hscales := tripleScaleSeparation_of_quadratic_gaps hfamily
    (initialNextThreshold_sq_le r) hselected
  exact ⟨hworking, hscales.1, hscales.2⟩

/-- We use the slightly larger `n^(1/4)` threshold in the finite AKS
construction; it automatically dominates the `n^(1/5)` balancedness scale
and is still far below the initial `n^(3/5)` family. -/
noncomputable def balanceThreshold (r : ℕ) : ℕ :=
  Nat.ceil ((r : ℝ) ^ (1 / 4 : ℝ))

lemma rpow_quarter_le_balanceThreshold (r : ℕ) :
    (r : ℝ) ^ (1 / 4 : ℝ) ≤ balanceThreshold r := by
  unfold balanceThreshold
  exact Nat.le_ceil _

lemma balanceThreshold_lt_rpow_add_one (r : ℕ) :
    (balanceThreshold r : ℝ) < (r : ℝ) ^ (1 / 4 : ℝ) + 1 := by
  unfold balanceThreshold
  exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)

lemma quarter_card_le_initialWorkingSize_real {r : ℕ}
    (hr : 4 ≤ r) (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ)) :
    (r : ℝ) / 4 ≤ initialWorkingSize r := by
  have hhalfNat := half_card_le_initialWorkingSize hquarter
  have hhalfCast : ((r / 2 : ℕ) : ℝ) ≤ initialWorkingSize r := by
    exact_mod_cast hhalfNat
  have hdecompNat := Nat.div_add_mod r 2
  have hmodNat := Nat.mod_lt r (by norm_num : 0 < (2 : ℕ))
  have hdecomp :
      (2 : ℝ) * ((r / 2 : ℕ) : ℝ) + (r % 2 : ℕ) = r := by
    exact_mod_cast hdecompNat
  have hmod : ((r % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hmodNat
  have hrFour : (4 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

lemma quarter_sqrt_le_initialNextThreshold
    {r : ℕ} (hr : 16 ≤ r)
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ)) :
    (r : ℝ) ^ (1 / 2 : ℝ) / 4 ≤ initialNextThreshold r := by
  have hworking := quarter_card_le_initialWorkingSize_real
    (by omega : 4 ≤ r) hquarter
  have hrReal : (16 : ℝ) ≤ r := by exact_mod_cast hr
  have hworkingFour : (4 : ℝ) ≤ initialWorkingSize r := by
    linarith
  have hworkingSqrt :
      2 ≤ (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) := by
    have hfour : (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    calc
      (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := hfour
      _ ≤ (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (z := (1 / 2 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 4) hworkingFour (by norm_num)
  have hscale :
      (r : ℝ) ^ (1 / 2 : ℝ) / 2 ≤
        (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) := by
    have hmono : ((r : ℝ) / 4) ^ (1 / 2 : ℝ) ≤
        (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hworking (by norm_num)
    have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4),
      hfour] at hmono
    exact hmono
  have hfloor :
      (initialWorkingSize r : ℝ) ^ (1 / 2 : ℝ) / 2 ≤
        initialNextThreshold r := by
    unfold initialNextThreshold
    exact half_le_natFloor hworkingSqrt
  linarith

lemma eighth_rpow_le_initialFamilySize
    {r : ℕ} (hr : 4 ≤ r)
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ))
    (hworkingPower :
      2 ≤ (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ)) :
    (r : ℝ) ^ (3 / 5 : ℝ) / 8 ≤ initialFamilySize r := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hworking := quarter_card_le_initialWorkingSize_real hr hquarter
  have hmono : ((r : ℝ) / 4) ^ (3 / 5 : ℝ) ≤
      (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hworking (by norm_num)
  have hfourPow : (4 : ℝ) ^ (3 / 5 : ℝ) ≤ 4 := by
    calc
      (4 : ℝ) ^ (3 / 5 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 4 by norm_num)
          (show (3 / 5 : ℝ) ≤ 1 by norm_num)
      _ = 4 := Real.rpow_one 4
  have hpowPos : 0 < (4 : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hscale : (r : ℝ) ^ (3 / 5 : ℝ) / 4 ≤
      ((r : ℝ) / 4) ^ (3 / 5 : ℝ) := by
    rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
      hpowPos hfourPow
  have hfloor := half_rpow_le_initialFamilySize hworkingPower
  calc
    (r : ℝ) ^ (3 / 5 : ℝ) / 8 ≤
        (((r : ℝ) / 4) ^ (3 / 5 : ℝ)) / 2 := by linarith
    _ ≤ ((initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ)) / 2 := by
      exact div_le_div_of_nonneg_right hmono (by norm_num)
    _ ≤ initialFamilySize r := hfloor

/-- Once the three power scales in the initial AKS stage are separated by
fixed constants, every remaining linear size, degree, and balancedness
side condition follows. -/
lemma initialSideConditions_of_power_bounds
    {gamma : ℝ} {r : ℕ}
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hr : 16 ≤ r)
    (hquarter : 24 ≤ (r : ℝ) ^ (1 / 4 : ℝ))
    (hthreeQuarter : 24 ≤ (r : ℝ) ^ (3 / 4 : ℝ))
    (hgammaQuarter : 32 ≤ gamma * (r : ℝ) ^ (1 / 4 : ℝ))
    (hsevenTwentieths : 16 ≤ (r : ℝ) ^ (7 / 20 : ℝ))
    (hgammaSevenTwentieths :
      32 ≤ gamma * (r : ℝ) ^ (7 / 20 : ℝ)) :
    balanceThreshold r + initialSelectedSize r ≤ r / 2 ∧
      (8 : ℝ) * (initialSelectedSize r + 3) ≤ gamma * r ∧
      2 ≤ balanceThreshold r ∧
      balanceThreshold r ≤ initialFamilySize r ∧
      (balanceThreshold r : ℝ) ≤
        gamma * ((initialFamilySize r : ℝ) - 1) ∧
      0 < initialFamilySize r ∧
      12 * initialSelectedSize r + 12 ≤ r := by
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (by omega : 0 < r)
  have hquarterTwo : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ) := by
    linarith
  have hworkingLower := quarter_card_le_initialWorkingSize_real
    (by omega : 4 ≤ r) hquarterTwo
  have hworkingFour : (4 : ℝ) ≤ initialWorkingSize r := by
    have hrReal : (16 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hworkingPower :
      2 ≤ (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) := by
    have hbase : (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    calc
      (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := hbase
      _ ≤ (4 : ℝ) ^ (3 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ (initialWorkingSize r : ℝ) ^ (3 / 5 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hworkingFour (by norm_num)
  have hfamilyLower := eighth_rpow_le_initialFamilySize
    (by omega : 4 ≤ r) hquarterTwo hworkingPower
  have hselectedUpper := initialSelectedSize_cast_le r
  have hthresholdUpper := balanceThreshold_lt_rpow_add_one r
  have hquarterThreeQuarter :
      (r : ℝ) ^ (1 / 4 : ℝ) * (r : ℝ) ^ (3 / 4 : ℝ) = r := by
    rw [← Real.rpow_add hrpos]
    norm_num
  have hquarterFamily :
      (r : ℝ) ^ (1 / 4 : ℝ) *
          (r : ℝ) ^ (7 / 20 : ℝ) =
        (r : ℝ) ^ (3 / 5 : ℝ) := by
    rw [← Real.rpow_add hrpos]
    norm_num
  have hroomReal :
      (2 * (balanceThreshold r + initialSelectedSize r) : ℕ) <
        (r : ℝ) := by
    push_cast
    nlinarith
  have hroomTwice :
      2 * (balanceThreshold r + initialSelectedSize r) ≤ r := by
    exact_mod_cast (le_of_lt hroomReal)
  have hroom : balanceThreshold r + initialSelectedSize r ≤ r / 2 := by
    omega
  have hdegreeReal :
      (8 : ℝ) * (initialSelectedSize r + 3) ≤ gamma * r := by
    have hmul := mul_le_mul_of_nonneg_right hgammaQuarter
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (3 / 4 : ℝ))
    rw [mul_assoc, hquarterThreeQuarter] at hmul
    nlinarith
  have htTwo : 2 ≤ balanceThreshold r := by
    have hthresholdLower := rpow_quarter_le_balanceThreshold r
    exact_mod_cast (hquarterTwo.trans hthresholdLower)
  have hfamilyScale :
      2 * (r : ℝ) ^ (1 / 4 : ℝ) ≤
        (r : ℝ) ^ (3 / 5 : ℝ) / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hsevenTwentieths
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (1 / 4 : ℝ))
    rw [hquarterFamily] at hmul
    nlinarith
  have htbReal : (balanceThreshold r : ℝ) ≤ initialFamilySize r := by
    exact le_of_lt (hthresholdUpper.trans_le
      ((show (r : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
          2 * (r : ℝ) ^ (1 / 4 : ℝ) by linarith).trans
        (hfamilyScale.trans hfamilyLower)))
  have htb : balanceThreshold r ≤ initialFamilySize r := by
    exact_mod_cast htbReal
  have hfamilyPositive : 0 < initialFamilySize r := by omega
  have hgammaFamilyScale :
      4 * (r : ℝ) ^ (1 / 4 : ℝ) ≤
        gamma * ((r : ℝ) ^ (3 / 5 : ℝ) / 8) := by
    have hmul := mul_le_mul_of_nonneg_right hgammaSevenTwentieths
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (1 / 4 : ℝ))
    have hmul' :
        32 * (r : ℝ) ^ (1 / 4 : ℝ) ≤
          gamma * (r : ℝ) ^ (3 / 5 : ℝ) := by
      calc
        32 * (r : ℝ) ^ (1 / 4 : ℝ) ≤
            (gamma * (r : ℝ) ^ (7 / 20 : ℝ)) *
              (r : ℝ) ^ (1 / 4 : ℝ) := hmul
        _ = gamma * (r : ℝ) ^ (3 / 5 : ℝ) := by
          rw [← hquarterFamily]
          ring
    nlinarith
  have hlarge : (balanceThreshold r : ℝ) ≤
      gamma * ((initialFamilySize r : ℝ) - 1) := by
    have hscaledFamily := mul_le_mul_of_nonneg_left hfamilyLower hgamma.le
    have hthresholdMargin :
        (r : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
          gamma * ((r : ℝ) ^ (3 / 5 : ℝ) / 8 - 1) := by
      nlinarith
    exact le_of_lt (hthresholdUpper.trans_le
      (hthresholdMargin.trans (by nlinarith)))
  have hcapacityReal :
      (12 * initialSelectedSize r + 12 : ℕ) ≤ (r : ℝ) := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_right hquarter
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (3 / 4 : ℝ))
    rw [hquarterThreeQuarter] at hmul
    nlinarith
  have hcapacity : 12 * initialSelectedSize r + 12 ≤ r := by
    exact_mod_cast hcapacityReal
  exact ⟨hroom, hdegreeReal, htTwo, htb, hlarge,
    hfamilyPositive, hcapacity⟩

/-- For every fixed positive balancedness constant, all elementary
side conditions of the canonical initial triple stage hold eventually. -/
theorem eventually_initialSideConditions
    (gamma : ℝ) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      balanceThreshold r + initialSelectedSize r ≤ r / 2 ∧
      (8 : ℝ) * (initialSelectedSize r + 3) ≤ gamma * r ∧
      2 ≤ balanceThreshold r ∧
      balanceThreshold r ≤ initialFamilySize r ∧
      (balanceThreshold r : ℝ) ≤
        gamma * ((initialFamilySize r : ℝ) - 1) ∧
      0 < initialFamilySize r ∧
      12 * initialSelectedSize r + 12 ≤ r := by
  have hpow (a : ℝ) (ha : 0 < a) (A : ℝ) :
      ∀ᶠ r : ℕ in Filter.atTop, A < (r : ℝ) ^ a := by
    have ht : Filter.Tendsto (fun r : ℕ ↦ (r : ℝ) ^ a)
        Filter.atTop Filter.atTop := by
      convert (tendsto_rpow_atTop ha).comp
        tendsto_natCast_atTop_atTop using 1
      funext r
      rfl
    have hge := ht.eventually (Filter.eventually_ge_atTop (A + 1))
    filter_upwards [hge] with r hr
    linarith
  have hevent : ∀ᶠ r : ℕ in Filter.atTop,
      24 < (r : ℝ) ^ (1 / 4 : ℝ) ∧
      24 < (r : ℝ) ^ (3 / 4 : ℝ) ∧
      32 / gamma < (r : ℝ) ^ (1 / 4 : ℝ) ∧
      16 < (r : ℝ) ^ (7 / 20 : ℝ) ∧
      32 / gamma < (r : ℝ) ^ (7 / 20 : ℝ) ∧
      16 ≤ r := by
    filter_upwards
      [hpow (1 / 4 : ℝ) (by norm_num) 24,
        hpow (3 / 4 : ℝ) (by norm_num) 24,
        hpow (1 / 4 : ℝ) (by norm_num) (32 / gamma),
        hpow (7 / 20 : ℝ) (by norm_num) 16,
        hpow (7 / 20 : ℝ) (by norm_num) (32 / gamma),
        (Filter.eventually_ge_atTop 16 :
          ∀ᶠ r : ℕ in Filter.atTop, 16 ≤ r)]
        with r hquarter hthreeQuarter hgammaQuarter
          hsevenTwentieths hgammaSevenTwentieths hr
    exact ⟨hquarter, hthreeQuarter, hgammaQuarter,
      hsevenTwentieths, hgammaSevenTwentieths, hr⟩
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, ?_⟩
  intro r hr
  obtain ⟨hquarter, hthreeQuarter, hgammaQuarter,
    hsevenTwentieths, hgammaSevenTwentieths, hr16⟩ := hN r hr
  have hgammaQuarter' :
      32 ≤ gamma * (r : ℝ) ^ (1 / 4 : ℝ) := by
    have := (div_lt_iff₀ hgamma).mp hgammaQuarter
    nlinarith
  have hgammaSevenTwentieths' :
      32 ≤ gamma * (r : ℝ) ^ (7 / 20 : ℝ) := by
    have := (div_lt_iff₀ hgamma).mp hgammaSevenTwentieths
    nlinarith
  exact initialSideConditions_of_power_bounds hgamma hgamma1 hr16
    hquarter.le hthreeQuarter.le hgammaQuarter'
    hsevenTwentieths.le hgammaSevenTwentieths'

/-- A canonical integer ratio parameter for the initial degree buckets. -/
noncomputable def initialRatioParameter (gamma : ℝ) : ℕ :=
  Nat.ceil (8 / gamma) + 1

lemma initialRatioParameter_pos (gamma : ℝ) :
    0 < initialRatioParameter gamma := by
  unfold initialRatioParameter
  omega

lemma eight_le_gamma_mul_initialRatioParameter
    {gamma : ℝ} (hgamma : 0 < gamma) :
    8 ≤ gamma * initialRatioParameter gamma := by
  have hceil : 8 / gamma ≤ (Nat.ceil (8 / gamma) : ℝ) :=
    Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hgamma.le
  unfold initialRatioParameter
  push_cast
  have hcancel : gamma * (8 / gamma) = 8 := by
    field_simp [ne_of_gt hgamma]
  rw [hcancel] at hmul
  nlinarith

/-- Exact canonical first-stage constructor.  All rounding choices from the
AKS proof are explicit; the hypotheses are precisely the eventual numerical
inequalities that remain to be discharged. -/
theorem exists_initialTripleExtension_of_canonical_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {gamma : ℝ} {t Q : ℕ}
    {Cset : Finset V}
    (hbal : IsBalanced G gamma t)
    (hbalc : IsBalanced Gᶜ gamma t)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ gamma * Q)
    (hroom : t + initialSelectedSize Cset.card ≤ Cset.card / 2)
    (hdegree : (8 : ℝ) * (initialSelectedSize Cset.card + 3) ≤
      gamma * Cset.card)
    (hgamma : 0 < gamma) (ht : 2 ≤ t)
    (htb : t ≤ initialFamilySize Cset.card)
    (hlarge : (t : ℝ) ≤
      gamma * ((initialFamilySize Cset.card : ℝ) - 1))
    (hb : 0 < initialFamilySize Cset.card)
    (hcapacity : 12 * initialSelectedSize Cset.card + 12 ≤ Cset.card)
    (hfirst :
      2 * ((initialFamilySize Cset.card - 1) *
          initialWorkingSize Cset.card ^ 8) <
        initialSelectedSize Cset.card *
          (initialDegreeThreshold Cset.card Q ^ 4 *
            initialNonneighborThreshold Cset.card ^ 4))
    (hsecond :
      2 * ((initialSelectedSize Cset.card).choose 3 *
          (initialNextThreshold Cset.card ^ 4 *
            initialWorkingSize Cset.card ^ 4)) <
        initialSelectedSize Cset.card *
          (initialDegreeThreshold Cset.card Q ^ 4 *
            initialNonneighborThreshold Cset.card ^ 4)) :
    Nonempty (InitialTripleExtension G (initialNextThreshold Cset.card) Cset) := by
  apply exists_initialTripleExtension_of_balanced_budgets
      hbal hbalc hgamma0 hgamma1 hroom
  · exact pairDegreeThreshold_le_of_large hgamma0 hgamma1 hQ
      hgammaQ hdegree
  · exact hgamma
  · exact ht
  · exact htb
  · exact hlarge
  · exact hb
  · exact ceilingNonneighborThreshold_capacity hcapacity
  · exact hfirst
  · exact hsecond

/-- Canonical first-stage constructor with the two polynomial estimates
reduced to their scale-separation forms. -/
theorem exists_initialTripleExtension_of_scale_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {gamma : ℝ} {t Q : ℕ}
    {Cset : Finset V}
    (hbal : IsBalanced G gamma t)
    (hbalc : IsBalanced Gᶜ gamma t)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ gamma * Q)
    (hroom : t + initialSelectedSize Cset.card ≤ Cset.card / 2)
    (hdegree : (8 : ℝ) * (initialSelectedSize Cset.card + 3) ≤
      gamma * Cset.card)
    (hgamma : 0 < gamma) (ht : 2 ≤ t)
    (htb : t ≤ initialFamilySize Cset.card)
    (hlarge : (t : ℝ) ≤
      gamma * ((initialFamilySize Cset.card : ℝ) - 1))
    (hb : 0 < initialFamilySize Cset.card)
    (hcapacity : 12 * initialSelectedSize Cset.card + 12 ≤ Cset.card)
    (hworking : 0 < initialWorkingSize Cset.card)
    (hfirstScale :
      2 * (81 * Q ^ 4) * (initialFamilySize Cset.card - 1) <
        initialSelectedSize Cset.card)
    (hsecondScale :
      2 * (81 * Q ^ 4) *
          ((initialSelectedSize Cset.card).choose 3 *
            (initialNextThreshold Cset.card ^ 4 *
              initialWorkingSize Cset.card ^ 4)) <
        initialSelectedSize Cset.card *
          initialWorkingSize Cset.card ^ 8) :
    Nonempty (InitialTripleExtension G (initialNextThreshold Cset.card) Cset) := by
  have hbudgets := tripleSelection_budgets_of_scale_separation hQ hworking
    (le_mul_ceilingQuotient _ hQ)
    (le_mul_ceilingQuotient _ (by norm_num : 0 < (3 : ℕ)))
    hfirstScale hsecondScale
  exact exists_initialTripleExtension_of_canonical_parameters
    hbal hbalc hgamma0 hgamma1 hQ hgammaQ hroom hdegree hgamma ht htb
    hlarge hb hcapacity hbudgets.1 hbudgets.2

/-- Beyond one size threshold, balancedness alone produces the complete
canonical initial triple extension, including its square-root residual
reservoir. -/
theorem eventually_exists_initialTripleExtension
    (gamma : ℝ) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} {Cset : Finset V},
      N ≤ Cset.card →
      IsBalanced G gamma (balanceThreshold Cset.card) →
      IsBalanced Gᶜ gamma (balanceThreshold Cset.card) →
      Nonempty
        (InitialTripleExtension G (initialNextThreshold Cset.card) Cset) := by
  let Q := initialRatioParameter gamma
  obtain ⟨Nscale, hNscale⟩ := eventually_initialScaleSeparation Q
  obtain ⟨Nside, hNside⟩ :=
    eventually_initialSideConditions gamma hgamma hgamma1
  refine ⟨max Nscale Nside, ?_⟩
  intro V instV instEq G Cset hcard hbal hbalc
  let _ := instV
  let _ := instEq
  have hscale := hNscale Cset.card ((le_max_left _ _).trans hcard)
  have hside := hNside Cset.card ((le_max_right _ _).trans hcard)
  exact exists_initialTripleExtension_of_scale_separation
    hbal hbalc hgamma.le hgamma1 (initialRatioParameter_pos gamma)
    (eight_le_gamma_mul_initialRatioParameter hgamma)
    hside.1 hside.2.1 hgamma hside.2.2.1 hside.2.2.2.1
    hside.2.2.2.2.1 hside.2.2.2.2.2.1 hside.2.2.2.2.2.2
    hscale.1 hscale.2.1 hscale.2.2

lemma rpow_fifth_le_balanceThreshold {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) ^ (1 / 5 : ℝ) ≤ balanceThreshold r := by
  calc
    (r : ℝ) ^ (1 / 5 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hr) (by norm_num)
    _ ≤ balanceThreshold r := rpow_quarter_le_balanceThreshold r

/-- Ramsey-freeness supplies all graph-theoretic and numerical hypotheses
of the initial AKS stage once the ambient order is large enough. -/
theorem ramseyFree_eventually_initialTripleExtension
    (C : ℝ) (hC : 0 < C) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 / 12 ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, N ≤ n → ∀ (G : SimpleGraph (Fin n)),
        RamseyFree C G →
        Nonempty
          (InitialTripleExtension G (initialNextThreshold n)
            (Finset.univ : Finset (Fin n))) := by
  obtain ⟨gamma, hgamma, hgammaSmall, Nbal, hbalanced⟩ :=
    ramseyFree_eventually_balanced_fifth C hC
  obtain ⟨Ninitial, hinitial⟩ :=
    eventually_exists_initialTripleExtension gamma hgamma
      (hgammaSmall.trans (by norm_num))
  have htend : Filter.Tendsto
      (fun r : ℕ ↦ (r : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop using 1
    funext r
    rfl
  have hevent := htend.eventually
    (Filter.eventually_ge_atTop ((Nbal : ℝ) + 1))
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Npower, hNpower⟩ := hevent
  refine ⟨gamma, hgamma, hgammaSmall,
    max 1 (max Ninitial Npower), ?_⟩
  intro n hn G hG
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnInitial : Ninitial ≤ n :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hnPower : Npower ≤ n :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  have hpow := hNpower n hnPower
  have hNbal : Nbal ≤ balanceThreshold n := by
    have hthreshold := rpow_quarter_le_balanceThreshold n
    exact_mod_cast (show (Nbal : ℝ) ≤ balanceThreshold n by
      linarith)
  have hbalances := hbalanced hn1 G hG hNbal
    (rpow_fifth_le_balanceThreshold hn1)
  have hbalUniv : IsBalanced G gamma
      (balanceThreshold (Finset.univ : Finset (Fin n)).card) := by
    simpa using hbalances.1
  have hbalcUniv : IsBalanced Gᶜ gamma
      (balanceThreshold (Finset.univ : Finset (Fin n)).card) := by
    simpa using hbalances.2
  have hresult := hinitial (V := Fin n) (G := G)
    (Cset := Finset.univ) (by simpa using hnInitial) hbalUniv hbalcUniv
  simpa using hresult

/-- The canonical rounded positive-stage parameters satisfy the nonlinear
AKS selection inequality automatically. -/
theorem exists_sizedPairExtension_of_canonical_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ} {t i Q nextMin : ℕ}
    {Cset : Finset V}
    (hbal : IsBalanced G (6 * epsilon) t)
    (hbalc : IsBalanced Gᶜ (6 * epsilon) t)
    (hgamma0 : 0 ≤ 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q)
    (htu : t + pairSelectedSize Q ≤ Cset.card / 2)
    (hlow : (pairDegreeThreshold Cset.card Q : ℝ) ≤
      (6 * epsilon) * (((Cset.card / 2 : ℕ) : ℝ) - 1) -
        (pairSelectedSize Q : ℝ))
    (hi : 1 ≤ i)
    (hq : pairNonneighborThreshold Cset.card Q +
        (Cset.card - 1) / 2 ≤ pairWorkingSize Cset.card Q)
    (hwpos : 0 < pairWorkingSize Cset.card Q)
    (hsize : max t (2 ^ i) ≤ pairNextThreshold Cset.card Q + 1)
    (hnext : nextMin ≤ pairNextThreshold Cset.card Q + 1) :
    Nonempty (SizedPairExtension G epsilon i nextMin Cset) := by
  apply exists_sizedPairExtension_of_ratio hbal hbalc hgamma0 hgamma1
      hQ rfl htu hlow hi hq hwpos
  · exact le_mul_ceilingQuotient _ hQ
  · exact le_mul_ceilingQuotient _ (by norm_num : 0 < (3 : ℕ))
  · rfl
  · exact hsize
  · exact hnext

/-- A positive AKS stage follows from three monotone largeness inequalities
on its source reservoir and the single recurrence inequality for the next
minimum size. -/
theorem exists_sizedPairExtension_of_large_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ} {t i Q nextMin : ℕ}
    {Cset : Finset V}
    (hbal : IsBalanced G (6 * epsilon) t)
    (hbalc : IsBalanced Gᶜ (6 * epsilon) t)
    (hgamma0 : 0 ≤ 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ (6 * epsilon) * Q)
    (hroom : 2 * (t + pairSelectedSize Q) ≤ Cset.card)
    (hcapacity : 12 * pairSelectedSize Q + 12 ≤ Cset.card)
    (hdegree : (8 : ℝ) * (pairSelectedSize Q + 3) ≤
      (6 * epsilon) * Cset.card)
    (hi : 1 ≤ i)
    (hblock : max t (2 ^ i) ≤ nextMin)
    (hnext : nextMin ≤ pairNextThreshold Cset.card Q + 1) :
    Nonempty (SizedPairExtension G epsilon i nextMin Cset) := by
  apply exists_sizedPairExtension_of_canonical_parameters
      hbal hbalc hgamma0 hgamma1 hQ
  · omega
  · exact pairDegreeThreshold_le_of_large hgamma0 hgamma1 hQ
      hgammaQ hdegree
  · exact hi
  · exact pairNonneighborThreshold_capacity hcapacity
  · unfold pairWorkingSize pairSelectedSize at *
    omega
  · exact hblock.trans hnext
  · exact hnext

/-- Backward minimum-reservoir recurrence.  One stage first removes
`18 Q^2` vertices and then keeps a quotient-sized common-nonneighbor set;
the `+2` supplies the exact slack lost by subtraction and rounding. -/
def reservoirRequirement (Q base : ℕ) : ℕ → ℕ
  | 0 => base
  | k + 1 => pairSelectedSize Q * (reservoirRequirement Q base k + 2)

lemma pairSelectedSize_pos {Q : ℕ} (hQ : 0 < Q) :
    0 < pairSelectedSize Q := by
  unfold pairSelectedSize
  positivity

lemma base_le_reservoirRequirement {Q base k : ℕ} (hQ : 0 < Q) :
    base ≤ reservoirRequirement Q base k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [reservoirRequirement]
      calc
        base ≤ reservoirRequirement Q base k + 2 := by omega
        _ ≤ pairSelectedSize Q * (reservoirRequirement Q base k + 2) :=
          Nat.le_mul_of_pos_left _ (pairSelectedSize_pos hQ)

/-- Closed geometric upper bound for the backward reservoir recurrence. -/
lemma reservoirRequirement_add_two_le
    {Q base k : ℕ} (hQ : 0 < Q) :
    reservoirRequirement Q base k + 2 ≤
      (pairSelectedSize Q + 1) ^ k * (base + 2) := by
  induction k with
  | zero => simp [reservoirRequirement]
  | succ k ih =>
      rw [reservoirRequirement, pow_succ]
      have hstep :
          pairSelectedSize Q *
                (reservoirRequirement Q base k + 2) + 2 ≤
            (pairSelectedSize Q + 1) *
              (reservoirRequirement Q base k + 2) := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_le_add_left (by omega) _
      calc
        pairSelectedSize Q *
              (reservoirRequirement Q base k + 2) + 2 ≤
            (pairSelectedSize Q + 1) *
              (reservoirRequirement Q base k + 2) := hstep
        _ ≤ (pairSelectedSize Q + 1) *
              ((pairSelectedSize Q + 1) ^ k * (base + 2)) := by
          gcongr
        _ = (pairSelectedSize Q + 1) ^ k *
              (pairSelectedSize Q + 1) * (base + 2) := by ring

/-- Number of positive AKS stages selected from a reservoir scale `t`.
The subtraction by three is the explicit rounding slack. -/
def logarithmicStageCount (B t : ℕ) : ℕ := Nat.log B t - 3

/-- The integer-log schedule fits the complete backward reservoir
recurrence below the square of its scale parameter. -/
lemma logarithmicSchedule_reservoir_bound
    {Q D B t : ℕ} (hQ : 0 < Q) (ht : 0 < t)
    (huB : pairSelectedSize Q + 1 ≤ B)
    (hDB : D + 2 ≤ B)
    (hlog : 4 ≤ Nat.log B t) :
    B * reservoirRequirement Q (D * t)
        (logarithmicStageCount B t + 1) ≤ t ^ 2 := by
  let L := Nat.log B t
  let K := logarithmicStageCount B t
  have hKL : K + 2 = L - 1 := by
    dsimp only [K, logarithmicStageCount, L]
    omega
  have hpowBase :
      (pairSelectedSize Q + 1) ^ (K + 1) ≤ B ^ (K + 1) :=
    Nat.pow_le_pow_left huB _
  have hbase : D * t + 2 ≤ B * t := by
    calc
      D * t + 2 ≤ D * t + 2 * t := by omega
      _ = (D + 2) * t := by ring
      _ ≤ B * t := Nat.mul_le_mul_right t hDB
  have hrec := reservoirRequirement_add_two_le
    (Q := Q) (base := D * t) (k := K + 1) hQ
  have hR : reservoirRequirement Q (D * t) (K + 1) + 2 ≤
      B ^ (L - 1) * t := by
    calc
      reservoirRequirement Q (D * t) (K + 1) + 2 ≤
          (pairSelectedSize Q + 1) ^ (K + 1) * (D * t + 2) := hrec
      _ ≤ B ^ (K + 1) * (B * t) :=
        Nat.mul_le_mul hpowBase hbase
      _ = B ^ (K + 2) * t := by rw [pow_succ]; ring
      _ = B ^ (L - 1) * t := by rw [hKL]
  have hLpos : 0 < L := by
    dsimp only [L]
    omega
  have hpowL : B ^ L ≤ t := by
    dsimp only [L]
    exact Nat.pow_log_le_self B (Nat.ne_of_gt ht)
  calc
    B * reservoirRequirement Q (D * t) (K + 1) ≤
        B * (B ^ (L - 1) * t) := by
      gcongr
      omega
    _ = B ^ L * t := by
      have hL : L - 1 + 1 = L := by omega
      calc
        B * (B ^ (L - 1) * t) = (B ^ (L - 1) * B) * t := by ring
        _ = B ^ (L - 1 + 1) * t := by rw [pow_succ]
        _ = B ^ L * t := by rw [hL]
    _ ≤ t * t := Nat.mul_le_mul_right t hpowL
    _ = t ^ 2 := by ring

/-- The initial square-root reservoir dominates the squared balancedness
threshold with the fixed slack needed by the integer-log schedule. -/
lemma balanceThreshold_sq_le_mul_initialNextThreshold
    {B r : ℕ} (hB : 16 ≤ B) (hr : 16 ≤ r)
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ)) :
    balanceThreshold r ^ 2 ≤ B * initialNextThreshold r := by
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (by omega : 0 < r)
  have hnext := quarter_sqrt_le_initialNextThreshold hr hquarter
  have hthreshold := balanceThreshold_lt_rpow_add_one r
  have hpow :
      ((r : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
        (r : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hrpos)]
    norm_num
  have hBReal : (16 : ℝ) ≤ B := by exact_mod_cast hB
  have hscaled := mul_le_mul_of_nonneg_left hnext
    (show (0 : ℝ) ≤ B by positivity)
  have hreal :
      ((balanceThreshold r ^ 2 : ℕ) : ℝ) ≤
        (B * initialNextThreshold r : ℕ) := by
    push_cast
    nlinarith [sq_nonneg
      ((r : ℝ) ^ (1 / 4 : ℝ) - 1)]
  exact_mod_cast hreal

/-- Fixed multiplier making the positive-stage degree estimate automatic. -/
noncomputable def positiveStageMultiplier (gamma : ℝ) (Q : ℕ) : ℕ :=
  max 4
    (Nat.ceil ((8 : ℝ) * (pairSelectedSize Q + 3) / gamma) + 1)

/-- Integer logarithm base used for the positive-stage schedule. -/
noncomputable def positiveStageLogBase (gamma : ℝ) (Q : ℕ) : ℕ :=
  max 16 (max (pairSelectedSize Q + 1)
    (positiveStageMultiplier gamma Q + 2))

lemma four_le_positiveStageMultiplier (gamma : ℝ) (Q : ℕ) :
    4 ≤ positiveStageMultiplier gamma Q := by
  exact le_max_left _ _

lemma positiveStageMultiplier_pos (gamma : ℝ) (Q : ℕ) :
    0 < positiveStageMultiplier gamma Q := by
  exact lt_of_lt_of_le (by norm_num) (four_le_positiveStageMultiplier gamma Q)

lemma positiveStage_degree_bound {gamma : ℝ} (hgamma : 0 < gamma)
    (Q : ℕ) :
    (8 : ℝ) * (pairSelectedSize Q + 3) ≤
      gamma * positiveStageMultiplier gamma Q := by
  have hceil :
      (8 : ℝ) * (pairSelectedSize Q + 3) / gamma ≤
        Nat.ceil ((8 : ℝ) * (pairSelectedSize Q + 3) / gamma) :=
    Nat.le_ceil _
  have hDnat :
      Nat.ceil ((8 : ℝ) * (pairSelectedSize Q + 3) / gamma) ≤
        positiveStageMultiplier gamma Q := by
    unfold positiveStageMultiplier
    omega
  have hDreal :
      (8 : ℝ) * (pairSelectedSize Q + 3) / gamma ≤
        positiveStageMultiplier gamma Q := by
    exact hceil.trans (by exact_mod_cast hDnat)
  have hmul := mul_le_mul_of_nonneg_left hDreal hgamma.le
  have hcancel :
      gamma * ((8 : ℝ) * (pairSelectedSize Q + 3) / gamma) =
        (8 : ℝ) * (pairSelectedSize Q + 3) := by
    field_simp [ne_of_gt hgamma]
  rwa [hcancel] at hmul

lemma sixteen_le_positiveStageLogBase (gamma : ℝ) (Q : ℕ) :
    16 ≤ positiveStageLogBase gamma Q := le_max_left _ _

lemma selected_add_one_le_positiveStageLogBase (gamma : ℝ) (Q : ℕ) :
    pairSelectedSize Q + 1 ≤ positiveStageLogBase gamma Q := by
  exact (le_max_left _ _).trans (le_max_right _ _)

lemma multiplier_add_two_le_positiveStageLogBase (gamma : ℝ) (Q : ℕ) :
    positiveStageMultiplier gamma Q + 2 ≤
      positiveStageLogBase gamma Q := by
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- The three fixed hypotheses of the positive-stage logarithmic schedule
hold once the ambient order is sufficiently large. -/
theorem eventually_positiveStageThresholds (gamma : ℝ) (Q : ℕ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      16 ≤ r ∧
      2 ≤ (r : ℝ) ^ (1 / 4 : ℝ) ∧
      pairSelectedSize Q ≤ balanceThreshold r ∧
      12 * pairSelectedSize Q + 12 ≤
        positiveStageMultiplier gamma Q * balanceThreshold r ∧
      4 ≤ Nat.log (positiveStageLogBase gamma Q) (balanceThreshold r) := by
  let B := positiveStageLogBase gamma Q
  let A := max (pairSelectedSize Q)
    (max (12 * pairSelectedSize Q + 12) (B ^ 4))
  have htend : Filter.Tendsto
      (fun r : ℕ ↦ (r : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop using 1
    funext r
    rfl
  have hevent := htend.eventually
    (Filter.eventually_ge_atTop ((A : ℝ) + 1))
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Npow, hNpow⟩ := hevent
  refine ⟨max 16 Npow, ?_⟩
  intro r hr
  have hr16 : 16 ≤ r := (le_max_left _ _).trans hr
  have hrPow : Npow ≤ r := (le_max_right _ _).trans hr
  have hpow := hNpow r hrPow
  have hthresholdLower := rpow_quarter_le_balanceThreshold r
  have hAt : A ≤ balanceThreshold r := by
    exact_mod_cast (show (A : ℝ) ≤ balanceThreshold r by linarith)
  have hselected : pairSelectedSize Q ≤ balanceThreshold r :=
    (le_max_left _ _).trans hAt
  have hcapacityRaw : 12 * pairSelectedSize Q + 12 ≤
      balanceThreshold r :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hAt
  have hDpos := positiveStageMultiplier_pos gamma Q
  have hcapacity : 12 * pairSelectedSize Q + 12 ≤
      positiveStageMultiplier gamma Q * balanceThreshold r :=
    hcapacityRaw.trans (Nat.le_mul_of_pos_left _ hDpos)
  have hBpow : B ^ 4 ≤ balanceThreshold r :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hAt
  have hB : 1 < B := by
    dsimp only [B]
    have := sixteen_le_positiveStageLogBase gamma Q
    omega
  have hlog : 4 ≤ Nat.log B (balanceThreshold r) :=
    Nat.le_log_of_pow_le hB hBpow
  have hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ) := by
    have hA2 : 2 ≤ A + 1 := by
      have hB16 : 16 ≤ B := by
        dsimp only [B]
        exact sixteen_le_positiveStageLogBase gamma Q
      have hBA : B ^ 4 ≤ A := by
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      omega
    have hA2real : (2 : ℝ) ≤ A + 1 := by exact_mod_cast hA2
    exact hA2real.trans hpow
  exact ⟨hr16, hquarter, hselected, hcapacity, by
    simpa only [B] using hlog⟩

/-- The integer logarithmic depth still contains a fixed positive power of
the ambient order. -/
lemma rpow_le_two_pow_logarithmicStageCount
    {B n : ℕ} (hB : 16 ≤ B) (hn : 1 ≤ n)
    (hscale :
      4 ≤ Real.log n / (8 * (B : ℝ))) :
    (n : ℝ) ^ (1 / (16 * (B : ℝ))) ≤
      (2 ^ logarithmicStageCount B (balanceThreshold n) : ℕ) := by
  let t := balanceThreshold n
  let L := Nat.log B t
  let K := logarithmicStageCount B t
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ht : 0 < t := by
    dsimp only [t]
    have hpow := rpow_quarter_le_balanceThreshold n
    have hpowPos := Real.rpow_pos_of_pos hnReal (1 / 4 : ℝ)
    exact_mod_cast (show (0 : ℝ) < balanceThreshold n by linarith)
  have hBgt : 1 < B := by omega
  have hBReal : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpowSuccNat : t < B ^ (L + 1) := by
    dsimp only [L]
    exact Nat.lt_pow_succ_log_self hBgt t
  have hpowSuccReal : (t : ℝ) < (B : ℝ) ^ (L + 1) := by
    exact_mod_cast hpowSuccNat
  have hlogUpper :
      Real.log t < (L + 1 : ℕ) * Real.log B := by
    have hmono := (Real.strictMonoOn_log.lt_iff_lt
      (show (0 : ℝ) < t by exact_mod_cast ht)
      (show (0 : ℝ) < (B : ℝ) ^ (L + 1) by positivity)).2
        hpowSuccReal
    rw [Real.log_pow] at hmono
    exact hmono
  have hnt : (n : ℝ) ^ (1 / 4 : ℝ) ≤ t :=
    rpow_quarter_le_balanceThreshold n
  have hlogLower := Real.log_le_log
    (Real.rpow_pos_of_pos hnReal (1 / 4 : ℝ)) hnt
  rw [Real.log_rpow hnReal] at hlogLower
  have hlogB : Real.log B ≤ (B : ℝ) := by
    exact (Real.log_le_sub_one_of_pos hBReal).trans (by linarith)
  have hlogBmul :
      ((L + 1 : ℕ) : ℝ) * Real.log B ≤
        ((L + 1 : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_left hlogB (by positivity)
  have hmain : Real.log n / 4 < ((L + 1 : ℕ) : ℝ) * B := by
    nlinarith
  have hxupper :
      Real.log n / (4 * (B : ℝ)) < ((L + 1 : ℕ) : ℝ) := by
    rw [show Real.log n / (4 * (B : ℝ)) =
      (Real.log n / 4) / B by ring]
    exact (div_lt_iff₀ hBReal).2 hmain
  have hxL :
      Real.log n / (8 * (B : ℝ)) ≤ (L : ℝ) - 3 := by
    have hdouble :
        Real.log n / (4 * (B : ℝ)) =
          2 * (Real.log n / (8 * (B : ℝ))) := by ring
    rw [hdouble] at hxupper
    norm_num at hxupper
    nlinarith
  have hL3 : 3 ≤ L := by
    exact_mod_cast (show (3 : ℝ) ≤ L by linarith)
  have hKcast : (K : ℝ) = (L : ℝ) - 3 := by
    dsimp only [K, logarithmicStageCount]
    rw [Nat.cast_sub (by simpa only [L] using hL3)]
    norm_num
    rfl
  have hxK :
      Real.log n / (8 * (B : ℝ)) ≤ (K : ℝ) := by
    rw [hKcast]
    exact hxL
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact le_of_lt (by nlinarith [Real.log_two_gt_d9])
  have hhalf :
      (Real.log n / (8 * (B : ℝ))) / 2 ≤
        (K : ℝ) * Real.log 2 := by
    calc
      (Real.log n / (8 * (B : ℝ))) / 2 ≤ (K : ℝ) / 2 :=
        div_le_div_of_nonneg_right hxK (by norm_num)
      _ ≤ (K : ℝ) * Real.log 2 := by
        have := mul_le_mul_of_nonneg_left hlogTwo
          (show (0 : ℝ) ≤ K by positivity)
        nlinarith
  have hexponent :
      Real.log n * (1 / (16 * (B : ℝ))) ≤
        (K : ℝ) * Real.log 2 := by
    convert hhalf using 1 <;> field_simp <;> ring
  rw [Real.rpow_def_of_pos hnReal]
  calc
    Real.exp (Real.log n * (1 / (16 * (B : ℝ)))) ≤
        Real.exp ((K : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr hexponent
    _ = ((2 ^ K : ℕ) : ℝ) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ = (2 ^ logarithmicStageCount B (balanceThreshold n) : ℕ) := by
      rfl

lemma succ_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
      omega

/-- Once the logarithmic schedule has passed a fixed depth depending on
`gamma`, its binomial interpolation range absorbs the leading coefficient
`gamma`. -/
lemma two_pow_le_gamma_mul_choose_of_stage
    {gamma : ℝ} (hgamma : 0 < gamma) {J K : ℕ}
    (hJ : J = Nat.ceil (2 / gamma) + 1) (hJK : J ≤ K) :
    (2 ^ K : ℕ) ≤ gamma * ((2 ^ K).choose 2 : ℝ) := by
  let m := 2 ^ K
  have hJpow : J + 1 ≤ 2 ^ J := succ_le_two_pow J
  have hpowMono : 2 ^ J ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hJK
  have hm : J + 1 ≤ m := hJpow.trans hpowMono
  have hceil : 2 / gamma ≤ (Nat.ceil (2 / gamma) : ℝ) :=
    Nat.le_ceil _
  have hceilNat : Nat.ceil (2 / gamma) ≤ m - 1 := by
    rw [hJ] at hm
    omega
  have hratio : 2 / gamma ≤ ((m - 1 : ℕ) : ℝ) :=
    hceil.trans (by exact_mod_cast hceilNat)
  have hgammaM : (2 : ℝ) ≤ gamma * ((m - 1 : ℕ) : ℝ) := by
    have := (div_le_iff₀ hgamma).mp hratio
    nlinarith
  have hchooseNat : 2 * m.choose 2 = m * (m - 1) := by
    rw [Nat.choose_two_right, mul_comm 2]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self m)
  have hchooseReal :
      (2 : ℝ) * (m.choose 2 : ℝ) =
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast hchooseNat
  have hmul := mul_le_mul_of_nonneg_left hgammaM
    (show (0 : ℝ) ≤ m by positivity)
  change (m : ℝ) ≤ gamma * (m.choose 2 : ℝ)
  nlinarith

/-- The complete interpolation range of the logarithmic schedule eventually
dominates a fixed positive power of the ambient order. -/
theorem eventually_rpow_le_gamma_logSchedule
    (gamma : ℝ) (hgamma : 0 < gamma) (B : ℕ) (hB : 16 ≤ B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (1 / (16 * (B : ℝ))) ≤ gamma *
        ((2 ^ logarithmicStageCount B (balanceThreshold n)).choose 2 : ℝ) := by
  let J := Nat.ceil (2 / gamma) + 1
  have hlogTend : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowTend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    rfl
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧
      (32 : ℝ) * B ≤ Real.log n ∧
      (B ^ (J + 3) : ℕ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    filter_upwards
      [(Filter.eventually_ge_atTop 1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n),
        hlogTend.eventually
          (Filter.eventually_ge_atTop ((32 : ℝ) * B)),
        hpowTend.eventually
          (Filter.eventually_ge_atTop ((B ^ (J + 3) : ℕ) : ℝ))]
        with n hn hlog hpow
    exact ⟨hn, hlog, hpow⟩
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hn1, hlogLarge, hpowLarge⟩ := hN n hn
  have hBReal : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hscale : 4 ≤ Real.log n / (8 * (B : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hBReal)).2
    nlinarith
  have hrpow := rpow_le_two_pow_logarithmicStageCount hB hn1 hscale
  have hthreshold := rpow_quarter_le_balanceThreshold n
  have hBpow : B ^ (J + 3) ≤ balanceThreshold n := by
    exact_mod_cast (show ((B ^ (J + 3) : ℕ) : ℝ) ≤
      balanceThreshold n by exact hpowLarge.trans hthreshold)
  have hBlog : J + 3 ≤ Nat.log B (balanceThreshold n) :=
    Nat.le_log_of_pow_le (by omega) hBpow
  have hJK : J ≤ logarithmicStageCount B (balanceThreshold n) := by
    unfold logarithmicStageCount
    omega
  have hcoefficient := two_pow_le_gamma_mul_choose_of_stage hgamma
    (J := J) (K := logarithmicStageCount B (balanceThreshold n)) rfl hJK
  exact hrpow.trans hcoefficient

/-- One step of the backward recurrence is sufficient for the exact
quotient threshold returned by the pair-selection construction. -/
lemma reservoirRequirement_le_pairNextThreshold
    {Q base k r : ℕ} (hQ : 0 < Q)
    (hr : reservoirRequirement Q base (k + 1) ≤ r) :
    reservoirRequirement Q base k ≤ pairNextThreshold r Q + 1 := by
  let u := pairSelectedSize Q
  let x := reservoirRequirement Q base k
  have hu : 0 < u := pairSelectedSize_pos hQ
  have hr' : u * (x + 2) ≤ r := by
    simpa only [reservoirRequirement, u, x] using hr
  have hsplit : u * (x + 2) = (x + 1) * u + u := by
    simp [Nat.mul_add, Nat.mul_comm]
    omega
  rw [hsplit] at hr'
  have huR : u ≤ r := by omega
  have hmul : (x + 1) * u ≤ r - u := by omega
  have hdiv : x + 1 ≤ (r - u) / u :=
    (Nat.le_div_iff_mul_le hu).2 hmul
  unfold pairNextThreshold pairWorkingSize
  change x ≤ (r - u) / u - 1 + 1
  omega

/-- Minimum source size for stage `j` of a chain ending at `terminal`.
Indices at or beyond the terminal simply use the base requirement. -/
def stageMinSize (Q base terminal j : ℕ) : ℕ :=
  reservoirRequirement Q base (terminal - j)

lemma stageMinSize_step {Q base terminal j : ℕ} (hj : j < terminal) :
    stageMinSize Q base terminal j =
      pairSelectedSize Q * (stageMinSize Q base terminal (j + 1) + 2) := by
  have hsub : terminal - j = (terminal - (j + 1)) + 1 := by omega
  rw [stageMinSize, hsub, reservoirRequirement]
  rfl

lemma base_le_stageMinSize {Q base terminal j : ℕ} (hQ : 0 < Q) :
    base ≤ stageMinSize Q base terminal j :=
  base_le_reservoirRequirement hQ

lemma stageMinSize_next_le_pairNextThreshold
    {Q base terminal j r : ℕ} (hQ : 0 < Q) (hj : j < terminal)
    (hr : stageMinSize Q base terminal j ≤ r) :
    stageMinSize Q base terminal (j + 1) ≤
      pairNextThreshold r Q + 1 := by
  rw [stageMinSize_step hj] at hr
  exact reservoirRequirement_le_pairNextThreshold hQ hr

/-- A single base-size threshold, propagated backward by
`stageMinSize`, supplies every positive block in the AKS chain. -/
theorem exists_pairBlockChain_of_large_base
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ} {t K Q base : ℕ}
    {Cset : Finset V}
    (hbal : IsBalanced G (6 * epsilon) t)
    (hbalc : IsBalanced Gᶜ (6 * epsilon) t)
    (hgamma0 : 0 ≤ 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ (6 * epsilon) * Q)
    (hbaseRoom : 2 * (t + pairSelectedSize Q) ≤ base)
    (hbaseCapacity : 12 * pairSelectedSize Q + 12 ≤ base)
    (hbaseDegree : (8 : ℝ) * (pairSelectedSize Q + 3) ≤
      (6 * epsilon) * base)
    (hbaseBlock : max t (2 ^ (K + 1)) ≤ base)
    (hsource : stageMinSize Q base (K + 2) 1 ≤ Cset.card) :
    Nonempty (PairBlockChain G epsilon 1 (K + 1) Cset) := by
  apply PairBlockChain.exists_of_sized_supply
      (stageMinSize Q base (K + 2)) hsource
  intro j hj1 hjtop R hR
  have hjterminal : j < K + 2 := by omega
  have hbaseMin : base ≤ stageMinSize Q base (K + 2) j :=
    base_le_stageMinSize hQ
  have hbaseR : base ≤ R.card := hbaseMin.trans hR
  have hdegreeR : (8 : ℝ) * (pairSelectedSize Q + 3) ≤
      (6 * epsilon) * R.card := by
    have hcast : (base : ℝ) ≤ R.card := by exact_mod_cast hbaseR
    exact hbaseDegree.trans
      (mul_le_mul_of_nonneg_left hcast hgamma0)
  have hjle : j ≤ K + 1 := by omega
  have hpow : 2 ^ j ≤ 2 ^ (K + 1) :=
    Nat.pow_le_pow_right (by norm_num) hjle
  have hblockBase : max t (2 ^ j) ≤ base := by
    exact max_le (le_trans (le_max_left _ _) hbaseBlock)
      (hpow.trans (le_trans (le_max_right _ _) hbaseBlock))
  have hblockNext : max t (2 ^ j) ≤
      stageMinSize Q base (K + 2) (j + 1) :=
    hblockBase.trans (base_le_stageMinSize hQ)
  apply exists_sizedPairExtension_of_large_reservoir
      hbal hbalc hgamma0 hgamma1 hQ hgammaQ
  · exact hbaseRoom.trans hbaseR
  · exact hbaseCapacity.trans hbaseR
  · exact hdegreeR
  · exact hj1
  · exact hblockNext
  · exact stageMinSize_next_le_pairNextThreshold hQ hjterminal hR

/-- Complete finite AKS endpoint after the initial triple has supplied the
first reservoir.  All positive stages are generated internally from one
base-size threshold. -/
theorem hasPrescribedCounts_of_initial_and_large_base
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ}
    {t K M Q base d0 : ℕ} {C0 : Finset V}
    (initial : InitialTripleExtension G d0 C0)
    (hbal : IsBalanced G (6 * epsilon) t)
    (hbalc : IsBalanced Gᶜ (6 * epsilon) t)
    (hgamma0 : 0 ≤ 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ (6 * epsilon) * Q)
    (hbaseRoom : 2 * (t + pairSelectedSize Q) ≤ base)
    (hbaseCapacity : 12 * pairSelectedSize Q + 12 ≤ base)
    (hbaseDegree : (8 : ℝ) * (pairSelectedSize Q + 3) ≤
      (6 * epsilon) * base)
    (hbaseBlock : max t (2 ^ (K + 1)) ≤ base)
    (hstart : stageMinSize Q base (K + 2) 1 ≤ d0 + 1)
    (hK : 1 ≤ K)
    (hM : (M : ℝ) ≤ 6 * epsilon * ((2 ^ K).choose 2 : ℝ)) :
    HasPrescribedCounts G M := by
  have hsource : stageMinSize Q base (K + 2) 1 ≤ initial.Cnext.card := by
    have hlarge := initial.next_large
    exact hstart.trans (by omega)
  obtain ⟨chain⟩ := exists_pairBlockChain_of_large_base hbal hbalc
    hgamma0 hgamma1 hQ hgammaQ hbaseRoom hbaseCapacity hbaseDegree
    hbaseBlock hsource
  exact hasPrescribedCounts_of_initial_and_pairChain initial.initial chain hK hM

/-- Finite AKS endpoint for the canonical integer-log schedule.  Its only
remaining asymptotic inputs are that the balance threshold dominates the
fixed selected set, the fixed capacity bound, and the logarithm has reached
four. -/
theorem hasPrescribedCounts_of_initial_logSchedule
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {epsilon : ℝ} {r M Q : ℕ}
    {C0 : Finset V}
    (initial : InitialTripleExtension G (initialNextThreshold r) C0)
    (hbal : IsBalanced G (6 * epsilon) (balanceThreshold r))
    (hbalc : IsBalanced Gᶜ (6 * epsilon) (balanceThreshold r))
    (hgamma : 0 < 6 * epsilon) (hgamma1 : 6 * epsilon ≤ 1)
    (hQ : 0 < Q) (hgammaQ : 8 ≤ (6 * epsilon) * Q)
    (hr : 16 ≤ r)
    (hquarter : 2 ≤ (r : ℝ) ^ (1 / 4 : ℝ))
    (hselected : pairSelectedSize Q ≤ balanceThreshold r)
    (hcapacity :
      12 * pairSelectedSize Q + 12 ≤
        positiveStageMultiplier (6 * epsilon) Q * balanceThreshold r)
    (hlog : 4 ≤
      Nat.log (positiveStageLogBase (6 * epsilon) Q) (balanceThreshold r))
    (hM : (M : ℝ) ≤ 6 * epsilon *
      ((2 ^ logarithmicStageCount
        (positiveStageLogBase (6 * epsilon) Q) (balanceThreshold r)).choose 2 : ℝ)) :
    HasPrescribedCounts G M := by
  let gamma := 6 * epsilon
  let t := balanceThreshold r
  let D := positiveStageMultiplier gamma Q
  let B := positiveStageLogBase gamma Q
  let K := logarithmicStageCount B t
  have hD4 : 4 ≤ D := by
    dsimp only [D, gamma]
    exact four_le_positiveStageMultiplier _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD4
  have hB16 : 16 ≤ B := by
    dsimp only [B, gamma]
    exact sixteen_le_positiveStageLogBase _ _
  have hBpos : 0 < B := by omega
  have huB : pairSelectedSize Q + 1 ≤ B := by
    dsimp only [B, gamma]
    exact selected_add_one_le_positiveStageLogBase _ _
  have hDB : D + 2 ≤ B := by
    dsimp only [B, D, gamma]
    exact multiplier_add_two_le_positiveStageLogBase _ _
  have htu : pairSelectedSize Q ≤ t := by
    simpa only [t] using hselected
  have ht : 0 < t := (pairSelectedSize_pos hQ).trans_le htu
  have hlogLocal : 4 ≤ Nat.log B t := by
    simpa only [B, t, gamma] using hlog
  have hbaseRoom : 2 * (t + pairSelectedSize Q) ≤ D * t := by
    calc
      2 * (t + pairSelectedSize Q) ≤ 4 * t := by omega
      _ ≤ D * t := Nat.mul_le_mul_right t hD4
  have hbaseDegree :
      (8 : ℝ) * (pairSelectedSize Q + 3) ≤ gamma * (D * t) := by
    have hfixed := positiveStage_degree_bound hgamma Q
    have hDt : (D : ℝ) ≤ D * t := by
      exact_mod_cast (show D ≤ D * t by
        exact Nat.le_mul_of_pos_right D ht)
    exact hfixed.trans (mul_le_mul_of_nonneg_left hDt hgamma.le)
  have hKL : K + 1 ≤ Nat.log B t := by
    dsimp only [K, logarithmicStageCount]
    omega
  have hBpow : B ^ (K + 1) ≤ t :=
    Nat.pow_le_of_le_log (Nat.ne_of_gt ht) hKL
  have htwoB : 2 ^ (K + 1) ≤ B ^ (K + 1) := by
    exact Nat.pow_le_pow_left (by omega : 2 ≤ B) _
  have htBase : t ≤ D * t := Nat.le_mul_of_pos_left t hDpos
  have hbaseBlock : max t (2 ^ (K + 1)) ≤ D * t := by
    exact max_le htBase ((htwoB.trans hBpow).trans htBase)
  have hreservoir :
      B * reservoirRequirement Q (D * t) (K + 1) ≤ t ^ 2 := by
    exact logarithmicSchedule_reservoir_bound hQ ht huB hDB hlogLocal
  have htNext : t ^ 2 ≤ B * initialNextThreshold r := by
    exact balanceThreshold_sq_le_mul_initialNextThreshold hB16 hr hquarter
  have hstartRaw :
      reservoirRequirement Q (D * t) (K + 1) ≤
        initialNextThreshold r := by
    have hmul := hreservoir.trans htNext
    exact Nat.le_of_mul_le_mul_left hmul hBpos
  have hstage : stageMinSize Q (D * t) (K + 2) 1 =
      reservoirRequirement Q (D * t) (K + 1) := by
    unfold stageMinSize
    congr 1
  have hstart : stageMinSize Q (D * t) (K + 2) 1 ≤
      initialNextThreshold r + 1 := by
    rw [hstage]
    omega
  have hK : 1 ≤ K := by
    dsimp only [K, logarithmicStageCount]
    omega
  apply hasPrescribedCounts_of_initial_and_large_base initial hbal hbalc
      hgamma.le hgamma1 hQ hgammaQ hbaseRoom
  · simpa only [D, t, gamma] using hcapacity
  · simpa only [gamma, Nat.cast_mul] using hbaseDegree
  · exact hbaseBlock
  · exact hstart
  · exact hK
  · simpa only [K, B, t, gamma] using hM

/-- Full graph-theoretic AKS construction at the canonical integer-log
depth.  The remaining last step is purely numerical: lower-bound the final
interpolation range by a fixed positive power of `n`. -/
theorem ramseyFree_eventually_prescribed_up_to_logSchedule
    (C : ℝ) (hC : 0 < C) :
    ∃ gamma : ℝ, ∃ Q B : ℕ,
      0 < gamma ∧ gamma ≤ 1 / 12 ∧ 0 < Q ∧
      B = positiveStageLogBase gamma Q ∧ ∃ N : ℕ,
        ∀ {n : ℕ}, N ≤ n → ∀ (G : SimpleGraph (Fin n)),
          RamseyFree C G → ∀ M : ℕ,
            (M : ℝ) ≤ gamma *
              ((2 ^ logarithmicStageCount B (balanceThreshold n)).choose 2 : ℝ) →
            HasPrescribedCounts G M := by
  obtain ⟨gamma, hgamma, hgammaSmall, Nbal, hbalanced⟩ :=
    ramseyFree_eventually_balanced_fifth C hC
  let Q := initialRatioParameter gamma
  let B := positiveStageLogBase gamma Q
  obtain ⟨Ninitial, hinitial⟩ :=
    eventually_exists_initialTripleExtension gamma hgamma
      (hgammaSmall.trans (by norm_num))
  obtain ⟨Npositive, hpositive⟩ :=
    eventually_positiveStageThresholds gamma Q
  have htend : Filter.Tendsto
      (fun r : ℕ ↦ (r : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop using 1
    funext r
    rfl
  have hevent := htend.eventually
    (Filter.eventually_ge_atTop ((Nbal : ℝ) + 1))
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨NbalPower, hNbalPower⟩ := hevent
  refine ⟨gamma, Q, B, hgamma, hgammaSmall,
    initialRatioParameter_pos gamma, rfl,
    max 1 (max NbalPower (max Ninitial Npositive)), ?_⟩
  intro n hn G hG M hM
  have hn1 : 1 ≤ n := by omega
  have hnBalPower : NbalPower ≤ n := by omega
  have hnInitial : Ninitial ≤ n := by omega
  have hnPositive : Npositive ≤ n := by omega
  have hpow := hNbalPower n hnBalPower
  have hthreshold := rpow_quarter_le_balanceThreshold n
  have hNbal : Nbal ≤ balanceThreshold n := by
    exact_mod_cast (show (Nbal : ℝ) ≤ balanceThreshold n by
      linarith)
  have hbalances := hbalanced hn1 G hG hNbal
    (rpow_fifth_le_balanceThreshold hn1)
  have hbalUniv : IsBalanced G gamma
      (balanceThreshold (Finset.univ : Finset (Fin n)).card) := by
    simpa using hbalances.1
  have hbalcUniv : IsBalanced Gᶜ gamma
      (balanceThreshold (Finset.univ : Finset (Fin n)).card) := by
    simpa using hbalances.2
  obtain ⟨initial⟩ := hinitial (V := Fin n) (G := G)
    (Cset := Finset.univ) (by simpa using hnInitial) hbalUniv hbalcUniv
  have initial' : InitialTripleExtension G (initialNextThreshold n)
      (Finset.univ : Finset (Fin n)) := by
    simpa using initial
  obtain ⟨hr16, hquarter, hselected, hcapacity, hlog⟩ :=
    hpositive n hnPositive
  let epsilon := gamma / 6
  have hgammaEq : 6 * epsilon = gamma := by
    dsimp only [epsilon]
    ring
  apply hasPrescribedCounts_of_initial_logSchedule
      (epsilon := epsilon) (r := n) (Q := Q) initial'
  · simpa only [hgammaEq] using hbalances.1
  · simpa only [hgammaEq] using hbalances.2
  · simpa only [hgammaEq] using hgamma
  · simpa only [hgammaEq] using hgammaSmall.trans (by norm_num)
  · exact initialRatioParameter_pos gamma
  · simpa only [hgammaEq, Q] using
      eight_le_gamma_mul_initialRatioParameter hgamma
  · exact hr16
  · exact hquarter
  · exact hselected
  · simpa only [hgammaEq] using hcapacity
  · simpa only [hgammaEq] using hlog
  · simpa only [hgammaEq, B] using hM

/-- Exact formal interface of the AKS prescribed-small-count theorem. -/
def AKSPrescribedSmallCounts : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ alpha : ℝ, 0 < alpha ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, N ≤ n → ∀ (G : SimpleGraph (Fin n)),
        RamseyFree C G → ∀ M : ℕ,
          (M : ℝ) ≤ (n : ℝ) ^ alpha → HasPrescribedCounts G M

/-- AKS prescribed small counts, with all finite selection, rounding,
balancedness, and logarithmic-reservoir estimates discharged. -/
theorem aksPrescribedSmallCounts : AKSPrescribedSmallCounts := by
  intro C hC
  obtain ⟨gamma, Q, B, hgamma, hgammaSmall, hQ, hBdef,
    Nconstruct, hconstruct⟩ :=
    ramseyFree_eventually_prescribed_up_to_logSchedule C hC
  have hB : 16 ≤ B := by
    rw [hBdef]
    exact sixteen_le_positiveStageLogBase gamma Q
  obtain ⟨Nnumeric, hnumeric⟩ :=
    eventually_rpow_le_gamma_logSchedule gamma hgamma B hB
  let alpha : ℝ := 1 / (16 * (B : ℝ))
  have hBReal : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  refine ⟨alpha, halpha, max Nconstruct Nnumeric, ?_⟩
  intro n hn G hG M hM
  have hnConstruct : Nconstruct ≤ n := (le_max_left _ _).trans hn
  have hnNumeric : Nnumeric ≤ n := (le_max_right _ _).trans hn
  have hrange := hnumeric n hnNumeric
  exact hconstruct hnConstruct G hG M (hM.trans (by
    simpa only [alpha] using hrange))

end AKSGraph
end Erdos88
