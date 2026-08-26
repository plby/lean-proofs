import ErdosProblems.Erdos486.Survivors

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Abstract dyadic deletion blocks

This module isolates the finite input needed by the global gliding-hump
argument.  All endpoint and modulus estimates are inequalities in `ℕ`, with
the rational constants cross-multiplied.  The analytic input is deliberately
only a finite-past recovery statement; it does not assume a global
counterexample.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The integral dyadic scale `2^j`. -/
def dyadicNat (j : ℕ) : ℕ :=
  2 ^ j

/-- The same dyadic scale, viewed as a real cutoff. -/
def dyadic (j : ℕ) : ℝ :=
  (dyadicNat j : ℝ)

@[simp]
theorem dyadicNat_pos (j : ℕ) : 0 < dyadicNat j := by
  simp [dyadicNat]

@[simp]
theorem dyadic_pos (j : ℕ) : 0 < dyadic j := by
  simp [dyadic, dyadicNat]

@[simp]
theorem dyadic_succ (j : ℕ) : dyadicNat (j + 1) = 2 * dyadicNat j := by
  simp [dyadicNat, pow_succ, Nat.mul_comm]

/-- Finite endpoint data at every scale.  The quantitative block properties
are required only from `firstScale` onward.  Values below `firstScale` are
irrelevant and let downstream definitions remain nondependent.

The bounds encode
`11*2^j/10 <= m <= 19*2^j/10` and
`19*2^j/20 <= q(j,m) <= 21*2^j/20` without division. -/
structure DyadicBlockGeometry where
  firstScale : ℕ
  endpoints : ℕ → Finset ℕ
  modulus : ℕ → ℕ → ℕ
  endpoint_lower : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    11 * dyadicNat j ≤ 10 * m
  endpoint_upper : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    10 * m ≤ 19 * dyadicNat j
  modulus_pos : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    0 < modulus j m
  modulus_lower : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    19 * dyadicNat j ≤ 20 * modulus j m
  modulus_upper : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    20 * modulus j m ≤ 21 * dyadicNat j
  enough_endpoints : ∀ {j : ℕ}, firstScale ≤ j →
    3 * dyadicNat j ≤ 8 * (endpoints j).card

/-- Moduli assigned by `G` at scales in `scales`. -/
def blockModuli (G : DyadicBlockGeometry) (scales : Set ℕ) : Set ℕ :=
  {q | ∃ j ∈ scales, ∃ m ∈ G.endpoints j, G.modulus j m = q}

/-- Residues assigned to one of the moduli occurring at the selected scales.
Equal moduli are automatically grouped into one row. -/
def blockResidues (G : DyadicBlockGeometry) (scales : Set ℕ)
    (q : blockModuli G scales) : Set (ZMod (q : ℕ)) :=
  {r | ∃ j ∈ scales, ∃ m ∈ G.endpoints j,
    G.modulus j m = (q : ℕ) ∧ r = (m : ZMod (q : ℕ))}

/-- The delayed-congruence survivor set induced by selected block scales. -/
def blockSurvivors (G : DyadicBlockGeometry) (scales : Set ℕ) : Set ℕ :=
  survivors (blockModuli G scales) (blockResidues G scales)

/-- The abstract input to the gliding-hump construction.

`footprint j` is an upper bound for the completed periodic footprint of the
`j`th block.  `summable_footprint` records the manuscript's summability
property, while `tail_budget` exposes the finite-sum consequence after the
starting scale has been enlarged.  `finite_recovery` is the periodic recovery
lemma in precisely the form used globally: every finite subsystem has a
limit at least one minus the sum of its block footprints. -/
structure DyadicBlockInterface where
  geometry : DyadicBlockGeometry
  footprint : ℕ → ℝ
  footprint_nonneg : ∀ j, 0 ≤ footprint j
  summable_footprint : Summable footprint
  tail_budget : ∀ J : Finset ℕ,
    (∀ j ∈ J, geometry.firstScale ≤ j) →
      (∑ j ∈ J, footprint j) ≤ (1 : ℝ) / 100
  finite_recovery : ∀ J : Finset ℕ,
    ∃ d : ℝ,
      Tendsto (logAverage (blockSurvivors geometry (J : Set ℕ))) atTop (nhds d) ∧
      1 - (∑ j ∈ J, footprint j) ≤ d

namespace DyadicBlockGeometry

variable (G : DyadicBlockGeometry)

/-- Every available endpoint is positive. -/
theorem endpoint_pos {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : 0 < m := by
  have h := G.endpoint_lower hj hm
  have hpow : 0 < dyadicNat j := dyadicNat_pos j
  omega

/-- The assigned modulus is strictly active at its endpoint. -/
theorem modulus_lt_endpoint {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : G.modulus j m < m := by
  have hq := G.modulus_upper hj hm
  have hm' := G.endpoint_lower hj hm
  have hpow : 0 < dyadicNat j := dyadicNat_pos j
  omega

/-- Endpoints at different available scales lie in disjoint, ordered
intervals. -/
theorem endpoint_lt_of_scale_lt {j k m n : ℕ}
    (hj0 : G.firstScale ≤ j) (hjk : j < k)
    (hm : m ∈ G.endpoints j) (hn : n ∈ G.endpoints k) : m < n := by
  have hm_upper := G.endpoint_upper hj0 hm
  have hk0 : G.firstScale ≤ k := hj0.trans (Nat.le_of_lt hjk)
  have hn_lower := G.endpoint_lower hk0 hn
  have hexp : j + 1 ≤ k := hjk
  have hpow : dyadicNat (j + 1) ≤ dyadicNat k := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have hgap : 19 * dyadicNat j < 11 * dyadicNat k := by
    calc
      19 * dyadicNat j < 11 * dyadicNat (j + 1) := by
        rw [dyadic_succ]
        have hp := dyadicNat_pos j
        nlinarith
      _ ≤ 11 * dyadicNat k := Nat.mul_le_mul_left 11 hpow
  omega

/-- Modulus ranges at different available scales are disjoint and ordered. -/
theorem modulus_lt_of_scale_lt {j k m n : ℕ}
    (hj0 : G.firstScale ≤ j) (hjk : j < k)
    (hm : m ∈ G.endpoints j) (hn : n ∈ G.endpoints k) :
    G.modulus j m < G.modulus k n := by
  have hq_upper := G.modulus_upper hj0 hm
  have hk0 : G.firstScale ≤ k := hj0.trans (Nat.le_of_lt hjk)
  have hr_lower := G.modulus_lower hk0 hn
  have hexp : j + 1 ≤ k := hjk
  have hpow : dyadicNat (j + 1) ≤ dyadicNat k := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have hgap : 21 * dyadicNat j < 19 * dyadicNat k := by
    calc
      21 * dyadicNat j < 19 * dyadicNat (j + 1) := by
        rw [dyadic_succ]
        have hp := dyadicNat_pos j
        nlinarith
      _ ≤ 19 * dyadicNat k := Nat.mul_le_mul_left 19 hpow
  omega

/-- Every endpoint at scale `j` lies below `2^(j+1)`. -/
theorem endpoint_lt_next_dyadic {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : m < dyadicNat (j + 1) := by
  have h := G.endpoint_upper hj hm
  rw [dyadic_succ]
  have hp := dyadicNat_pos j
  omega

/-- The manuscript's cardinality and endpoint bounds give a fixed amount of
harmonic mass at each available scale. -/
theorem endpoint_harmonic_mass {j : ℕ} (hj : G.firstScale ≤ j) :
    (15 : ℝ) / 76 ≤ ∑ m ∈ G.endpoints j, (m : ℝ)⁻¹ := by
  let Q : ℝ := dyadicNat j
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast dyadicNat_pos j
  have heach : ∀ m ∈ G.endpoints j, (10 : ℝ) / (19 * Q) ≤ (m : ℝ)⁻¹ := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast G.endpoint_pos hj hm
    have hmupper : (10 : ℝ) * m ≤ 19 * Q := by
      dsimp [Q]
      exact_mod_cast G.endpoint_upper hj hm
    have hmle : (m : ℝ) ≤ 19 * Q / 10 := by linarith
    have hinv := one_div_le_one_div_of_le hmpos hmle
    simpa only [one_div, inv_div] using! hinv
  have hsum :
      ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) ≤
        ∑ m ∈ G.endpoints j, (m : ℝ)⁻¹ := by
    calc
      ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) =
          ∑ _m ∈ G.endpoints j, ((10 : ℝ) / (19 * Q)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun m hm ↦ heach m hm
  have hcard : (3 : ℝ) * Q ≤ 8 * (G.endpoints j).card := by
    dsimp [Q]
    exact_mod_cast G.enough_endpoints hj
  calc
    (15 : ℝ) / 76 ≤
        ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) := by
      field_simp [ne_of_gt hQ]
      nlinarith
    _ ≤ _ := hsum

/-- No selected available block can assign modulus zero. -/
theorem zero_not_mem_blockModuli {scales : Set ℕ}
    (hscales : ∀ j ∈ scales, G.firstScale ≤ j) :
    0 ∉ blockModuli G scales := by
  rintro ⟨j, hj, m, hm, hq⟩
  have := G.modulus_pos (hscales j hj) hm
  omega

/-- An endpoint selected from an installed scale is deleted by its own
assigned row. -/
theorem endpoint_not_mem_blockSurvivors {scales : Set ℕ} {j m : ℕ}
    (hj : j ∈ scales) (hm : m ∈ G.endpoints j)
    (hj0 : G.firstScale ≤ j) :
    m ∉ blockSurvivors G scales := by
  let q : blockModuli G scales :=
    ⟨G.modulus j m, ⟨j, hj, m, hm, rfl⟩⟩
  apply not_mem_survivors_of_assigned (n := q) (G.modulus_lt_endpoint hj0 hm)
  exact ⟨j, hj, m, hm, rfl, rfl⟩

end DyadicBlockGeometry

end Erdos486
