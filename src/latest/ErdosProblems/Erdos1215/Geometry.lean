import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# The finite alternating-wall labyrinth for Erdős Problem 1215

This module isolates the planar-geometric part of the negative solution.  A path
starts at zero, ends on the unit circle, and is only required to avoid the walls after its initial
endpoint.  Its length is the extended total variation `eVariationOn γ (Set.Icc 0 1)`.
-/

open Set Metric
open scoped ENNReal Topology

noncomputable section

namespace Erdos1215

/-- The endpoint-correct geometric path predicate.  In the polynomial application the strict
sublevel condition is likewise imposed only on `Ioc 0 1`, since `P(0) = 1`. -/
def IsUnitPath (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1

/-- The extended length used in the statement of Problem 1215. -/
def GeometricPathELength (γ : ℝ → ℂ) : ℝ≥0∞ :=
  eVariationOn γ (Icc 0 1)

/-- Times at which the path first meets the circle of radius `r`. -/
def circleHitSet (γ : ℝ → ℂ) (r : ℝ) : Set ℝ :=
  {t ∈ Icc 0 1 | ‖γ t‖ = r}

/-- The first time at which the path meets the circle of radius `r`. -/
def firstCircleHit (γ : ℝ → ℂ) (r : ℝ) : ℝ :=
  sInf (circleHitSet γ r)

lemma continuousOn_norm {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    ContinuousOn (fun t ↦ ‖γ t‖) (Icc 0 1) :=
  hγ.norm

lemma circleHitSet_isCompact {γ : ℝ → ℂ} {r : ℝ}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    IsCompact (circleHitSet γ r) := by
  apply isCompact_Icc.of_isClosed_subset
  · rw [circleHitSet]
    exact isClosed_Icc.isClosed_eq hγ.norm continuousOn_const
  · intro t ht
    exact ht.1

lemma circleHitSet_nonempty {γ : ℝ → ℂ} {r : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (circleHitSet γ r).Nonempty := by
  rcases hγ with ⟨hγcont, hγ0, hγ1⟩
  have hrange : r ∈ Icc (‖γ 0‖) (‖γ 1‖) := by
    simpa [hγ0, hγ1] using ⟨hr0, hr1⟩
  obtain ⟨t, ht, htr⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hγcont.norm) hrange
  exact ⟨t, ht, htr⟩

lemma firstCircleHit_mem {γ : ℝ → ℂ} {r : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    firstCircleHit γ r ∈ circleHitSet γ r := by
  exact (circleHitSet_isCompact hγ.1).sInf_mem
    (circleHitSet_nonempty hγ hr0 hr1)

lemma firstCircleHit_le_of_mem {γ : ℝ → ℂ} {r t : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht : t ∈ circleHitSet γ r) :
    firstCircleHit γ r ≤ t := by
  exact (circleHitSet_isCompact hγ.1).isLeast_sInf
    (circleHitSet_nonempty hγ hr0 hr1) |>.2 ht

lemma firstCircleHit_mem_Icc {γ : ℝ → ℂ} {r : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    firstCircleHit γ r ∈ Icc (0 : ℝ) 1 :=
  (firstCircleHit_mem hγ hr0 hr1).1

lemma norm_firstCircleHit {γ : ℝ → ℂ} {r : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖γ (firstCircleHit γ r)‖ = r :=
  (firstCircleHit_mem hγ hr0 hr1).2

lemma firstCircleHit_pos {γ : ℝ → ℂ} {r : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 < firstCircleHit γ r := by
  have ht := firstCircleHit_mem_Icc hγ hr0.le hr1
  refine lt_of_le_of_ne ht.1 ?_
  intro hzero
  have hnorm := norm_firstCircleHit hγ hr0.le hr1
  rw [← hzero, hγ.2.1, norm_zero] at hnorm
  linarith

lemma firstCircleHit_lt {γ : ℝ → ℂ} {r s : ℝ}
    (hγ : IsUnitPath γ) (hr0 : 0 ≤ r) (hrs : r < s) (hs1 : s ≤ 1) :
    firstCircleHit γ r < firstCircleHit γ s := by
  have hs0 : 0 ≤ s := hr0.trans (le_of_lt hrs)
  have hts_mem := firstCircleHit_mem hγ hs0 hs1
  have hts_Icc := hts_mem.1
  have hcont : ContinuousOn (fun t ↦ ‖γ t‖) (Icc 0 (firstCircleHit γ s)) :=
    hγ.1.norm.mono (Icc_subset_Icc_right hts_Icc.2)
  have hrange : r ∈ Icc (‖γ 0‖) (‖γ (firstCircleHit γ s)‖) := by
    rw [hγ.2.1, norm_zero, hts_mem.2]
    exact ⟨hr0, hrs.le⟩
  obtain ⟨t, htIcc, htr⟩ :=
    (intermediate_value_Icc hts_Icc.1 hcont) hrange
  have hfirst_le : firstCircleHit γ r ≤ t :=
    firstCircleHit_le_of_mem hγ hr0 (hrs.le.trans hs1) ⟨
      ⟨htIcc.1, htIcc.2.trans hts_Icc.2⟩, htr⟩
  have hle : firstCircleHit γ r ≤ firstCircleHit γ s :=
    hfirst_le.trans htIcc.2
  refine hle.lt_of_ne ?_
  intro heq
  have hrnorm := norm_firstCircleHit hγ hr0 (hrs.le.trans hs1)
  rw [heq, hts_mem.2] at hrnorm
  exact (ne_of_lt hrs) hrnorm.symm

/-- At even levels the wall blocks the left two thirds of the circle; at odd levels it blocks
the right two thirds. -/
def alternatingWall (r : ℕ → ℝ) (j : ℕ) : Set ℂ :=
  {z | ‖z‖ = r j ∧ if Even j then z.re ≤ r j / 2 else -r j / 2 ≤ z.re}

/-- The finite family of walls with indices `0, ..., m`. -/
def alternatingWalls (r : ℕ → ℝ) (m : ℕ) : Set ℂ :=
  ⋃ j ∈ Iic m, alternatingWall r j

/-- Endpoint-correct wall avoidance: the initial point is deliberately excluded. -/
def AvoidsAlternatingWallsAfterStart (γ : ℝ → ℂ) (r : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ t ∈ Ioc (0 : ℝ) 1, γ t ∉ alternatingWalls r m

lemma not_mem_alternatingWall_of_avoids {γ : ℝ → ℂ} {r : ℕ → ℝ} {m j : ℕ}
    (havoid : AvoidsAlternatingWallsAfterStart γ r m) (hj : j ≤ m)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    γ t ∉ alternatingWall r j := by
  intro hwall
  exact havoid t ht (by
    simp only [alternatingWalls, mem_iUnion]
    exact ⟨j, ⟨hj, hwall⟩⟩)

lemma firstHit_gate {γ : ℝ → ℂ} {r : ℕ → ℝ} {m j : ℕ}
    (hγ : IsUnitPath γ) (havoid : AvoidsAlternatingWallsAfterStart γ r m)
    (hj : j ≤ m) (hr0 : 0 < r j) (hr1 : r j ≤ 1) :
    if Even j then r j / 2 < (γ (firstCircleHit γ (r j))).re
    else (γ (firstCircleHit γ (r j))).re < -r j / 2 := by
  have htIcc := firstCircleHit_mem_Icc hγ hr0.le hr1
  have htIoc : firstCircleHit γ (r j) ∈ Ioc (0 : ℝ) 1 :=
    ⟨firstCircleHit_pos hγ hr0 hr1, htIcc.2⟩
  have hnot := not_mem_alternatingWall_of_avoids havoid hj htIoc
  have hnorm := norm_firstCircleHit hγ hr0.le hr1
  simp only [alternatingWall, mem_ofPred_eq, hnorm, true_and] at hnot
  split_ifs at hnot ⊢ <;> linarith

lemma successive_firstHit_dist_gt {γ : ℝ → ℂ} {r : ℕ → ℝ} {m j : ℕ} {q : ℝ}
    (hγ : IsUnitPath γ) (havoid : AvoidsAlternatingWallsAfterStart γ r m)
    (hj : j < m) (hr0 : ∀ k ≤ m, 0 < r k) (hr1 : ∀ k ≤ m, r k ≤ 1)
    (hq : ∀ k ≤ m, q < r k) :
    q < dist (γ (firstCircleHit γ (r j)))
      (γ (firstCircleHit γ (r (j + 1)))) := by
  have hjm : j ≤ m := hj.le
  have hsjm : j + 1 ≤ m := hj
  have hjgate := firstHit_gate hγ havoid hjm (hr0 j hjm) (hr1 j hjm)
  have hsgate := firstHit_gate hγ havoid hsjm (hr0 (j + 1) hsjm) (hr1 (j + 1) hsjm)
  rw [Complex.dist_eq]
  refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm
    (γ (firstCircleHit γ (r j)) - γ (firstCircleHit γ (r (j + 1)))))
  rw [Complex.sub_re]
  by_cases heven : Even j
  · simp only [heven, if_pos, Nat.even_add_one, not_true_eq_false, if_false] at hjgate hsgate
    rw [abs_of_pos] <;>
      linarith [hr0 j hjm, hr0 (j + 1) hsjm, hq j hjm, hq (j + 1) hsjm]
  · simp only [heven, if_false, Nat.even_add_one, not_false_eq_true, if_true] at hjgate hsgate
    rw [abs_of_neg] <;>
      linarith [hr0 j hjm, hr0 (j + 1) hsjm, hq j hjm, hq (j + 1) hsjm]

/-- Generic alternating-wall lower bound.  If every wall radius is larger than `q`, each of the
`m` successive gate changes costs more than `q` in chord distance. -/
theorem alternatingWalls_geometricPathELength_gt {γ : ℝ → ℂ} {r : ℕ → ℝ}
    {m : ℕ} {q : ℝ} (hm : 0 < m) (hq0 : 0 ≤ q)
    (hγ : IsUnitPath γ) (havoid : AvoidsAlternatingWallsAfterStart γ r m)
    (hr0 : ∀ j ≤ m, 0 < r j) (hr1 : ∀ j ≤ m, r j ≤ 1)
    (hrmono : StrictMonoOn r (Iic m)) (hq : ∀ j ≤ m, q < r j) :
    ENNReal.ofReal ((m : ℝ) * q) < GeometricPathELength γ := by
  let τ : ℕ → ℝ := fun j ↦ firstCircleHit γ (r j)
  have hτ_strict : StrictMonoOn τ (Iic m) := by
    intro i hi j hj hij
    exact firstCircleHit_lt hγ (hr0 i hi).le (hrmono hi hj hij) (hr1 j hj)
  have hsum_le :
      (∑ j ∈ Finset.range m, edist (γ (τ (j + 1))) (γ (τ j))) ≤ GeometricPathELength γ := by
    apply eVariationOn.sum_le_of_monotoneOn_Iic hτ_strict.monotoneOn
    intro j hj
    exact firstCircleHit_mem_Icc hγ (hr0 j hj).le (hr1 j hj)
  have hedge (j : ℕ) (hj : j ∈ Finset.range m) :
      ENNReal.ofReal q < edist (γ (τ (j + 1))) (γ (τ j)) := by
    rw [edist_comm, edist_dist]
    have hdist := successive_firstHit_dist_gt hγ havoid
      (Finset.mem_range.1 hj) hr0 hr1 hq
    exact (ENNReal.ofReal_lt_ofReal_iff (hq0.trans_lt hdist)).2 hdist
  have hsum_lt :
      (∑ _j ∈ Finset.range m, ENNReal.ofReal q) <
        ∑ j ∈ Finset.range m, edist (γ (τ (j + 1))) (γ (τ j)) := by
    exact ENNReal.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.2 (Nat.ne_of_gt hm)) fun j hj ↦ hedge j hj
  refine lt_of_eq_of_lt ?_ (hsum_lt.trans_le hsum_le)
  simp

/-- Equally spaced wall radii in the annulus `1 / 2 < ‖z‖ < 3 / 4`.  The denominator uses
`m + 2`, so all levels `0, ..., m` are strictly inside the outer radius. -/
def standardWallRadius (m j : ℕ) : ℝ :=
  (1 : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) / (4 * ((m + 2 : ℕ) : ℝ))

lemma half_lt_standardWallRadius (m j : ℕ) :
    (1 : ℝ) / 2 < standardWallRadius m j := by
  unfold standardWallRadius
  have hpos : 0 < ((j + 1 : ℕ) : ℝ) / (4 * ((m + 2 : ℕ) : ℝ)) := by
    exact div_pos (Nat.cast_pos.2 (by omega))
      (mul_pos (by norm_num) (Nat.cast_pos.2 (by omega)))
  linarith

lemma standardWallRadius_lt_three_quarters {m j : ℕ} (hj : j ≤ m) :
    standardWallRadius m j < (3 : ℝ) / 4 := by
  have hjcast : ((j + 1 : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
    exact Nat.cast_lt.2 (by omega)
  have hden : 0 < (4 : ℝ) * ((m + 2 : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.2 (by omega))
  have hfrac :
      ((j + 1 : ℕ) : ℝ) / (4 * ((m + 2 : ℕ) : ℝ)) < 1 / 4 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  unfold standardWallRadius
  linarith

lemma standardWallRadius_strictMonoOn (m : ℕ) :
    StrictMonoOn (standardWallRadius m) (Iic m) := by
  intro i _hi j _hj hij
  unfold standardWallRadius
  have hden : 0 < (4 : ℝ) * ((m + 2 : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.2 (by omega))
  exact add_lt_add_right
    ((div_lt_div_iff_of_pos_right hden).2 (Nat.cast_lt.2 (by omega))) ((1 : ℝ) / 2)

/-- The concrete `m + 1`-wall labyrinth forces more than `m / 2` total variation. -/
theorem standardAlternatingWalls_geometricPathELength_gt {γ : ℝ → ℂ} {m : ℕ}
    (hm : 0 < m) (hγ : IsUnitPath γ)
    (havoid : AvoidsAlternatingWallsAfterStart γ (standardWallRadius m) m) :
    ENNReal.ofReal ((m : ℝ) / 2) < GeometricPathELength γ := by
  have h := alternatingWalls_geometricPathELength_gt (r := standardWallRadius m)
    (m := m) (q := (1 : ℝ) / 2) hm (by norm_num) hγ havoid
    (fun j _hj ↦ (by linarith [half_lt_standardWallRadius m j]))
    (fun j hj ↦ (standardWallRadius_lt_three_quarters hj).le.trans (by norm_num))
    (standardWallRadius_strictMonoOn m)
    (fun j _hj ↦ half_lt_standardWallRadius m j)
  simpa [div_eq_mul_inv] using h

/-- An explicit number of walls sufficient to force length greater than `L`. -/
def wallCount (L : ℝ) : ℕ :=
  ⌈2 * L⌉₊ + 1

lemma wallCount_pos (L : ℝ) : 0 < wallCount L := by
  unfold wallCount
  omega

lemma lt_wallCount_half (L : ℝ) : L < (wallCount L : ℝ) / 2 := by
  have hceil : 2 * L ≤ ((⌈2 * L⌉₊ : ℕ) : ℝ) := Nat.le_ceil (2 * L)
  unfold wallCount
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Fully explicit geometric layer: the alternating walls determined by `L` force every
endpoint-correct unit path avoiding them after time zero to have extended variation greater than
`L`.  No rectifiability assumption is needed; infinite variation is handled by `ℝ≥0∞`. -/
theorem explicit_labyrinth_forces_long_path {L : ℝ} (hL : 0 ≤ L) {γ : ℝ → ℂ}
    (hγ : IsUnitPath γ)
    (havoid : AvoidsAlternatingWallsAfterStart γ
      (standardWallRadius (wallCount L)) (wallCount L)) :
    ENNReal.ofReal L < eVariationOn γ (Icc (0 : ℝ) 1) := by
  have hmaze := standardAlternatingWalls_geometricPathELength_gt
    (m := wallCount L) (wallCount_pos L) hγ havoid
  have hreal := lt_wallCount_half L
  have hofReal :
      ENNReal.ofReal L < ENNReal.ofReal ((wallCount L : ℝ) / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (hL.trans_lt hreal)).2 hreal
  exact hofReal.trans (by simpa [GeometricPathELength] using hmaze)

end Erdos1215
