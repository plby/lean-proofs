import ErdosProblems.Erdos1038.EndpointNormalization
import ErdosProblems.Erdos1038.ResidualDeficit
import ErdosProblems.Erdos1038.EmpiricalPotential

/-!
# The endpoint-normalized polynomial as a residual configuration

This file passes from the endpoint normalization of a component-atomized
polynomial to the finite residual model.  Equal residual roots are aggregated
into one index, with their multiplicities used as probability weights, and all
root locations are shifted by `+1` so that the endpoint root `-1` becomes the
pole at zero.

The last part gives the local geometric interpretation of `residualRadius`:
for the component containing a residual root, its width is at least twice the
corresponding residual radius.
-/

open scoped BigOperators Real
open Finset MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- Distinct residual root locations of an endpoint-normalized polynomial. -/
abbrev NormalizedResidualIndex {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f) :=
  ↑(endpointResidualRoots h.normalizedPolynomial).toFinset

/-- A residual location's multiplicity, normalized by the total residual
multiplicity. -/
def normalizedResidualWeight {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f)
    (i : NormalizedResidualIndex h) : ℝ :=
  ((endpointResidualRoots h.normalizedPolynomial).count (i : ℝ) : ℝ) /
    ((endpointResidualRoots h.normalizedPolynomial).card : ℝ)

/-- Shifted residual root location.  The same shift sends the endpoint root
`-1` to zero. -/
def normalizedResidualLocation {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f)
    (i : NormalizedResidualIndex h) : ℝ :=
  (i : ℝ) + 1

/-- Ratio of endpoint multiplicity to total residual multiplicity. -/
def normalizedEndpointResidualRatio {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f) : ℝ :=
  (endpointMultiplicity h.normalizedPolynomial : ℝ) /
    ((endpointResidualRoots h.normalizedPolynomial).card : ℝ)

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

lemma normalized_residual_card_pos
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    0 < (endpointResidualRoots h.normalizedPolynomial).card :=
  Multiset.card_pos.mpr hres

lemma normalizedResidualIndex_nonempty
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    Nonempty (NormalizedResidualIndex h) := by
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp
    (h.normalized_residual_card_pos hres)
  exact ⟨⟨r, Multiset.mem_toFinset.mpr hr⟩⟩

/-- The finite residual configuration obtained by aggregating equal residual
roots and shifting every distinct location by `+1`. -/
def normalizedResidualConfiguration
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    ResidualConfiguration (NormalizedResidualIndex h) where
  weight := normalizedResidualWeight h
  weight_pos := by
    intro i
    apply div_pos
    · exact_mod_cast Multiset.count_pos.mpr
        (Multiset.mem_toFinset.mp i.property)
    · exact_mod_cast h.normalized_residual_card_pos hres
  sum_weight := by
    let s := endpointResidualRoots h.normalizedPolynomial
    change ∑ i : ↑s.toFinset, ((s.count (i : ℝ) : ℝ) / (s.card : ℝ)) = 1
    rw [Finset.sum_coe_sort s.toFinset
      (fun r : ℝ ↦ (s.count r : ℝ) / (s.card : ℝ)),
      ← Finset.sum_div, ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
    exact div_self (by exact_mod_cast (h.normalized_residual_card_pos hres).ne')
  location := normalizedResidualLocation h
  location_mem := by
    intro i
    have hi : (i : ℝ) ∈ endpointResidualRoots h.normalizedPolynomial :=
      Multiset.mem_toFinset.mp i.property
    have hiIcc := h.normalized_residual_root_mem_Icc hi
    have hb0 := h.normalizedRightBoundary_nonneg
    constructor
    · dsimp [normalizedResidualLocation]
      linarith [hiIcc.1, hb0]
    · dsimp [normalizedResidualLocation]
      linarith [hiIcc.2]

@[simp]
lemma normalizedResidualConfiguration_weight
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (i : NormalizedResidualIndex h) :
    (h.normalizedResidualConfiguration hres).weight i =
      ((endpointResidualRoots h.normalizedPolynomial).count (i : ℝ) : ℝ) /
        ((endpointResidualRoots h.normalizedPolynomial).card : ℝ) := rfl

@[simp]
lemma normalizedResidualConfiguration_location
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (i : NormalizedResidualIndex h) :
    (h.normalizedResidualConfiguration hres).location i = (i : ℝ) + 1 := rfl

lemma normalizedResidualLocation_injective :
    Function.Injective (normalizedResidualLocation h) := by
  intro i j hij
  apply Subtype.ext
  dsimp [normalizedResidualLocation] at hij
  linarith

lemma normalizedResidualConfiguration_location_injective
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    Function.Injective (h.normalizedResidualConfiguration hres).location :=
  h.normalizedResidualLocation_injective

/-- Distinct normalized residual locations inherit the ambient real order,
so the shifted configuration is strictly ordered by its canonical index. -/
lemma normalizedResidualConfiguration_location_strictMono
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    StrictMono (h.normalizedResidualConfiguration hres).location := by
  intro i j hij
  simp only [normalizedResidualConfiguration_location]
  change (i : ℝ) < (j : ℝ) at hij
  linarith

/-- Every residual root is strictly to the right of the endpoint component's
right boundary. -/
lemma normalizedRightBoundary_lt_residual_root {r : ℝ}
    (hr : r ∈ endpointResidualRoots h.normalizedPolynomial) :
    h.normalizedRightBoundary < r := by
  have hrIcc := h.normalized_residual_root_mem_Icc hr
  apply lt_of_le_of_ne hrIcc.1
  intro hbr
  have hbnot : h.normalizedRightBoundary ∉
      sublevelSet h.normalizedPolynomial := by
    simpa [normalizedRightBoundary] using!
      sublevelComponent_sSup_not_mem h.normalized_admissible
        (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  apply hbnot
  rw [hbr]
  exact root_mem_sublevelSet (mem_endpointResidualRoots.mp hr).1

/-- The endpoint-to-residual multiplicity ratio is at least one. -/
theorem one_le_normalizedEndpointResidualRatio
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    1 ≤ normalizedEndpointResidualRatio h := by
  have hcard : (endpointResidualRoots h.normalizedPolynomial).card ≤
      endpointMultiplicity h.normalizedPolynomial := by
    have htotal := h.endpointMultiplicity_add_residual_card
    have hhalf := h.natDegree_le_twice_endpointMultiplicity
    omega
  rw [normalizedEndpointResidualRatio]
  apply (le_div_iff₀ (by
    exact_mod_cast h.normalized_residual_card_pos hres)).2
  simpa using! (show
    ((endpointResidualRoots h.normalizedPolynomial).card : ℝ) ≤
      (endpointMultiplicity h.normalizedPolynomial : ℝ) by
        exact_mod_cast hcard)

/-- Aggregating equal residual roots by their multiplicities does not change
their normalized logarithmic sum. -/
lemma normalizedResidualConfiguration_weighted_log_sum
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) (x : ℝ) :
    ∑ i, (h.normalizedResidualConfiguration hres).weight i *
        Real.log |x - (h.normalizedResidualConfiguration hres).location i| =
      ((endpointResidualRoots h.normalizedPolynomial).card : ℝ)⁻¹ *
        ((endpointResidualRoots h.normalizedPolynomial).map fun r ↦
          Real.log |(x - 1) - r|).sum := by
  let s := endpointResidualRoots h.normalizedPolynomial
  have haggr :
      (s.map fun r ↦ Real.log |(x - 1) - r|).sum =
        ∑ r ∈ s.toFinset,
          (s.count r : ℝ) * Real.log |(x - 1) - r| := by
    simpa [nsmul_eq_mul] using!
      (Finset.sum_multiset_map_count s
        (fun r ↦ Real.log |(x - 1) - r|))
  change ∑ i : ↑s.toFinset,
      ((s.count (i : ℝ) : ℝ) / (s.card : ℝ)) *
        Real.log |x - ((i : ℝ) + 1)| =
    (s.card : ℝ)⁻¹ * (s.map fun r ↦ Real.log |(x - 1) - r|).sum
  rw [Finset.sum_coe_sort s.toFinset
    (fun r : ℝ ↦ ((s.count r : ℝ) / (s.card : ℝ)) *
      Real.log |x - (r + 1)|)]
  calc
    ∑ r ∈ s.toFinset,
        ((s.count r : ℝ) / (s.card : ℝ)) *
          Real.log |x - (r + 1)| =
        ∑ r ∈ s.toFinset,
          ((s.count r : ℝ) * Real.log |(x - 1) - r|) /
            (s.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [show x - (r + 1) = (x - 1) - r by ring]
      ring
    _ = (∑ r ∈ s.toFinset,
          (s.count r : ℝ) * Real.log |(x - 1) - r|) /
            (s.card : ℝ) := by
      rw [Finset.sum_div]
    _ = (s.card : ℝ)⁻¹ *
          (s.map fun r ↦ Real.log |(x - 1) - r|).sum := by
      rw [← haggr]
      exact (inv_mul_eq_div _ _).symm

/-- Exact residual normalization of the full root-log sum.  This identity is
algebraic and remains true at pole locations under Lean's convention
`Real.log 0 = 0`. -/
theorem normalized_residualPotential_eq_root_log_sum
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) (x : ℝ) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) x =
      ((endpointResidualRoots h.normalizedPolynomial).card : ℝ)⁻¹ *
        (h.normalizedPolynomial.roots.map fun r ↦
          Real.log |(x - 1) - r|).sum := by
  let p := h.normalizedPolynomial
  let s := endpointResidualRoots p
  let m := endpointMultiplicity p
  have hsplit :
      (p.roots.map fun r ↦ Real.log |(x - 1) - r|).sum =
        (m : ℝ) * Real.log |x| +
          (s.map fun r ↦ Real.log |(x - 1) - r|).sum := by
    rw [← replicate_endpoint_add_residual p]
    simp [p, s, m]
  rw [residualPotential,
    h.normalizedResidualConfiguration_weighted_log_sum hres]
  change ((m : ℝ) / (s.card : ℝ)) * Real.log |x| +
      (s.card : ℝ)⁻¹ *
        (s.map fun r ↦ Real.log |(x - 1) - r|).sum =
    (s.card : ℝ)⁻¹ *
      (p.roots.map fun r ↦ Real.log |(x - 1) - r|).sum
  rw [hsplit]
  rw [div_eq_mul_inv]
  ring

/-- The empirical potential is a positive scalar multiple of the residual
potential after the shift `x ↦ x + 1`. -/
theorem empiricalPotential_eq_normalized_residualPotential
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) (x : ℝ) :
    empiricalPotential h.normalizedPolynomial (x - 1) =
      ((endpointResidualRoots h.normalizedPolynomial).card : ℝ) /
          (h.normalizedPolynomial.natDegree : ℝ) *
        residualPotential (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) x := by
  have hn : ((endpointResidualRoots h.normalizedPolynomial).card : ℝ) ≠ 0 := by
    exact_mod_cast (h.normalized_residual_card_pos hres).ne'
  have hd : (h.normalizedPolynomial.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (h.normalized_admissible.monic.natDegree_pos.mpr
      h.normalized_admissible.ne_one).ne'
  rw [empiricalPotential,
    h.normalized_residualPotential_eq_root_log_sum hres]
  field_simp

/-- Consequently the empirical and residual potentials have exactly the same
strict sign after shifting coordinates. -/
theorem normalized_residualPotential_neg_iff_empiricalPotential_neg
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) (x : ℝ) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) x < 0 ↔
      empiricalPotential h.normalizedPolynomial (x - 1) < 0 := by
  rw [h.empiricalPotential_eq_normalized_residualPotential hres]
  have hc : 0 <
      ((endpointResidualRoots h.normalizedPolynomial).card : ℝ) /
        (h.normalizedPolynomial.natDegree : ℝ) := by
    exact div_pos
      (by exact_mod_cast h.normalized_residual_card_pos hres)
      (by
        exact_mod_cast (h.normalized_admissible.monic.natDegree_pos.mpr
          h.normalized_admissible.ne_one))
  constructor
  · intro hx
    exact mul_neg_of_pos_of_neg hc hx
  · intro hx
    apply lt_of_not_ge
    intro hnonneg
    exact (not_lt_of_ge (mul_nonneg hc.le hnonneg)) hx

/-- Away from polynomial roots, the residual potential is exactly the
residual-card normalization of `log |p|`. -/
theorem normalized_residualPotential_eq_log_abs_eval
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {x : ℝ} (hx : x ∉ rootSet h.normalizedPolynomial) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) (x + 1) =
      ((endpointResidualRoots h.normalizedPolynomial).card : ℝ)⁻¹ *
        Real.log |h.normalizedPolynomial.eval x| := by
  rw [h.normalized_residualPotential_eq_root_log_sum hres]
  rw [show x + 1 - 1 = x by ring,
    ← log_abs_eval_eq_sum_log_abs_roots h.normalized_admissible hx]

/-- The shifted polynomial roots are precisely the endpoint pole at zero and
the distinct residual pole locations. -/
lemma shifted_mem_normalized_roots_iff
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) (x : ℝ) :
    x - 1 ∈ h.normalizedPolynomial.roots ↔
      x = 0 ∨
        ∃ i : NormalizedResidualIndex h,
          x = (h.normalizedResidualConfiguration hres).location i := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hxne : x - 1 ≠ (-1 : ℝ) := by
        intro heq
        apply hx0
        linarith
      have hxs : x - 1 ∈ endpointResidualRoots h.normalizedPolynomial :=
        mem_endpointResidualRoots.mpr ⟨hx, hxne⟩
      let i : NormalizedResidualIndex h :=
        ⟨x - 1, Multiset.mem_toFinset.mpr hxs⟩
      refine ⟨i, ?_⟩
      change x = (x - 1) + 1
      ring
  · rintro (rfl | ⟨i, rfl⟩)
    · simpa using! h.neg_one_mem_normalized_roots
    · have hi : (i : ℝ) ∈ endpointResidualRoots h.normalizedPolynomial :=
        Multiset.mem_toFinset.mp i.property
      simpa using! (mem_endpointResidualRoots.mp hi).1

/-- The endpoint component boundary, shifted by `+1`, is a residual
separation point with potential exactly zero. -/
theorem normalized_boundary_isResidualSeparationPoint
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    IsResidualSeparationPoint (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h)
      (h.normalizedRightBoundary + 1) := by
  have hbnot : h.normalizedRightBoundary ∉
      sublevelSet h.normalizedPolynomial := by
    simpa [normalizedRightBoundary] using!
      sublevelComponent_sSup_not_mem h.normalized_admissible
        (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  have hbnotroot : h.normalizedRightBoundary ∉
      rootSet h.normalizedPolynomial := by
    intro hb
    exact hbnot (rootSet_subset_sublevelSet h.normalizedPolynomial hb)
  refine ⟨by linarith [h.normalizedRightBoundary_nonneg], ?_, ?_⟩
  · intro i
    have hi : (i : ℝ) ∈ endpointResidualRoots h.normalizedPolynomial :=
      Multiset.mem_toFinset.mp i.property
    change h.normalizedRightBoundary + 1 < (i : ℝ) + 1
    linarith [h.normalizedRightBoundary_lt_residual_root hi]
  · have hpotential :=
      h.normalized_residualPotential_eq_log_abs_eval hres hbnotroot
    rw [h.normalizedRightBoundary_abs_eval_eq_one, Real.log_one,
      mul_zero] at hpotential
    rw [hpotential]

theorem exists_normalized_isResidualSeparationPoint
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    ∃ b, IsResidualSeparationPoint (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) b :=
  ⟨h.normalizedRightBoundary + 1,
    h.normalized_boundary_isResidualSeparationPoint hres⟩

/-- Exact equality of the shifted polynomial sublevel set and the residual
negative set with its pole locations restored. -/
theorem shifted_sublevelSet_eq_residualNegativeWithPoles
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    {x : ℝ | x - 1 ∈ sublevelSet h.normalizedPolynomial} =
      residualNegativeWithPoles (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  ext x
  change (x - 1 ∈ sublevelSet h.normalizedPolynomial) ↔
    x = 0 ∨
      (∃ i : NormalizedResidualIndex h,
        x = (h.normalizedResidualConfiguration hres).location i) ∨
      residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) x < 0
  by_cases hxroot : x - 1 ∈ h.normalizedPolynomial.roots
  · constructor
    · intro hx
      exact Or.imp_right (fun hi ↦ Or.inl hi)
        ((h.shifted_mem_normalized_roots_iff hres x).mp hxroot)
    · intro hx
      exact root_mem_sublevelSet hxroot
  · have hpoles : ¬ (x = 0 ∨
        ∃ i : NormalizedResidualIndex h,
          x = (h.normalizedResidualConfiguration hres).location i) := by
      intro hpoles
      exact hxroot ((h.shifted_mem_normalized_roots_iff hres x).mpr hpoles)
    have hxrootSet : x - 1 ∉ rootSet h.normalizedPolynomial := by
      simpa only [mem_rootSet_iff] using! hxroot
    constructor
    · intro hxsub
      right
      right
      apply (h.normalized_residualPotential_neg_iff_empiricalPotential_neg
        hres x).mpr
      exact (empiricalPotential_neg_iff_sublevel h.normalized_admissible
        hxrootSet).mpr hxsub
    · rintro (hx0 | hi | hpotential)
      · exact False.elim (hpoles (Or.inl hx0))
      · exact False.elim (hpoles (Or.inr hi))
      · apply (empiricalPotential_neg_iff_sublevel
          h.normalized_admissible hxrootSet).mp
        exact (h.normalized_residualPotential_neg_iff_empiricalPotential_neg
          hres x).mp hpotential

/-- The residual model also preserves the sublevel volume exactly. -/
theorem volume_residualNegativeWithPoles_eq_normalized_sublevelVolume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    volume (residualNegativeWithPoles (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h)) =
      sublevelVolume h.normalizedPolynomial := by
  rw [← h.shifted_sublevelSet_eq_residualNegativeWithPoles hres]
  rw [sublevelVolume]
  change volume ((fun x : ℝ ↦ x + (-1)) ⁻¹'
      sublevelSet h.normalizedPolynomial) =
    volume (sublevelSet h.normalizedPolynomial)
  exact measure_preimage_add_right (volume : MeasureTheory.Measure ℝ) (-1)
    (sublevelSet h.normalizedPolynomial)

theorem volume_residualNegativeWithPoles_eq_sublevelVolume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    volume (residualNegativeWithPoles (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h)) = sublevelVolume f :=
  (h.volume_residualNegativeWithPoles_eq_normalized_sublevelVolume hres).trans
    h.normalized_sublevelVolume

end EndpointNormalizationHypotheses

/-! ## Local component radius -/

/-- The contribution to the residual potential away from one distinguished
residual pole, evaluated at an arbitrary point. -/
def residualBackgroundAway {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) (x : ℝ) : ℝ := by
  classical
  exact k * Real.log |x| +
    ∑ j ∈ Finset.univ.erase i,
      C.weight j * Real.log |x - C.location j|

lemma residualPotential_eq_backgroundAway_add {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) (x : ℝ) :
    residualPotential C k x = residualBackgroundAway C k i x +
      C.weight i * Real.log |x - C.location i| := by
  classical
  rw [residualPotential, residualBackgroundAway,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  ring

lemma residualBackgroundAway_location {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) :
    residualBackgroundAway C k i (C.location i) =
      residualBackgroundAt C k i := by
  rw [residualBackgroundAway, residualBackgroundAt,
    abs_of_pos (lt_of_lt_of_le zero_lt_one (C.location_mem i).1)]

/-- Log-concavity of distance to a point lying strictly outside an interval,
written with the barycentric weights of an interior point. -/
lemma weighted_log_abs_sub_le_log_abs_sub
    {a d b y : ℝ} (had : a < d) (hdb : d < b)
    (hy : y < a ∨ b < y) :
    (b - d) / (b - a) * Real.log |a - y| +
        (d - a) / (b - a) * Real.log |b - y| ≤
      Real.log |d - y| := by
  have hab : 0 < b - a := by linarith
  have hlam : 0 ≤ (b - d) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hdb.le) hab.le
  have hmu : 0 ≤ (d - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr had.le) hab.le
  have hsum : (b - d) / (b - a) + (d - a) / (b - a) = 1 := by
    field_simp [hab.ne']
    ring
  have hay : 0 < |a - y| := by
    rw [abs_pos]
    rcases hy with hy | hy <;> linarith
  have hby : 0 < |b - y| := by
    rw [abs_pos]
    rcases hy with hy | hy <;> linarith
  have hmean :
      (b - d) / (b - a) * |a - y| +
          (d - a) / (b - a) * |b - y| = |d - y| := by
    rcases hy with hy | hy
    · rw [abs_of_pos (by linarith : 0 < a - y),
          abs_of_pos (by linarith : 0 < b - y),
          abs_of_pos (by linarith : 0 < d - y)]
      field_simp [hab.ne']
      ring
    · rw [abs_of_neg (by linarith : a - y < 0),
          abs_of_neg (by linarith : b - y < 0),
          abs_of_neg (by linarith : d - y < 0)]
      field_simp [hab.ne']
      ring
  have hconcave := strictConcaveOn_log_Ioi.concaveOn.2
    (show |a - y| ∈ Ioi (0 : ℝ) from hay)
    (show |b - y| ∈ Ioi (0 : ℝ) from hby)
    hlam hmu hsum
  simpa only [smul_eq_mul, hmean] using! hconcave

/-- Analytic form of the manuscript's local component-radius lemma.  If two
zeros of the residual potential surround exactly one residual pole, their
distance is at least twice that pole's explicit residual radius. -/
theorem two_mul_residualRadius_le_of_local_endpoints
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k a b : ℝ} (i : ι) (hk : 0 ≤ k) (ha0 : 0 < a)
    (hai : a < C.location i) (hib : C.location i < b)
    (hout : ∀ j, j ≠ i → C.location j < a ∨ b < C.location j)
    (hWa : residualPotential C k a = 0)
    (hWb : residualPotential C k b = 0) :
    2 * residualRadius C k i ≤ b - a := by
  classical
  let d := C.location i
  have hadi : a < d := by simpa [d] using! hai
  have hdib : d < b := by simpa [d] using! hib
  let lam := (b - d) / (b - a)
  let mu := (d - a) / (b - a)
  have hab : 0 < b - a := by linarith
  have hlam0 : 0 < lam := by
    exact div_pos (sub_pos.mpr hdib) hab
  have hmu0 : 0 < mu := by
    exact div_pos (sub_pos.mpr hadi) hab
  have hlammu : lam + mu = 1 := by
    dsimp [lam, mu]
    field_simp [hab.ne']
    ring
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hlogzero :
      lam * Real.log a + mu * Real.log b ≤ Real.log d := by
    have hlog := weighted_log_abs_sub_le_log_abs_sub
      (a := a) (d := d) (b := b) (y := 0)
      (by simpa [d] using! hai) (by simpa [d] using! hib) (Or.inl ha0)
    simpa [abs_of_pos ha0, abs_of_pos (by linarith : 0 < b),
      abs_of_pos hd0] using! hlog
  have hklog :
      lam * (k * Real.log a) + mu * (k * Real.log b) ≤
        k * Real.log d := by
    have := mul_le_mul_of_nonneg_left hlogzero hk
    nlinarith
  have hsumlog :
      lam * (∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |a - C.location j|) +
        mu * (∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |b - C.location j|) ≤
      ∑ j ∈ Finset.univ.erase i,
        C.weight j * Real.log |d - C.location j| := by
    calc
      lam * (∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |a - C.location j|) +
          mu * (∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |b - C.location j|) =
        ∑ j ∈ Finset.univ.erase i, C.weight j *
          (lam * Real.log |a - C.location j| +
            mu * Real.log |b - C.location j|) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |d - C.location j| := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (C.weight_pos j).le
        apply weighted_log_abs_sub_le_log_abs_sub
        · simpa [d] using! hai
        · simpa [d] using! hib
        · exact hout j (Finset.mem_erase.mp hj).1
  have hbackground :
      lam * residualBackgroundAway C k i a +
          mu * residualBackgroundAway C k i b ≤
        residualBackgroundAt C k i := by
    change lam * (k * Real.log |a| +
        ∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |a - C.location j|) +
      mu * (k * Real.log |b| +
        ∑ j ∈ Finset.univ.erase i,
          C.weight j * Real.log |b - C.location j|) ≤
      k * Real.log d + ∑ j ∈ Finset.univ.erase i,
        C.weight j * Real.log |d - C.location j|
    rw [abs_of_pos ha0, abs_of_pos (by linarith : 0 < b)]
    nlinarith [hklog, hsumlog]
  have hbacka : residualBackgroundAway C k i a =
      -C.weight i * Real.log (d - a) := by
    have hdecomp := residualPotential_eq_backgroundAway_add C k i a
    rw [hWa, abs_of_neg (by linarith [hai])] at hdecomp
    have harg : -(a - C.location i) = d - a := by simp [d]
    rw [harg] at hdecomp
    linarith
  have hbackb : residualBackgroundAway C k i b =
      -C.weight i * Real.log (b - d) := by
    have hdecomp := residualPotential_eq_backgroundAway_add C k i b
    rw [hWb, abs_of_pos (by linarith [hib])] at hdecomp
    have harg : b - C.location i = b - d := by rfl
    rw [harg] at hdecomp
    linarith
  have hlogradius :
      Real.log (residualRadius C k i) ≤
        lam * Real.log (d - a) + mu * Real.log (b - d) := by
    rw [log_residualRadius]
    rw [hbacka, hbackb] at hbackground
    have hwi := C.weight_pos i
    field_simp [hwi.ne']
    nlinarith
  have hlogmean :
      lam * Real.log (d - a) + mu * Real.log (b - d) ≤
        Real.log (lam * (d - a) + mu * (b - d)) := by
    have hconcave := strictConcaveOn_log_Ioi.concaveOn.2
      (show d - a ∈ Ioi (0 : ℝ) from sub_pos.mpr hadi)
      (show b - d ∈ Ioi (0 : ℝ) from sub_pos.mpr hdib)
      hlam0.le hmu0.le hlammu
    simpa only [smul_eq_mul] using! hconcave
  let q := lam * (d - a) + mu * (b - d)
  have hqpos : 0 < q := by
    exact add_pos (mul_pos hlam0 (sub_pos.mpr hadi))
      (mul_pos hmu0 (sub_pos.mpr hdib))
  have hradius_le_q : residualRadius C k i ≤ q := by
    have hlog : Real.log (residualRadius C k i) ≤ Real.log q :=
      hlogradius.trans hlogmean
    calc
      residualRadius C k i = Real.exp (Real.log (residualRadius C k i)) := by
        rw [Real.exp_log (residualRadius_pos C k i)]
      _ ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr hlog
      _ = q := Real.exp_log hqpos
  have hqle : q ≤ (b - a) / 2 := by
    have hsquare : 0 ≤ ((d - a) - (b - d)) ^ 2 := sq_nonneg _
    dsimp [q, lam, mu]
    field_simp [hab.ne']
    nlinarith
  nlinarith

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- Polynomial form of the local component-radius lemma: every residual
component has width at least twice its aggregated residual radius. -/
theorem two_mul_residualRadius_le_normalized_component_width
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (i : NormalizedResidualIndex h) :
    2 * residualRadius (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) i ≤
      sSup (sublevelComponent h.normalizedPolynomial (i : ℝ)) -
        sInf (sublevelComponent h.normalizedPolynomial (i : ℝ)) := by
  let p := h.normalizedPolynomial
  let r : ℝ := i
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hirres : r ∈ endpointResidualRoots p := by
    exact Multiset.mem_toFinset.mp i.property
  have hirroot : r ∈ p.roots := (mem_endpointResidualRoots.mp hirres).1
  have hirne : r ≠ (-1 : ℝ) := (mem_endpointResidualRoots.mp hirres).2
  have hirsub : r ∈ sublevelSet p := root_mem_sublevelSet hirroot
  let a := sInf (sublevelComponent p r)
  let b := sSup (sublevelComponent p r)
  have hcomponent : sublevelComponent p r = Ioo a b := by
    simpa [p, r, a, b] using!
      sublevelComponent_eq_Ioo h.normalized_admissible hirsub
  have hrI : r ∈ Ioo a b := by
    rw [← hcomponent]
    exact mem_connectedComponentIn hirsub
  have ha_not_sub : a ∉ sublevelSet p := by
    simpa [p, r, a] using!
      sublevelComponent_sInf_not_mem h.normalized_admissible hirsub
  have hb_not_sub : b ∉ sublevelSet p := by
    simpa [p, r, b] using!
      sublevelComponent_sSup_not_mem h.normalized_admissible hirsub
  have ha_not_root : a ∉ rootSet p := by
    intro ha
    exact ha_not_sub (rootSet_subset_sublevelSet p ha)
  have hb_not_root : b ∉ rootSet p := by
    intro hb
    exact hb_not_sub (rootSet_subset_sublevelSet p hb)
  have hend := sublevelComponent_endpoints_frontier
    h.normalized_admissible hirsub
  have haeval : |p.eval a| = 1 := by
    simpa [p, r, a] using! frontier_sublevelSet_abs_eval_eq_one p hend.1
  have hbeval : |p.eval b| = 1 := by
    simpa [p, r, b] using! frontier_sublevelSet_abs_eval_eq_one p hend.2
  have hr0 : 0 ≤ r := by
    have hrIcc := h.normalized_residual_root_mem_Icc hirres
    linarith [hrIcc.1, h.normalizedRightBoundary_nonneg]
  have hneg_not_component : (-1 : ℝ) ∉ sublevelComponent p r := by
    intro hnegC
    have hcomponents : sublevelComponent p r = sublevelComponent p (-1) :=
      connectedComponentIn_eq hnegC
    have hrequal := h.normalized_componentAtomized hirroot
      h.neg_one_mem_normalized_roots hcomponents
    exact hirne hrequal
  have hneg_b : (-1 : ℝ) < b := by linarith [hrI.2, hr0]
  have hneg_le_a : (-1 : ℝ) ≤ a := by
    apply le_of_not_gt
    intro hnega
    apply hneg_not_component
    rw [hcomponent]
    exact ⟨hnega, hneg_b⟩
  have hneg_ne_a : (-1 : ℝ) ≠ a := by
    intro hnega
    apply ha_not_sub
    rw [← hnega]
    exact root_mem_sublevelSet h.neg_one_mem_normalized_roots
  have hneg_a : (-1 : ℝ) < a := lt_of_le_of_ne hneg_le_a hneg_ne_a
  have hout : ∀ j, j ≠ i →
      C.location j < a + 1 ∨ b + 1 < C.location j := by
    intro j hji
    let q : ℝ := j
    have hjres : q ∈ endpointResidualRoots p := by
      exact Multiset.mem_toFinset.mp j.property
    have hjroot : q ∈ p.roots := (mem_endpointResidualRoots.mp hjres).1
    have hqoutside : q < a ∨ b < q := by
      rcases lt_trichotomy q a with hqa | hqa | haq
      · exact Or.inl hqa
      · exfalso
        apply ha_not_sub
        rw [← hqa]
        exact root_mem_sublevelSet hjroot
      · rcases lt_trichotomy b q with hbq | hbq | hqb
        · exact Or.inr hbq
        · exfalso
          apply hb_not_sub
          rw [hbq]
          exact root_mem_sublevelSet hjroot
        · exfalso
          have hqC : q ∈ sublevelComponent p r := by
            rw [hcomponent]
            exact ⟨haq, hqb⟩
          have hcomponents : sublevelComponent p r =
              sublevelComponent p q := connectedComponentIn_eq hqC
          have hrq := h.normalized_componentAtomized hirroot hjroot hcomponents
          apply hji
          apply Subtype.ext
          exact hrq.symm
    change (j : ℝ) + 1 < a + 1 ∨ b + 1 < (j : ℝ) + 1
    rcases hqoutside with hqoutside | hqoutside
    · exact Or.inl (by simpa [q] using! add_lt_add_right hqoutside 1)
    · exact Or.inr (by simpa [q] using! add_lt_add_right hqoutside 1)
  have hWa : residualPotential C k (a + 1) = 0 := by
    have hpotential := h.normalized_residualPotential_eq_log_abs_eval
      hres ha_not_root
    change residualPotential C k (a + 1) =
      ((endpointResidualRoots p).card : ℝ)⁻¹ * Real.log |p.eval a|
      at hpotential
    rw [haeval, Real.log_one, mul_zero] at hpotential
    exact hpotential
  have hWb : residualPotential C k (b + 1) = 0 := by
    have hpotential := h.normalized_residualPotential_eq_log_abs_eval
      hres hb_not_root
    change residualPotential C k (b + 1) =
      ((endpointResidualRoots p).card : ℝ)⁻¹ * Real.log |p.eval b|
      at hpotential
    rw [hbeval, Real.log_one, mul_zero] at hpotential
    exact hpotential
  have hk : 0 ≤ k := by
    linarith [h.one_le_normalizedEndpointResidualRatio hres]
  have hlocal := two_mul_residualRadius_le_of_local_endpoints C i hk
    (by linarith [hneg_a])
    (by change a + 1 < (i : ℝ) + 1; linarith [hrI.1])
    (by change (i : ℝ) + 1 < b + 1; linarith [hrI.2])
    hout hWa hWb
  change 2 * residualRadius C k i ≤ b - a
  linarith

/-- Measure form of the local radius bound. -/
theorem ofReal_two_mul_residualRadius_le_normalized_component_volume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (i : NormalizedResidualIndex h) :
    ENNReal.ofReal
        (2 * residualRadius (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h) i) ≤
      volume (sublevelComponent h.normalizedPolynomial (i : ℝ)) := by
  have hi : (i : ℝ) ∈ h.normalizedPolynomial.roots :=
    (mem_endpointResidualRoots.mp
      (Multiset.mem_toFinset.mp i.property)).1
  rw [sublevelComponent_eq_Ioo h.normalized_admissible
    (root_mem_sublevelSet hi), Real.volume_Ioo]
  exact ENNReal.ofReal_le_ofReal
    (h.two_mul_residualRadius_le_normalized_component_width hres i)

/-- The normalized polynomial supplies all hypotheses of the residual-deficit
radius estimate; only the explicit upper bound on `k` remains to be checked in
the low-`k` case split. -/
theorem normalizedResidualRadiusSum_gt_one_third
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (hk : normalizedEndpointResidualRatio h ≤ 29 / 20) :
    1 / 3 < residualRadiusSum (h.normalizedResidualConfiguration hres)
      (normalizedEndpointResidualRatio h) := by
  exact residualRadiusSum_gt_one_third_of_separation
    (h.normalizedResidualConfiguration hres)
    (h.one_le_normalizedEndpointResidualRatio hres) hk
    (h.normalizedResidualConfiguration_location_injective hres)
    (h.normalized_boundary_isResidualSeparationPoint hres)

theorem two_lt_sqrt_two_add_twice_normalizedResidualRadiusSum
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (hk : normalizedEndpointResidualRatio h ≤ 29 / 20) :
    2 < Real.sqrt 2 +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  exact two_lt_sqrt_two_add_twice_residualRadiusSum_of_separation
    (h.normalizedResidualConfiguration hres)
    (h.one_le_normalizedEndpointResidualRatio hres) hk
    (h.normalizedResidualConfiguration_location_injective hres)
    (h.normalized_boundary_isResidualSeparationPoint hres)

end EndpointNormalizationHypotheses

end

end Erdos1038
