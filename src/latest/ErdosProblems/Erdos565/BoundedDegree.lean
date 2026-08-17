import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Janson
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# A bounded one-degree Janson witness

This file repairs the small compactness gap in the bounded one-degree argument used in the
proof of Erdős problem 565.  The admissible set of strict Janson witnesses is open, so an
energy-minimising witness need not exist.  We instead take the infimum of the one-degree
energies and use a uniform contraction to contradict its defining property.
-/

open scoped BigOperators NNReal

namespace Erdos565
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum of the squares of the weighted singleton degrees. -/
def oneDegreeEnergy (H : Hypergraph V) (ν : EdgeWeight H) : ℝ :=
  ∑ v : V, weightedDegree H ν {v} ^ 2

lemma oneDegreeEnergy_nonneg (H : Hypergraph V) (ν : EdgeWeight H) :
    0 ≤ oneDegreeEnergy H ν := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma oneDegreeEnergy_add (H : Hypergraph V) (ν μ : EdgeWeight H) :
    oneDegreeEnergy H (ν + μ) =
      oneDegreeEnergy H ν + 2 * (∑ v : V,
        weightedDegree H ν {v} * weightedDegree H μ {v}) + oneDegreeEnergy H μ := by
  simp only [oneDegreeEnergy, weightedDegree_add]
  simp_rw [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

lemma oneDegreeEnergy_scale (H : Hypergraph V) (c : ℝ≥0) (ν : EdgeWeight H) :
    oneDegreeEnergy H (scale c ν) = (c : ℝ) ^ 2 * oneDegreeEnergy H ν := by
  simp only [oneDegreeEnergy, weightedDegree_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- In a uniform hypergraph the sum of the singleton degrees is the rank times the mass. -/
lemma sum_weightedDegree_singleton_eq {H : Hypergraph V} {s : ℕ}
    (hH : H.IsUniform s) (ν : EdgeWeight H) :
    (∑ v : V, weightedDegree H ν {v}) = (s : ℝ) * mass H ν := by
  classical
  simp only [weightedDegree, mass, Finset.singleton_subset_iff]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ E ∈ H, ∑ v : V, if v ∈ E then (ν E : ℝ) else 0) =
        ∑ E ∈ H, (E.card : ℝ) * (ν E : ℝ) := by
          apply Finset.sum_congr rfl
          intro E hE
          simp
    _ = ∑ E ∈ H, (s : ℝ) * (ν E : ℝ) := by
          apply Finset.sum_congr rfl
          intro E hE
          rw [hH E hE]
    _ = (s : ℝ) * ∑ E ∈ H, (ν E : ℝ) := by
          rw [Finset.mul_sum]

/-- Extend a normalized witness on a restriction by zero. -/
lemma exists_normalized_of_restrict_isJanson {H : Hypergraph V} {W : Finset V}
    {p R y : ℝ} (hJ : (H.restrict W).IsJanson p R)
    (hp : 0 < p) (hR : 0 < R) (hy : 0 < y) :
    ∃ ν : EdgeWeight H,
      mass H ν = y ∧ Lambda H p ν < y ^ 2 / R ∧
        ∀ E, E ∉ H.restrict W → ν E = 0 := by
  obtain ⟨ν, hmass, hLambda⟩ := hJ.exists_normalized hp hR hy
  let μ : EdgeWeight H := zeroExtend (H.restrict_subset W) ν
  refine ⟨μ, ?_, ?_, ?_⟩
  · simpa [μ, mass_zeroExtend] using hmass
  · simpa [μ, Lambda_zeroExtend] using hLambda
  · intro E hE
    simp [μ, hE]

/-- Convex combination of two nonnegative edge weights. -/
def convexWeight {H : Hypergraph V} (t : ℝ≥0) (ν μ : EdgeWeight H) : EdgeWeight H :=
  scale (1 - t) ν + scale t μ

lemma mass_convexWeight {H : Hypergraph V} {t : ℝ≥0} (ht : t ≤ 1)
    (ν μ : EdgeWeight H) :
    mass H (convexWeight t ν μ) =
      (1 - (t : ℝ)) * mass H ν + (t : ℝ) * mass H μ := by
  rw [convexWeight, mass_add, mass_scale, mass_scale]
  norm_cast
  rw [NNReal.coe_sub ht]
  norm_num

lemma weightedDegree_convexWeight {H : Hypergraph V} {t : ℝ≥0} (ht : t ≤ 1)
    (ν μ : EdgeWeight H) (L : Finset V) :
    weightedDegree H (convexWeight t ν μ) L =
      (1 - (t : ℝ)) * weightedDegree H ν L +
        (t : ℝ) * weightedDegree H μ L := by
  rw [convexWeight, weightedDegree_add, weightedDegree_scale, weightedDegree_scale]
  norm_cast
  rw [NNReal.coe_sub ht]
  norm_num

lemma oneDegreeEnergy_convexWeight {H : Hypergraph V} {t : ℝ≥0} (ht : t ≤ 1)
    (ν μ : EdgeWeight H) :
    oneDegreeEnergy H (convexWeight t ν μ) =
      (1 - (t : ℝ)) ^ 2 * oneDegreeEnergy H ν +
        2 * (1 - (t : ℝ)) * (t : ℝ) *
          (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) +
        (t : ℝ) ^ 2 * oneDegreeEnergy H μ := by
  simp only [oneDegreeEnergy, weightedDegree_convexWeight ht]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- The Janson energy is convex as a function of the edge weight. -/
lemma Lambda_convexWeight {H : Hypergraph V} {p : ℝ} (hp : 0 < p)
    {t : ℝ≥0} (ht : t ≤ 1) (ν μ : EdgeWeight H) :
    Lambda H p (convexWeight t ν μ) ≤
      (1 - (t : ℝ)) * Lambda H p ν + (t : ℝ) * Lambda H p μ := by
  simp only [Lambda]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro L hL
  rw [weightedDegree_convexWeight ht]
  have ht0 : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have hconv := Erdos565.FiniteAnalysis.sq_convex_combination_le
    (a := weightedDegree H μ L) (b := weightedDegree H ν L) ht0 ht1
  have hden : 0 < p ^ L.card := pow_pos hp _
  rw [div_le_iff₀ hden]
  calc
    ((1 - (t : ℝ)) * weightedDegree H ν L +
          (t : ℝ) * weightedDegree H μ L) ^ 2 ≤
        (t : ℝ) * weightedDegree H μ L ^ 2 +
          (1 - (t : ℝ)) * weightedDegree H ν L ^ 2 := by
            simpa [add_comm] using hconv
    _ = ((1 - (t : ℝ)) *
          (weightedDegree H ν L ^ 2 / p ^ L.card) +
        (t : ℝ) * (weightedDegree H μ L ^ 2 / p ^ L.card)) * p ^ L.card := by
          field_simp
          ring

lemma weightedDegree_eq_zero_of_supported_on {H : Hypergraph V} {W : Finset V}
    (ν : EdgeWeight H) (hsupp : ∀ E, E ∉ H.restrict W → ν E = 0)
    {v : V} (hv : v ∉ W) : weightedDegree H ν {v} = 0 := by
  rw [weightedDegree]
  apply Finset.sum_eq_zero
  intro E hE
  have hEnot : E ∉ H.restrict W := by
    intro hEr
    have hsub := (mem_restrict.mp hEr).2
    have hcontains : {v} ⊆ E := (Finset.mem_filter.mp hE).2
    exact hv (hsub (Finset.singleton_subset_iff.mp hcontains))
  simp [hsupp E hEnot]

/-- The singleton energy is at most the square of the sum of singleton degrees. -/
lemma oneDegreeEnergy_le_sq_sum (H : Hypergraph V) (ν : EdgeWeight H) :
    oneDegreeEnergy H ν ≤ (∑ v : V, weightedDegree H ν {v}) ^ 2 := by
  exact Erdos565.FiniteAnalysis.sum_sq_le_sq_sum_of_nonneg Finset.univ
    (fun v ↦ weightedDegree H ν {v})
    (fun v _ ↦ weightedDegree_nonneg H ν {v})

/-- A normalized weight on an `s`-uniform hypergraph has singleton energy at most
`s²` times the square of its mass. -/
lemma oneDegreeEnergy_le_uniform {H : Hypergraph V} {s : ℕ}
    (hH : H.IsUniform s) (ν : EdgeWeight H) :
    oneDegreeEnergy H ν ≤ (s : ℝ) ^ 2 * mass H ν ^ 2 := by
  calc
    oneDegreeEnergy H ν ≤ (∑ v : V, weightedDegree H ν {v}) ^ 2 :=
      oneDegreeEnergy_le_sq_sum H ν
    _ = (s : ℝ) ^ 2 * mass H ν ^ 2 := by
      rw [sum_weightedDegree_singleton_eq hH]
      ring

/-- The fixed interpolation parameter used in the infimum argument. -/
noncomputable def contractionParameter (β M : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (1 / (2 * β * M))

lemma contractionParameter_pos {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) :
    0 < contractionParameter β M := by
  apply lt_min
  · norm_num
  · positivity

lemma contractionParameter_le_half (β M : ℝ) :
    contractionParameter β M ≤ 1 / 2 := min_le_left _ _

lemma contractionParameter_mul_le_half {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) :
    contractionParameter β M * (β * M) ≤ 1 / 2 := by
  have ht := min_le_right (1 / 2 : ℝ) (1 / (2 * β * M))
  have hβM : 0 < β * M := mul_pos hβ hM
  calc
    contractionParameter β M * (β * M) ≤
        (1 / (2 * β * M)) * (β * M) :=
      mul_le_mul_of_nonneg_right ht hβM.le
    _ = 1 / 2 := by field_simp

lemma contractionParameter_le_one (β M : ℝ) : contractionParameter β M ≤ 1 :=
  (contractionParameter_le_half β M).trans (by norm_num)

lemma contractionFactor_pos {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) :
    0 < 1 - contractionParameter β M / 2 := by
  have ht := contractionParameter_le_half β M
  linarith

lemma contractionFactor_lt_one {β M : ℝ} (hβ : 0 < β) (hM : 0 < M) :
    1 - contractionParameter β M / 2 < 1 := by
  have ht := contractionParameter_pos hβ hM
  linarith

private def normalizedWitnessEnergies (H : Hypergraph V) (p R : ℝ) : Set ℝ :=
  {q | ∃ ν : EdgeWeight H,
    mass H ν = Real.sqrt R ∧ Lambda H p ν < 1 ∧ q = oneDegreeEnergy H ν}

private lemma normalizedWitnessEnergies_bddBelow (H : Hypergraph V) (p R : ℝ) :
    BddBelow (normalizedWitnessEnergies H p R) := by
  refine ⟨0, ?_⟩
  rintro q ⟨ν, -, -, rfl⟩
  exact oneDegreeEnergy_nonneg H ν

private lemma exists_normalized_unit_of_restrict_isJanson {H : Hypergraph V}
    {W : Finset V} {p R : ℝ} (hJ : (H.restrict W).IsJanson p R)
    (hp : 0 < p) (hR : 0 < R) :
    ∃ ν : EdgeWeight H,
      mass H ν = Real.sqrt R ∧ Lambda H p ν < 1 ∧
        ∀ E, E ∉ H.restrict W → ν E = 0 := by
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  obtain ⟨ν, hm, hL, hsupp⟩ :=
    exists_normalized_of_restrict_isJanson hJ hp hR hsqrt
  refine ⟨ν, hm, ?_, hsupp⟩
  calc
    Lambda H p ν < Real.sqrt R ^ 2 / R := hL
    _ = 1 := by rw [Real.sq_sqrt hR.le]; exact div_self hR.ne'

private lemma lowDegreeSet_large (C : Finset V) {H : Hypergraph V} {s : ℕ}
    (hH : H.IsUniform s) (hs : 0 < s) (ν : EdgeWeight H) {y β : ℝ}
    (hmass : mass H ν = y) (hy : 0 < y) (hβ : 0 < β)
    (hC : 0 < C.card) :
    let M : ℝ := C.card
    let T : ℝ := (s : ℝ) * y / (β * M)
    let W := C.filter fun v : V ↦ weightedDegree H ν {v} ≤ T
    (1 - β) * M ≤ W.card := by
  classical
  dsimp only
  let M : ℝ := C.card
  let T : ℝ := (s : ℝ) * y / (β * M)
  let W : Finset V := C.filter fun v ↦ weightedDegree H ν {v} ≤ T
  let B : Finset V := C.filter fun v ↦ T < weightedDegree H ν {v}
  have hM : 0 < M := by
    change (0 : ℝ) < C.card
    exact_mod_cast hC
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hBcard : (B.card : ℝ) < β * M := by
    by_cases hB : B.Nonempty
    · have hsumlt : (B.card : ℝ) * T <
          ∑ v ∈ B, weightedDegree H ν {v} := by
        have h := Finset.sum_lt_sum_of_nonempty hB (fun v hv ↦ by
          have := (Finset.mem_filter.mp hv).2
          simpa using this)
        simpa using h
      have hsumle : (∑ v ∈ B, weightedDegree H ν {v}) ≤
          ∑ v : V, weightedDegree H ν {v} := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        intro v hvU hvB
        exact weightedDegree_nonneg H ν {v}
      have htotal : (∑ v : V, weightedDegree H ν {v}) = (s : ℝ) * y := by
        rw [sum_weightedDegree_singleton_eq hH, hmass]
      have hprod : (B.card : ℝ) * T < (s : ℝ) * y :=
        hsumlt.trans_le (hsumle.trans_eq htotal)
      by_contra hnot
      have hle : β * M ≤ (B.card : ℝ) := le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_right hle hT.le
      have heq : (β * M) * T = (s : ℝ) * y := by
        dsimp [T]
        field_simp
      linarith
    · have : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      simp [this, hβ, hM]
  have hpartition : W.card + B.card = C.card := by
    simpa [W, B, not_le] using
      (Finset.card_filter_add_card_filter_not (s := C)
        (fun v ↦ weightedDegree H ν {v} ≤ T))
  have hpartitionR : (W.card : ℝ) + (B.card : ℝ) = M := by
    change (W.card : ℝ) + (B.card : ℝ) = (C.card : ℝ)
    exact_mod_cast hpartition
  linarith

private lemma crossEnergy_le_of_supported_on {H : Hypergraph V} {s : ℕ}
    (hH : H.IsUniform s) (ν μ : EdgeWeight H) {W : Finset V} {T y : ℝ}
    (hν : ∀ v ∈ W, weightedDegree H ν {v} ≤ T)
    (hμmass : mass H μ = y)
    (hμsupp : ∀ E, E ∉ H.restrict W → μ E = 0) :
    (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) ≤
      T * (s : ℝ) * y := by
  classical
  have hout : ∀ v ∈ (Finset.univ : Finset V), v ∉ W →
      weightedDegree H ν {v} * weightedDegree H μ {v} = 0 := by
    intro v hvU hvW
    rw [weightedDegree_eq_zero_of_supported_on μ hμsupp hvW, mul_zero]
  calc
    (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) =
        ∑ v ∈ W, weightedDegree H ν {v} * weightedDegree H μ {v} := by
      symm
      exact Finset.sum_subset (Finset.subset_univ W) hout
    _ ≤ ∑ v ∈ W, T * weightedDegree H μ {v} := by
      exact Finset.sum_le_sum fun v hv ↦
        mul_le_mul_of_nonneg_right (hν v hv) (weightedDegree_nonneg H μ {v})
    _ = T * ∑ v ∈ W, weightedDegree H μ {v} := by rw [Finset.mul_sum]
    _ = T * ∑ v : V, weightedDegree H μ {v} := by
      congr 1
      exact Finset.sum_subset (Finset.subset_univ W) fun v hvU hvW ↦
        weightedDegree_eq_zero_of_supported_on μ hμsupp hvW
    _ = T * (s : ℝ) * y := by
      rw [sum_weightedDegree_singleton_eq hH, hμmass]
      ring

private lemma exists_contracting_normalizedWitness {H : Hypergraph V} {s : ℕ}
    {p R β : ℝ} (hH : H.IsUniform s) (hs : 0 < s) (hp : 0 < p)
    (hR : 0 < R) (hβ : 0 < β) (C : Finset V) (hC : 0 < C.card)
    (hlocal : ∀ W : Finset V,
      W ⊆ C → (1 - β) * (C.card : ℝ) ≤ (W.card : ℝ) →
        (H.restrict W).IsJanson p R)
    (ν : EdgeWeight H) (hνmass : mass H ν = Real.sqrt R)
    (hνLambda : Lambda H p ν < 1)
    (hνenergy :
      2 * (s : ℝ) ^ 2 * (Real.sqrt R) ^ 2 /
          (β * (C.card : ℝ)) < oneDegreeEnergy H ν) :
    ∃ ω : EdgeWeight H,
      mass H ω = Real.sqrt R ∧ Lambda H p ω < 1 ∧
        oneDegreeEnergy H ω <
          (1 - contractionParameter β (C.card : ℝ) / 2) *
            oneDegreeEnergy H ν := by
  classical
  let M : ℝ := C.card
  let y : ℝ := Real.sqrt R
  let t : ℝ := contractionParameter β M
  let T : ℝ := (s : ℝ) * y / (β * M)
  let W : Finset V := C.filter fun v ↦ weightedDegree H ν {v} ≤ T
  have hM : 0 < M := by
    change (0 : ℝ) < C.card
    exact_mod_cast hC
  have hy : 0 < y := by simpa [y] using Real.sqrt_pos.2 hR
  have hβM : 0 < β * M := mul_pos hβ hM
  have ht : 0 < t := contractionParameter_pos hβ hM
  have htHalf : t ≤ 1 / 2 := contractionParameter_le_half β M
  have htLtOne : t < 1 := htHalf.trans_lt (by norm_num)
  have htOne : t ≤ 1 := htLtOne.le
  have htβM : t * (β * M) ≤ 1 / 2 := contractionParameter_mul_le_half hβ hM
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hνmass' : mass H ν = y := by simpa [y] using hνmass
  have hνenergy' : 2 * (s : ℝ) ^ 2 * y ^ 2 / (β * M) <
      oneDegreeEnergy H ν := by simpa [y, M] using hνenergy
  have hνenergyPos : 0 < oneDegreeEnergy H ν := by
    have hleft : 0 < 2 * (s : ℝ) ^ 2 * y ^ 2 / (β * M) := by
      have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
      positivity
    exact hleft.trans hνenergy'
  have hWlarge : (1 - β) * M ≤ (W.card : ℝ) := by
    simpa [M, y, T, W] using lowDegreeSet_large C hH hs ν hνmass' hy hβ hC
  have hWC : W ⊆ C := Finset.filter_subset _ _
  obtain ⟨μ, hμmass, hμLambda, hμsupp⟩ :=
    exists_normalized_unit_of_restrict_isJanson
      (hlocal W hWC (by simpa [M] using hWlarge)) hp hR
  have hμmass' : mass H μ = y := by simpa [y] using hμmass
  have hWdegree : ∀ v ∈ W, weightedDegree H ν {v} ≤ T := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hcrossLe :
      (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) ≤
        T * (s : ℝ) * y :=
    crossEnergy_le_of_supported_on hH ν μ hWdegree hμmass' hμsupp
  have hTidentity : T * (s : ℝ) * y =
      (s : ℝ) ^ 2 * y ^ 2 / (β * M) := by
    dsimp [T]
    field_simp
  have hcross :
      (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) <
        oneDegreeEnergy H ν / 2 := by
    rw [hTidentity] at hcrossLe
    have hrewrite : 2 * (s : ℝ) ^ 2 * y ^ 2 / (β * M) =
        2 * ((s : ℝ) ^ 2 * y ^ 2 / (β * M)) := by ring
    rw [hrewrite] at hνenergy'
    linarith
  have hμenergyLe : oneDegreeEnergy H μ ≤ (s : ℝ) ^ 2 * y ^ 2 := by
    calc
      oneDegreeEnergy H μ ≤ (s : ℝ) ^ 2 * mass H μ ^ 2 :=
        oneDegreeEnergy_le_uniform hH μ
      _ = (s : ℝ) ^ 2 * y ^ 2 := by rw [hμmass']
  have hscaled : 2 * (s : ℝ) ^ 2 * y ^ 2 <
      oneDegreeEnergy H ν * (β * M) := by
    rw [div_lt_iff₀ hβM] at hνenergy'
    simpa [mul_assoc] using hνenergy'
  have hμenergy : oneDegreeEnergy H μ <
      (β * M) * oneDegreeEnergy H ν / 2 := by
    nlinarith
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hτ : τ ≤ 1 := by exact_mod_cast htOne
  let ω : EdgeWeight H := convexWeight τ ν μ
  have hωmass : mass H ω = y := by
    dsimp [ω]
    rw [mass_convexWeight hτ, hνmass', hμmass']
    change (1 - t) * y + t * y = y
    ring
  have hωLambda : Lambda H p ω < 1 := by
    have hconv := Lambda_convexWeight hp hτ ν μ
    change Lambda H p ω ≤
      (1 - t) * Lambda H p ν + t * Lambda H p μ at hconv
    have hstrict : (1 - t) * Lambda H p ν + t * Lambda H p μ <
        (1 - t) * 1 + t * 1 :=
      add_lt_add
        (mul_lt_mul_of_pos_left hνLambda (sub_pos.mpr htLtOne))
        (mul_lt_mul_of_pos_left hμLambda ht)
    exact hconv.trans_lt (by simpa using hstrict)
  have hcrossTerm :
      2 * (1 - t) * t *
          (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) <
        (1 - t) * t * oneDegreeEnergy H ν := by
    have hcoeff : 0 < 2 * (1 - t) * t :=
      mul_pos (mul_pos (by norm_num) (sub_pos.mpr htLtOne)) ht
    have hmul := mul_lt_mul_of_pos_left hcross hcoeff
    calc
      _ < (2 * (1 - t) * t) * (oneDegreeEnergy H ν / 2) := hmul
      _ = (1 - t) * t * oneDegreeEnergy H ν := by ring
  have hμTerm : t ^ 2 * oneDegreeEnergy H μ <
      t ^ 2 * ((β * M) * oneDegreeEnergy H ν / 2) :=
    mul_lt_mul_of_pos_left hμenergy (sq_pos_of_pos ht)
  have hthird : t ^ 2 * ((β * M) * oneDegreeEnergy H ν / 2) ≤
      t * oneDegreeEnergy H ν / 4 := by
    have hmul := mul_le_mul_of_nonneg_right htβM
      (mul_nonneg ht.le hνenergyPos.le)
    have hmul' := mul_le_mul_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      _ = ((t * (β * M)) * (t * oneDegreeEnergy H ν)) * (1 / 2) := by ring
      _ ≤ ((1 / 2) * (t * oneDegreeEnergy H ν)) * (1 / 2) := hmul'
      _ = t * oneDegreeEnergy H ν / 4 := by ring
  have hcoef :
      (1 - t) ^ 2 * oneDegreeEnergy H ν +
          (1 - t) * t * oneDegreeEnergy H ν +
          t ^ 2 * ((β * M) * oneDegreeEnergy H ν / 2) ≤
        (1 - t / 2) * oneDegreeEnergy H ν := by
    calc
      _ ≤ (1 - t) ^ 2 * oneDegreeEnergy H ν +
          (1 - t) * t * oneDegreeEnergy H ν +
          t * oneDegreeEnergy H ν / 4 := by
            have hx := add_le_add_left hthird
              ((1 - t) ^ 2 * oneDegreeEnergy H ν +
                (1 - t) * t * oneDegreeEnergy H ν)
            convert hx using 1 <;> ring
      _ ≤ (1 - t / 2) * oneDegreeEnergy H ν := by
        have htQ : 0 ≤ t * oneDegreeEnergy H ν :=
          mul_nonneg ht.le hνenergyPos.le
        nlinarith
  have hωeq := oneDegreeEnergy_convexWeight hτ ν μ
  have hωenergy : oneDegreeEnergy H ω <
      (1 - t / 2) * oneDegreeEnergy H ν := by
    change oneDegreeEnergy H ω =
        (1 - t) ^ 2 * oneDegreeEnergy H ν +
          2 * (1 - t) * t *
            (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) +
          t ^ 2 * oneDegreeEnergy H μ at hωeq
    rw [hωeq]
    calc
      _ = (1 - t) ^ 2 * oneDegreeEnergy H ν +
          (2 * (1 - t) * t *
            (∑ v : V, weightedDegree H ν {v} * weightedDegree H μ {v}) +
            t ^ 2 * oneDegreeEnergy H μ) := by ring
      _ < (1 - t) ^ 2 * oneDegreeEnergy H ν +
          ((1 - t) * t * oneDegreeEnergy H ν +
            t ^ 2 * ((β * M) * oneDegreeEnergy H ν / 2)) :=
        add_lt_add_right (add_lt_add hcrossTerm hμTerm) _
      _ = (1 - t) ^ 2 * oneDegreeEnergy H ν +
          (1 - t) * t * oneDegreeEnergy H ν +
          t ^ 2 * ((β * M) * oneDegreeEnergy H ν / 2) := by ring
      _ ≤ _ := hcoef
  refine ⟨ω, by simpa [y] using hωmass, hωLambda, ?_⟩
  simpa [t, M] using hωenergy

/-- **Bounded one-degrees.**  If every restriction obtained by deleting at most a `β` proportion
of the vertices is `(p,R)`-Janson, then the whole uniform hypergraph has a normalized strict
Janson witness whose singleton-degree energy is bounded by `2s²R/(βM)`.

The proof deliberately uses an infimum and a near-minimizer.  Thus it does not assume that the
open set cut out by `Lambda < 1` contains an energy minimizer. -/
private theorem exists_bounded_oneDegree_on (C : Finset V) {H : Hypergraph V}
    {s : ℕ} {p R β : ℝ}
    (hH : H.IsUniform s) (hs : 0 < s) (hp : 0 < p) (hR : 0 < R) (hβ : 0 < β)
    (hC : 0 < C.card)
    (hlocal : ∀ W : Finset V,
      W ⊆ C → (1 - β) * (C.card : ℝ) ≤ (W.card : ℝ) →
        (H.restrict W).IsJanson p R) :
    ∃ ν : EdgeWeight H,
      mass H ν = Real.sqrt R ∧ Lambda H p ν < 1 ∧
        oneDegreeEnergy H ν ≤
          2 * (s : ℝ) ^ 2 * mass H ν ^ 2 /
            (β * (C.card : ℝ)) := by
  classical
  let M : ℝ := C.card
  let y : ℝ := Real.sqrt R
  let B : ℝ := 2 * (s : ℝ) ^ 2 * y ^ 2 / (β * M)
  have hM : 0 < M := by
    change (0 : ℝ) < C.card
    exact_mod_cast hC
  have hy : 0 < y := by simpa [y] using Real.sqrt_pos.2 hR
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hβM : 0 < β * M := mul_pos hβ hM
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hCLarge : (1 - β) * M ≤ (C.card : ℝ) := by
    change (1 - β) * M ≤ M
    nlinarith [mul_pos hβ hM]
  obtain ⟨ν₀, hν₀mass, hν₀Lambda, hν₀supp⟩ :=
    exists_normalized_unit_of_restrict_isJanson
      (hlocal C (fun _ hx ↦ hx) (by simpa [M] using hCLarge)) hp hR
  by_cases hgood : ∃ ν : EdgeWeight H,
      mass H ν = y ∧ Lambda H p ν < 1 ∧ oneDegreeEnergy H ν ≤ B
  · obtain ⟨ν, hmass, hLambda, henergy⟩ := hgood
    refine ⟨ν, by simpa [y] using hmass, hLambda, ?_⟩
    simpa [B, M, hmass] using henergy
  · have hlarge : ∀ ν : EdgeWeight H,
        mass H ν = y → Lambda H p ν < 1 → B < oneDegreeEnergy H ν := by
      intro ν hm hL
      exact lt_of_not_ge fun hle ↦ hgood ⟨ν, hm, hL, hle⟩
    let A : Set ℝ := normalizedWitnessEnergies H p R
    have hAne : A.Nonempty := by
      refine ⟨oneDegreeEnergy H ν₀, ?_⟩
      exact ⟨ν₀, by simpa [y] using hν₀mass, hν₀Lambda, rfl⟩
    have hAbdd : BddBelow A := normalizedWitnessEnergies_bddBelow H p R
    let q : ℝ := sInf A
    have hBq : B ≤ q := by
      apply le_csInf hAne
      rintro a ⟨ν, hm, hL, rfl⟩
      exact (hlarge ν (by simpa [y] using hm) hL).le
    have hq : 0 < q := hB.trans_le hBq
    let t : ℝ := contractionParameter β M
    let c : ℝ := 1 - t / 2
    have ht : 0 < t := contractionParameter_pos hβ hM
    have htHalf : t ≤ 1 / 2 := contractionParameter_le_half β M
    have htOne : t ≤ 1 := htHalf.trans (by norm_num)
    have htβM : t * (β * M) ≤ 1 / 2 :=
      contractionParameter_mul_le_half hβ hM
    have hc : 0 < c := by
      dsimp [c, t]
      exact contractionFactor_pos hβ hM
    have hcOne : c < 1 := by
      dsimp [c, t]
      exact contractionFactor_lt_one hβ hM
    have hqdiv : q < q / c := by
      rw [lt_div_iff₀ hc]
      nlinarith
    obtain ⟨a, ⟨ν, hνmass, hνLambda, haeq⟩, ha⟩ :=
      exists_lt_of_csInf_lt hAne hqdiv
    subst a
    have hνmass' : mass H ν = y := by simpa [y] using hνmass
    have hνenergy : B < oneDegreeEnergy H ν := hlarge ν hνmass' hνLambda
    obtain ⟨ω, hωmass, hωLambda, hωenergy'⟩ :=
      exists_contracting_normalizedWitness hH hs hp hR hβ C hC hlocal ν hνmass hνLambda
        (by simpa [B, y, M] using hνenergy)
    have hωenergy : oneDegreeEnergy H ω < c * oneDegreeEnergy H ν := by
      simpa [c, t, M] using hωenergy'
    have hqω : q ≤ oneDegreeEnergy H ω := by
      apply csInf_le hAbdd
      exact ⟨ω, hωmass, hωLambda, rfl⟩
    have hcνq : c * oneDegreeEnergy H ν < q := by
      calc
        c * oneDegreeEnergy H ν < c * (q / c) := mul_lt_mul_of_pos_left ha hc
        _ = q := by field_simp
    exact False.elim ((not_lt_of_ge hqω) (hωenergy.trans hcνq))

/-- Carrier-local bounded one-degree witness.  The denominator is the cardinality of `carrier`,
not the cardinality of the ambient type.  All restrictions requested from the local Janson
hypothesis are subsets of `carrier`.

The support hypothesis records the form used in the projected copy-hypergraph application.  The
proof in fact only needs the stronger local-Janson hypothesis: weights outside the carrier are
uniformly contracted away by the infimum argument. -/
theorem exists_bounded_oneDegree_onCarrier (carrier : Finset V) {H : Hypergraph V}
    {s : ℕ} {p R β : ℝ} (hH : H.IsUniform s)
    (_hcarrier : H.vertices ⊆ carrier) (hs : 0 < s) (hp : 0 < p)
    (hR : 0 < R) (hβ : 0 < β) (hcarrier : 0 < carrier.card)
    (hlocal : ∀ W : Finset V, W ⊆ carrier →
      (1 - β) * (carrier.card : ℝ) ≤ (W.card : ℝ) →
        (H.restrict W).IsJanson p R) :
    ∃ ν : EdgeWeight H,
      mass H ν = Real.sqrt R ∧ Lambda H p ν < 1 ∧
        oneDegreeEnergy H ν ≤
          2 * (s : ℝ) ^ 2 * mass H ν ^ 2 / (β * (carrier.card : ℝ)) := by
  exact exists_bounded_oneDegree_on carrier hH hs hp hR hβ hcarrier hlocal

/-- Ambient-type form of the bounded one-degree lemma. -/
theorem exists_bounded_oneDegree {H : Hypergraph V} {s : ℕ} {p R β : ℝ}
    (hH : H.IsUniform s) (hs : 0 < s) (hp : 0 < p) (hR : 0 < R) (hβ : 0 < β)
    (hV : 0 < Fintype.card V)
    (hlocal : ∀ W : Finset V,
      (1 - β) * (Fintype.card V : ℝ) ≤ (W.card : ℝ) →
        (H.restrict W).IsJanson p R) :
    ∃ ν : EdgeWeight H,
      mass H ν = Real.sqrt R ∧ Lambda H p ν < 1 ∧
        oneDegreeEnergy H ν ≤
          2 * (s : ℝ) ^ 2 * mass H ν ^ 2 /
            (β * (Fintype.card V : ℝ)) := by
  simpa using exists_bounded_oneDegree_on (Finset.univ : Finset V) hH hs hp hR hβ
    (by simpa using hV)
    (fun W _hW hsize ↦ hlocal W (by simpa using hsize))

end Hypergraph
end Erdos565
