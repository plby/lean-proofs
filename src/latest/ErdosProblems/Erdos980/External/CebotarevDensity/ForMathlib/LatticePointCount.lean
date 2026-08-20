module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Effective lattice-point count with a Lipschitz-boundary error term

The effective (with explicit `O(tᵈ⁻¹)` rate) strengthening of
`tendsto_card_div_pow_atTop_volume`: for a bounded measurable region whose boundary is
covered by finitely many Lipschitz images of the unit cube, the number of points of the
scaled integer lattice inside the region equals the volume times `nᵈ` up to `O(nᵈ⁻¹)`.

This is the single deepest analytic input to the class-field-theory-free formalisation of
Chebotarev's density theorem: it upgrades the leading-term ideal count to an effective count
with a power-saving error, hence the analytic continuation of the abelian `L`-functions past
`Re s = 1`. It is stated here for a future mathlib contribution.

## Strategy

Following the boundary-cell argument of Lang, GTM 110 Ch. VI §3 Theorem 3 (p. 129) and
Widmer / Gun–Ramaré–Sivaraman: the number of points of the scaled lattice `n⁻¹·ℤ^ι` in `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells of the `n⁻¹ℤ^ι` grid that meet
the frontier `∂s` (`abs_card_inter_sub_volume_mul_pow_le`); that count is `O(nᵈ⁻¹)` because
`∂s` is a finite union of Lipschitz images of the unit cube `[0,1]ᵈ⁻¹`
(`ncard_index_image_frontier_le`, via the single-chart bound `ncard_index_image_chart_le`).

## Main results

* `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`: the terminal export.
* `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`,
  `Chebotarev.ncard_index_image_le_of_diam_le`,
  `Chebotarev.setFinite_index_image_of_isBounded`: building blocks reused by the unit-grid
  ideal-congruence count.

## References

* Serge Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994, Ch. V §2 and
  Ch. VI §3 (Theorem 3), p. 129 (the boundary-cell estimate).
* S. Gun, O. Ramaré, J. Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243
  (2023) 13–37, §3.3 (Lipschitz class of the boundary) and §3.5 (counting points), after
  K. Debaene.
-/

open Submodule Pointwise MeasureTheory Set BoxIntegral.unitPartition

open scoped NNReal

namespace Chebotarev

@[expose] public section

section Sublemmas

variable {ι : Type*} [Fintype ι]

private lemma ceil_natCast_mul_le_ceil_natCast_mul_add (n : ℕ) {a b r : ℝ} (h : a ≤ b + r) :
    (⌈(n : ℝ) * a⌉ : ℤ) ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ :=
  calc (⌈(n : ℝ) * a⌉ : ℤ)
      ≤ ⌈(n : ℝ) * b + (n : ℝ) * r⌉ :=
        Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    _ ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _

private lemma abs_sub_le_one_div_of_ceil_natCast_mul_eq {n : ℕ} (hn : 0 < (n : ℝ)) {a b : ℝ}
    (h : ⌈(n : ℝ) * a⌉ = ⌈(n : ℝ) * b⌉) : |a - b| ≤ 1 / n := by
  have hr : (⌈(n : ℝ) * a⌉ : ℝ) = ⌈(n : ℝ) * b⌉ := by exact_mod_cast h
  rw [show a - b = ((n : ℝ) * a - (n : ℝ) * b) / n by field_simp, abs_div, abs_of_pos hn,
    div_le_div_iff_of_pos_right hn, abs_le]
  constructor <;>
    nlinarith [Int.le_ceil ((n : ℝ) * a), Int.le_ceil ((n : ℝ) * b),
      Int.ceil_lt_add_one ((n : ℝ) * a), Int.ceil_lt_add_one ((n : ℝ) * b), hr]

-- The `Fintype ι` instance is needed for the `sup`-metric on `ι → ℝ`, so the
-- `unusedFintypeInType` linter (which only inspects the conclusion) is a false positive here.
/-- The `index n`-image of a bounded set is finite: only finitely many cells of the `n⁻¹ℤ^ι`
grid meet a bounded set. -/
theorem setFinite_index_image_of_isBounded (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ι → ℝ)
  set F : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ : ι ↦ Finset.Icc (⌈-((n : ℝ) * R)⌉ - 1) (⌈(n : ℝ) * R⌉ - 1) with hF
  refine Set.Finite.subset (Finset.finite_toSet F) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, index_apply]
  intro i
  have hxi : |x i| ≤ R := by
    have hd : dist (x i) ((0 : ι → ℝ) i) ≤ dist x 0 := dist_le_pi_dist x 0 i
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hd
    exact hd.trans (by simpa [Real.dist_eq] using hR hx)
  rcases abs_le.mp hxi with ⟨hlo, hhi⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact ⟨sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1,
    sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1⟩

/-- **Bounded-diameter cell incidence.** A set `T ⊆ ι → ℝ` of diameter `≤ r` meets at most
`(2⌈n·r⌉₊ + 1)ᵈ` cells of the `n⁻¹ℤ^ι` grid, i.e. its `index n`-image has at most that many
points. (Here `ι → ℝ` carries the sup metric, so a cube of side `1/n` has diameter `1/n`.) -/
theorem ncard_index_image_le_of_diam_le (n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ}
    (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) :
    (index n '' T).ncard ≤ (2 * ⌈(n : ℝ) * r⌉₊ + 1) ^ Fintype.card ι := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [image_empty, ncard_empty, zero_le]
  set K : ℕ := ⌈(n : ℝ) * r⌉₊ with hK
  set c : ι → ℤ := index n x₀ with hc
  set F : Finset (ι → ℤ) := Fintype.piFinset fun i ↦ Finset.Icc (c i - K) (c i + K) with hF
  have hsub : index n '' T ⊆ ↑F := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hdx : |x i - x₀ i| ≤ r := by
      have h1 : dist (x i) (x₀ i) ≤ dist x x₀ := dist_le_pi_dist x x₀ i
      rw [Real.dist_eq] at h1
      exact h1.trans ((Metric.dist_le_diam_of_mem hbdd hx hx₀).trans hdiam)
    rcases abs_le.mp hdx with ⟨hlo, hhi⟩
    have hKeq : (K : ℤ) = ⌈(n : ℝ) * r⌉ := hK ▸ Int.natCast_ceil_eq_ceil (by positivity)
    have hub :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x i) (b := x₀ i) (r := r) (by linarith)
    have hlb :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x₀ i) (b := x i) (r := r) (by linarith)
    simp only [index_apply, hc]
    constructor <;> lia
  refine (Set.ncard_le_ncard hsub F.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset, hF, Fintype.card_piFinset]
  have hcard : ∀ i, (Finset.Icc (c i - K) (c i + K)).card = 2 * K + 1 := by
    intro i
    rw [Int.card_Icc]
    lia
  rw [Finset.prod_congr rfl fun i _ ↦ hcard i, Finset.prod_const, Finset.card_univ]

/-- **Single-chart cell count.** For one `M`-Lipschitz map `φ : (Fin (d-1) → ℝ) → (ι → ℝ)`,
the number of grid cells of the `n⁻¹ℤ^ι` grid meeting the image `φ '' [0,1]ᵈ⁻¹` is at most
`(2⌈M⌉₊ + 1)ᵈ · (n+1)ᵈ⁻¹ = O(nᵈ⁻¹)`. -/
theorem ncard_index_image_chart_le {κ : Type*} [Fintype κ] {M : ℝ≥0} {φ : (κ → ℝ) → (ι → ℝ)}
    (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) :
    (index n '' (φ '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card κ) := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  set q : (κ → ℝ) → (κ → ℤ) :=
    fun y k ↦ ⌈(n : ℝ) * y k⌉ with hq
  set T : Finset (κ → ℤ) :=
    Finset.Icc (0 : κ → ℤ) (fun _ ↦ (n : ℤ)) with hT
  have hdiam : ∀ v : κ → ℤ,
      Metric.diam (Set.Icc 0 1 ∩ q ⁻¹' {v}) ≤ 1 / n := by
    intro v
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' ↦ ?_
    rw [dist_pi_le_iff (by positivity)]
    intro k
    have hce : ⌈(n : ℝ) * y k⌉ = ⌈(n : ℝ) * y' k⌉ :=
      (congrFun hy.2 k).trans (congrFun hy'.2 k).symm
    rw [Real.dist_eq]
    exact abs_sub_le_one_div_of_ceil_natCast_mul_eq hn0 hce
  have hcover : index n '' (φ '' Set.Icc 0 1) ⊆
      ⋃ v ∈ T, index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyT : q y ∈ T := by
      rw [hT, Finset.mem_Icc]
      refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
      · simp only [hq, Pi.zero_apply]
        rw [Int.le_ceil_iff]
        push_cast
        linarith [mul_nonneg hn0.le (hy.1 k)]
      · simp only [hq]
        rw [Int.ceil_le]
        have hyk : y k ≤ 1 := hy.2 k
        push_cast
        nlinarith [hn0]
    exact Set.mem_biUnion hyT ⟨φ y, ⟨y, ⟨hy, rfl⟩, rfl⟩, rfl⟩
  have hpiece : ∀ v : κ → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).ncard
        ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι := by
    intro v
    have hbddφ : Bornology.IsBounded (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) :=
      hφ.isBounded_image ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left)
    have hdimg : Metric.diam (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) ≤ (M : ℝ) * (1 / n) :=
      (hφ.diam_image_le _ ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left)).trans
        (mul_le_mul_of_nonneg_left (hdiam v) (by positivity))
    refine (ncard_index_image_le_of_diam_le n (by positivity) hdimg hbddφ).trans ?_
    rw [show (n : ℝ) * ((M : ℝ) * (1 / n)) = (M : ℝ) by field_simp]
  have hfin : ∀ v : κ → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).Finite :=
    fun v ↦ setFinite_index_image_of_isBounded n
      (hφ.isBounded_image ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left))
  refine (Set.ncard_le_ncard hcover (T.finite_toSet.biUnion fun v _ ↦ hfin v)).trans ?_
  refine (Finset.set_ncard_biUnion_le T _).trans ?_
  have hsum : ∑ v ∈ T, (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).ncard
      ≤ ∑ _v ∈ T, (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι :=
    by
      induction T using Finset.induction_on with
      | empty => exact Nat.le_refl 0
      | insert v T hv ih =>
          rw [Finset.sum_insert hv, Finset.sum_insert hv]
          exact Nat.add_le_add (hpiece v) ih
  refine hsum.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardT : T.card = (n + 1) ^ (Fintype.card κ) := by
    rw [hT, Pi.card_Icc]
    simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_natCast_add_one, Finset.prod_const,
      Finset.card_univ]
  rw [hcardT, Nat.cast_id]

/-- **Boundary-cell count.** If a set `t` is covered by `m` images `φⱼ '' [0,1]ᵈ⁻¹` of
`M`-Lipschitz maps, the number of grid cells meeting `t` is `O(nᵈ⁻¹)`, with constant
`m · (2⌈M⌉₊+1)ᵈ · 2ᵈ⁻¹`. (The boundary-cell estimate is the case `t = ∂s`.) -/
theorem ncard_index_image_frontier_le {t : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0}
    {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)}
    (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : t ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (index n '' t).ncard
      ≤ (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1))
          * n ^ (Fintype.card ι - 1) := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hbddφ : ∀ j, Bornology.IsBounded (φ j '' Set.Icc 0 1) := fun j ↦
    (hφ j).isBounded_image (Metric.isBounded_Icc 0 1)
  have hfin : ∀ j : Fin m, (index n '' (φ j '' Set.Icc 0 1)).Finite := fun j ↦
    setFinite_index_image_of_isBounded n (hbddφ j)
  have hsub : index n '' t ⊆ ⋃ j, index n '' (φ j '' Set.Icc 0 1) := by
    rw [← Set.image_iUnion]
    exact Set.image_mono hcov
  refine (Set.ncard_le_ncard hsub (Set.finite_iUnion hfin)).trans ?_
  refine (Set.ncard_iUnion_le_of_fintype _).trans ?_
  have hsum : ∑ j : Fin m, (index n '' (φ j '' Set.Icc 0 1)).ncard
      ≤ ∑ _j : Fin m,
          (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ Fintype.card (Fin (Fintype.card ι - 1)) :=
    by
      let U : Finset (Fin m) := Finset.univ
      change (∑ j ∈ U, (index n '' (φ j '' Set.Icc 0 1)).ncard)
        ≤ ∑ _j ∈ U,
            (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι
              * (n + 1) ^ Fintype.card (Fin (Fintype.card ι - 1))
      induction U using Finset.induction_on with
      | empty => exact Nat.le_refl 0
      | insert j U hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          exact Nat.add_le_add (ncard_index_image_chart_le (hφ j) hn) ih
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (n + 1) ^ (Fintype.card ι - 1) ≤
      2 ^ (Fintype.card ι - 1) * n ^ (Fintype.card ι - 1) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by lia) _
  calc
    (m : ℕ) * ((2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1))
      ≤ m * ((2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι
          * (2 ^ (Fintype.card ι - 1) * n ^ (Fintype.card ι - 1))) := by gcongr
    _ = m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1)
          * n ^ (Fintype.card ι - 1) := by ring

omit [Fintype ι] in
private lemma index_mem_image_frontier_of_box_meet_not_subset {n : ℕ} [NeZero n]
    {s : Set (ι → ℝ)} {ν : ι → ℤ} (hmeet : ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty)
    (hnsub : ¬ (box n ν : Set (ι → ℝ)) ⊆ s) : ν ∈ index n '' frontier s := by
  have hconn : IsPreconnected (box n ν : Set (ι → ℝ)) := by
    rw [BoxIntegral.Box.coe_eq_pi]
    exact (convex_pi fun _ _ ↦ convex_Ioc _ _).isPreconnected
  obtain ⟨xc, hxcb, hxcs⟩ : ((box n ν : Set (ι → ℝ)) ∩ sᶜ).Nonempty := by
    rw [Set.not_subset] at hnsub
    exact hnsub.imp fun _ ⟨hx, hxs⟩ ↦ ⟨hx, hxs⟩
  by_contra hcon
  have hcon' : (box n ν : Set (ι → ℝ)) ∩ frontier s = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxb, hxf⟩
    exact hcon ⟨x, hxf, mem_box_iff_index.mp hxb⟩
  have hsplit : (box n ν : Set (ι → ℝ)) ⊆ interior s ∪ (closure s)ᶜ := by
    intro x hx
    by_contra hxc
    rw [Set.mem_union, not_or, Set.notMem_compl_iff] at hxc
    exact (Set.eq_empty_iff_forall_notMem.mp hcon' x) ⟨hx, hxc.2, hxc.1⟩
  rcases hconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr (interior_subset.trans subset_closure)) hsplit
    with hsub | hsub
  · exact hxcs (interior_subset (hsub hxcb))
  · obtain ⟨x, hxb, hxs⟩ := hmeet
    exact (hsub hxb) (subset_closure hxs)

private lemma measureReal_biUnion_box (n : ℕ) [NeZero n] (t : Finset (ι → ℤ)) :
    volume.real (⋃ ν ∈ t, (box n ν : Set (ι → ℝ))) = t.card / (n : ℝ) ^ Fintype.card ι := by
  have hvol_box : ∀ ν : ι → ℤ,
      volume.real (box n ν : Set (ι → ℝ)) = 1 / (n : ℝ) ^ Fintype.card ι := by
    intro ν
    rw [measureReal_def, volume_box]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [measureReal_biUnion_finset (fun ν _ ν' _ h ↦ disjoint.mp h)
    (fun ν _ ↦ (box n ν).measurableSet_coe) (fun ν _ ↦ (box n ν).isBounded.measure_lt_top.ne)]
  simp_rw [hvol_box]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Count ↔ volume bridge.** The number of points of `n⁻¹ℤ^ι` in a bounded measurable `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells meeting `∂s`. This is the
effective form of the sandwich behind `tendsto_card_div_pow_atTop_volume`. -/
theorem abs_card_inter_sub_volume_mul_pow_le {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) :
    |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
        - volume.real s * (n : ℝ) ^ Fintype.card ι|
      ≤ (index n '' frontier s).ncard := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  have hvs : volume s ≠ ⊤ := hbdd.measure_lt_top.ne
  set Inside : Set (ι → ℤ) := {ν | (box n ν : Set (ι → ℝ)) ⊆ s}
  set Meet : Set (ι → ℤ) := {ν | ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty}
  set Bd : Set (ι → ℤ) := index n '' frontier s
  have hInsideFin : Inside.Finite := setFinite_index n hmeas.nullMeasurableSet hvs
  have hBdFin : Bd.Finite :=
    setFinite_index_image_of_isBounded n (hbdd.closure.subset frontier_subset_closure)
  have hMeetSub : Meet ⊆ index n '' s := by
    rintro ν ⟨x, hxb, hxs⟩
    exact ⟨x, hxs, mem_box_iff_index.mp hxb⟩
  have hMeetFin : Meet.Finite :=
    (setFinite_index_image_of_isBounded n hbdd).subset hMeetSub
  set Tag : Set (ι → ℤ) := {ν | tag n ν ∈ s} with hTag
  have himg : index n '' (s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag := by
    ext ν
    simp only [hTag, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hxs, hxL⟩, rfl⟩
      rwa [tag_index_eq_self_of_mem_smul_span n hxL]
    · intro hν
      exact ⟨tag n ν, ⟨hν, tag_mem_smul_span n ν⟩, index_tag n ν⟩
  have hNeq : Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag.ncard := by
    rw [Nat.card_coe_set_eq, ← himg]
    refine (Set.InjOn.ncard_image ?_).symm
    intro x hx y hy h
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 h
  have hIT : Inside ⊆ Tag := fun ν hν ↦ hν (tag_mem n ν)
  have hTM : Tag ⊆ Meet := fun ν hν ↦ ⟨tag n ν, tag_mem n ν, hν⟩
  have hMIB : Meet ⊆ Inside ∪ Bd := by
    intro ν hν
    by_cases hsub : (box n ν : Set (ι → ℝ)) ⊆ s
    · exact Or.inl hsub
    · exact Or.inr (index_mem_image_frontier_of_box_meet_not_subset hν hsub)
  have hcard_IT : Inside.ncard ≤ Tag.ncard :=
    Set.ncard_le_ncard hIT (hMeetFin.subset hTM)
  have hcard_TM : Tag.ncard ≤ Meet.ncard := Set.ncard_le_ncard hTM hMeetFin
  have hcard_MIB : Meet.ncard ≤ Inside.ncard + Bd.ncard :=
    (Set.ncard_le_ncard hMIB (hInsideFin.union hBdFin)).trans (Set.ncard_union_le _ _)
  set V : ℝ := volume.real s * (n : ℝ) ^ Fintype.card ι with hV
  have hnpow : (0 : ℝ) < (n : ℝ) ^ Fintype.card ι := by positivity
  have hcardI : (hInsideFin.toFinset).card = Inside.ncard :=
    (Set.ncard_eq_toFinset_card _ hInsideFin).symm
  have hcardM : (hMeetFin.toFinset).card = Meet.ncard :=
    (Set.ncard_eq_toFinset_card _ hMeetFin).symm
  have hvol_lower : (Inside.ncard : ℝ) ≤ V := by
    have hsub : (⋃ ν ∈ hInsideFin.toFinset, (box n ν : Set (ι → ℝ))) ⊆ s :=
      Set.iUnion₂_subset fun ν hν ↦ hInsideFin.mem_toFinset.mp hν
    have hle := measureReal_mono hsub hvs
    rw [measureReal_biUnion_box n hInsideFin.toFinset, hcardI, div_le_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hvol_upper : V ≤ (Meet.ncard : ℝ) := by
    have hsub : s ⊆ ⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ)) := by
      intro x hxs
      refine Set.mem_iUnion₂.mpr ⟨index n x, hMeetFin.mem_toFinset.mpr ?_,
        mem_box_iff_index.mpr rfl⟩
      exact ⟨x, mem_box_iff_index.mpr rfl, hxs⟩
    have hfinU : volume (⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ))) ≠ ⊤ :=
      (measure_biUnion_finset_le _ _).trans_lt (by
        simp only [volume_box]
        exact ENNReal.sum_lt_top.mpr fun _ _ ↦
          ENNReal.div_lt_top ENNReal.one_ne_top
            (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)))) |>.ne
    have hle := measureReal_mono hsub hfinU
    rw [measureReal_biUnion_box n hMeetFin.toFinset, hcardM, le_div_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hITr : (Inside.ncard : ℝ) ≤ (Tag.ncard : ℝ) := by exact_mod_cast hcard_IT
  have hMIBr : (Meet.ncard : ℝ) ≤ (Inside.ncard : ℝ) + (Bd.ncard : ℝ) := by
    exact_mod_cast hcard_MIB
  have hTMr : (Tag.ncard : ℝ) ≤ (Meet.ncard : ℝ) := by exact_mod_cast hcard_TM
  rw [hNeq, abs_le]
  exact ⟨by linarith, by linarith⟩

end Sublemmas

/-- **Effective lattice-point count (Lang GTM 110 Ch. V §2 / p. 129; Gun–Ramaré–Sivaraman,
*Counting ideals in ray classes*, J. Number Theory 243 (2023) §3.3–3.5, after Debaene).**
For a bounded measurable set `s ⊆ ι → ℝ` whose frontier is covered by finitely many
Lipschitz images of the unit cube `[0,1]^{d-1}` (`d = #ι`), the number of points of the
scaled integer lattice `n⁻¹·ℤ^ι` lying in `s` equals `vol(s)·nᵈ` up to an error `O(nᵈ⁻¹)`.
This is the effective form of `tendsto_card_div_pow_atTop_volume` (whose conclusion is the
rate-free limit `card / nᵈ → vol s`). -/
theorem exists_card_inter_smul_lattice_sub_volume_mul_pow_le
    {ι : Type*} [Fintype ι] (s : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
          - volume.real s * (n : ℝ) ^ Fintype.card ι|
        ≤ C * (n : ℝ) ^ (Fintype.card ι - 1) := by
  obtain ⟨m, M, φ, hφ, hcov⟩ := hlip
  refine ⟨(m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1) : ℕ),
    fun n hn ↦ ?_⟩
  refine (abs_card_inter_sub_volume_mul_pow_le hbdd hmeas hn).trans ?_
  refine (Nat.cast_le.mpr (ncard_index_image_frontier_le hφ hcov hn)).trans ?_
  exact le_of_eq (by push_cast; ring)

end

end Chebotarev
