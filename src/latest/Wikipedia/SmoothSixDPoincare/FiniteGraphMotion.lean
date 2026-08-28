import Wikipedia.SmoothSixDPoincare.GraphMotionStep

/-!
# The supported finite graph motion and actual model separation

A sufficiently fine finite subdivision uses the uniform displacement bound.
Its exact endpoint tracks the lower center line to the prescribed upper
height. Preserved horizontal and normal coordinates exclude all other
possible intersections, so the two entire model sheet images are disjoint.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- A genuine smooth family, uniformly supported in the specified open model domain. -/
structure GraphMotion {h : ℝ} {U : Set Space} (g : GraphMotionData h U) where
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
    ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph g.height 1 s

/-- Construct the whole finite motion from the actual supported graph data. -/
theorem GraphMotionData.nonempty_graphMotion {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) : Nonempty (GraphMotion g) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_radius_graphStep g.smooth_cutoff g.compact_cutoff
  obtain ⟨N, hN, hNsmall⟩ := Real.exists_nat_pos_inv_lt hε
  let δ : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : 0 ≤ δ := (inv_pos.mpr hNreal).le
  have htotal : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hNreal.ne'
  let B : ℕ → ℝ × Space → Space := graphStep g.cutoff δ
  let A : ℝ × Space → Space := SmallPerturbation.composeFamily B N
  have htrack : ∀ j ≤ N, ∀ s,
      SmallPerturbation.composeFamily B j (1, firstSheet (s, 0)) =
        verticalGraph g.height ((j : ℝ) * δ) s := by
    intro j
    induction j with
    | zero =>
      intro _ s
      simp [SmallPerturbation.composeFamily, firstSheet, verticalGraph]
    | succ j ih =>
      intro hj s
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have htime : (j : ℝ) * δ ∈ Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Nat.cast_nonneg j) hδ, ?_⟩
        calc
          (j : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hδ
          _ = 1 := htotal
      change graphStep g.cutoff δ j
        (1, SmallPerturbation.composeFamily B j (1, firstSheet (s, 0))) = _
      rw [ih hjN s, graphStep_tracking g htime s, Nat.cast_add, Nat.cast_one]
  refine ⟨{
    support := Prod.snd '' tsupport g.cutoff
    compact_support := g.compact_cutoff.isCompact.image continuous_snd
    support_subset := ?_
    family := A
    smooth := SmallPerturbation.contDiff_composeFamily
      (fun i => contDiff_graphStep g.smooth_cutoff δ i) N
    initial := SmallPerturbation.composeFamily_zero (graphStep_zero g.cutoff δ) N
    diffeomorph := SmallPerturbation.exists_diffeomorph_composeFamily (hsmall δ hδ hNsmall) N
    fixed := fun t z hz => SmallPerturbation.composeFamily_fixed
      (fun i t _ hz => graphStep_fixed g.cutoff δ i t hz) N t hz
    horizontal := fun t z => SmallPerturbation.composeFamily_preserves (B := B)
      (f := fun z : Space => z.1.1)
      (graphStep_horizontal g.cutoff δ) N t z
    normal := fun t z => SmallPerturbation.composeFamily_preserves (B := B)
      (f := fun z : Space => z.2)
      (graphStep_normal g.cutoff δ) N t z
    tracking := ?_ }⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact g.support_cutoff hp
  · intro s
    change SmallPerturbation.composeFamily B N (1, firstSheet (s, 0)) = _
    rw [htrack N le_rfl s, htotal]

/-- Coordinate preservation forces any possible intersection onto the exactly tracked line. -/
theorem GraphMotion.firstSheet_ne_secondSheet {h : ℝ} {U : Set Space}
    {g : GraphMotionData h U} (a : GraphMotion g) (hh : 0 < h) (p q : Sheet) :
    a.family (1, firstSheet p) ≠ secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : g.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [verticalGraph, secondSheet, one_mul] using
      congrArg (fun z : Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ g.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (g.above q.1 habs).ne ht.symm

/-- The actual endpoint has no intersection anywhere between the two whole model images. -/
theorem GraphMotion.disjoint_ranges {h : ℝ} {U : Set Space}
    {g : GraphMotionData h U} (a : GraphMotion g) (hh : 0 < h) :
    Disjoint (range (fun p => a.family (1, firstSheet p))) (range (secondSheet h)) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  exact a.firstSheet_ne_secondSheet hh p q hq.symm

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
