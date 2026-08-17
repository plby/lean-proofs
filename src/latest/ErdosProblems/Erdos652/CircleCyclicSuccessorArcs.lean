import ErdosProblems.Erdos652.Circles
import Submission.UnitCircleCyclicSuccessorArcs

/-!
# Successor arcs on an arbitrary positive-radius circle

The upstream construction is stated for unit circles.  This file transports it
through the affine similarity `x ↦ r⁻¹ • (x - c)`.
-/

open Classical
noncomputable section

namespace Erdos652

private def normalizeCircle (c : Point) (r : ℝ) (x : Point) : Point :=
  r⁻¹ • (x - c)

private def denormalizeCircle (c : Point) (r : ℝ) (x : Point) : Point :=
  c + r • x

private lemma denormalize_normalize (c : Point) {r : ℝ} (hr : r ≠ 0) (x : Point) :
    denormalizeCircle c r (normalizeCircle c r x) = x := by
  simp [denormalizeCircle, normalizeCircle, smul_smul, hr]

private lemma normalize_denormalize (c : Point) {r : ℝ} (hr : r ≠ 0) (x : Point) :
    normalizeCircle c r (denormalizeCircle c r x) = x := by
  simp [denormalizeCircle, normalizeCircle, smul_smul, hr]

private lemma normalize_injective (c : Point) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (normalizeCircle c r) := by
  intro x y hxy
  simpa only [denormalize_normalize c hr] using congrArg (denormalizeCircle c r) hxy

private lemma denormalize_injective (c : Point) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (denormalizeCircle c r) := by
  intro x y hxy
  simpa only [normalize_denormalize c hr] using congrArg (normalizeCircle c r) hxy

/-- The cyclic successor arcs supplied upstream, transported from the unit
circle to a circle of positive radius. -/
lemma circleCyclicSuccessorArcs
    (c : Point) (r : ℝ) (hr : 0 < r)
    (S : Finset Point)
    (hS : (↑S : Set Point) ⊆ circle (c, r))
    (hcard : 3 ≤ S.card) :
    ∃ (succ : {x : Point // x ∈ S} → {x : Point // x ∈ S})
      (carrier arcInterior : {x : Point // x ∈ S} → Set Point)
      (γ : (x : {x : Point // x ∈ S}) → Set.Icc (0 : ℝ) 1 → Point),
      Function.Bijective succ ∧
        (∀ x, x.1 ≠ (succ x).1) ∧
          (∀ x,
            Continuous (γ x) ∧
              Function.Injective (γ x) ∧
                (∀ t, γ x t ∈ circle (c, r)) ∧
                  γ x ⟨0, by simp⟩ = x.1 ∧
                    γ x ⟨1, by simp⟩ = (succ x).1 ∧
                      carrier x = Set.range (γ x) ∧
                        arcInterior x =
                          Set.range
                            (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                              γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
            (∀ x y : {y : Point // y ∈ S}, y.1 ∉ arcInterior x) ∧
              (∀ x y, x ≠ y → arcInterior x ∩ arcInterior y = ∅) ∧
                (∀ x y,
                  (Sym2.mk x.1 (succ x).1 : Sym2 Point) =
                    Sym2.mk y.1 (succ y).1 → x = y) := by
  let n := normalizeCircle c r
  let d := denormalizeCircle c r
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hninj : Function.Injective n := normalize_injective c hr0
  have hdinj : Function.Injective d := denormalize_injective c hr0
  let T := S.image n
  have hTcard : T.card = S.card := Finset.card_image_of_injective S hninj
  have hTcircle : (↑T : Set Point) ⊆ UnitCircle 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hxS, rfl⟩
    have hx := hS hxS
    change dist (n x) 0 = 1
    dsimp [n, normalizeCircle]
    rw [show (0 : Point) = r⁻¹ • 0 by simp, dist_smul₀]
    have hdist : dist (x - c) 0 = dist x c := by
      simpa using (dist_sub_right x c c)
    rw [hdist]
    have hxc : dist x c = r := hx
    rw [hxc, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    field_simp
  have hT3 : 3 ≤ T.card := by simpa [hTcard] using hcard
  obtain ⟨succ₀, carrier₀, interior₀, γ₀, hsucc₀, hne₀, harc₀,
      hvertices₀, hdisjoint₀, hunique₀⟩ :=
    UnitCircleCyclicSuccessorArcs 0 T hTcircle hT3
  let e : {x : Point // x ∈ S} ≃ {x : Point // x ∈ T} :=
    { toFun := fun x => ⟨n x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨d y.1, by
        rcases Finset.mem_image.mp y.2 with ⟨x, hxS, hx⟩
        have hy : y.1 = n x := hx.symm
        simpa [hy, d, n, denormalize_normalize c hr0] using hxS⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact denormalize_normalize c hr0 x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact normalize_denormalize c hr0 y.1 }
  let succ : {x : Point // x ∈ S} → {x : Point // x ∈ S} :=
    fun x => e.symm (succ₀ (e x))
  let γ : (x : {x : Point // x ∈ S}) → Set.Icc (0 : ℝ) 1 → Point :=
    fun x t => d (γ₀ (e x) t)
  let carrier : {x : Point // x ∈ S} → Set Point := fun x => Set.range (γ x)
  let arcInterior : {x : Point // x ∈ S} → Set Point := fun x =>
    Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
      γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)
  have hsucc : Function.Bijective succ := by
    simpa [succ, Function.comp_def] using
      e.symm.bijective.comp (hsucc₀.comp e.bijective)
  refine ⟨succ, carrier, arcInterior, γ, hsucc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxeq
    apply hne₀ (e x)
    have hnxy := congrArg n hxeq
    simpa [succ, e, n, d, normalize_denormalize c hr0] using hnxy
  · intro x
    rcases harc₀ (e x) with
      ⟨hcont, hinj, hcircle, hstart, hend, hcarrier, hinterior⟩
    refine ⟨?_, hdinj.comp hinj, ?_, ?_, ?_, rfl, rfl⟩
    · exact continuous_const.add (hcont.const_smul r)
    · intro t
      change dist (d (γ₀ (e x) t)) c = r
      dsimp [d, denormalizeCircle]
      have hz : dist (γ₀ (e x) t) 0 = 1 := hcircle t
      calc
        dist (c + r • γ₀ (e x) t) c = dist (r • γ₀ (e x) t) 0 := by
          simpa using (dist_add_left (r • γ₀ (e x) t) 0 c)
        _ = ‖r‖ * dist (γ₀ (e x) t) 0 := by
          simpa using (dist_smul₀ r (γ₀ (e x) t) 0)
        _ = r := by rw [hz, Real.norm_eq_abs, abs_of_pos hr, mul_one]
    · change d (γ₀ (e x) ⟨0, by simp⟩) = x.1
      rw [hstart]
      exact denormalize_normalize c hr0 x.1
    · change d (γ₀ (e x) ⟨1, by simp⟩) = (e.symm (succ₀ (e x))).1
      rw [hend]
      rfl
  · intro x y hy
    rcases hy with ⟨t, ht⟩
    have hnormalized := congrArg n ht
    have hpoint : (e y).1 = γ₀ (e x)
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ := by
      simpa [γ, e, n, d, normalize_denormalize c hr0] using hnormalized.symm
    apply hvertices₀ (e x) (e y)
    rw [(harc₀ (e x)).2.2.2.2.2.2]
    exact ⟨t, hpoint.symm⟩
  · intro x y hxy
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hzx, hzy⟩
    rcases hzx with ⟨s, hs⟩
    rcases hzy with ⟨t, ht⟩
    have hnst := congrArg n (hs.trans ht.symm)
    have hγeq : γ₀ (e x) ⟨s.1, ⟨le_of_lt s.2.1, le_of_lt s.2.2⟩⟩ =
        γ₀ (e y) ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ := by
      simpa [γ, n, d, normalize_denormalize c hr0] using hnst
    have hxye : e x ≠ e y := fun h => hxy (e.injective h)
    have hempty := hdisjoint₀ (e x) (e y) hxye
    have hmem : γ₀ (e x) ⟨s.1, ⟨le_of_lt s.2.1, le_of_lt s.2.2⟩⟩ ∈
        interior₀ (e x) ∩ interior₀ (e y) := by
      rw [(harc₀ (e x)).2.2.2.2.2.2, (harc₀ (e y)).2.2.2.2.2.2]
      exact ⟨⟨s, rfl⟩, ⟨t, hγeq.symm⟩⟩
    simpa [hempty] using hmem
  · intro x y hxy
    apply e.injective
    apply hunique₀
    simpa [succ, e, n, d, normalize_denormalize c hr0] using
      congrArg (Sym2.map n) hxy

end Erdos652
