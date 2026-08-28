import Wikipedia.HopfProblem.DegreeCollapseLinearTimeBumpIsotopy
import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# One transverse belt crossing of the whole moving model sheet

A sheet at negative height is translated in its height direction. The
horizontal and belt coordinates are fixed. A cutoff plateau at its center
forces the entire time trace to meet the belt exactly once, at time one
half. The derivative there is an invertible height scaling plus the two
complementary coordinate inclusions, proving actual transversality.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def beltCrossingSheet (a : ℝ) (w : A) : (ℝ × A) × B := ((-a, w), 0)

def beltCrossingBelt (y : B) : (ℝ × A) × B := ((0, 0), y)

def beltCrossingDisplacement (a : ℝ) : (ℝ × A) × B := ((2 * a, 0), 0)

def beltCrossingTrack (β : ((ℝ × A) × B) → ℝ) (a : ℝ) (p : ℝ × A) : (ℝ × A) × B :=
  beltCrossingSheet a p.2 + (p.1 * β (beltCrossingSheet a p.2)) • beltCrossingDisplacement a

theorem beltCrossingSheet_smooth (a : ℝ) :
    ContDiff ℝ ∞ (beltCrossingSheet (A := A) (B := B) a) :=
  (contDiff_const.prodMk contDiff_id).prodMk contDiff_const

theorem beltCrossingBelt_smooth : ContDiff ℝ ∞ (beltCrossingBelt (A := A) (B := B)) :=
  contDiff_const.prodMk contDiff_id

theorem beltCrossingTrack_smooth {β : ((ℝ × A) × B) → ℝ} (hβ : ContDiff ℝ ∞ β) (a : ℝ) :
    ContDiff ℝ ∞ (beltCrossingTrack β a) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × A => beltCrossingSheet (B := B) a p.2) :=
    (beltCrossingSheet_smooth a).comp contDiff_snd
  exact hs.add ((contDiff_fst.mul (hβ.comp hs)).smul contDiff_const)

theorem beltCrossingTrack_eq_belt_iff (β : ((ℝ × A) × B) → ℝ) {a : ℝ} (ha : 0 < a)
    (hβ : β (beltCrossingSheet a (0 : A)) = 1) (t : ℝ) (w : A) (y : B) :
    beltCrossingTrack β a (t, w) = beltCrossingBelt y ↔ t = 1 / 2 ∧ w = 0 ∧ y = 0 := by
  constructor
  · intro he
    have hw : w = 0 := by
      have hh := congrArg (fun z : (ℝ × A) × B => z.1.2) he
      simpa only [beltCrossingTrack, beltCrossingSheet, beltCrossingDisplacement,
        beltCrossingBelt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_zero, add_zero] using hh
    have hy : y = 0 := by
      have hh := congrArg Prod.snd he
      simpa only [beltCrossingTrack, beltCrossingSheet, beltCrossingDisplacement,
        beltCrossingBelt, Prod.snd_add, Prod.smul_snd, smul_zero, add_zero] using hh.symm
    subst w
    have hh := congrArg (fun z : (ℝ × A) × B => z.1.1) he
    change -a + (t * β (beltCrossingSheet a (0 : A))) * (2 * a) = 0 at hh
    rw [hβ, mul_one] at hh
    exact ⟨by nlinarith, rfl, hy⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hscalar : (1 / 2 : ℝ) * β (beltCrossingSheet a (0 : A)) = 1 / 2 := by rw [hβ, mul_one]
    change beltCrossingSheet a (0 : A) +
      ((1 / 2 : ℝ) * β (beltCrossingSheet a (0 : A))) • beltCrossingDisplacement a = _
    rw [hscalar]
    ext <;> simp [beltCrossingSheet, beltCrossingDisplacement, beltCrossingBelt] <;> ring

theorem beltCrossingTrack_endpoints_avoid (β : ((ℝ × A) × B) → ℝ) {a : ℝ} (ha : 0 < a)
    (hβ : β (beltCrossingSheet a (0 : A)) = 1) (w : A) (y : B) :
    beltCrossingTrack β a (0, w) ≠ beltCrossingBelt y ∧
      beltCrossingTrack β a (1, w) ≠ beltCrossingBelt y := by
  constructor <;> intro h
  · have hh := ((beltCrossingTrack_eq_belt_iff β ha hβ 0 w y).mp h).1
    norm_num at hh
  · have hh := ((beltCrossingTrack_eq_belt_iff β ha hβ 1 w y).mp h).1
    norm_num at hh

theorem beltCrossingTrack_transverse (β : ((ℝ × A) × B) → ℝ) {a : ℝ} (ha : 0 < a)
    (hβ : β =ᶠ[𝓝 (beltCrossingSheet a (0 : A))] (fun _ => (1 : ℝ))) :
    NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, B) 𝓘(ℝ, (ℝ × A) × B)
      (beltCrossingTrack β a) beltCrossingBelt (1 / 2, 0) 0 := by
  let Q : (ℝ × A) →L[ℝ] ℝ × A :=
    ((2 * a) • ContinuousLinearMap.fst ℝ ℝ A).prod (ContinuousLinearMap.snd ℝ ℝ A)
  let L : (ℝ × A) →L[ℝ] (ℝ × A) × B := Q.prod 0
  let offset : (ℝ × A) × B := ((-a, 0), 0)
  have hc : Continuous (fun p : ℝ × A => beltCrossingSheet a p.2 : ℝ × A → (ℝ × A) × B) :=
    (continuous_const.prodMk continuous_snd).prodMk continuous_const
  have hgerm : beltCrossingTrack β a =ᶠ[𝓝 ((1 / 2 : ℝ), (0 : A))]
      (fun p => L p + offset) := by
    have hnear := (hc.continuousAt (x := ((1 / 2 : ℝ), (0 : A)))).tendsto.eventually hβ
    filter_upwards [hnear] with p hp
    change β (beltCrossingSheet a p.2) = 1 at hp
    simp only [beltCrossingTrack, hp, mul_one]
    ext <;> simp [beltCrossingSheet, beltCrossingDisplacement, Q, L, offset] <;> ring
  have hder : fderiv ℝ (beltCrossingTrack β a) ((1 / 2 : ℝ), (0 : A)) = L :=
    hgerm.fderiv_eq.trans (L.hasFDerivAt.add_const offset).fderiv
  have hbder : fderiv ℝ (beltCrossingBelt : B → (ℝ × A) × B) 0 =
      ContinuousLinearMap.inr ℝ (ℝ × A) B :=
    (ContinuousLinearMap.inr ℝ (ℝ × A) B).fderiv
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv, hder, hbder]
  change Surjective (L.coprod (ContinuousLinearMap.inr ℝ (ℝ × A) B))
  intro z
  refine ⟨((z.1.1 / (2 * a), z.1.2), z.2), ?_⟩
  change L (z.1.1 / (2 * a), z.1.2) + ((0, 0), z.2) = z
  ext <;> simp [L, Q] <;> field_simp [ha.ne']

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
