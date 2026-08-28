import Wikipedia.HopfProblem.DegreeCollapseMiddleBeltChart

/-!
# The supported crossing concerns the whole original belt

Full chart recognition and support preservation exclude belt points outside
the local parametrization. The exact local crossing is therefore the unique
crossing with the whole original embedded belt. Transversality to its local
parametrization implies transversality to the original native belt map.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B D E HZ H Y M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HZ] {I : ModelWithCorners ℝ D HZ}
  [TopologicalSpace Y] [ChartedSpace HZ Y]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_supported_full_belt_crossing
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) J ((ℝ × A) × B) M ∞)
    (h0 : (0 : (ℝ × A) × B) ∈ Φ.source) (b : Y → M) (hb : Injective b)
    (hrecognition : ∀ z ∈ Φ.source, Φ z ∈ range b ↔ z.1 = 0)
    (χ : B → Y) (y₀ : Y) (hχ0 : χ 0 = y₀)
    (haxis : ∀ y : B, Φ (beltCrossingBelt y) = b (χ y))
    (hbsm : ContMDiffAt I J ∞ b y₀) (hχsm : ContMDiffAt 𝓘(ℝ, B) I ∞ χ 0) :
    ∃ a : ℝ, 0 < a ∧ beltCrossingSheet a (0 : A) ∈ Φ.source ∧
      ∃ (F : ℝ × M → M) (K : Set M),
        IsCompact K ∧ K ⊆ Φ.target ∧ ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ F ∧
        (∀ y, F (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = F (t, y)) ∧
        (∀ t y, y ∉ K → F (t, y) = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : A, beltCrossingSheet a w ∈ Φ.source → ∀ y : Y,
          (F (t, Φ (beltCrossingSheet a w)) = b y ↔ t = 1 / 2 ∧ w = 0 ∧ y = y₀)) ∧
        ContMDiffAt 𝓘(ℝ, ℝ × A) J ∞
          (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) (1 / 2, 0) ∧
        NativeTransversality.At 𝓘(ℝ, ℝ × A) I J
          (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) b (1 / 2, 0) y₀ := by
  obtain ⟨a, ha, hsheet, F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hcount, htrace, -, htrans⟩ :=
    exists_native_single_belt_crossing Φ h0
  have hcenter : Φ 0 = b y₀ := (haxis 0).trans (congrArg b hχ0)
  have htarget (t : ℝ) (x : (ℝ × A) × B) (hx : x ∈ Φ.source) :
      F (t, Φ x) ∈ Φ.target := by
    have hbase := Φ.map_source' hx
    obtain ⟨d, hd⟩ := hFd t
    by_contra hnot
    have hy : d (F (t, Φ x)) = F (t, Φ x) :=
      (hd _).trans (hFfix t _ (fun hh => hnot (hKΦ hh)))
    have he : Φ x = F (t, Φ x) := d.injective ((hd _).trans hy.symm)
    exact hnot (he ▸ hbase)
  have hcross : F ((1 / 2 : ℝ), Φ (beltCrossingSheet a (0 : A))) =
      Φ (beltCrossingBelt (A := A) (0 : B)) :=
    (hcount (1 / 2) (by constructor <;> norm_num) 0 0 hsheet h0).mpr ⟨rfl, rfl, rfl⟩
  refine ⟨a, ha, hsheet, F, K, hK, hKΦ, hF, hF0, hFd, hFfix, ?_, htrace, ?_⟩
  · intro t ht w hw y
    constructor
    · intro he
      have hby : b y ∈ Φ.target := he ▸ htarget t (beltCrossingSheet a w) hw
      let z := Φ.symm (b y)
      have hz : z ∈ Φ.source := Φ.map_target' hby
      have hzy : Φ z = b y := Φ.right_inv' hby
      have hz0 : z.1 = 0 := (hrecognition z hz).mp ⟨y, hzy.symm⟩
      have hzshape : z = beltCrossingBelt z.2 := Prod.ext hz0 rfl
      have hzsource : beltCrossingBelt z.2 ∈ Φ.source := hzshape ▸ hz
      have hh : F (t, Φ (beltCrossingSheet a w)) = Φ (beltCrossingBelt z.2) :=
        he.trans (hzy.symm.trans (congrArg Φ hzshape))
      obtain ⟨htime, hw0, hz2⟩ := (hcount t ht w z.2 hw hzsource).mp hh
      have hzall : z = 0 := Prod.ext hz0 hz2
      exact ⟨htime, hw0, hb (hzy.symm.trans ((congrArg Φ hzall).trans hcenter))⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact hcross.trans hcenter
  · let L : (ℝ × A) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × A) J
      (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) ((1 / 2 : ℝ), (0 : A))
    let R : D →L[ℝ] E := mfderiv I J b y₀
    let C : B →L[ℝ] D := mfderiv 𝓘(ℝ, B) I χ 0
    have hder : (mfderiv 𝓘(ℝ, B) J (Φ ∘ beltCrossingBelt) 0 : B →L[ℝ] E) = R.comp C := by
      have heq : Φ ∘ beltCrossingBelt = b ∘ χ := funext haxis
      rw [heq, mfderiv_comp 0 (by rw [hχ0]; exact hbsm.mdifferentiableAt (by simp))
        (hχsm.mdifferentiableAt (by simp)), hχ0]
      rfl
    have hsum := htrans hcross.symm
    rw [hder] at hsum
    change Surjective (L.coprod (R.comp C)) at hsum
    intro _
    change Surjective (L.coprod R)
    intro z
    obtain ⟨w, hw⟩ := hsum z
    exact ⟨(w.1, C w.2), hw⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
