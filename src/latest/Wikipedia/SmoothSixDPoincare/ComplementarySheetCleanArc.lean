import Wikipedia.SmoothSixDPoincare.CleanArcPrescribedPath
import Wikipedia.HopfProblem.DegreeCollapseChartAxisCurve

/-!
# Clean arcs between complementary sheets in a prescribed path class

The sheet dimensions may differ. Both endpoint charts, their exact full-image
recognition, and the embedded immersive joining arc are constructed from the
original sheets and input path. The arc retains the input path's based class.
In particular this applies to a loop and a three-dimensional belt in dimension five.
-/

noncomputable section

open Set Function Filter Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage

open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D B : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def terminalCoordinates : Diffeomorph 𝓘(ℝ, ℝ × (D × B)) 𝓘(ℝ, ℝ × (B × D))
    (ℝ × (D × B)) (ℝ × (B × D)) ∞ where
  toEquiv := {
    toFun := fun z => (z.1 - 1, (z.2.2, z.2.1))
    invFun := fun z => (z.1 + 1, (z.2.2, z.2.1))
    left_inv := by intro z; ext <;> simp
    right_inv := by intro z; ext <;> simp }
  contMDiff_toFun := ((contDiff_fst.sub contDiff_const).prodMk
    (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff
  contMDiff_invFun := ((contDiff_fst.add contDiff_const).prodMk
    (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff

variable {E M X Y : Type*} {m n : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [IsManifold (𝓡 m) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [IsManifold (𝓡 n) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

local notation "P" => EuclideanSpace ℝ (Fin m)
local notation "Q" => EuclideanSpace ℝ (Fin n)
local notation "V" => P × Q
local notation "W" => ℝ × V

theorem exists_clean_sheet_arc_in_path_class {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) g y))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (x : X) (y : Y) (hx : f x ∉ range g) (hy : g y ∉ range f)
    (γ : Path (f x) (g y)) :
    ∃ Φ Ψ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
      (0 : W) ∈ Φ.source ∧ ((1 : ℝ), (0 : V)) ∈ Ψ.source ∧
      Φ 0 = f x ∧ Ψ (1, 0) = g y ∧
      Φ.target ⊆ (range g)ᶜ ∧ Ψ.target ⊆ (range f)ᶜ ∧
      (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∃ a : C(ℝ, M), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
        (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
        IsClosedEmbedding (fun t : unitInterval => a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range f ↔ t = 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range g ↔ t = 1) ∧
        ∃ (h0 : a 0 = f x) (h1 : a 1 = g y),
          ((CurveImmersion.intervalPath a).cast h0.symm h1.symm).Homotopic γ := by
  have hclosedf : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  have hclosedg : IsClosed (range g) := (isCompact_range hg.continuous).isClosed
  obtain ⟨Φ, hΦ0, hΦx, hΦavoid, hΦrec⟩ := exists_clean_sheet_axis_chart hf hfe hfi n
    (by simp only [finrank_euclideanSpace_fin]; omega) x hclosedg.isOpen_compl hx
  obtain ⟨Q₀, hQ0, hQy, hQavoid, hQrec⟩ := exists_clean_sheet_axis_chart hg hge hgi m
    (by simp only [finrank_euclideanSpace_fin]; omega) y hclosedf.isOpen_compl hy
  let T := terminalCoordinates (D := P) (B := Q)
  let Ψ := T.toPartialDiffeomorph.trans Q₀
  have hT1 : T ((1 : ℝ), (0 : V)) = 0 := by
    change ((1 : ℝ) - 1, ((0 : Q), (0 : P))) = 0
    rw [sub_self]
    rfl
  have hΨ1 : ((1 : ℝ), (0 : V)) ∈ Ψ.source := by
    refine ⟨mem_univ _, ?_⟩
    change T (1, 0) ∈ Q₀.source
    rw [hT1]
    exact hQ0
  have hΨy : Ψ (1, 0) = g y := by
    change Q₀ (T (1, 0)) = g y
    rw [hT1]
    exact hQy
  have hΨavoid : Ψ.target ⊆ (range f)ᶜ := fun z hz => hQavoid hz.1
  have hΨrec : ∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Q₀ (T z) ∈ range g ↔ _
    rw [hQrec (T z) hz.2]
    change z.1 - 1 = 0 ∧ z.2.1 = 0 ↔ _
    rw [sub_eq_zero]
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨Z, hZ, h1Z, hZΨ, hb, hib⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hf0 : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (t, (0 : V)) ∈ range f → t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    exact fun h => ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
  have hg0 : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (t, (0 : V)) ∈ range g → t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    exact fun h => (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
  have hf1 : ∀ᶠ t in 𝓝 (1 : ℝ), Ψ (t, (0 : V)) ∈ range f → t = 1 := by
    filter_upwards [hZ.mem_nhds h1Z] with t ht
    exact fun h => (hΨavoid (Ψ.map_source' (hZΨ t ht)) h).elim
  have hg1 : ∀ᶠ t in 𝓝 (1 : ℝ), Ψ (t, (0 : V)) ∈ range g → t = 1 := by
    filter_upwards [hZ.mem_nhds h1Z] with t ht
    exact fun h => ((hΨrec (t, 0) (hZΨ t ht)).mp h).1
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact fun h => hx ⟨y, h.symm⟩
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid, ha0', ha1', hclass⟩ :=
    exists_clean_arc_two_images_in_path_class ha hb hU hZ h0U h1Z hia hib
      (γ.cast hΦx hΨy) hends (by omega)
      ⟨f, hf.continuous⟩ hf ⟨g, hg.continuous⟩ hg hclosedg
      (by simp only [finrank_euclideanSpace_fin]; omega)
      (by simp only [finrank_euclideanSpace_fin]; omega) hf0 hf1 hg0 hg1
  have ha0 : a 0 = f x := ha0'.trans hΦx
  have ha1 : a 1 = g y := ha1'.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec,
    a, ha', hleft, hright, hemb, hi, ?_, ?_, ha0, ha1,
    hclass.pathCast hΦx.symm hΨy.symm⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩).1 h
    · rintro rfl
      rw [ha0]
      exact mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩).2 h
    · rintro rfl
      rw [ha1]
      exact mem_range_self y

end Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage
