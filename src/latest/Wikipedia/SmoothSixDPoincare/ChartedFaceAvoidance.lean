import Wikipedia.SmoothSixDPoincare.OpenFaceShrinking
import Wikipedia.SmoothSixDPoincare.GlobalAmbientAvoidance

/-!
# Whole-face avoidance using only its retained smooth chart

These moves apply to a face already transported through earlier surgeries.
No global diffeomorphism to its original Morse level is required: an open
chart containing its whole closed disk parameters suffices.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E H X N F H' Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
  (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, N)) J (X × N) Y ∞)
  (g : C(X × MorseHandle.UnitDisk N, Y))
  (hsource : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Φ.source)
  (hface : ∀ x (w : MorseHandle.UnitDisk N), Φ (x, w.val) = g (x, w))

include hsource hface in
theorem exists_avoiding_of_charted_face {K : Set Y} (hK : IsClosed K)
    (hcore : ∀ x, g (x, ⟨0, by simp⟩) ∉ K) :
    ∃ D : Diffeomorph J J Y Y ∞, IsotopicToIdentity D ∧ Disjoint (range (D ∘ g)) K := by
  obtain ⟨a, ha, ha₁, hthin⟩ := exists_uniform_face_avoidance_radius g hK hcore
  obtain ⟨_, _, _, D, ⟨A⟩, hscale⟩ :=
    exists_product_disk_shrinking_of_open_face Φ hsource ha ha₁
  refine ⟨D, A.isotopicToIdentity, disjoint_left.mpr ?_⟩
  rintro _ ⟨⟨x, w⟩, rfl⟩ hmem
  have hnorm : ‖a • w.val‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_of_le_one_right ha.le (mem_closedBall_zero_iff.mp w.property)
  let w' : MorseHandle.UnitDisk N := ⟨a • w.val, mem_closedBall_zero_iff.mpr (hnorm.trans ha₁)⟩
  have heq : D (g (x, w)) = g (x, w') := by
    rw [← hface x w, hscale x w.val (mem_closedBall_zero_iff.mp w.property)]
    exact hface x w'
  exact hthin x w' hnorm (heq ▸ hmem)

variable [FiniteDimensional ℝ E] [IsManifold I ∞ X] [I.Boundaryless] [T2Space X]
  [FiniteDimensional ℝ F] [IsManifold J ∞ Y] [J.Boundaryless]
  {G K Z : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace K] {L : ModelWithCorners ℝ G K} [L.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace K Z] [IsManifold L ∞ Z] [CompactSpace Z]

include hsource hface in
theorem exists_ambient_avoiding_charted_face {k : Z → Y} (hk : ContMDiff L J ∞ k)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ G < Module.finrank ℝ F) :
    ∃ D : Diffeomorph J J Y Y ∞,
      IsotopicToIdentity D ∧ Disjoint (range (D ∘ g)) (range k) := by
  let c : X → Y := fun x => g (x, ⟨0, by simp⟩)
  have hc : ContMDiff I J ∞ c := by
    have hzero : ContMDiff I (I.prod 𝓘(ℝ, N)) ∞ (fun x : X => (x, (0 : N))) :=
      contMDiff_id.prodMk contMDiff_const
    have h := Φ.contMDiffOn_toFun.comp_contMDiff hzero
      (fun x => hsource ⟨mem_univ x, mem_closedBall_self zero_le_one⟩)
    exact h.congr (fun x => (hface x ⟨0, by simp⟩).symm)
  obtain ⟨e, he, havoid⟩ := NativeTransversality.exists_ambient_avoiding_diffeomorph hc hk hdim
  let Θ := Φ.trans e.toPartialDiffeomorph
  let g' : C(X × MorseHandle.UnitDisk N, Y) :=
    ⟨fun z => e (g z), e.toHomeomorph.continuous.comp g.continuous⟩
  have hsource' : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Θ.source :=
    fun z hz => ⟨hsource hz, mem_univ _⟩
  have hface' (x) (w : MorseHandle.UnitDisk N) : Θ (x, w.val) = g' (x, w) :=
    congrArg e (hface x w)
  have hcore' (x) : g' (x, ⟨0, by simp⟩) ∉ range k :=
    disjoint_left.mp havoid ⟨x, rfl⟩
  obtain ⟨D, hD, hdisjoint⟩ := exists_avoiding_of_charted_face Θ g' hsource' hface'
    (isCompact_range hk.continuous).isClosed hcore'
  exact ⟨e.trans D, he.trans hD, hdisjoint⟩

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
