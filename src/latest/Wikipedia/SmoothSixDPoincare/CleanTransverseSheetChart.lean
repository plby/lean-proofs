import Wikipedia.SmoothSixDPoincare.TransverseSheetChart
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Exact local sheet images in the constructed transverse chart

The embedding topology lets us shrink the target to exclude all other branches
of either sheet patch. In the resulting chart, membership in each complete
patch image is exactly vanishing of its complementary coordinate. Thus the
off-axis region is genuinely clean relative to both patches.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- The constructed chart identifies the full two embedded patch images with its two axes. -/
theorem exists_clean_simultaneous_sheetChart {f : D → M} {g : Z → M}
    {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hembf : IsEmbedding (fun x : U => f x)) (hembg : IsEmbedding (fun z : V => g z))
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ b : ℝ, 0 < b ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
      closedBall (0 : D) b ×ˢ closedBall (0 : Z) b ⊆ Φ.source ∧
      Φ.source ⊆ U ×ˢ V ∧ Φ.target ⊆ O ∧
      (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
      (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) ∧
      (∀ q ∈ Φ.source, (Φ q ∈ f '' U ↔ q.2 = 0) ∧ (Φ q ∈ g '' V ↔ q.1 = 0)) := by
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright⟩ :=
    exists_simultaneous_sheetChart hU hV h0U h0V hf hg hzero hdim ht hO h0O
  have hballU : IsOpen {x : U | (x : D) ∈ ball 0 a} :=
    isOpen_ball.preimage continuous_subtype_val
  have hballV : IsOpen {z : V | (z : Z) ∈ ball 0 a} :=
    isOpen_ball.preimage continuous_subtype_val
  obtain ⟨A, hA, hpreA⟩ := hembf.isInducing.isOpen_iff.mp hballU
  obtain ⟨B, hB, hpreB⟩ := hembg.isInducing.isOpen_iff.mp hballV
  have h0A : f 0 ∈ A := by
    have hz : (⟨0, h0U⟩ : U) ∈ {x : U | (x : D) ∈ ball 0 a} := mem_ball_self ha
    rw [← hpreA] at hz
    exact hz
  have h0B : g 0 ∈ B := by
    have hz : (⟨0, h0V⟩ : V) ∈ {z : V | (z : Z) ∈ ball 0 a} := mem_ball_self ha
    rw [← hpreB] at hz
    exact hz
  have hsmallF {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : x ∈ closedBall 0 a := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun x : U => f x) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact ball_subset_closedBall hx'
  have hsmallG {z : Z} (hz : z ∈ V) (hzB : g z ∈ B) : z ∈ closedBall 0 a := by
    have hz' : (⟨z, hz⟩ : V) ∈ (fun z : V => g z) ⁻¹' B := hzB
    rw [hpreB] at hz'
    exact ball_subset_closedBall hz'
  let Ψ := PartialChart.restrictTarget Φ (hA.inter hB)
  have h0Φ : (0, 0) ∈ Φ.source := hprod
    ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩
  have hcenter : Φ (0, 0) = f 0 := hleft 0 h0Φ
  have h0Ψ : (0, 0) ∈ Ψ.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ (0, 0) ∈ A ∩ B
    rw [hcenter]
    exact ⟨h0A, hzero ▸ h0B⟩
  obtain ⟨b, hb, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds h0Ψ)
  refine ⟨b, hb, Ψ, ?_, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1,
    (fun x hx => hleft x hx.1), (fun z hz => hright z hz.1), ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · rintro ⟨x, z⟩ hq
    have hAq : Φ (x, z) ∈ A := hq.2.1
    have hBq : Φ (x, z) ∈ B := hq.2.2
    constructor
    · constructor
      · rintro ⟨u, hu, heq⟩
        have huA : f u ∈ A := heq ▸ hAq
        have haxis : (u, 0) ∈ Φ.source :=
          hprod ⟨hsmallF hu huA, mem_closedBall_self ha.le⟩
        have hpair : (x, z) = (u, 0) := Φ.toPartialEquiv.injOn hq.1 haxis
          (heq.symm.trans (hleft u haxis).symm)
        exact congrArg Prod.snd hpair
      · intro hz
        change z = 0 at hz
        subst z
        exact ⟨x, (hsource hq.1).1, (hleft x hq.1).symm⟩
    · constructor
      · rintro ⟨v, hv, heq⟩
        have hvB : g v ∈ B := heq ▸ hBq
        have haxis : (0, v) ∈ Φ.source :=
          hprod ⟨mem_closedBall_self ha.le, hsmallG hv hvB⟩
        have hpair : (x, z) = (0, v) := Φ.toPartialEquiv.injOn hq.1 haxis
          (heq.symm.trans (hright v haxis).symm)
        exact congrArg Prod.fst hpair
      · intro hx
        change x = 0 at hx
        subst x
        exact ⟨z, (hsource hq.1).2, (hright z hq.1).symm⟩

end Wikipedia.SmoothSixDPoincare
