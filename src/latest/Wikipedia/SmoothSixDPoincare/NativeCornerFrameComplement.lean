import Wikipedia.SmoothSixDPoincare.SheetFrameTangentImage

/-!
# Native transversality gives complementary normal-frame images at a corner

Both actual strip germs are retained in the same disk. Every original sheet
tangent projects into its corresponding constructed frame. Surjectivity of
the original transverse tangent sum therefore gives surjectivity of the two
normal frames together, without assuming a compatibility of arbitrary frames.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {A B C H D D' Z E M N N' : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup D'] [NormedSpace ℝ D']
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace N'] [ChartedSpace D' N']

/-- The original transverse sheets span the actual tubular normal model through their frames. -/
theorem surjective_corner_normalFrames
    {F : N → M} {G : N' → M} {k l : (ℝ × ℝ) → M}
    (d : StripNormalData A B (E := E) (range F) k)
    (e : StripNormalData C H (E := E) (range G) l)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D') 𝓘(ℝ, E) ∞ G)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    (hl : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ l (s, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ q, Ψ (q, 0) = f q)
    {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c₁ c₂ : (ℝ × ℝ) → (ℝ × ℝ)}
    (hc₁ : ContDiffAt ℝ ∞ c₁ p) (hc₂ : ContDiffAt ℝ ∞ c₂ p)
    (hct : c₁ p = (t, 0)) (hcs : c₂ p = (s, 0))
    (hci₁ : Surjective (fderiv ℝ c₁ p)) (hci₂ : Surjective (fderiv ℝ c₂ p))
    (hgerm₁ : f =ᶠ[𝓝 p] k ∘ c₁) (hgerm₂ : f =ᶠ[𝓝 p] l ∘ c₂)
    {x : N} {y : N'} (hx : F x = k (t, 0)) (hy : G y = l (s, 0))
    (htrans : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, D') 𝓘(ℝ, E) G y))) :
    Surjective ((d.normalFrame Ψ t).coprod (e.normalFrame Ψ s)) := by
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p)
  let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x
  let DG : D' →L[ℝ] E := mfderiv 𝓘(ℝ, D') 𝓘(ℝ, E) G y
  have hFx : F x = f p := by
    have heq := hgerm₁.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hct] at heq
    exact hx.trans heq.symm
  have hGy : G y = f p := by
    have heq := hgerm₂.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcs] at heq
    exact hy.trans heq.symm
  have htarget : f p ∈ Ψ.target := by
    have h := Ψ.map_source' hp
    rwa [hzero p] at h
  have hQ : Surjective Q := TransverseCoordinates.surjective_mfderiv_normalCoordinate Ψ htarget
  have hfirst (u : D) : Q (DF u) ∈ (d.normalFrame Ψ t).range := by
    have h := d.normal_sheet_tangent_mem_frame_of_strip_germ Ψ hF ht hk hzero hp
      hc₁ hct hci₁ hgerm₁ hx u
    rw [hFx] at h
    exact h
  have hsecond (v : D') : Q (DG v) ∈ (e.normalFrame Ψ s).range := by
    have h := e.normal_sheet_tangent_mem_frame_of_strip_germ Ψ hG hs hl hzero hp
      hc₂ hcs hci₂ hgerm₂ hy v
    rw [hGy] at h
    exact h
  intro z
  obtain ⟨w, hw⟩ := hQ z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans w
  obtain ⟨a, ha⟩ := hfirst u
  obtain ⟨b, hb⟩ := hsecond v
  change d.normalFrame Ψ t a = Q (DF u) at ha
  change e.normalFrame Ψ s b = Q (DG v) at hb
  refine ⟨(a, b), ?_⟩
  change d.normalFrame Ψ t a + e.normalFrame Ψ s b = z
  rw [ha, hb, ← map_add]
  change Q (((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
    (mfderiv 𝓘(ℝ, D') 𝓘(ℝ, E) G y)) (u, v)) = z
  rw [huv]
  exact hw

end Wikipedia.SmoothSixDPoincare
