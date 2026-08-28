import Wikipedia.HopfProblem.DegreeCollapseSmallRadialDisk

/-!
# An entire embedded disk undergoing the unique native belt crossing

The local sheet is reparametrized by a global bounded disk map with
invertible differential. Its whole image remains in the original chart,
the original intersection count remains exact, and the time trace remains
transverse to the whole original belt.
-/

noncomputable section

open Set Function Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

section Precomposition

variable {A B E H H' M Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ B H'} {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace Y] [ChartedSpace H' Y]

theorem native_transversality_precomp_surjective {T : A → M} {g : Y → M}
    {ψ : A → A} {x : A} {y : Y}
    (hT : MDifferentiableAt 𝓘(ℝ, A) J T (ψ x))
    (hψ : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, A) ψ x)
    (hs : Surjective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A) ψ x))
    (ht : NativeTransversality.At 𝓘(ℝ, A) I J T g (ψ x) y) :
    NativeTransversality.At 𝓘(ℝ, A) I J (T ∘ ψ) g x y := by
  intro he
  have hsurj := ht he
  rw [mfderiv_comp x hT hψ]
  let D₁ : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) J T (ψ x)
  let D₂ : B →L[ℝ] E := mfderiv I J g y
  let C : A →L[ℝ] A := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A) ψ x
  change Surjective ((D₁.comp C).coprod D₂)
  change Surjective (D₁.coprod D₂) at hsurj
  change Surjective C at hs
  intro v
  obtain ⟨⟨u, w⟩, huw⟩ := hsurj v
  obtain ⟨z, hz⟩ := hs u
  refine ⟨(z, w), ?_⟩
  change D₁ (C z) + D₂ w = v
  rw [hz]
  exact huw

end Precomposition

variable {A B V E H H' M Y : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ V H'} {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace Y] [ChartedSpace H' Y]

theorem exists_global_crossing_disk
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) J ((ℝ × A) × B) M ∞)
    (a : ℝ) (hs : beltCrossingSheet a (0 : A) ∈ Φ.source)
    (F : ℝ × M → M) (hF : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ F)
    (b : Y → M) (v : Y)
    (hcount : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : A, beltCrossingSheet a w ∈ Φ.source →
      ∀ y : Y, (F (t, Φ (beltCrossingSheet a w)) = b y ↔
        t = 1 / 2 ∧ w = 0 ∧ y = v))
    (htrace : ContMDiffAt 𝓘(ℝ, ℝ × A) J ∞
      (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) (1 / 2, 0))
    (htrans : NativeTransversality.At 𝓘(ℝ, ℝ × A) I J
      (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) b (1 / 2, 0) v) :
    ∃ g : A → M, ContMDiff 𝓘(ℝ, A) J ∞ g ∧ Injective g ∧
      (∀ x, Injective (mfderiv 𝓘(ℝ, A) J g x)) ∧
      IsClosedEmbedding (fun x : closedBall (0 : A) 1 => g x.val) ∧
      g 0 = Φ (beltCrossingSheet a (0 : A)) ∧ (∀ x, g x ∈ Φ.target) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : A, ∀ y : Y,
        (F (t, g x) = b y ↔ t = 1 / 2 ∧ x = 0 ∧ y = v)) ∧
      ContMDiff 𝓘(ℝ, ℝ × A) J ∞ (fun p : ℝ × A => F (p.1, g p.2)) ∧
      NativeTransversality.At 𝓘(ℝ, ℝ × A) I J
        (fun p : ℝ × A => F (p.1, g p.2)) b (1 / 2, 0) v := by
  let L : A →L[ℝ] (ℝ × A) × B :=
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)
  have hL : Injective L := by
    intro x y hxy
    exact congrArg (fun z : (ℝ × A) × B => z.1.2) hxy
  have hcoords (z : A) : L z + beltCrossingSheet a (0 : A) = beltCrossingSheet a z := by
    ext <;> simp [L, beltCrossingSheet]
  obtain ⟨ψ, hψ, hψi, hψd, hψ0, hsource, hg, hgi, hgd, hclosed⟩ :=
    exists_global_affine_disk_in_chart Φ L hL (beltCrossingSheet a (0 : A)) hs
  simp only [hcoords] at hsource hclosed
  let g : A → M := fun x => Φ (beltCrossingSheet a (ψ x))
  have heq : (fun y => Φ (L (ψ y) + beltCrossingSheet a (0 : A))) = g :=
    funext (fun y => congrArg Φ (hcoords (ψ y)))
  rw [heq] at hg hgi hgd
  have hzero : g 0 = Φ (beltCrossingSheet a (0 : A)) := by
    dsimp only [g]
    rw [hψ0]
  refine ⟨g, hg, hgi, hgd, hclosed, hzero,
    fun x => Φ.map_source' (hsource x), ?_, ?_, ?_⟩
  · intro t ht x y
    change F (t, Φ (beltCrossingSheet a (ψ x))) = b y ↔ _
    rw [hcount t ht (ψ x) (hsource x) y]
    have hzeroiff : ψ x = 0 ↔ x = 0 :=
      ⟨fun h => hψi (h.trans hψ0.symm), fun h => h ▸ hψ0⟩
    rw [hzeroiff]
  · have hfst : ContMDiff 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ) ∞ Prod.fst := contDiff_fst.contMDiff
    have hsnd : ContMDiff 𝓘(ℝ, ℝ × A) 𝓘(ℝ, A) ∞ Prod.snd := contDiff_snd.contMDiff
    exact hF.comp (hfst.prodMk (hg.comp hsnd))
  · let P : ℝ × A → ℝ × A := fun p => (p.1, ψ p.2)
    have hP : ContDiff ℝ ∞ P := contDiff_fst.prodMk (hψ.comp contDiff_snd)
    have hP0 : P ((1 / 2 : ℝ), (0 : A)) = (1 / 2, 0) := Prod.ext rfl hψ0
    have hPd : fderiv ℝ P ((1 / 2 : ℝ), (0 : A)) =
        (ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ ψ 0) :=
      ((hasFDerivAt_id (1 / 2 : ℝ)).prodMap ((1 / 2 : ℝ), (0 : A))
        (hψ.differentiable (by simp) 0).hasFDerivAt).fderiv
    have hPsurj : Surjective (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × A) P (1 / 2, 0)) := by
      rw [mfderiv_eq_fderiv, hPd]
      rintro ⟨t, w⟩
      obtain ⟨x, hx⟩ := (hψd 0).2 w
      exact ⟨(t, x), Prod.ext rfl hx⟩
    have hT : MDifferentiableAt 𝓘(ℝ, ℝ × A) J
        (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) (P (1 / 2, 0)) := by
      rw [hP0]
      exact htrace.mdifferentiableAt (by simp)
    have ht : NativeTransversality.At 𝓘(ℝ, ℝ × A) I J
        (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) b (P (1 / 2, 0)) v := by
      rw [hP0]
      exact htrans
    exact native_transversality_precomp_surjective hT
      (hP.contMDiff.mdifferentiableAt (by simp)) hPsurj ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
