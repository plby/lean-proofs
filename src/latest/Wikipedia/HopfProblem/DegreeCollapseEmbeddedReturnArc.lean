import Wikipedia.HopfProblem.DegreeCollapseNativeOpenCurveGerms

/-!
# An embedded return arc retaining the continuation germs of a local arc

Given a local immersed arc and a path between its two endpoints inside an
open native manifold, the return curve is made smoothly embedded in that
open target. Its initial germ continues the local arc past the positive
endpoint; its final germ continues it from below the negative endpoint.
Disjointness of the two arc interiors is not asserted here.
-/

noncomputable section

open Set Function Filter ContinuousMap TopologicalSpace
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem injective_mfderiv_curve_translate {α : ℝ → N} {s c : ℝ}
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (s + c))
    (hi : Injective (mfderiv 𝓘(ℝ, ℝ) J α (s + c))) :
    Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (t + c)) s) := by
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s :=
    (contMDiff_id.add (contMDiff_const (c := c)) :
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => t + c)).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => id t + c) s = _
    rw [fderiv_add_const, fderiv_id]
  change Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => t + c)) s)
  rw [mfderiv_comp s hα ht]
  intro x y hxy
  apply hi
  have hdx : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x = x :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L x) hd
  have hdy : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y = y :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L y) hd
  change mfderiv 𝓘(ℝ, ℝ) J α (s + c)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s x) =
    mfderiv 𝓘(ℝ, ℝ) J α (s + c)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + c) s y) at hxy
  rw [hdx, hdy] at hxy
  exact hxy

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]

theorem exists_embedded_return_arc_inside_open (S : Opens N)
    {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hinj : InjOn α (Icc (-R) R))
    (hderiv : ∀ s ∈ Ioo (-R) R, Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hplus : α r ∈ S) (hminus : α (-r) ∈ S)
    (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
      ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let a : ℝ → N := fun t => α (t + r)
  let b : ℝ → N := fun t => α (t + (-1 - r))
  let U : Set ℝ := (fun t : ℝ => t + r) ⁻¹' Ioo (-R) R
  let V : Set ℝ := (fun t : ℝ => t + (-1 - r)) ⁻¹' Ioo (-R) R
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hp : r ∈ Ioo (-R) R := ⟨by linarith, hrR⟩
  have hm : -r ∈ Ioo (-R) R := ⟨by linarith, by linarith⟩
  have h0U : (0 : ℝ) ∈ U := by simpa only [U, mem_preimage, zero_add] using hp
  have h1V : (1 : ℝ) ∈ V := by
    change 1 + (-1 - r) ∈ Ioo (-R) R
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hm
  have ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V :=
    hα.comp (contMDiff_id.add contMDiff_const).contMDiffOn (fun _ ht => ht)
  have ha0 : a 0 = α r := by dsimp [a]; rw [zero_add]
  have hb1 : b 1 = α (-r) := by dsimp [b]; congr 1; ring
  have hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0) := by
    apply injective_mfderiv_curve_translate
    · simpa only [zero_add] using
        (hα.contMDiffAt (Ioo_mem_nhds hp.1 hp.2)).mdifferentiableAt (by simp)
    · exact (zero_add r).symm ▸ hderiv r hp
  have hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1) := by
    apply injective_mfderiv_curve_translate
    · simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using
        (hα.contMDiffAt (Ioo_mem_nhds hm.1 hm.2)).mdifferentiableAt (by simp)
    · exact (show (1 : ℝ) + (-1 - r) = -r by ring).symm ▸ hderiv (-r) hm
  have haS : a 0 ∈ S := ha0.symm ▸ hplus
  have hbS : b 1 ∈ S := hb1.symm ▸ hminus
  have hpath : Path (⟨a 0, haS⟩ : S) (⟨b 1, hbS⟩ : S) :=
    γ.cast (Subtype.ext ha0) (Subtype.ext hb1)
  have hxy : a 0 ≠ b 1 := by
    rw [ha0, hb1]
    intro hh
    have heq := hinj ⟨hp.1.le, hp.2.le⟩ ⟨hm.1.le, hm.2.le⟩ hh
    linarith
  exact exists_embedded_native_open_arc_with_local_germs S ha hb hU hV h0U h1V haS hbS
    hia hib hpath hxy hdim

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
