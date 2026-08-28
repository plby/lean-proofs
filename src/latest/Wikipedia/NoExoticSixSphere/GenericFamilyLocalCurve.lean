import Wikipedia.NoExoticSixSphere.GenericFamilyClosedCurve
import Wikipedia.NoExoticSixSphere.FamilyDoublePointGerm
import Wikipedia.NoExoticSixSphere.SetGermCoordinates

/-!
# The closed double-curve construction is local

Only smoothness near the selected point and its actual regular residual are
needed. A smooth representative preserves the spatial-derivative germ. The
resulting curve chart is transferred back through equality of the actual
double-point closure germs on a swap-invariant open neighborhood.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyEmbedding

open OperatorRank CorankOneCoordinates

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem diagonal_not_mem_closure_doublePoints_of_local [FiniteDimensional ℝ W]
    (f : ℝ → V → W) {U : Set (ℝ × V)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (uncurry f) U) (p : ℝ × V) (hp : p ∈ U)
    (hi : Injective (fderiv ℝ (f p.1) p.2)) :
    (p.1, (p.2, p.2)) ∉ closure (doublePoints f) := by
  obtain ⟨G, hG, hGe⟩ := SmoothCurveExtension.exists_global hU hp hf
  let g := curry G
  have hg : ContDiff ℝ ∞ (uncurry g) := hG
  have he : uncurry g =ᶠ[𝓝 p] uncurry f := hGe
  have hJp := (spatial_fderiv_eventuallyEq he).eq_of_nhds
  have hgi : Injective (fderiv ℝ (g p.1) p.2) := hJp.symm ▸ hi
  intro hcl
  exact diagonal_not_mem_closure_doublePoints g hg p.1 p.2 hgi
    ((diagonal_mem_closedDoublePoints_iff he).mpr hcl)

theorem exists_closed_curve_of_local_regular_residual
    {T E F : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : T → V → W)
    {U : Set (T × V)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (uncurry f) U)
    (p : T × V) (hp : p ∈ U)
    (hres : ∃ c : Coordinates V W E F,
      fderiv ℝ (f p.1) p.2 ∈ domain c ∧
      CorankOne.residual (operatorEquiv c (fderiv ℝ (f p.1) p.2)) = 0 ∧
      Bijective (fderiv ℝ (fun q : T × V ↦ CorankOne.residual
        (operatorEquiv c (fderiv ℝ (f q.1) q.2))) p)) :
    ∃ hc : (p.1, (p.2, p.2)) ∈ closure (doublePoints f),
    ∃ d : OpenPartialHomeomorph (closure (doublePoints f)) ℝ,
      (⟨(p.1, (p.2, p.2)), hc⟩ : closure (doublePoints f)) ∈ d.source ∧
      d ⟨(p.1, (p.2, p.2)), hc⟩ = 0 ∧
      (∀ r ∈ d.source, swapClosure f r ∈ d.source) ∧
      ∀ r ∈ d.source, d (swapClosure f r) = -d r := by
  obtain ⟨G, hG, hGe⟩ := SmoothCurveExtension.exists_global hU hp hf
  let g := curry G
  have hg : ContDiff ℝ ∞ (uncurry g) := hG
  have he : uncurry g =ᶠ[𝓝 p] uncurry f := hGe
  have hJ := spatial_fderiv_eventuallyEq he
  have hJp := hJ.eq_of_nhds
  obtain ⟨a, ha, hz, hb⟩ := hres
  have hR : (fun q : T × V ↦ CorankOne.residual
      (operatorEquiv a (fderiv ℝ (g q.1) q.2))) =ᶠ[𝓝 p]
      (fun q : T × V ↦ CorankOne.residual
        (operatorEquiv a (fderiv ℝ (f q.1) q.2))) := by
    filter_upwards [hJ] with q hq
    rw [hq]
  obtain ⟨_, hgp, k, hkq, hkzero, _, hkswap, hkneg, _⟩ :=
    FamilyLinearCoordinates.exists_closed_curve_of_regular_residual g hg p
      ⟨a, hJp.symm ▸ ha, hJp.symm ▸ hz, (hR.fderiv_eq (𝕜 := ℝ)).symm ▸ hb⟩
  have hfp : (p.1, (p.2, p.2)) ∈ closure (doublePoints f) :=
    (diagonal_mem_closedDoublePoints_iff he).mp hgp
  let r₀ : closure (doublePoints f) := ⟨(p.1, (p.2, p.2)), hfp⟩
  let g₀ : closure (doublePoints g) := ⟨(p.1, (p.2, p.2)), hgp⟩
  obtain ⟨N₀, hN₀eq, hN₀open, hN₀p⟩ :=
    mem_nhds_iff.mp (closedDoublePoints_eventuallyEq he.symm)
  let N := N₀ ∩ swapPair ⁻¹' N₀
  have hswap : Continuous (swapPair : T × (V × V) → T × (V × V)) :=
    continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)
  have hN : IsOpen N := hN₀open.inter (hN₀open.preimage hswap)
  have hNp : (p.1, (p.2, p.2)) ∈ N := ⟨hN₀p, hN₀p⟩
  have hNeq : ∀ x ∈ N, x ∈ closure (doublePoints f) ↔ x ∈ closure (doublePoints g) :=
    fun _ hx ↦ Iff.of_eq (hN₀eq hx.1)
  let e := SetGerm.coordinates (closure (doublePoints f)) (closure (doublePoints g))
    N hNeq hN r₀ g₀
  have eval {r : closure (doublePoints f)} (hr : r ∈ e.source) : (e r).val = r.val :=
    SetGerm.coordinates_val _ _ _ _ _ _ _ hr
  have he₀ : e r₀ = g₀ := Subtype.ext (eval hNp)
  have hswapN {r : closure (doublePoints f)} (hr : r ∈ e.source) :
      swapClosure f r ∈ e.source := ⟨hr.2, hr.1⟩
  have hcommute {r : closure (doublePoints f)} (hr : r ∈ e.source) :
      e (swapClosure f r) = swapClosure g (e r) := by
    apply Subtype.ext
    rw [eval (hswapN hr)]
    change swapPair r.val = swapPair (e r).val
    rw [eval hr]
  let d := e.trans k
  have hdp : r₀ ∈ d.source := by
    refine ⟨hNp, ?_⟩
    change e r₀ ∈ k.source
    rw [he₀]
    exact hkq
  refine ⟨hfp, d, hdp, ?_, ?_, ?_⟩
  · change k (e r₀) = 0
    rw [he₀]
    exact hkzero
  · intro r hr
    refine ⟨hswapN hr.1, ?_⟩
    change e (swapClosure f r) ∈ k.source
    rw [hcommute hr.1]
    exact hkswap (e r) hr.2
  · intro r hr
    change k (e (swapClosure f r)) = -k (e r)
    rw [hcommute hr.1]
    exact hkneg (e r) hr.2

end NoExoticSixSphere.FamilyEmbedding
