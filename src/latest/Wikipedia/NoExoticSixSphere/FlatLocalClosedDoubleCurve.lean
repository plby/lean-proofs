import Wikipedia.NoExoticSixSphere.FlatClosedDoubleCurve
import Wikipedia.NoExoticSixSphere.FlatSmoothGerm
import Wikipedia.NoExoticSixSphere.FlatDoublePointGerm
import Wikipedia.NoExoticSixSphere.SetGermCoordinates

/-!
# A closed double-curve chart for a locally smooth flat map

A smooth representative supplies the chart, and equality of the actual
closed double-point germs transfers it to the original map. Restricting to
a swap-invariant neighborhood retains the involution and its sign change.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_local_closed_double_curve_chart (h : U × ℝ → F)
    {A : Set (U × ℝ)} (hA : IsOpen A) (hh : ContDiffOn ℝ ∞ h A)
    (p : U × ℝ) (hp : p ∈ A) (hz : vertical h p = 0)
    (hb : Bijective (fderiv ℝ (vertical h) p)) :
    ∃ hc : (p, p) ∈ closure (doublePoints h),
    ∃ d : OpenPartialHomeomorph (closure (doublePoints h)) ℝ,
      (⟨(p, p), hc⟩ : closure (doublePoints h)) ∈ d.source ∧
      d ⟨(p, p), hc⟩ = 0 ∧
      (∀ r ∈ d.source, d r = (r.val.1.2 - r.val.2.2) / 2) ∧
      (∀ r ∈ d.source, swapClosure h r ∈ d.source) ∧
      (∀ r ∈ d.source, d (swapClosure h r) = -d r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (d.symm s).val) d.target := by
  obtain ⟨g, hg, he, hv, hD⟩ := exists_global_representative hA hp hh
  obtain ⟨hgp, c, hcsource, hczero, hcapply, hcswap, hcneg, hcsmooth⟩ :=
    exists_closed_double_curve_chart g hg p (hv.trans hz) (hD.symm ▸ hb)
  have hgdiag : (p, p) ∈ closure (doublePoints g) := by
    simpa only [pair, add_zero, sub_zero, Prod.eta] using hgp
  have hdiag : (p, p) ∈ closure (doublePoints h) :=
    (diagonal_mem_closedDoublePoints_iff he).mp hgdiag
  let r₀ : closure (doublePoints h) := ⟨(p, p), hdiag⟩
  let g₀ : closure (doublePoints g) := ⟨(p, p), hgdiag⟩
  have hgc : g₀ ∈ c.source := by
    simpa only [g₀, pair, add_zero, sub_zero, Prod.eta] using hcsource
  have hgz : c g₀ = 0 := by
    simpa only [g₀, pair, add_zero, sub_zero, Prod.eta] using hczero
  obtain ⟨N₀, hN₀eq, hN₀open, hN₀p⟩ :=
    mem_nhds_iff.mp (closedDoublePoints_eventuallyEq he.symm)
  let N := N₀ ∩ Prod.swap ⁻¹' N₀
  have hN : IsOpen N := hN₀open.inter (hN₀open.preimage continuous_swap)
  have hNp : (p, p) ∈ N := ⟨hN₀p, hN₀p⟩
  have hNeq : ∀ x ∈ N, x ∈ closure (doublePoints h) ↔ x ∈ closure (doublePoints g) :=
    fun _ hx ↦ Iff.of_eq (hN₀eq hx.1)
  let e := SetGerm.coordinates (closure (doublePoints h)) (closure (doublePoints g))
    N hNeq hN r₀ g₀
  have eval {r : closure (doublePoints h)} (hr : r ∈ e.source) : (e r).val = r.val :=
    SetGerm.coordinates_val _ _ _ _ _ _ _ hr
  have he₀ : e r₀ = g₀ := Subtype.ext (eval hNp)
  let d := e.trans c
  have hdsource : r₀ ∈ d.source := by
    refine ⟨hNp, ?_⟩
    change e r₀ ∈ c.source
    rw [he₀]
    exact hgc
  have hdapply : ∀ r ∈ d.source, d r = (r.val.1.2 - r.val.2.2) / 2 := by
    intro r hr
    change c (e r) = _
    rw [hcapply, eval hr.1]
  have hdswap : ∀ r ∈ d.source, swapClosure h r ∈ d.source := by
    intro r hr
    have hrN : r.val ∈ N := hr.1
    have hsN : (swapClosure h r).val ∈ N := ⟨hrN.2, hrN.1⟩
    have hswap : e (swapClosure h r) = swapClosure g (e r) := by
      apply Subtype.ext
      rw [eval hsN]
      change Prod.swap r.val = Prod.swap (e r).val
      rw [eval hr.1]
    refine ⟨hsN, ?_⟩
    change e (swapClosure h r) ∈ c.source
    rw [hswap]
    exact hcswap (e r) hr.2
  refine ⟨hdiag, d, hdsource, ?_, hdapply, hdswap, ?_, ?_⟩
  · change c (e r₀) = 0
    rw [he₀]
    exact hgz
  · intro r hr
    rw [hdapply _ (hdswap r hr), hdapply r hr]
    change (r.val.2.2 - r.val.1.2) / 2 = -((r.val.1.2 - r.val.2.2) / 2)
    ring
  · apply (hcsmooth.mono (fun _ hs ↦ hs.1)).congr
    intro s hs
    change (e.symm (c.symm s)).val = (c.symm s).val
    exact SetGerm.coordinates_symm_val _ _ _ _ _ _ _ hs.2

end NoExoticSixSphere.FlatDoubleCurve
