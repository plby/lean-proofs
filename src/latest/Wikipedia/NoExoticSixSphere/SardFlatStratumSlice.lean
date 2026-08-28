import Wikipedia.NoExoticSixSphere.SardFlatStratum

/-!
# Reducing a finite vanishing stratum to one fewer source dimension

Restrict the inverse of the actual stratum chart to its zero slice. This
produces a smooth map on an open Euclidean domain whose critical values
contain the original stratum's local image. No lower-dimensional Sard
theorem is assumed in the construction of this map.
-/

open scoped ContDiff Manifold
open Set Module

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

theorem exists_flatStratumSlice {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hxU : x ∈ U) (hx : x ∈ flatPoints f k) (hx' : x ∉ flatPoints f (k + 1)) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin (finrank ℝ E - 1))),
      ∃ g : EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) → F,
        IsOpen V ∧ ContDiffOn ℝ ∞ g V ∧
        f '' (W ∩ flatPoints f k) ⊆
          g '' {z | z ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g z)} := by
  obtain ⟨Φ, hxΦ, hΦU, hfirst, hdf⟩ := exists_flatStratumChart hU hf hk hxU hx hx'
  let K := EuclideanSpace ℝ (Fin (finrank ℝ E - 1))
  let j : K → ℝ × K := fun z ↦ (0, z)
  let V : Set K := j ⁻¹' Φ.target
  let p : K → E := Φ.symm ∘ j
  let g : K → F := f ∘ p
  have hj : ContDiff ℝ ∞ j := contDiff_const.prodMk contDiff_id
  have hV : IsOpen V := Φ.open_target.preimage hj.continuous
  have hΦ : ContDiffOn ℝ ∞ Φ.symm Φ.target := Φ.contMDiffOn_invFun.contDiffOn
  have hp : ContDiffOn ℝ ∞ p V := hΦ.comp hj.contDiffOn (fun _ hz ↦ hz)
  have hpU : MapsTo p V U := fun z hz ↦ hΦU (Φ.map_target' hz)
  have hg : ContDiffOn ℝ ∞ g V := hf.comp hp hpU
  refine ⟨Φ.source, Φ.open_source, hxΦ, hΦU, V, g, hV, hg, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  let z : K := (Φ y).2
  have hjz : j z = Φ y := Prod.ext (hfirst y hy).symm rfl
  have hz : z ∈ V := by
    change j z ∈ Φ.target
    rw [hjz]
    exact Φ.map_source' hy.1
  have hpy : p z = y := by
    change Φ.symm (j z) = y
    rw [hjz]
    exact Φ.left_inv' hy.1
  have hzero : fderiv ℝ g z = 0 := by
    have hd := fderiv_comp z
      ((hf.contDiffAt (hU.mem_nhds (hpU hz))).differentiableAt (by simp))
      ((hp.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))
    change fderiv ℝ g z = (fderiv ℝ f (p z)).comp (fderiv ℝ p z) at hd
    rw [hpy, hdf y hy, ContinuousLinearMap.zero_comp] at hd
    exact hd
  refine ⟨z, ⟨hz, ?_⟩, congrArg f hpy⟩
  intro hs
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hs w
  rw [hzero, zero_apply] at hv
  exact hw hv.symm

end NoExoticSixSphere.Sard
