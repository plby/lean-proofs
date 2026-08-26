import ErdosProblems.Erdos633.CrossingIndicator
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Almost-everywhere validity of triangle crossings

The excluded vertex heights and supporting lines are strict affine
subspaces, hence null for planar volume. The geometric crossing formula
therefore holds almost everywhere for every nondegenerate triangle.
-/

namespace Erdos633

open MeasureTheory

def horizontalAffineLine (r : ℝ) : AffineSubspace ℝ ℂ where
  carrier := {z | z.im = r}
  smul_vsub_vadd_mem' := by
    intro t p q s hp hq hs
    change p.im = r at hp
    change q.im = r at hq
    change s.im = r at hs
    change (t • (p - q) + s).im = r
    simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul,
      hp, hq, hs, sub_self, mul_zero, zero_add]

theorem horizontalAffineLine_ne_top (r : ℝ) : horizontalAffineLine r ≠ ⊤ := by
  intro h
  have hz : (⟨0, r + 1⟩ : ℂ) ∈ horizontalAffineLine r := by rw [h]; trivial
  change r + 1 = r at hz
  linarith

theorem volume_horizontal_line (r : ℝ) : volume {z : ℂ | z.im = r} = 0 :=
  Measure.addHaar_affineSubspace volume (horizontalAffineLine r) (horizontalAffineLine_ne_top r)

theorem ae_im_ne (r : ℝ) : ∀ᵐ z : ℂ ∂volume, z.im ≠ r := by
  apply ae_iff.mpr
  simpa only [not_not] using volume_horizontal_line r

theorem Triangle.barycentric_zero_set (P : Triangle) (k : Fin 3) :
    {z | P.barycentric z k = 0} =
      (affineSpan ℝ {P.edgeStart k, P.edgeEnd k} : Set ℂ) := by
  ext z
  change P.barycentric z k = 0 ↔ z ∈ affineSpan ℝ {P.edgeStart k, P.edgeEnd k}
  exact (P.barycentric_eq_zero_iff_lineMap k z).trans
    (mem_affineSpan_pair_iff_exists_lineMap_eq).symm

theorem Triangle.supportingLine_ne_top (P : Triangle) (k : Fin 3) :
    affineSpan ℝ {P.edgeStart k, P.edgeEnd k} ≠ ⊤ := by
  intro h
  have hz : P.vertex k ∈ (affineSpan ℝ {P.edgeStart k, P.edgeEnd k} : Set ℂ) := by
    rw [h]
    trivial
  rw [← P.barycentric_zero_set] at hz
  change P.barycentric (P.vertex k) k = 0 at hz
  rw [P.barycentric_vertex, if_pos rfl] at hz
  exact one_ne_zero hz

theorem Triangle.volume_barycentric_zero (P : Triangle) (k : Fin 3) :
    volume {z | P.barycentric z k = 0} = 0 := by
  rw [P.barycentric_zero_set]
  exact Measure.addHaar_affineSubspace volume _ (P.supportingLine_ne_top k)

theorem Triangle.ae_barycentric_ne (P : Triangle) (k : Fin 3) :
    ∀ᵐ z ∂volume, P.barycentric z k ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not] using P.volume_barycentric_zero k

theorem Triangle.ae_crossingRegular (P : Triangle) : ∀ᵐ z ∂volume, P.CrossingRegular z := by
  have hh : ∀ᵐ z : ℂ ∂volume, ∀ k : Fin 3, (P.vertex k).im ≠ z.im := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [ae_im_ne (P.vertex k).im] with z hz
    exact hz.symm
  have hd : ∀ᵐ z ∂volume, ∀ k : Fin 3, P.barycentric z k ≠ 0 :=
    ae_all_iff.mpr P.ae_barycentric_ne
  filter_upwards [hh, hd] with z hz hd
  exact ⟨hz, hd⟩

theorem Triangle.crossingAt_ae_eq_indicator (P : Triangle) :
    (fun z => (P.crossingAt z : ℝ)) =ᵐ[volume]
      (interior P.carrier).indicator (fun _ => P.orientationSign) := by
  filter_upwards [P.ae_crossingRegular] with z hz
  exact P.crossingAt_eq_indicator z hz

end Erdos633
