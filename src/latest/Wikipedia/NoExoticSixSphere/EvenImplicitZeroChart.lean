import Wikipedia.NoExoticSixSphere.ImplicitCurveCoordinates
import Wikipedia.NoExoticSixSphere.RegularLevelChart

/-!
# A symmetric local zero-curve chart with its actual free coordinate

For an even equation with invertible derivative in the remaining variables,
the constructed chart on the actual zero subtype is precisely projection to
the free real coordinate. Its source is invariant under reflection, and its
inverse is smooth as a map into the original ambient space.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace NoExoticSixSphere.ImplicitCurve

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def reflectPoint (q : P × ℝ) : P × ℝ := (q.1, -q.2)

omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [NormedAddCommGroup P] in
theorem reflectPoint_involutive : Involutive (reflectPoint (P := P)) := by
  intro q
  simp [reflectPoint]

def reflection (Φ : P × ℝ → F) (heven : ∀ p s, Φ (p, -s) = Φ (p, s)) :
    {q : P × ℝ // Φ q = 0} ≃ₜ {q : P × ℝ // Φ q = 0} where
  toFun q := ⟨reflectPoint q.val, (heven q.val.1 q.val.2).trans q.property⟩
  invFun q := ⟨reflectPoint q.val, (heven q.val.1 q.val.2).trans q.property⟩
  left_inv q := Subtype.ext (reflectPoint_involutive q.val)
  right_inv q := Subtype.ext (reflectPoint_involutive q.val)
  continuous_toFun :=
    (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.neg).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.neg).subtype_mk _

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ F]
  [NormedSpace ℝ P] [NormedSpace ℝ F] in
theorem reflection_involutive (Φ : P × ℝ → F) (heven : ∀ p s, Φ (p, -s) = Φ (p, s)) :
    Involutive (reflection Φ heven) := fun q ↦ Subtype.ext (reflectPoint_involutive q.val)

omit [FiniteDimensional ℝ F] in
theorem exists_symmetric_zero_chart (Φ : P × ℝ → F) (hΦ : ContDiff ℝ ∞ Φ)
    (p : P) (hz : Φ (p, 0) = 0)
    (hb : Bijective (fderiv ℝ (fun q : P ↦ Φ (q, 0)) p))
    (heven : ∀ p s, Φ (p, -s) = Φ (p, s)) :
    ∃ d : OpenPartialHomeomorph {q : P × ℝ // Φ q = 0} ℝ,
      (⟨(p, 0), hz⟩ : {q : P × ℝ // Φ q = 0}) ∈ d.source ∧
      (∀ q, d q = q.val.2) ∧
      (∀ q ∈ d.source, reflection Φ heven q ∈ d.source) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (d.symm s).val) d.target := by
  obtain ⟨e, hep, _, heq⟩ :=
    exists_coordinates Φ univ isOpen_univ p (mem_univ _) hΦ.contDiffOn hb
  let q₀ : {q : P × ℝ // Φ q = 0} := ⟨(p, 0), hz⟩
  have hfirst : ∀ q ∈ e.source, (e q).1 = Φ q := fun q _ ↦ congrArg Prod.fst (heq q)
  let c := RegularLevelChart.chart e.toOpenPartialHomeomorph hfirst q₀
  let r := reflection Φ heven
  let d := c.restrOpen (r ⁻¹' c.source) (c.open_source.preimage r.continuous)
  have hc₀ : q₀ ∈ c.source := hep
  have hr₀ : r q₀ = q₀ := by
    apply Subtype.ext
    simp [r, reflection, reflectPoint, q₀]
  have hd₀ : q₀ ∈ d.source := by
    refine ⟨hc₀, ?_⟩
    change r q₀ ∈ c.source
    rw [hr₀]
    exact hc₀
  have happly (q : {q : P × ℝ // Φ q = 0}) : d q = q.val.2 := by
    change (e q.val).2 = q.val.2
    rw [heq]
  have hreflect (q : {q : P × ℝ // Φ q = 0}) (hq : q ∈ d.source) : r q ∈ d.source := by
    change q ∈ c.source ∧ r q ∈ c.source at hq
    change r q ∈ c.source ∧ r (r q) ∈ c.source
    exact ⟨hq.2, (reflection_involutive Φ heven q).symm ▸ hq.1⟩
  refine ⟨d, hd₀, happly, hreflect, ?_⟩
  have hi : ContDiffOn ℝ ∞ (fun s : ℝ ↦ e.symm (0, s)) d.target :=
    e.contMDiffOn_invFun.contDiffOn.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hs ↦ hs.1)
  apply hi.congr
  intro s hs
  exact RegularLevelChart.chart_symm_val e.toOpenPartialHomeomorph hfirst q₀ hs.1

end NoExoticSixSphere.ImplicitCurve
