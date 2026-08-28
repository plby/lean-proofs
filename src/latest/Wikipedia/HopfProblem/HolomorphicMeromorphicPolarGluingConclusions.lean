import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarGluingSections
import Wikipedia.HopfProblem.HolomorphicMeromorphicField

/-!
# Nonzero denominator and proportionality for the native polar sections

The glued denominator is not the zero section on a nonempty manifold,
because each original denominator has a nonzero holomorphic germ. If the
two native bundle sections are proportional by a complex constant, linearity
of their original trivializations gives the same proportionality of local
holomorphic numerators and denominators. Cancellation takes place in the
actual fraction-stalk fields and identifies the original meromorphic section
with the corresponding constant section.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M] {s : Section I M ⊤}
  {ι : Type*} (A : ι → PolarLocal.Presentation I M s)
  (hcover : ∀ x : M, ∃ i, x ∈ (A i).domain)

/-- The actual glued denominator is a nonzero native holomorphic section. -/
theorem denominatorSection_ne_zero [Nonempty M] : denominatorSection I M A hcover ≠ 0 := by
  intro hzero
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨i, hx⟩ := hcover x
  have hden : (A i).denominator = 0 := by
    apply ContMDiffMap.ext
    intro y
    have hy : denominatorSection I M A hcover y.val = 0 :=
      congrArg (fun t : ContMDiffSection I ℂ ω (cocycle I M A hcover).core.Fiber => t y.val)
        hzero
    exact (denominatorSection_eq_zero_iff I M A hcover i y.property).mp hy
  apply (A i).denominator_ne_zero ⟨x, hx⟩
  rw [hden, map_zero]

private theorem local_numerator_eq_const_mul_denominator (c : ℂ)
    (hprop : numeratorSection I M A hcover = c • denominatorSection I M A hcover) (i : ι) :
    (A i).numerator =
      algebraMap ℂ (HolomorphicFunctionSheaf.Section I M (A i).domain) c * (A i).denominator := by
  apply ContMDiffMap.ext
  intro x
  change (A i).numerator x = c * (A i).denominator x
  let L := ((cocycle I M A hcover).core.localTriv i).linearEquivAt ℂ x.val x.property
  have hn : L (numeratorSection I M A hcover x.val) = (A i).numerator x :=
    congrArg Prod.snd (numeratorSection_localTriv I M A hcover i x.property)
  have hd : L (denominatorSection I M A hcover x.val) = (A i).denominator x :=
    congrArg Prod.snd (denominatorSection_localTriv I M A hcover i x.property)
  have hpoint : numeratorSection I M A hcover x.val = c • denominatorSection I M A hcover x.val :=
    congrArg (fun t : ContMDiffSection I ℂ ω (cocycle I M A hcover).core.Fiber => t x.val) hprop
  calc
    (A i).numerator x = L (numeratorSection I M A hcover x.val) := hn.symm
    _ = L (c • denominatorSection I M A hcover x.val) := congrArg L hpoint
    _ = c • L (denominatorSection I M A hcover x.val) := L.map_smul c _
    _ = c * (A i).denominator x := by rw [hd, smul_eq_mul]

/-- Proportionality of the two genuine bundle sections makes the original
meromorphic function the corresponding constant, as an equality of full
meromorphic sections and not just of ordinary values. -/
theorem proportionality_constancy (c : ℂ)
    (hprop : numeratorSection I M A hcover = c • denominatorSection I M A hcover) :
    s = algebraMap ℂ (Section I M ⊤) c := by
  apply section_ext
  intro x
  obtain ⟨i, hx⟩ := hcover x.val
  have hq : sectionGerm I M (A i).domain ⟨x.val, hx⟩ (A i).denominator ≠ 0 :=
    fun h => (A i).denominator_ne_zero ⟨x.val, hx⟩
      ((sectionGerm_eq_zero_iff I M (A i).domain ⟨x.val, hx⟩ (A i).denominator).mp h)
  calc
    s x = fraction I M (A i).domain (A i).numerator (A i).denominator ⟨x.val, hx⟩ :=
      (A i).fraction_eq ⟨x.val, hx⟩
    _ = sectionGerm I M (A i).domain ⟨x.val, hx⟩
        (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M (A i).domain) c) := by
      rw [fraction, local_numerator_eq_const_mul_denominator I M A hcover c hprop i,
        map_mul, mul_div_cancel_right₀ _ hq]
    _ = sectionGerm I M ⊤ x
        (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M ⊤) c) :=
      sectionGerm_restrict I M (show (A i).domain ≤ ⊤ from le_top) ⟨x.val, hx⟩
        (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M ⊤) c)
    _ = (algebraMap ℂ (Section I M ⊤) c) x := by
      rw [algebraMap_section, ofHolomorphic_apply]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing
