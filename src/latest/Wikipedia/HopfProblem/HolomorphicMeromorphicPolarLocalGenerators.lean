import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPresentation
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarSurfaceReduced

/-!
# Actual local generators for the polar denominator ideals

The reduced stalk pair has isolated common zero for every pair of native
representatives. After choosing representatives, their nonzero denominator
germs persist on an actual open neighborhood. Equality of the original
meromorphic germs gives equality on a smaller neighborhood. Away from the
isolated center one member of the pair is a unit; at the center the proved
cancellation law applies. Consequently the same local denominator generates
every denominator ideal on that neighborhood.

This proves the local-principality needed for a polar line bundle without
assuming coherence or local principality as extra input.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal

open PolarAlgebra

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- The rich reduced-pair data yield an actual neighborhood on which one
native holomorphic denominator generates every polar denominator ideal. -/
theorem exists_presentation_of_reduced_pair (s : Section I M ⊤) (x : M)
    (a b : HolomorphicStalk I M x) (hb : b ≠ 0)
    (hs : s ⟨x, Set.mem_univ x⟩ = ofHolomorphicGerm I M x a / ofHolomorphicGerm I M x b)
    (hcancel : ∀ h : HolomorphicStalk I M x, b ∣ h * a ↔ b ∣ h)
    (hisolated : PolarSurfaceReduced.NativeIsolatedCommonZero I M x a b) :
    ∃ D : Presentation I M s, x ∈ D.domain := by
  obtain ⟨U, hxU, A, hA⟩ := (HolomorphicFunctionSheaf.presheaf I M).exists_germ_eq a
  obtain ⟨V, hVU, hxV, B, hB⟩ :=
    (HolomorphicFunctionSheaf.presheaf I M).exists_le_germ_eq b hxU
  let AV := HolomorphicFunctionSheaf.restrictionAlgHom I M hVU A
  have hAV : holomorphicGerm I M V ⟨x, hxV⟩ AV = a :=
    (holomorphicGerm_restrict I M hVU ⟨x, hxV⟩ A).trans hA
  have hBV : holomorphicGerm I M V ⟨x, hxV⟩ B = b := hB
  have hBV0 : holomorphicGerm I M V ⟨x, hxV⟩ B ≠ 0 := hBV ▸ hb
  have hiso := hisolated V hxV AV B hAV hBV
  obtain ⟨W, hWV, hxW, hWq⟩ :=
    HolomorphicFunctionSheaf.exists_open_restriction_germs_ne_zero I V B x hxV hBV0
  have hnbhd : {y : M | y ∈ W ∧
      (HolomorphicFunctionSheaf.extendManifoldSection I V AV y = 0 →
        HolomorphicFunctionSheaf.extendManifoldSection I V B y = 0 → y = x)} ∈ 𝓝 x :=
    inter_mem (W.isOpen.mem_nhds hxW) hiso
  obtain ⟨T, hT, hTo, hxT⟩ := mem_nhds_iff.mp hnbhd
  let T' : Opens M := ⟨T, hTo⟩
  have hTW : T' ≤ W := fun y hy => (hT hy).1
  have hTV : T' ≤ V := hTW.trans hWV
  let pT := HolomorphicFunctionSheaf.restrictionAlgHom I M hTV AV
  let qT := HolomorphicFunctionSheaf.restrictionAlgHom I M hTV B
  have hpTx : holomorphicGerm I M T' ⟨x, hxT⟩ pT = a :=
    (holomorphicGerm_restrict I M hTV ⟨x, hxT⟩ AV).trans hAV
  have hqTx : holomorphicGerm I M T' ⟨x, hxT⟩ qT = b :=
    (holomorphicGerm_restrict I M hTV ⟨x, hxT⟩ B).trans hBV
  have hqT : ∀ y : T', holomorphicGerm I M T' y qT ≠ 0 := by
    intro y
    have hnonzero : holomorphicGerm I M W (Set.inclusion hTW y)
        (HolomorphicFunctionSheaf.restrictionAlgHom I M hWV B) ≠ 0 :=
      hWq (Set.inclusion hTW y)
    intro hz
    exact hnonzero ((holomorphicGerm_restrict I M hWV (Set.inclusion hTW y) B).trans
      ((holomorphicGerm_restrict I M hTV y B).symm.trans hz))
  let localFraction := ofFraction I M T' pT qT hqT
  have heqx : s ⟨x, Set.mem_univ x⟩ = localFraction ⟨x, hxT⟩ := by
    change s ⟨x, Set.mem_univ x⟩ =
      ofHolomorphicGerm I M x (holomorphicGerm I M T' ⟨x, hxT⟩ pT) /
        ofHolomorphicGerm I M x (holomorphicGerm I M T' ⟨x, hxT⟩ qT)
    rw [hpTx, hqTx]
    exact hs
  obtain ⟨K, hKtop, hKT, hxK, hK⟩ := exists_neighborhood_eq_of_germ_eq I M
    s localFraction x (Set.mem_univ x) hxT heqx
  let pK := HolomorphicFunctionSheaf.restrictionAlgHom I M hKT pT
  let qK := HolomorphicFunctionSheaf.restrictionAlgHom I M hKT qT
  have hpKx : holomorphicGerm I M K ⟨x, hxK⟩ pK = a :=
    (holomorphicGerm_restrict I M hKT ⟨x, hxK⟩ pT).trans hpTx
  have hqKx : holomorphicGerm I M K ⟨x, hxK⟩ qK = b :=
    (holomorphicGerm_restrict I M hKT ⟨x, hxK⟩ qT).trans hqTx
  have hqK : ∀ y : K, holomorphicGerm I M K y qK ≠ 0 := by
    intro y
    simpa only [qK, holomorphicGerm_restrict] using hqT (Set.inclusion hKT y)
  have hfrac : ∀ y : K, s ⟨y.val, Set.mem_univ y.val⟩ = fraction I M K pK qK y := by
    intro y
    exact (hK y).trans (fraction_restrict I M hKT pT qT y).symm
  have hcenter : denominatorIdeal (HolomorphicStalk I M x)
      (fraction I M K pK qK ⟨x, hxK⟩) =
      Ideal.span ({holomorphicGerm I M K ⟨x, hxK⟩ qK} : Set _) := by
    change denominatorIdeal (HolomorphicStalk I M x)
      (ofHolomorphicGerm I M x (holomorphicGerm I M K ⟨x, hxK⟩ pK) /
        ofHolomorphicGerm I M x (holomorphicGerm I M K ⟨x, hxK⟩ qK)) = _
    rw [hpKx, hqKx]
    dsimp only [ofHolomorphicGerm]
    ext h
    rw [mem_denominatorIdeal_div_iff (HolomorphicStalk I M x) a b hb,
      Ideal.mem_span_singleton]
    exact hcancel h
  have hisoK : ∀ y : K, pK y = 0 → qK y = 0 → y.val = x := by
    intro y hpy hqy
    apply (hT (hKT y.property)).2
    · rw [HolomorphicFunctionSheaf.extendManifoldSection_apply I V AV y.val
        (hTV (hKT y.property))]
      exact hpy
    · rw [HolomorphicFunctionSheaf.extendManifoldSection_apply I V B y.val
        (hTV (hKT y.property))]
      exact hqy
  have hall := fraction_denominatorIdeal_eq_span_of_isolated_common_zero I M
    pK qK ⟨x, hxK⟩ hqK hcenter hisoK
  refine ⟨⟨K, pK, qK, hqK, hfrac, ?_⟩, hxK⟩
  intro y
  rw [hfrac y]
  exact hall y

/-- Every genuine global meromorphic function on a complex surface has
actual locally principal denominator presentations near every point. -/
theorem exists_presentation_at (e : (ℂ × ℂ) ≃L[ℂ] E)
    (s : Section I M ⊤) (x : M) : ∃ D : Presentation I M s, x ∈ D.domain := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective
    (HolomorphicStalk I M x) (s ⟨x, Set.mem_univ x⟩)
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  obtain ⟨a, b, hb, hcross, hcancel, hisolated⟩ :=
    PolarSurfaceReduced.exists_reduced_pair I M e x p q hq0
  apply exists_presentation_of_reduced_pair I M s x a b hb _ hcancel hisolated
  refine hpq.symm.trans ?_
  apply (div_eq_div_iff
    ((ofHolomorphicGerm_eq_zero_iff I M x q).not.mpr hq0)
    ((ofHolomorphicGerm_eq_zero_iff I M x b).not.mpr hb)).mpr
  simpa only [ofHolomorphicGerm, map_mul, mul_comm] using
    congrArg (ofHolomorphicGerm I M x) hcross

/-- Choose actual presentations centered at every original point. Their
domains cover the original manifold by construction. -/
def presentationAt (e : (ℂ × ℂ) ≃L[ℂ] E) (s : Section I M ⊤) (x : M) :
    Presentation I M s := (exists_presentation_at I M e s x).choose

theorem mem_presentationAt (e : (ℂ × ℂ) ≃L[ℂ] E) (s : Section I M ⊤) (x : M) :
    x ∈ (presentationAt I M e s x).domain :=
  (exists_presentation_at I M e s x).choose_spec

theorem presentationAt_cover (e : (ℂ × ℂ) ≃L[ℂ] E) (s : Section I M ⊤) :
    ∀ x : M, ∃ i : M, x ∈ (presentationAt I M e s i).domain :=
  fun x => ⟨x, mem_presentationAt I M e s x⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal
