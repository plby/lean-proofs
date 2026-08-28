import Wikipedia.HopfProblem.DegreeCollapseCommonTransverseRange
import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart

/-!
# Common original transverse coordinates and cylinder restriction

The actual endpoint label charts construct their relative chart, also
after a prescribed linear change to signed block coordinates. Restricting
both charts gives exactly one common open label range. The original
native cylinder restricts to that range with its maps and field retained.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {D B Z E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_common_transverse_coordinates (e : D ≃L[ℝ] B)
    (Q P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞)
    (hQ0 : (0 : D) ∈ Q.source) (hP0 : (0 : D) ∈ P.source)
    (hQfix : Q 0 = 0) (hPfix : P 0 = 0) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B Z ∞)
      (H : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, B) B B ∞) (U : Set Z),
      IsOpen U ∧ (0 : Z) ∈ U ∧ (0 : B) ∈ H.source ∧ H 0 = 0 ∧
      Q' 0 = 0 ∧ P' 0 = 0 ∧ Q'.source = H.source ∧ P'.source = H.target ∧
      Q'.target = U ∧ P'.target = U ∧ U ⊆ Q.target ∩ P.target ∧
      (∀ u ∈ Q'.source, e.symm u ∈ Q.source) ∧
      (∀ u ∈ P'.source, e.symm u ∈ P.source) ∧
      (∀ u, Q' u = Q (e.symm u)) ∧ (∀ u, P' u = P (e.symm u)) ∧
      (∀ u ∈ H.source, P' (H u) = Q' u) ∧
      ∀ u, H u = e (P.symm (Q (e.symm u))) := by
  let R := e.symm.toDiffeomorph.toPartialDiffeomorph
  let Qe := R.trans Q
  let Pe := R.trans P
  have hQe0 : (0 : B) ∈ Qe.source := by
    change (0 : B) ∈ univ ∧ e.symm 0 ∈ Q.source
    rw [map_zero]
    exact ⟨mem_univ _, hQ0⟩
  have hPe0 : (0 : B) ∈ Pe.source := by
    change (0 : B) ∈ univ ∧ e.symm 0 ∈ P.source
    rw [map_zero]
    exact ⟨mem_univ _, hP0⟩
  have hQezero : Qe 0 = 0 := by change Q (e.symm 0) = 0; rw [map_zero, hQfix]
  have hPezero : Pe 0 = 0 := by change P (e.symm 0) = 0; rw [map_zero, hPfix]
  let H := Qe.trans Pe.symm
  have h0 : (0 : B) ∈ H.source := by
    refine ⟨hQe0, ?_⟩
    change Qe 0 ∈ Pe.target
    rw [hQezero, ← hPezero]
    exact Pe.map_source' hPe0
  have hH0 : H 0 = 0 := by
    change Pe.symm (Qe 0) = 0
    rw [hQezero, ← hPezero]
    exact Pe.left_inv' hPe0
  have hHs : H.source ⊆ Qe.source := fun _ hu => hu.1
  have hHt : H.target ⊆ Pe.source := fun _ hu => hu.1
  have hdiagram (u : B) (hu : u ∈ H.source) : Pe (H u) = Qe u :=
    Pe.right_inv' hu.2
  obtain ⟨Q', P', U, hU, h0U, hQs, hPs, hQt, hPt, hUsub, hQmap, hPmap⟩ :=
    exists_common_transverse_range Qe Pe H h0 hQezero hHs hHt hdiagram
  refine ⟨Q', P', H, U, hU, h0U, h0, hH0,
    (hQmap 0).trans hQezero, (hPmap 0).trans hPezero,
    hQs, hPs, hQt, hPt, ?_, ?_, ?_, hQmap, hPmap, ?_, fun _ => rfl⟩
  · intro z hz
    exact ⟨(hUsub hz).1.1, (hUsub hz).2.1⟩
  · intro u hu
    exact (hHs (hQs ▸ hu)).2
  · intro u hu
    exact (hHt (hPs ▸ hu)).2
  · intro u hu
    exact (hPmap (H u)).trans ((hdiagram u hu).trans (hQmap u).symm)

theorem exists_restricted_native_cylinder
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U O : Set Z} (hsource : A.source = U ×ˢ univ) (hO : IsOpen O) (hOU : O ⊆ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA : ∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
      (fun _ : Z × ℝ => (0, 1)) y) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      B.source = O ×ˢ univ ∧ B.source ⊆ A.source ∧ B.target ⊆ A.target ∧
      (∀ z, B z = A z) ∧
      ∀ y ∈ B.target, V y = FlowConstruction.partialChartField B.symm
        (fun _ : Z × ℝ => (0, 1)) y := by
  let B := PartialChart.restrictSource A (hO.prod isOpen_univ)
  have hsub : O ×ˢ (univ : Set ℝ) ⊆ A.source := by
    rw [hsource]
    exact fun z hz => ⟨hOU hz.1, hz.2⟩
  have hBs : B.source = O ×ˢ univ := inter_eq_right.mpr hsub
  exact ⟨B, hBs, fun _ hz => hz.1, fun _ hy => hy.1, fun _ => rfl,
    fun y hy => hA y hy.1⟩

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
