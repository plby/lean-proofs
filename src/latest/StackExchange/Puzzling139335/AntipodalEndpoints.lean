import StackExchange.Puzzling139335.AntipodalArcContainment
import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.LoopVariation.Geometric.ExtensionContradiction

/-!
# Antipodal endpoints of a congruent two-piece cut

The topological three-arc decomposition and the concrete truncated-variation
estimate show that congruent pieces cut a centrally symmetric Jordan boundary
at antipodal points.  No boundary-length assumption is made.
-/

open Set Schoenflies

namespace Puzzling139335

theorem common_cut_endpoints_eq_free_involution
    {C C₁ C₂ Γ M N : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (houter : IsCutPair C p q M N)
    (hcut₁ : IsCutPair C₁ p q Γ M) (hcut₂ : IsCutPair C₂ p q Γ N)
    (e g : Plane ≃ᵢ Plane) (he : e '' C₁ = C₂) (hg : g '' C = C)
    (hinv : Function.Involutive g) (hfree : ∀ x ∈ C, g x ≠ x) : q = g p := by
  by_contra hq
  rcases cutPair_has_antipodal_bridge hC g.toHomeomorph hg hinv hfree houter hq with
    hMN | hNM
  · obtain ⟨K, hK, hN, hfirst, hsecond⟩ := hMN
    have himageK : IsArcBetween (g '' K) (g q) p := by
      have himage := hK.image_homeomorph g.toHomeomorph
      change IsArcBetween (g '' K) (g q) (g (g p)) at himage
      rwa [hinv p] at himage
    exact LoopVariation.common_cut_excludes_three_arc_extension hcut₁ hcut₂
      e.isometry he g.isometry hK (houter.fst.image_homeomorph g.toHomeomorph)
      himageK hfirst hsecond hN.symm
  · obtain ⟨K, hK, hM, hfirst, hsecond⟩ := hNM
    have he' : e.symm '' C₂ = C₁ := by
      rw [← he, image_image]
      simp
    have himageK : IsArcBetween (g '' K) (g q) p := by
      have himage := hK.image_homeomorph g.toHomeomorph
      change IsArcBetween (g '' K) (g q) (g (g p)) at himage
      rwa [hinv p] at himage
    exact LoopVariation.common_cut_excludes_three_arc_extension hcut₂ hcut₁
      e.symm.isometry he' g.isometry hK (houter.snd.image_homeomorph g.toHomeomorph)
      himageK hfirst hsecond hM.symm

/-- In a centrally symmetric Jordan domain, the endpoints of a common cut
between congruent Jordan boundaries are antipodal. -/
theorem common_cut_endpoints_antipodal
    {C C₁ C₂ Γ M N : Set Plane} {p q c : Plane}
    (hC : IsJordanCurve C) (houter : IsCutPair C p q M N)
    (hcut₁ : IsCutPair C₁ p q Γ M) (hcut₂ : IsCutPair C₂ p q Γ N)
    (e : Plane ≃ᵢ Plane) (he : e '' C₁ = C₂)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    q = AffineIsometryEquiv.pointReflection ℝ c p := by
  let g := (AffineIsometryEquiv.pointReflection ℝ c).toIsometryEquiv
  have hfix (x : Plane) : g x = x ↔ x = c :=
    AffineIsometryEquiv.pointReflection_fixed_iff
  have hinv : Function.Involutive g :=
    AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c
  have hcnot : c ∉ C :=
    hC.not_mem_of_involution_unique_fixed g.toHomeomorph hsym hinv
      (AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) c) (fun x hx => (hfix x).mp hx)
  have hfree : ∀ x ∈ C, g x ≠ x := by
    intro x hx hxe
    exact hcnot ((hfix x).mp hxe ▸ hx)
  exact common_cut_endpoints_eq_free_involution hC houter hcut₁ hcut₂ e g he hsym hinv hfree

namespace JordanCrosscut

theorem endpoints_antipodal_of_congruent_boundaries
    {C Γ M N : Set Plane} {p q c : Plane}
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (e : Plane ≃ᵢ Plane) (he : e '' (Γ ∪ M) = Γ ∪ N)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    q = AffineIsometryEquiv.pointReflection ℝ c p := by
  have hcut₁ : IsCutPair (Γ ∪ M) p q Γ M :=
    ⟨h.arc, houter.fst, rfl, h.inter_arc_eq houter⟩
  have hcut₂ : IsCutPair (Γ ∪ N) p q Γ N :=
    ⟨h.arc, houter.snd, rfl, h.inter_arc_eq houter.symm⟩
  exact common_cut_endpoints_antipodal h.curve houter hcut₁ hcut₂ e he hsym

/-- The geometric formulation: if the two closed sides of a Jordan crosscut
are congruent and the outer boundary is central, its endpoints are antipodal. -/
theorem endpoints_antipodal_of_congruent_sides
    {C Γ M N : Set Plane} {p q c : Plane}
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (hcongr : Congruent (closure (inside (M ∪ Γ))) (closure (inside (N ∪ Γ))))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    q = AffineIsometryEquiv.pointReflection ℝ c p := by
  obtain ⟨e, he⟩ := hcongr
  have hM := jordan_curve_theorem (h.isJordanCurve_union houter)
  have hN := jordan_curve_theorem (h.isJordanCurve_union houter.symm)
  have hboundary : e '' (M ∪ Γ) = N ∪ Γ := by
    calc
      e '' (M ∪ Γ) = e '' frontier (closure (inside (M ∪ Γ))) := by
        rw [frontier_closure_inside hM]
      _ = frontier (e '' closure (inside (M ∪ Γ))) :=
        e.toHomeomorph.image_frontier _
      _ = N ∪ Γ := by rw [he, frontier_closure_inside hN]
  apply h.endpoints_antipodal_of_congruent_boundaries houter e.toIsometryEquiv ?_ hsym
  change e '' (Γ ∪ M) = Γ ∪ N
  simpa only [union_comm] using hboundary

end JordanCrosscut

end Puzzling139335
