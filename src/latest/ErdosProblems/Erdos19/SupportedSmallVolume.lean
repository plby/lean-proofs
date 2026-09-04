import ErdosProblems.Erdos19.SmallVolumeMinThree
import ErdosProblems.Erdos19.VertexTransport

/-! # Small-volume bounds on the actual support of the hypergraph -/

namespace Erdos19.SetHypergraph

universe u

theorem eventually_small_pair_volume_min_three_fintype (h : ℕ) (hh : 1 ≤ h) :
    ∃ N : ℕ, ∀ (X : Type u) [Fintype X], N ≤ Fintype.card X →
      ∀ H : SetHypergraph X, H.IsLinear → (∀ e : H, 3 ≤ e.1.ncard) →
      (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (∑ e : H, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card X) ^ 2 →
      ∃ q : ℕ, 2 * h * q ≤ (h + 6) * Fintype.card X ∧ H.EdgeColorable q := by
  classical
  obtain ⟨N, hN⟩ := eventually_small_pair_volume_min_three h hh
  refine ⟨N, ?_⟩
  intro X _ hn H hlinear hmin hvolume
  let f := Fintype.equivFin X
  let J := H.vertexImage f
  have hJlinear : J.IsLinear := (H.vertexImage_isLinear_iff f f.injective).mpr hlinear
  have hJmin : ∀ e : J, 3 ≤ e.1.ncard := by
    rintro ⟨e, g, hg, rfl⟩
    rw [Set.ncard_image_of_injective _ f.injective]
    exact hmin ⟨g, hg⟩
  have hJvolume : (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
      (∑ e : J, e.1.ncard * (e.1.ncard - 1)) < (Fintype.card X) ^ 2 := by
    rw [H.vertexImage_sum_pair_weight f f.injective]
    exact hvolume
  obtain ⟨q, hq, hc⟩ := hN (Fintype.card X) hn J hJlinear hJmin hJvolume
  exact ⟨q, hq, (H.vertexImage_edgeColorable_iff f f.injective q).mp hc⟩

theorem eventually_small_pair_volume_supported (h : ℕ) (hh : 1 ≤ h) :
    ∃ N : ℕ, ∀ (X : Type u) [Fintype X], ∀ U : Set X, N ≤ U.ncard →
      ∀ H : SetHypergraph X, H.IsLinear → (∀ e : H, e.1 ⊆ U) →
      (∀ e : H, 3 ≤ e.1.ncard) →
      (32 * h ^ 2 * (1 + 4 * h * (1 + 4 * h))) *
        (∑ e : H, e.1.ncard * (e.1.ncard - 1)) < U.ncard ^ 2 →
      ∃ q : ℕ, 2 * h * q ≤ (h + 6) * U.ncard ∧ H.EdgeColorable q := by
  classical
  obtain ⟨N, hN⟩ := eventually_small_pair_volume_min_three_fintype.{u} h hh
  refine ⟨N, ?_⟩
  intro X _ U hn H hlinear hsupport hmin hvolume
  let : Fintype U := Fintype.ofFinite U
  let J := H.onVertexSet U
  have hcard : Fintype.card U = U.ncard := Set.fintypeCard_eq_ncard _
  have himage : J.vertexImage (Subtype.val : U → X) = H :=
    H.vertexImage_onVertexSet_eq U (fun e he ↦ hsupport ⟨e, he⟩)
  have hJlinear : J.IsLinear := by
    apply (J.vertexImage_isLinear_iff Subtype.val Subtype.val_injective).mp
    simpa only [himage] using hlinear
  have hJmin : ∀ e : J, 3 ≤ e.1.ncard := by
    intro e
    have h := hmin ⟨Subtype.val '' e.1, e.2⟩
    simpa only [Set.ncard_image_of_injective _ Subtype.val_injective] using h
  have hweight : (∑ e : J, e.1.ncard * (e.1.ncard - 1)) =
      ∑ e : H, e.1.ncard * (e.1.ncard - 1) := by
    rw [← J.vertexImage_sum_pair_weight Subtype.val Subtype.val_injective, himage]
  obtain ⟨q, hq, hc⟩ := hN U (by simpa only [hcard] using hn) J hJlinear hJmin
    (by simpa only [hweight, hcard] using hvolume)
  refine ⟨q, by simpa only [hcard] using hq, ?_⟩
  have hc' := (J.vertexImage_edgeColorable_iff Subtype.val Subtype.val_injective q).mpr hc
  simpa only [himage] using hc'

#print axioms eventually_small_pair_volume_min_three_fintype
#print axioms eventually_small_pair_volume_supported

end Erdos19.SetHypergraph
