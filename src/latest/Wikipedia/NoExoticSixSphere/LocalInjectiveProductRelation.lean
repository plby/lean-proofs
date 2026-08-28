import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# Uniform local injectivity near a compact zero section

Local injectivity at every point of a compact zero section yields a uniform
small parameter ball and an open neighborhood of the base diagonal. Pairs
in that neighborhood with small parameters belong to a common injectivity
chart. No global injectivity of the zero section is required.
-/

noncomputable section

open Set Function Metric

namespace NoExoticSixSphere

theorem exists_uniform_localInjective_product_relation
    {X P Y : Type*} [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup P]
    (F : X × P → Y)
    (hlocal : ∀ x, ∃ U : Set (X × P), IsOpen U ∧ (x, 0) ∈ U ∧ InjOn F U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set (X × X), IsOpen V ∧
      (∀ x, (x, x) ∈ V) ∧ ∀ x y, (x, y) ∈ V → ∀ v w,
        ‖v‖ ≤ ε → ‖w‖ ≤ ε → F (x, v) = F (y, w) → x = y ∧ v = w := by
  let R : Set ((X × X) × (P × P)) := ⋃ U : {U : Set (X × P) // IsOpen U ∧ InjOn F U},
    {q | (q.1.1, q.2.1) ∈ U.val ∧ (q.1.2, q.2.2) ∈ U.val}
  have hR : IsOpen R := isOpen_iUnion fun U ↦
    (U.property.1.preimage (continuous_fst.fst.prodMk continuous_snd.fst)).inter
      (U.property.1.preimage (continuous_fst.snd.prodMk continuous_snd.snd))
  let K : Set (X × X) := range (fun x : X ↦ (x, x))
  have hK : IsCompact K := isCompact_range (continuous_id.prodMk continuous_id)
  have hKR : K ×ˢ ({0} : Set (P × P)) ⊆ R := by
    rintro ⟨⟨x, y⟩, vw⟩ ⟨⟨z, hz⟩, hvw⟩
    have hx : z = x := congrArg Prod.fst hz
    have hy : z = y := congrArg Prod.snd hz
    subst x y
    have hvw' : vw = 0 := hvw
    subst vw
    obtain ⟨U, hU, hzU, hiU⟩ := hlocal z
    exact mem_iUnion.mpr ⟨⟨U, hU, hiU⟩, hzU, hzU⟩
  obtain ⟨V, W, hV, hW, hKV, hzW, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hR hKR
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (hzW (mem_singleton 0)))
  refine ⟨δ / 2, by linarith, V, hV, fun x ↦ hKV ⟨x, rfl⟩, ?_⟩
  intro x y hxy v w hv hw he
  have hmem : (v, w) ∈ W := by
    apply hball
    rw [mem_ball, dist_zero_right, Prod.norm_def]
    exact (max_le hv hw).trans_lt (by linarith)
  have hq : ((x, y), (v, w)) ∈ R := hVW ⟨hxy, hmem⟩
  obtain ⟨U, hleft, hright⟩ := mem_iUnion.mp hq
  have hpair := U.property.2 hleft hright he
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end NoExoticSixSphere
