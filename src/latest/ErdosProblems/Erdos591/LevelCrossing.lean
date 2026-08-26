import ErdosProblems.Erdos591.LevelState

open Set Ordinal

namespace Erdos591.Negative.Exact.Levels

/-- Complete the current body and extract a later large level, using two
of the retained `omega^omega` factors.  The added segment contains the
new box marker, and every one of its coordinates is above `bound`. -/
theorem State.cross_level {W : Set G} {m r k j : ℕ}
    (s : State W m (r + 2) k) (hk : 0 < k) (hj : 0 < j) (bound : ℕ) :
    ∃ U : Set G, U ⊆ W ∧ ∃ (s' : State U m r j) (t : List TaggedCoord),
      t ≠ [] ∧ HasBox t ∧ (∀ z ∈ t, bound < z.value) ∧
      s'.fragment = s.fragment ++ t := by
  obtain ⟨a, ha, v, hvne, habove, hv⟩ :=
    s.maximal.complete_above (rawLevel_pairwise W s.outer s.size) hk bound
  have haLevel : (a.1 : InnerLevels.OrderedSL) ∈ Level W s.outer := ha
  let V := Child W s.outer a.1
  have hVroot : ∀ x ∈ V, x.1.length = m :=
    fun x hx ↦ s.root x hx.1
  have hVtype : continuationBound (r + 2) ≤ typeLT V :=
    s.retained a.1 haLevel
  have hVprefix : ∀ x ∈ V, s.outer ++ [a.1] <+: x.1 := fun _ hx ↦ hx.2
  obtain ⟨U, p, hUV, hprefix, _, hlevel, hretained⟩ :=
    exists_large_level_extending_prefix V hVroot (s.outer ++ [a.1])
      hVprefix r (j + 1) hVtype
  obtain ⟨n, u, hun, htype, hmax⟩ := exists_level_maximal_prefix hlevel
  have hUW : U ⊆ W := fun _ hx ↦ (hUV hx).1
  let s' : State U m r j :=
    { outer := p
      size := n
      body := u
      maximal := ⟨hun, htype, hmax⟩
      root := fun x hx ↦ s.root x (hUW hx)
      retained := hretained }
  rcases hprefix with ⟨q, hq⟩
  let t := plainBody v ++ (q.flatMap taggedLevel ++ (⟨n, true⟩ :: plainBody u))
  have htbox : HasBox t := by
    refine ⟨⟨n, true⟩, ?_, rfl⟩
    exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
  have htne : t ≠ [] := by
    intro hnil
    rcases htbox with ⟨z, hz, _⟩
    rw [hnil] at hz
    exact List.not_mem_nil hz
  have hfragment : s'.fragment = s.fragment ++ t := by
    change partialSequence m p n u = partialSequence m s.outer s.size s.body ++ t
    rw [← hq]
    simpa only [t, List.append_assoc] using
      partialSequence_cross m s.outer q s.size n a.1 s.body v u a.2 hv
  have hpair : t.Pairwise (fun a b ↦ a.value < b.value) := by
    have hp := s'.fragment_pairwise hj
    rw [hfragment] at hp
    exact (List.pairwise_append.mp hp).2.1
  have htabove : ∀ z ∈ t, bound < z.value :=
    above_append_of_pairwise hpair (plainBody_ne_nil hvne) (above_plainBody habove)
  exact ⟨U, hUW, s', t, htne, htbox, htabove, hfragment⟩

end Erdos591.Negative.Exact.Levels
