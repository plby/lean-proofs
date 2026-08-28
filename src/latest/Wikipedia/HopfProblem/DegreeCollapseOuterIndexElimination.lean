import Wikipedia.HopfProblem.DegreeCollapseOuterIndexMinimalMorse

/-!
# Eliminate indices one and five by the constructed handle trade

At fixed minimal total count, minimize the sum of the index-one and index-five
counts. The actual one-to-three trade contradicts this secondary minimum
whenever an index-one point exists. Negation preserves the cost and turns
index five into index one. Thus both outer intermediate indices vanish.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem outer_index_minimal_index_one_count_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E g).ncard = (criticalPoints E f).ncard →
      nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
        nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 := by
  by_contra hnot
  have hfinite : {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  obtain ⟨q, hqcrit, hq1⟩ := (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hnot)
  change {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard = 1 at hzero
  obtain ⟨m, hmset⟩ := Set.ncard_eq_one.mp hzero
  have hmem : m ∈ {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 0} := by
    rw [hmset]
    exact mem_singleton m
  let mc : criticalPoints E f := ⟨m, hmem.1⟩
  have hminimum (z : criticalPoints E f) (hz : nativeMorseIndex E f z = 0) : z = mc := by
    apply Subtype.ext
    have hzmem : z.val ∈ {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨z.property, hz⟩
    rwa [hmset, mem_singleton_iff] at hzmem
  obtain ⟨g, hg, hmg, hinjg, hcount, hcount1, -, hother⟩ :=
    exists_one_to_three_handle_trade_of_ordered_indices S hf hm e hdim horder
      mc ⟨q, hqcrit⟩ hmem.2 hq1 hminimum
  have hcost := hsecondary g hg hmg hinjg hcount
  have hcount5 := hother 5 (by omega) (by omega)
  omega

theorem outer_index_minimality_neg
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E g).ncard = (criticalPoints E f).ncard →
      nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
        nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E g).ncard = (criticalPoints E (fun x => -f x)).ncard →
      nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
        nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  intro g hg hmg hinjg hcard
  have hh := hsecondary (fun x => -g x) hg.neg (isMorse_neg hmg)
    (distinct_critical_values_neg hinjg) (by simpa only [criticalPoints_neg] using hcard)
  have hf1 := nativeMorseCount_neg hf hm (k := 1) (by omega)
  have hf5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hg1 := nativeMorseCount_neg hg hmg (k := 1) (by omega)
  have hg5 := nativeMorseCount_neg hg hmg (k := 5) (by omega)
  simp only [hdim, Nat.reduceSub] at hf1 hf5 hg1 hg5
  omega

theorem outer_index_minimal_outer_counts_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E g).ncard = (criticalPoints E f).ncard →
      nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
        nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 := by
  refine ⟨outer_index_minimal_index_one_count_zero S hf hm e hdim horder hzero hsecondary, ?_⟩
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
    (distinct_critical_values_neg S.distinct)
  have horderN : ∀ p q : criticalPoints E (fun x => -f x), -f p < -f q →
      nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q := by
    intro p q hpq
    let pf : criticalPoints E f := ⟨p.val, by simpa only [criticalPoints_neg] using p.property⟩
    let qf : criticalPoints E f := ⟨q.val, by simpa only [criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hzeroN : nativeMorseCount E (fun x => -f x) 0 = 1 := by
    have hc := nativeMorseCount_neg hf hm (k := 6) (by omega)
    simpa only [hdim, Nat.sub_self, hsix] using hc
  have honeN := outer_index_minimal_index_one_count_zero T hf.neg (isMorse_neg hm)
    e hdim horderN hzeroN (outer_index_minimality_neg hf hm hdim hsecondary)
  have hc := nativeMorseCount_neg hf hm (k := 5) (by omega)
  simpa only [hdim, Nat.reduceSub, honeN] using hc.symm

variable (E M) in
theorem exists_minimal_ordered_morse_system_without_outer_indices
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q →
          nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f 6 = 1 ∧
        nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 ∧
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hminimal, hsecondary⟩ :=
    exists_outer_index_minimal_ordered_morse_system E M
  rw [hdim] at hsix
  obtain ⟨hone, hfive⟩ := outer_index_minimal_outer_counts_zero S hf hm e hdim
    horder hzero hsix hsecondary
  exact ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
