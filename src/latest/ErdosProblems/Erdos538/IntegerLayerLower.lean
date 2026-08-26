import ErdosProblems.Erdos538.WeightedAveraging

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Positive squarefree integers at most `N` with exactly `k` distinct prime
factors. -/
def squarefreePrimeLayer (N k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => Squarefree n ∧ n.primeFactors.card = k

/-- Reciprocal mass valued in nonnegative rationals. -/
def reciprocalMassNN (A : Finset ℕ) : ℚ≥0 :=
  ∑ a ∈ A, (1 : ℚ≥0) / a

/-- Weight of the members of an arbitrary finite set satisfying `P`. -/
noncomputable def weightedFilterMass {ι : Type*} (items : Finset ι)
    (P : ι → Prop) (w : ι → ℚ≥0) : ℚ≥0 := by
  classical
  exact ∑ x ∈ items with P x, w x

/-- Push reciprocal integer weights forward along the prime-support map. -/
noncomputable def primeSupportPushWeight (layer : Finset ℕ)
    (S : Finset ℕ) : ℚ≥0 := by
  classical
  exact ∑ n ∈ layer with n.primeFactors = S, (1 : ℚ≥0) / n

/-- Grouping by prime support preserves total reciprocal weight. -/
theorem sum_primeSupportPushWeight
    (layer : Finset ℕ) :
    (∑ S ∈ layer.image Nat.primeFactors, primeSupportPushWeight layer S) =
      reciprocalMassNN layer := by
  classical
  have hmap : ∀ n ∈ layer, n.primeFactors ∈ layer.image Nat.primeFactors :=
    fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩
  simpa [primeSupportPushWeight, reciprocalMassNN] using
    (Finset.sum_fiberwise_of_maps_to hmap
      (fun n : ℕ => (1 : ℚ≥0) / n))

/-- The same pushforward identity after filtering supports by an arbitrary
predicate. -/
theorem sum_primeSupportPushWeight_filter
    (layer : Finset ℕ) (P : Finset ℕ → Prop) :
    weightedSupportMass (layer.image Nat.primeFactors) P
        (primeSupportPushWeight layer) =
      weightedFilterMass layer (fun n => P n.primeFactors)
        (fun n => (1 : ℚ≥0) / n) := by
  classical
  let supports := layer.image Nat.primeFactors
  have h := Finset.sum_fiberwise_eq_sum_filter layer
    (supports.filter P) Nat.primeFactors (fun n : ℕ => (1 : ℚ≥0) / n)
  have heq : layer.filter (fun n => n.primeFactors ∈ supports.filter P) =
      layer.filter (fun n => P n.primeFactors) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, -, hP⟩
      exact ⟨hn, hP⟩
    · rintro ⟨hn, hP⟩
      exact ⟨hn, Finset.mem_image.mpr ⟨n, hn, rfl⟩, hP⟩
  rw [heq] at h
  simpa only [weightedSupportMass, weightedFilterMass,
    primeSupportPushWeight, supports] using h

/-- Prime supports of the layer lie in the finite ground set `[0,N+1)`. -/
theorem primeFactors_subset_range_succ_of_mem_layer
    {N k n : ℕ} (hn : n ∈ squarefreePrimeLayer N k) :
    n.primeFactors ⊆ Finset.range (N + 1) := by
  intro p hp
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpn : p ≤ n := Nat.le_of_dvd hnpos hpdvd
  exact Finset.mem_range.mpr (by omega)

/-- Quantitative finite integer-layer construction: every squarefree exact
prime-support layer has an admissible cap-two subfamily retaining at least a
`1/(4k²)` share of its reciprocal mass. -/
theorem exists_admissible_squarefreeLayer_quarter_sq_with_subset
    (N k : ℕ) (hk : 0 < k) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      A ⊆ squarefreePrimeLayer N k ∧
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (4 * k * k) • reciprocalMassNN A := by
  classical
  let layer := squarefreePrimeLayer N k
  let supports := layer.image Nat.primeFactors
  let w := primeSupportPushWeight layer
  have hsub : ∀ S ∈ supports, S ⊆ Finset.range (N + 1) := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
    exact primeFactors_subset_range_succ_of_mem_layer hn
  have hcard : ∀ S ∈ supports, S.card = k := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
    exact (Finset.mem_filter.mp hn).2.2
  obtain ⟨color, z, hcap, hmass⟩ :=
    exists_weighted_checksum_quarter_sq (N + 1) k hk supports w hsub hcard
  let F := RainbowChecksum k ({z} : Finset (ZMod (2 * k * k)))
  let A := patternIntegerFamily N color F
  have hAdm : Admissible 2 N A :=
    patternIntegerFamily_admissible_of_patternCap (by omega) color F hcap
  have htotal : (∑ S ∈ supports, w S) = reciprocalMassNN layer := by
    simpa [supports, w] using sum_primeSupportPushWeight layer
  have hselected : weightedSupportMass supports
      (fun S => RainbowChecksum k {z} (S.1.map color)) w =
      ∑ n ∈ layer with RainbowChecksum k {z}
        (n.primeFactors.1.map color), (1 : ℚ≥0) / n := by
    simpa [supports, w, weightedSupportMass, weightedFilterMass] using
      sum_primeSupportPushWeight_filter layer
        (fun S => RainbowChecksum k {z} (S.1.map color))
  have hA : A = layer.filter (fun n => RainbowChecksum k {z}
      (n.primeFactors.1.map color)) := by
    ext n
    simp only [A, F, patternIntegerFamily, layer, squarefreePrimeLayer,
      Finset.mem_filter, Finset.mem_Icc, supportSignature]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hsq, hselect⟩
      have hkcard : n.primeFactors.card = k := by
        simpa using hselect.2.1
      exact ⟨⟨⟨hn1, hnN⟩, hsq, hkcard⟩, hselect⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hsq, hkcard⟩, hselect⟩
      exact ⟨⟨hn1, hnN⟩, hsq, hselect⟩
  have hAsub : A ⊆ squarefreePrimeLayer N k := by
    rw [hA]
    exact (Finset.filter_subset _ _).trans (by simp [layer])
  refine ⟨A, hAdm, hAsub, ?_⟩
  rw [htotal, hselected] at hmass
  simpa [reciprocalMassNN, hA] using hmass

/-- The subset-free form recorded as the basic exact-layer lower bound. -/
theorem exists_admissible_squarefreeLayer_quarter_sq
    (N k : ℕ) (hk : 0 < k) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (4 * k * k) • reciprocalMassNN A := by
  obtain ⟨A, hA, -, hmass⟩ :=
    exists_admissible_squarefreeLayer_quarter_sq_with_subset N k hk
  exact ⟨A, hA, hmass⟩

end Erdos538
