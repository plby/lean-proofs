/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterSeparatedCenters

/-!
# Low-rank resonances for a generic Hunter direction

For a fixed nonzero integer step and a rationally independent tuple of
bounded integral characters, the corresponding phase tuple is Haar-uniform.
A finite union bound therefore supplies directions for which the space of
very small bounded resonances has uniformly small rank.
-/

namespace Erdos721.HunterDiophantine

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal MeasureTheory Topology

open HunterTorus HunterPhase HunterDistributedCenters HunterCenters HunterLattice

/-- The centered alphabet contains every integer in `[-H,H]`. -/
lemma exists_frequencyCodeValue {H : ℕ} {z : ℤ} (hz : |z| ≤ H) :
    ∃ a : Fin (2 * H + 1), (a : ℤ) - H = z := by
  have hzlower : -(H : ℤ) ≤ z := (abs_le.mp hz).1
  have hzupper : z ≤ (H : ℤ) := (abs_le.mp hz).2
  let n : ℕ := Int.toNat (z + H)
  have hn : (n : ℤ) = z + H := by
    exact Int.toNat_of_nonneg (by omega)
  have hnlt : n < 2 * H + 1 := by
    omega
  refine ⟨⟨n, hnlt⟩, ?_⟩
  change (n : ℤ) - H = z
  omega

/-- Encode a bounded integral vector in the centered finite alphabet. -/
noncomputable def encodeFrequency {D H : ℕ} (ξ : Fin D → ℤ)
    (hξ : ∀ i, |ξ i| ≤ H) : FrequencyCode D H :=
  fun i ↦ Classical.choose (exists_frequencyCodeValue (hξ i))

@[simp] lemma decodeFrequency_encodeFrequency {D H : ℕ}
    (ξ : Fin D → ℤ) (hξ : ∀ i, |ξ i| ≤ H) :
    decodeFrequency (encodeFrequency ξ hξ) = ξ := by
  funext i
  exact Classical.choose_spec (exists_frequencyCodeValue (hξ i))

/-- Code of the zero frequency. -/
def zeroFrequencyCode (D H : ℕ) : FrequencyCode D H :=
  fun _ ↦ ⟨H, by omega⟩

@[simp] lemma decodeFrequency_zeroFrequencyCode (D H : ℕ) :
    decodeFrequency (zeroFrequencyCode D H) = 0 := by
  funext i
  simp [decodeFrequency, zeroFrequencyCode]

/-- Multiplication by a positive natural number is onto a finite-dimensional
unit torus. -/
lemma surjective_nsmul_torus {D d : ℕ} (hd : 0 < d) :
    Surjective (fun x : Torus D ↦ d • x) := by
  intro y
  let x : Torus D := fun i ↦
    (((centeredCoord (y i) / d : ℝ)) : AddCircle (1 : ℝ))
  refine ⟨x, ?_⟩
  funext i
  rw [← AddCircle.coe_equivIco (p := (1 : ℝ))
    (a := -(1 / 2 : ℝ)) (y := y i)]
  change d • (((centeredCoord (y i) / d : ℝ)) : AddCircle (1 : ℝ)) =
    ((centeredCoord (y i) : ℝ) : AddCircle (1 : ℝ))
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  field_simp

/-- The phase tuple after multiplication by a positive integer step. -/
def steppedPhaseHom {D R : ℕ} (d : ℕ)
    (ξ : Fin R → FrequencyCode D H) : Torus D →+ Torus R where
  toFun θ := d • phaseHom (fun j ↦ decodeFrequency (ξ j)) θ
  map_zero' := by simp
  map_add' x y := by simp

@[simp] lemma steppedPhaseHom_apply {D H R : ℕ} (d : ℕ)
    (ξ : Fin R → FrequencyCode D H) (θ : Torus D) :
    steppedPhaseHom d ξ θ =
      phaseHom (fun j ↦ decodeFrequency (ξ j)) (d • θ) := by
  exact (map_nsmul (phaseHom (fun j ↦ decodeFrequency (ξ j))) d θ).symm

lemma continuous_steppedPhaseHom {D H R : ℕ} (d : ℕ)
    (ξ : Fin R → FrequencyCode D H) :
    Continuous (steppedPhaseHom d ξ) := by
  change Continuous (fun θ : Torus D ↦
    d • phaseHom (fun j ↦ decodeFrequency (ξ j)) θ)
  exact (continuous_phaseHom _).nsmul d

lemma surjective_steppedPhaseHom {D H R : ℕ} {d : ℕ} (hd : 0 < d)
    (ξ : Fin R → FrequencyCode D H)
    (hξ : LinearIndependent ℚ
      (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row) :
    Surjective (steppedPhaseHom d ξ) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_nsmul_torus (D := R) hd y
  obtain ⟨θ, hθ⟩ := phaseHom_surjective_of_linearIndependent
    (fun j ↦ decodeFrequency (ξ j)) hξ z
  refine ⟨θ, ?_⟩
  simp only [steppedPhaseHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hθ]
  exact hz

/-- For one positive step and one independent frequency tuple, the event that
all phases are at most `epsilon` has its exact product-box volume. -/
lemma volume_steppedPhaseBox {D H R : ℕ} {d : ℕ} (hd : 0 < d)
    (ξ : Fin R → FrequencyCode D H)
    (hξ : LinearIndependent ℚ
      (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : 2 * epsilon ≤ 1) :
    volume (steppedPhaseHom d ξ ⁻¹' centeredBox R epsilon) =
      ENNReal.ofReal (2 * epsilon) ^ R := by
  have hmp : MeasurePreserving (steppedPhaseHom d ξ) :=
    measurePreserving_of_continuous_surjective
      (steppedPhaseHom d ξ) (continuous_steppedPhaseHom d ξ)
      (surjective_steppedPhaseHom hd ξ hξ)
  rw [hmp.measure_preimage
    (centeredBox_compact R epsilon).measurableSet.nullMeasurableSet]
  exact volume_centeredBox hepsilon0 hepsilon

/-- A tuple witnesses failure of the desired resonance-rank bound when it is
rationally independent and all its stepped phases lie in the small box. -/
def resonanceTupleEvent {D H R : ℕ} (d : ℕ) (epsilon : ℝ)
    (ξ : Fin R → FrequencyCode D H) : Set (Torus D) :=
  {θ | LinearIndependent ℚ
      (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row ∧
    steppedPhaseHom d ξ θ ∈ centeredBox R epsilon}

lemma measurableSet_resonanceTupleEvent {D H R : ℕ}
    (d : ℕ) (epsilon : ℝ) (ξ : Fin R → FrequencyCode D H) :
    MeasurableSet (resonanceTupleEvent d epsilon ξ) := by
  classical
  by_cases hξ : LinearIndependent ℚ
      (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row
  · exact (continuous_steppedPhaseHom d ξ).measurable
      (centeredBox_compact R epsilon).measurableSet |>.congr
        (by ext θ; simp [resonanceTupleEvent, hξ])
  · simpa [resonanceTupleEvent, hξ] using (MeasurableSet.empty :
      MeasurableSet (∅ : Set (Torus D)))

lemma volume_resonanceTupleEvent_le {D H R : ℕ} {d : ℕ} (hd : 0 < d)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : 2 * epsilon ≤ 1)
    (ξ : Fin R → FrequencyCode D H) :
    volume (resonanceTupleEvent d epsilon ξ) ≤
      ENNReal.ofReal (2 * epsilon) ^ R := by
  classical
  by_cases hξ : LinearIndependent ℚ
      (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row
  · rw [show resonanceTupleEvent d epsilon ξ =
        steppedPhaseHom d ξ ⁻¹' centeredBox R epsilon by
          ext θ; simp [resonanceTupleEvent, hξ],
      volume_steppedPhaseBox hd ξ hξ hepsilon0 hepsilon]
  · simp [resonanceTupleEvent, hξ]

/-- Union of all independent small-phase tuples for the positive steps
`1,...,N`. -/
def someHighRankResonanceEvent (D H R N : ℕ) (epsilon : ℝ) :
    Set (Torus D) :=
  ⋃ d : Fin N, ⋃ ξ : Fin R → FrequencyCode D H,
    resonanceTupleEvent (d + 1) epsilon ξ

lemma volume_someHighRankResonanceEvent_le
    {D H R N : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon : 2 * epsilon ≤ 1) :
    volume (someHighRankResonanceEvent D H R N epsilon) ≤
      (N * ((2 * H + 1) ^ D) ^ R : ℕ) *
        ENNReal.ofReal (2 * epsilon) ^ R := by
  classical
  rw [someHighRankResonanceEvent]
  calc
    volume (⋃ d : Fin N, ⋃ ξ : Fin R → FrequencyCode D H,
        resonanceTupleEvent (d + 1) epsilon ξ) ≤
        ∑ d : Fin N, ∑ ξ : Fin R → FrequencyCode D H,
          volume (resonanceTupleEvent (d + 1) epsilon ξ) := by
      calc
        _ ≤ ∑ d : Fin N, volume (⋃ ξ : Fin R → FrequencyCode D H,
              resonanceTupleEvent (d + 1) epsilon ξ) :=
          measure_iUnion_fintype_le _ _
        _ ≤ ∑ d : Fin N, ∑ ξ : Fin R → FrequencyCode D H,
              volume (resonanceTupleEvent (d + 1) epsilon ξ) := by
          apply Finset.sum_le_sum
          intro d _hd
          exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _d : Fin N, ∑ _ξ : Fin R → FrequencyCode D H,
        ENNReal.ofReal (2 * epsilon) ^ R := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro ξ _hξ
      exact volume_resonanceTupleEvent_le (Nat.succ_pos d) hepsilon0 hepsilon ξ
    _ = (N * ((2 * H + 1) ^ D) ^ R : ℕ) *
        ENNReal.ofReal (2 * epsilon) ^ R := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fun]
      push_cast
      ring

/-- The pointwise formulation of low resonance rank consumed by the orbit
lemma. -/
def LowResonanceRank {D H R : ℕ} (N : ℕ) (epsilon : ℝ)
    (θ : Torus D) : Prop :=
  ∀ d : Fin N, ∀ ξ : Fin R → FrequencyCode D H,
    LinearIndependent ℚ
        (rationalMatrix (fun j ↦ decodeFrequency (ξ j))).row →
      steppedPhaseHom (d + 1) ξ θ ∉ centeredBox R epsilon

/-- Bounded frequency codes whose character is small at `alpha`. -/
def resonantCodes {D H : ℕ} (epsilon : ℝ) (alpha : Torus D) :
    Set (FrequencyCode D H) :=
  {a | ‖integerDot (decodeFrequency a) alpha‖ ≤ epsilon}

/-- Rational space generated by all bounded small characters. -/
def resonanceSubspace {D H : ℕ} (epsilon : ℝ) (alpha : Torus D) :
    Submodule ℚ (Fin D → ℚ) :=
  Submodule.span ℚ
    ((fun a ↦ castIntVector (decodeFrequency a)) ''
      resonantCodes (H := H) epsilon alpha)

lemma castIntVector_mem_resonanceSubspace {D H : ℕ}
    {epsilon : ℝ} {alpha : Torus D} {a : FrequencyCode D H}
    (ha : a ∈ resonantCodes epsilon alpha) :
    castIntVector (decodeFrequency a) ∈
      resonanceSubspace (H := H) epsilon alpha := by
  exact Submodule.subset_span ⟨a, ha, rfl⟩

/-- The union-bound condition rules out `R` independent resonant
frequencies, hence the whole resonance space has dimension below `R`. -/
lemma finrank_resonanceSubspace_lt {D H R N : ℕ} {epsilon : ℝ}
    {θ : Torus D} (hθ : LowResonanceRank (H := H) (R := R) N epsilon θ)
    (d : Fin N) :
    Module.finrank ℚ
        (resonanceSubspace (H := H) epsilon ((d.val + 1) • θ)) < R := by
  classical
  let alpha : Torus D := (d.val + 1) • θ
  let S : Set (Fin D → ℚ) :=
    (fun a ↦ castIntVector (decodeFrequency a)) ''
      resonantCodes (H := H) epsilon alpha
  let m := Module.finrank ℚ (Submodule.span ℚ S)
  by_contra hlt
  have hR : R ≤ m := by
    have hR' := Nat.le_of_not_gt hlt
    change R ≤ m at hR'
    exact hR'
  obtain ⟨f, hfmem, _hfspan, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  let j : Fin R ↪ Fin m :=
    ⟨fun i ↦ ⟨i, lt_of_lt_of_le i.isLt hR⟩,
      fun a b h ↦ by
        have hab : a.val = b.val := by
          simpa only [Fin.mk.injEq] using h
        apply Fin.ext
        exact hab⟩
  have hfj : ∀ i : Fin R, f (j i) ∈ S := fun i ↦ hfmem (j i)
  choose ξ hξres hξcast using fun i : Fin R ↦ hfj i
  have hrows : (rationalMatrix
      (fun i ↦ decodeFrequency (ξ i))).row =
      fun i ↦ f (j i) := by
    funext i k
    exact congrFun (hξcast i) k
  have hξind : LinearIndependent ℚ
      (rationalMatrix (fun i ↦ decodeFrequency (ξ i))).row := by
    rw [hrows]
    exact hfind.comp _ j.injective
  have hbox : steppedPhaseHom (d.val + 1) ξ θ ∈ centeredBox R epsilon := by
    intro i _hi
    rw [steppedPhaseHom_apply]
    simp only [phaseHom_apply]
    simpa [Metric.mem_closedBall, dist_eq_norm, alpha, resonantCodes] using hξres i
  exact hθ d ξ hξind hbox

/-- Any resonance space of rank below `R` is one of the coded spaces used in
the finite center-selection argument.  A basis chosen from the resonant
codes is padded by zero frequencies. -/
lemma exists_codedSubspace_eq_resonanceSubspace {D H R : ℕ}
    {epsilon : ℝ} {alpha : Torus D}
    (hrank : Module.finrank ℚ
      (resonanceSubspace (H := H) epsilon alpha) < R) :
    ∃ ξ : Fin R → FrequencyCode D H,
      codedSubspace ξ = resonanceSubspace (H := H) epsilon alpha := by
  classical
  let S : Set (Fin D → ℚ) :=
    (fun a ↦ castIntVector (decodeFrequency a)) ''
      resonantCodes (H := H) epsilon alpha
  let m := Module.finrank ℚ (Submodule.span ℚ S)
  have hmR : m < R := by
    change Module.finrank ℚ (Submodule.span ℚ S) < R at hrank
    change m < R
    exact hrank
  obtain ⟨f, hfmem, hfspan, _hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  choose a hares hacast using hfmem
  let ξ : Fin R → FrequencyCode D H := fun j ↦
    if hj : j.val < m then a ⟨j.val, hj⟩ else zeroFrequencyCode D H
  refine ⟨ξ, ?_⟩
  change Submodule.span ℚ
      (Set.range fun i ↦ castIntVector (decodeFrequency (ξ i))) =
    Submodule.span ℚ S
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨j, rfl⟩ := hv
    change castIntVector (decodeFrequency (ξ j)) ∈
      Submodule.span ℚ S
    by_cases hj : j.val < m
    · have hξ : ξ j = a ⟨j.val, hj⟩ := by simp [ξ, hj]
      rw [hξ]
      exact Submodule.subset_span
        ⟨a ⟨j.val, hj⟩, hares ⟨j.val, hj⟩, rfl⟩
    · rw [show ξ j = zeroFrequencyCode D H by simp [ξ, hj],
        decodeFrequency_zeroFrequencyCode]
      convert (Submodule.span ℚ S).zero_mem
      ext i
      simp [castIntVector]
  · rw [← hfspan]
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    let j : Fin R := ⟨i.val, lt_trans i.isLt hmR⟩
    have hj : j.val < m := i.isLt
    have hξ : ξ j = a i := by
      simp only [ξ, dif_pos hj]
      congr
    rw [← hacast i, ← hξ]
    exact Submodule.subset_span ⟨j, rfl⟩

lemma lowResonanceRank_of_notMem {D H R N : ℕ} {epsilon : ℝ}
    {θ : Torus D}
    (hθ : θ ∉ someHighRankResonanceEvent D H R N epsilon) :
    LowResonanceRank (H := H) (R := R) N epsilon θ := by
  classical
  intro d ξ hξ hbox
  apply hθ
  simp only [someHighRankResonanceEvent, mem_iUnion]
  exact ⟨d, ξ, hξ, hbox⟩

/-! ### Excluding exceptionally small positive multiples -/

/-- Multiplication by `d` as an additive torus endomorphism. -/
def nsmulTorusHom (D d : ℕ) : Torus D →+ Torus D where
  toFun θ := d • θ
  map_zero' := by simp
  map_add' x y := by simp

lemma continuous_nsmulTorusHom (D d : ℕ) :
    Continuous (nsmulTorusHom D d) := by
  change Continuous (fun θ : Torus D ↦ d • θ)
  fun_prop

lemma measurePreserving_nsmulTorusHom {D d : ℕ} (hd : 0 < d) :
    MeasurePreserving (nsmulTorusHom D d) :=
  measurePreserving_of_continuous_surjective (nsmulTorusHom D d)
    (continuous_nsmulTorusHom D d) (surjective_nsmul_torus hd)

/-- Some positive multiple among `1,...,N` lies in a small coordinate box. -/
def someSmallMultipleEvent (D N : ℕ) (r : ℝ) : Set (Torus D) :=
  ⋃ d : Fin N, nsmulTorusHom D (d + 1) ⁻¹' centeredBox D r

lemma volume_someSmallMultipleEvent_le {D N : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1) :
    volume (someSmallMultipleEvent D N r) ≤
      N * ENNReal.ofReal (2 * r) ^ D := by
  rw [someSmallMultipleEvent]
  calc
    volume (⋃ d : Fin N,
        nsmulTorusHom D (d + 1) ⁻¹' centeredBox D r) ≤
        ∑ d : Fin N,
          volume (nsmulTorusHom D (d + 1) ⁻¹' centeredBox D r) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ _d : Fin N, ENNReal.ofReal (2 * r) ^ D := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [(measurePreserving_nsmulTorusHom (Nat.succ_pos d)).measure_preimage
        (centeredBox_compact D r).measurableSet.nullMeasurableSet,
        volume_centeredBox hr0 hr]
    _ = N * ENNReal.ofReal (2 * r) ^ D := by simp

/-- Uniform exclusion of small positive multiples. -/
def NoSmallMultiple {D : ℕ} (N : ℕ) (r : ℝ) (θ : Torus D) : Prop :=
  ∀ d : Fin N, nsmulTorusHom D (d + 1) θ ∉ centeredBox D r

lemma noSmallMultiple_of_notMem {D N : ℕ} {r : ℝ} {θ : Torus D}
    (hθ : θ ∉ someSmallMultipleEvent D N r) :
    NoSmallMultiple N r θ := by
  intro d hd
  exact hθ (mem_iUnion_of_mem d hd)

/-- The two Haar union bounds choose a direction which simultaneously has
low bounded-resonance rank and no exceptionally small positive multiple. -/
theorem exists_goodDirection {D H R Nrank Nsmall : ℕ} {epsilon r : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon : 2 * epsilon ≤ 1)
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (hsmall :
      (Nrank * ((2 * H + 1) ^ D) ^ R : ℕ) *
          ENNReal.ofReal (2 * epsilon) ^ R +
        Nsmall * ENNReal.ofReal (2 * r) ^ D < 1) :
    ∃ θ : Torus D,
      LowResonanceRank (H := H) (R := R) Nrank epsilon θ ∧
        NoSmallMultiple Nsmall r θ := by
  let high := someHighRankResonanceEvent D H R Nrank epsilon
  let small := someSmallMultipleEvent D Nsmall r
  have hhigh : volume high ≤
      (Nrank * ((2 * H + 1) ^ D) ^ R : ℕ) *
        ENNReal.ofReal (2 * epsilon) ^ R :=
    volume_someHighRankResonanceEvent_le hepsilon0 hepsilon
  have hsmall' : volume small ≤
      Nsmall * ENNReal.ofReal (2 * r) ^ D :=
    volume_someSmallMultipleEvent_le hr0 hr
  have hbad : volume (high ∪ small) < 1 :=
    (measure_union_le high small |>.trans (add_le_add hhigh hsmall')).trans_lt hsmall
  have hproper : high ∪ small ≠ Set.univ := by
    intro heq
    rw [heq, volume_univ] at hbad
    exact (lt_irrefl 1) hbad
  obtain ⟨θ, hθ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  refine ⟨θ, lowResonanceRank_of_notMem ?_,
    noSmallMultiple_of_notMem ?_⟩
  · exact fun h ↦ hθ (Or.inl h)
  · exact fun h ↦ hθ (Or.inr h)

end Erdos721.HunterDiophantine
