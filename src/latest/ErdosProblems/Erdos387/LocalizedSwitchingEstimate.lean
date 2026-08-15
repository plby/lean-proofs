/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RoughIntervalEstimate

/-!
# Localized reciprocal sum after divisor switching

For fixed `B`, the exact switching inequalities put the complementary
factor `b` in a multiplicative interval whose endpoints depend on the
product `D` of the other coordinates.  This file tensors the one-dimensional
short-interval estimate over those other coordinates.  It is the finite,
fixed-parameter counterpart of the dyadic localization in BNPZ §7.2.
-/

namespace Erdos387

open scoped BigOperators

open Finset Nat Real

namespace RoughHarmonic

/-- Cumulative rough reciprocal mass is monotone in its endpoint. -/
theorem roughReciprocalMass_mono {z T U : ℕ} (hTU : T ≤ U) :
    roughReciprocalMass z T ≤ roughReciprocalMass z U := by
  unfold roughReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    apply mem_roughPositiveUpTo_iff.mpr
    have hmData := mem_roughPositiveUpTo_iff.mp hm
    exact ⟨hmData.1, hmData.2.1.trans hTU, hmData.2.2⟩
  · intro m hmU hmT
    positivity

/-- Dividing the endpoints `D/(3g)` and `(2BD)/g` produces a uniformly
bounded multiplicative interval once `D ≥ 6g`. -/
theorem switchedInterval_ratio_le
    {B D g : ℕ} (hB : 0 < B) (hg : 0 < g) (hD : 6 * g ≤ D) :
    ((((2 * B * D) / g : ℕ) : ℝ) /
        ((D / (3 * g) : ℕ) : ℝ)) ≤ 12 * B := by
  let A := D / (3 * g)
  have hden : 0 < 3 * g := Nat.mul_pos (by norm_num) hg
  have hA2 : 2 ≤ A := by
    apply (Nat.le_div_iff_mul_le hden).2
    nlinarith
  have hDlt : D < (3 * g) * (A + 1) := by
    simpa [A] using Nat.lt_mul_div_succ D hden
  have hDlt' : D < 6 * g * A := by
    have hAone : A + 1 ≤ 2 * A := by omega
    calc
      D < (3 * g) * (A + 1) := hDlt
      _ ≤ (3 * g) * (2 * A) := Nat.mul_le_mul_left _ hAone
      _ = 6 * g * A := by ring
  have hnum : 2 * B * D ≤ g * (12 * B * A) := by
    have hmul := (Nat.mul_lt_mul_left
      (Nat.mul_pos (by omega : 0 < 2) hB)).2 hDlt'
    nlinarith
  have hquot : (2 * B * D) / g ≤ 12 * B * A :=
    Nat.div_le_of_le_mul hnum
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  apply (div_le_iff₀ hApos).2
  change ((((2 * B * D) / g : ℕ) : ℝ)) ≤
    (12 : ℝ) * B * (A : ℝ)
  exact_mod_cast hquot

end RoughHarmonic

namespace CoverBPZ

/-- Replace the distinguished coordinate by `1`, retaining all other
switched factors. -/
def switchedOtherVector
    {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X) : Fin S.k → ℕ :=
  fun j => if j = i then 1 else C.val.factor j

theorem prod_switchedOtherVector
    {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X) :
    ∏ j : Fin S.k, switchedOtherVector i C j = C.val.otherValue i := by
  classical
  unfold switchedOtherVector TupleCertificate.otherValue
  rw [← Finset.prod_erase (s := Finset.univ)
    (f := fun j : Fin S.k => if j = i then 1 else C.val.factor j)]
  · apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  · simp

/-- Certificates localized at one distinguished switched coordinate. -/
noncomputable def SwitchedLargeTupleCertificatesAt
    {B K : ℕ} (S : BPZSection6Input B K)
    (X z large : ℕ) (i : Fin S.k) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact (SwitchedLargeTupleCertificates S X z large).filter fun C =>
    C.val.factor i < C.val.otherValue i ∧
    (large + 1) * C.val.otherValue i ≤ X ∧
    C.val.otherValue i < 3 * S.g i * C.val.factor i ∧
    C.val.factor i * S.g i < 2 * B * C.val.otherValue i

theorem mem_switchedLargeTupleCertificatesAt_iff
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} :
    C ∈ SwitchedLargeTupleCertificatesAt S X z large i ↔
      C ∈ SwitchedLargeTupleCertificates S X z large ∧
      C.val.factor i < C.val.otherValue i ∧
      (large + 1) * C.val.otherValue i ≤ X ∧
      C.val.otherValue i < 3 * S.g i * C.val.factor i ∧
      C.val.factor i * S.g i < 2 * B * C.val.otherValue i := by
  classical
  simp [SwitchedLargeTupleCertificatesAt]

/-- The localized sets cover every switched certificate. -/
theorem exists_mem_switchedLargeTupleCertificatesAt
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large) :
    ∃ i : Fin S.k, C ∈ SwitchedLargeTupleCertificatesAt S X z large i := by
  classical
  obtain ⟨⟨i, hiLt, hiScale, hiLower, hiUpper⟩, _hrough⟩ :=
    mem_switchedLargeTupleCertificates_iff.mp hC
  exact ⟨i,
    mem_switchedLargeTupleCertificatesAt_iff.mpr
      ⟨hC, hiLt, hiScale, hiLower, hiUpper⟩⟩

/-- Full rough vectors whose product is nontrivial enough to support the
localized switched interval.  The distinguished coordinate will equal `1`
for encoded certificates, but allowing every rough value gives a convenient
Cartesian majorant. -/
noncomputable def localizedRoughOtherVectors (k z T : ℕ) :
    Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin k =>
    roughPositiveUpTo z T).filter fun f =>
      z ≤ ∏ j : Fin k, f j

/-- Dependent pairs `(other coordinates, b)` in the switched multiplicative
interval. -/
noncomputable def localizedRoughSwitchPairs
    (k B g z T : ℕ) : Finset (Sigma fun _ : Fin k → ℕ => ℕ) := by
  classical
  exact (localizedRoughOtherVectors k z T).sigma fun f =>
    RoughHarmonic.roughPositiveIoc z
      ((∏ j : Fin k, f j) / (3 * g))
      ((2 * B * (∏ j : Fin k, f j)) / g)

/-- Encode a switched certificate by the other-coordinate vector and the
distinguished complementary factor. -/
def localizedSwitchEncode
    {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X) :
    Sigma fun _ : Fin S.k → ℕ => ℕ :=
  ⟨switchedOtherVector i C, C.val.factor i⟩

theorem localizedSwitchEncode_injective
    {B K X : ℕ} {S : BPZSection6Input B K} (i : Fin S.k) :
    Function.Injective
      (localizedSwitchEncode (X := X) (S := S) i) := by
  intro C₁ C₂ h
  apply Subtype.ext
  apply Subtype.ext
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    exact congrArg (fun x : Sigma fun _ : Fin S.k → ℕ => ℕ => x.2) h
  · have hv := congrArg
        (fun x : Sigma fun _ : Fin S.k → ℕ => ℕ => x.1 j) h
    simpa [localizedSwitchEncode, switchedOtherVector, hji,
      TupleCertificate.factor] using hv

private theorem rough_le_of_pos_ne_one
    {z m : ℕ} (hm : 0 < m) (hrough : IsZRough z m) (hm1 : m ≠ 1) :
    z ≤ m := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hzp : z ≤ p := by
    by_contra hnot
    exact hrough p hp (Nat.lt_of_not_ge hnot) hpm
  exact hzp.trans (Nat.le_of_dvd hm hpm)

private theorem otherValue_rough_of_mem_at
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificatesAt S X z large i) :
    IsZRough z (C.val.otherValue i) := by
  intro p hp hpz hpD
  unfold TupleCertificate.otherValue at hpD
  obtain ⟨j, _hj, hpj⟩ :=
    (hp.prime.dvd_finsetProd_iff C.val.factor).mp hpD
  exact switchedCertificate_factor_rough
    (mem_switchedLargeTupleCertificatesAt_iff.mp hC).1 j p hp hpz hpj

/-- The localized encoding lands in the dependent rough-pair majorant. -/
theorem localizedSwitchEncode_mem_pairs
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hB : 0 < B)
    (hC : C ∈ SwitchedLargeTupleCertificatesAt S X z large i) :
    localizedSwitchEncode i C ∈ localizedRoughSwitchPairs S.k B (S.g i) z
      (2 * B * (X / (large + 1)) + 1) := by
  classical
  let T := 2 * B * (X / (large + 1)) + 1
  let f := switchedOtherVector i C
  let D := C.val.otherValue i
  have hAt := mem_switchedLargeTupleCertificatesAt_iff.mp hC
  have hbase := hAt.1
  have hiLt := hAt.2.1
  have hiScale := hAt.2.2.1
  have hiLower := hAt.2.2.2.1
  have hiUpper := hAt.2.2.2.2
  have hDPos : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun j _ => C.val.positive j
  have hD1 : D ≠ 1 := by
    have hbiPos := C.val.positive i
    omega
  have hDge : z ≤ D :=
    rough_le_of_pos_ne_one hDPos (otherValue_rough_of_mem_at hC) hD1
  have hfMem : f ∈ localizedRoughOtherVectors S.k z T := by
    rw [localizedRoughOtherVectors, Finset.mem_filter,
      Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · intro j
      apply mem_roughPositiveUpTo_iff.mpr
      by_cases hji : j = i
      · subst j
        refine ⟨by simp [f, switchedOtherVector], by simp [f, switchedOtherVector, T], ?_⟩
        have hone : IsZRough z 1 := by
          intro p hp hpz hpOne
          exact hp.ne_one (Nat.dvd_one.mp hpOne)
        simpa [f, switchedOtherVector] using hone
      · have hjLe := switchedCertificate_factor_le_div hbase j
        have hjT : C.val.factor j ≤ T := by
          apply hjLe.trans
          dsimp [T]
          calc
            X / (large + 1) = 1 * (X / (large + 1)) := by simp
            _ ≤ (2 * B) * (X / (large + 1)) :=
              Nat.mul_le_mul_right _ (by omega)
            _ ≤ 2 * B * (X / (large + 1)) + 1 := Nat.le_add_right _ _
        simpa [f, switchedOtherVector, hji] using
          (show 0 < C.val.factor j ∧ C.val.factor j ≤ T ∧
              IsZRough z (C.val.factor j) from
            ⟨C.val.positive j, hjT, switchedCertificate_factor_rough hbase j⟩)
    · rw [prod_switchedOtherVector]
      exact hDge
  have hdenPos : 0 < 3 * S.g i := Nat.mul_pos (by norm_num) (S.g_pos i)
  have hbLower : D / (3 * S.g i) < C.val.factor i := by
    apply (Nat.div_lt_iff_lt_mul hdenPos).2
    simpa [Nat.mul_comm] using hiLower
  have hbUpper : C.val.factor i ≤ (2 * B * D) / S.g i := by
    apply (Nat.le_div_iff_mul_le (S.g_pos i)).2
    exact hiUpper.le
  change Sigma.mk f (C.val.factor i) ∈
    localizedRoughSwitchPairs S.k B (S.g i) z T
  rw [localizedRoughSwitchPairs, Finset.mem_sigma]
  refine ⟨hfMem, ?_⟩
  rw [prod_switchedOtherVector]
  apply RoughHarmonic.mem_roughPositiveIoc.mpr
  exact ⟨hbLower, hbUpper, switchedCertificate_factor_rough hbase i⟩

/-- Reciprocal weight of one dependent switched pair. -/
noncomputable def localizedSwitchPairWeight
    {k : ℕ} (x : Sigma fun _ : Fin k → ℕ => ℕ) : ℝ :=
  (1 : ℝ) / ((∏ j : Fin k, x.1 j : ℕ) * x.2 : ℕ)

theorem localizedSwitchPairWeight_encode
    {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X) :
    localizedSwitchPairWeight (localizedSwitchEncode i C) =
      (1 : ℝ) / C.val.value := by
  unfold localizedSwitchPairWeight localizedSwitchEncode
  rw [prod_switchedOtherVector, ← C.val.factor_mul_otherValue i]
  push_cast
  ring

/-- At a fixed distinguished coordinate, certificate reciprocal mass is
bounded by the corresponding dependent rough-pair sum. -/
theorem switchedCertificateAt_reciprocalSum_le_pairs
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (i : Fin S.k) :
    (∑ C ∈ SwitchedLargeTupleCertificatesAt S X z large i,
        (1 : ℝ) / C.val.value) ≤
      ∑ x ∈ localizedRoughSwitchPairs S.k B (S.g i) z
          (2 * B * (X / (large + 1)) + 1),
        localizedSwitchPairWeight x := by
  classical
  let A := SwitchedLargeTupleCertificatesAt S X z large i
  let P := localizedRoughSwitchPairs S.k B (S.g i) z
    (2 * B * (X / (large + 1)) + 1)
  let enc := localizedSwitchEncode (X := X) (S := S) i
  have hinj : Function.Injective enc :=
    localizedSwitchEncode_injective (X := X) (S := S) i
  have himage : A.image enc ⊆ P := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨C, hCA, rfl⟩ := hx
    exact localizedSwitchEncode_mem_pairs hB hCA
  have hsumImage :
      (∑ C ∈ A, (1 : ℝ) / C.val.value) =
        ∑ x ∈ A.image enc, localizedSwitchPairWeight x := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro C hC
      exact (localizedSwitchPairWeight_encode i C).symm
    · intro C₁ h₁ C₂ h₂ h
      exact hinj h
  change (∑ C ∈ A, (1 : ℝ) / C.val.value) ≤
    ∑ x ∈ P, localizedSwitchPairWeight x
  rw [hsumImage]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage
    (by intro x hxP hxImage; unfold localizedSwitchPairWeight; positivity)

/-- The dependent rough-pair sum gains one full factor of `1 / log z`.
All other coordinates are absorbed into a cumulative rough harmonic tensor.
-/
theorem localizedRoughSwitchPairs_sum_le
    {C : ℝ} {N k B g z T : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hg : 0 < g)
    (hzg : 6 * g ≤ z) :
    (∑ x ∈ localizedRoughSwitchPairs k B g z T,
        localizedSwitchPairWeight x) ≤
      ((12 * B : ℝ) * C / Real.log z) *
        roughReciprocalMass z (2 * B * T ^ k + 1) *
          (roughReciprocalMass z T) ^ k := by
  classical
  let V := localizedRoughOtherVectors k z T
  let W := 2 * B * T ^ k + 1
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hvectorMass :
      (∑ f ∈ V, (1 : ℝ) / (∏ j : Fin k, f j : ℕ)) ≤
        (roughReciprocalMass z T) ^ k := by
    let R := roughPositiveUpTo z T
    let F := Fintype.piFinset (fun _ : Fin k => R)
    have hVF : V ⊆ F := by
      intro f hf
      have hfData := Finset.mem_filter.mp hf
      exact hfData.1
    calc
      (∑ f ∈ V, (1 : ℝ) / (∏ j : Fin k, f j : ℕ)) ≤
          ∑ f ∈ F, (1 : ℝ) / (∏ j : Fin k, f j : ℕ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hVF
          (by intro f hfF hfV; positivity)
      _ = ∑ f ∈ F, ∏ j : Fin k, ((1 : ℝ) / f j) := by
        apply Finset.sum_congr rfl
        intro f hf
        push_cast
        simp only [one_div, Finset.prod_inv_distrib]
      _ = (roughReciprocalMass z T) ^ k := by
        change (∑ f ∈ Fintype.piFinset (fun _ : Fin k => R),
            ∏ j : Fin k, (1 : ℝ) / f j) =
          (∑ m ∈ R, (1 : ℝ) / m) ^ k
        exact (Finset.sum_pow' R (fun m : ℕ => (1 : ℝ) / m) k).symm
  rw [localizedRoughSwitchPairs, Finset.sum_sigma]
  change (∑ f ∈ V, ∑ b ∈ RoughHarmonic.roughPositiveIoc z
      ((∏ j : Fin k, f j) / (3 * g))
      ((2 * B * (∏ j : Fin k, f j)) / g),
        localizedSwitchPairWeight ⟨f, b⟩) ≤ _
  let Q : ℝ := ((12 * B : ℝ) * C / Real.log z) *
    roughReciprocalMass z W
  have hper : ∀ f ∈ V,
      (∑ b ∈ RoughHarmonic.roughPositiveIoc z
          ((∏ j : Fin k, f j) / (3 * g))
          ((2 * B * (∏ j : Fin k, f j)) / g),
            localizedSwitchPairWeight ⟨f, b⟩) ≤
        ((1 : ℝ) / (∏ j : Fin k, f j : ℕ)) * Q := by
    intro f hf
    let D := ∏ j : Fin k, f j
    let A := D / (3 * g)
    let U := (2 * B * D) / g
    have hfData := Finset.mem_filter.mp hf
    have hDge : z ≤ D := hfData.2
    have hD6 : 6 * g ≤ D := hzg.trans hDge
    have hAone : 1 ≤ A := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by norm_num) hg)).2
      dsimp [A, D]
      nlinarith
    have hshort := RoughHarmonic.roughReciprocalIocMass_le_roughMass_div_log
      (U := U) hC hcheb hzN hz hAone
    have hratio : ((U : ℝ) / (A : ℝ)) ≤ 12 * B := by
      simpa [U, A, D] using RoughHarmonic.switchedInterval_ratio_le hB hg hD6
    have hcoef : C * ((U : ℝ) / A) / Real.log z ≤
        (12 * B : ℝ) * C / Real.log z := by
      apply (div_le_div_iff_of_pos_right hlogz).2
      calc
        C * ((U : ℝ) / A) ≤ C * (12 * B : ℝ) :=
          mul_le_mul_of_nonneg_left hratio hC.le
        _ = (12 * B : ℝ) * C := by ring
    have hfcoord : ∀ j : Fin k, f j ≤ T := by
      intro j
      have hj := (Fintype.mem_piFinset.mp hfData.1) j
      exact (mem_roughPositiveUpTo_iff.mp hj).2.1
    have hDle : D ≤ T ^ k := by
      dsimp [D]
      calc
        (∏ j : Fin k, f j) ≤ ∏ _j : Fin k, T := by
          exact Finset.prod_le_prod (fun j _ => Nat.zero_le (f j))
            (fun j _ => hfcoord j)
        _ = T ^ k := by simp
    have hUW : U / z ≤ W := by
      have hUle : U ≤ 2 * B * T ^ k := by
        calc
          U ≤ 2 * B * D := Nat.div_le_self _ _
          _ ≤ 2 * B * T ^ k := Nat.mul_le_mul_left _ hDle
      dsimp [W]
      exact (Nat.div_le_self U z).trans (hUle.trans (Nat.le_add_right _ _))
    have hmass := RoughHarmonic.roughReciprocalMass_mono (z := z) hUW
    have hshort' : RoughHarmonic.roughReciprocalIocMass z A U ≤ Q := by
      calc
        RoughHarmonic.roughReciprocalIocMass z A U ≤
            (C * ((U : ℝ) / A) / Real.log z) *
              roughReciprocalMass z (U / z) := by
          simpa [A, U] using hshort
        _ ≤ ((12 * B : ℝ) * C / Real.log z) *
              roughReciprocalMass z W := by
          exact mul_le_mul hcoef hmass
            (by unfold roughReciprocalMass; positivity)
            (by positivity)
        _ = Q := rfl
    have hinner :
        (∑ b ∈ RoughHarmonic.roughPositiveIoc z A U,
            localizedSwitchPairWeight ⟨f, b⟩) =
          ((1 : ℝ) / D) * RoughHarmonic.roughReciprocalIocMass z A U := by
      unfold RoughHarmonic.roughReciprocalIocMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      unfold localizedSwitchPairWeight
      dsimp [D]
      push_cast
      ring
    rw [show (∏ j : Fin k, f j) / (3 * g) = A from rfl,
      show (2 * B * (∏ j : Fin k, f j)) / g = U from rfl,
      hinner]
    exact mul_le_mul_of_nonneg_left hshort' (by positivity)
  calc
    (∑ f ∈ V, ∑ b ∈ RoughHarmonic.roughPositiveIoc z
        ((∏ j : Fin k, f j) / (3 * g))
        ((2 * B * (∏ j : Fin k, f j)) / g),
          localizedSwitchPairWeight ⟨f, b⟩) ≤
        ∑ f ∈ V, ((1 : ℝ) / (∏ j : Fin k, f j : ℕ)) * Q := by
      exact Finset.sum_le_sum hper
    _ = (∑ f ∈ V, (1 : ℝ) / (∏ j : Fin k, f j : ℕ)) * Q := by
      rw [Finset.sum_mul]
    _ ≤ (roughReciprocalMass z T) ^ k * Q :=
      mul_le_mul_of_nonneg_right hvectorMass (by
        unfold Q
        apply mul_nonneg
        · exact div_nonneg
            (mul_nonneg (by positivity) hC.le) hlogz.le
        · unfold roughReciprocalMass
          positivity)
    _ = ((12 * B : ℝ) * C / Real.log z) *
          roughReciprocalMass z (2 * B * T ^ k + 1) *
            (roughReciprocalMass z T) ^ k := by
      dsimp [Q, W]
      ring

private theorem sum_biUnion_le_sum_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ s.biUnion t, f b) ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := by
        exact Finset.sum_nonneg fun b hb => hf b
      have hunion := Finset.sum_union_inter
        (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      calc
        (∑ b ∈ t a ∪ s.biUnion t, f b) ≤
            (∑ b ∈ t a, f b) + ∑ b ∈ s.biUnion t, f b := by
          linarith
        _ ≤ (∑ b ∈ t a, f b) + ∑ a ∈ s, ∑ b ∈ t a, f b :=
          add_le_add_right ih _

/-- Union of all coordinate-localized switched certificate sets. -/
noncomputable def SwitchedLargeTupleCertificatesAtUnion
    {B K : ℕ} (S : BPZSection6Input B K) (X z large : ℕ) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact (Finset.univ : Finset (Fin S.k)).biUnion
    (SwitchedLargeTupleCertificatesAt S X z large)

theorem switchedLargeTupleCertificates_subset_atUnion
    {B K X z large : ℕ} (S : BPZSection6Input B K) :
    SwitchedLargeTupleCertificates S X z large ⊆
      SwitchedLargeTupleCertificatesAtUnion S X z large := by
  classical
  intro C hC
  obtain ⟨i, hi⟩ := exists_mem_switchedLargeTupleCertificatesAt S hC
  rw [SwitchedLargeTupleCertificatesAtUnion, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- The complete switched reciprocal sum with the short-interval saving.
The factor `k` is the harmless union bound over the distinguished coordinate.
-/
theorem switchedCertificate_reciprocalSum_le_localized
    {C : ℝ} {N B K X z large : ℕ} (S : BPZSection6Input B K)
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hzg : ∀ i : Fin S.k, 6 * S.g i ≤ z) :
    (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        (1 : ℝ) / C.val.value) ≤
      (S.k : ℝ) *
        (((12 * B : ℝ) * C / Real.log z) *
          roughReciprocalMass z
            (2 * B * (2 * B * (X / (large + 1)) + 1) ^ S.k + 1) *
          (roughReciprocalMass z
            (2 * B * (X / (large + 1)) + 1)) ^ S.k) := by
  classical
  let T := 2 * B * (X / (large + 1)) + 1
  let Q : ℝ := ((12 * B : ℝ) * C / Real.log z) *
    roughReciprocalMass z (2 * B * T ^ S.k + 1) *
      (roughReciprocalMass z T) ^ S.k
  have hbaseUnion :
      (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
          (1 : ℝ) / C.val.value) ≤
        ∑ C ∈ SwitchedLargeTupleCertificatesAtUnion S X z large,
          (1 : ℝ) / C.val.value := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (switchedLargeTupleCertificates_subset_atUnion S)
      (by intro C hCU hCbase; positivity)
  have hunionSum :
      (∑ C ∈ SwitchedLargeTupleCertificatesAtUnion S X z large,
          (1 : ℝ) / C.val.value) ≤
        ∑ i : Fin S.k,
          ∑ C ∈ SwitchedLargeTupleCertificatesAt S X z large i,
            (1 : ℝ) / C.val.value := by
    unfold SwitchedLargeTupleCertificatesAtUnion
    exact sum_biUnion_le_sum_sum Finset.univ
      (SwitchedLargeTupleCertificatesAt S X z large)
      (fun C => (1 : ℝ) / C.val.value) (by intro C; positivity)
  have hper : ∀ i : Fin S.k,
      (∑ C ∈ SwitchedLargeTupleCertificatesAt S X z large i,
          (1 : ℝ) / C.val.value) ≤ Q := by
    intro i
    apply (switchedCertificateAt_reciprocalSum_le_pairs S hB i).trans
    simpa [T, Q] using localizedRoughSwitchPairs_sum_le
      hC hcheb hzN hz hB (S.g_pos i) (hzg i)
  calc
    (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        (1 : ℝ) / C.val.value) ≤
        ∑ C ∈ SwitchedLargeTupleCertificatesAtUnion S X z large,
          (1 : ℝ) / C.val.value := hbaseUnion
    _ ≤ ∑ i : Fin S.k,
          ∑ C ∈ SwitchedLargeTupleCertificatesAt S X z large i,
            (1 : ℝ) / C.val.value := hunionSum
    _ ≤ ∑ _i : Fin S.k, Q := Finset.sum_le_sum fun i hi => hper i
    _ = (S.k : ℝ) * Q := by simp
    _ = (S.k : ℝ) *
        (((12 * B : ℝ) * C / Real.log z) *
          roughReciprocalMass z
            (2 * B * (2 * B * (X / (large + 1)) + 1) ^ S.k + 1) *
          (roughReciprocalMass z
            (2 * B * (X / (large + 1)) + 1)) ^ S.k) := by
      rfl

/-- Named right-hand side of the localized switched reciprocal estimate. -/
noncomputable def localizedSwitchedReciprocalEnvelope
    {B K : ℕ} (S : BPZSection6Input B K)
    (C : ℝ) (X z large : ℕ) : ℝ :=
  (S.k : ℝ) *
    (((12 * B : ℝ) * C / Real.log z) *
      roughReciprocalMass z
        (2 * B * (2 * B * (X / (large + 1)) + 1) ^ S.k + 1) *
      (roughReciprocalMass z
        (2 * B * (X / (large + 1)) + 1)) ^ S.k)

theorem switchedCertificate_reciprocalSum_le_localizedEnvelope
    {C : ℝ} {N B K X z large : ℕ} (S : BPZSection6Input B K)
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hzg : ∀ i : Fin S.k, 6 * S.g i ≤ z) :
    (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        (1 : ℝ) / C.val.value) ≤
      localizedSwitchedReciprocalEnvelope S C X z large := by
  simpa only [localizedSwitchedReciprocalEnvelope] using
    switchedCertificate_reciprocalSum_le_localized
      S hC hcheb hzN hz hB hzg

end CoverBPZ

end Erdos387
