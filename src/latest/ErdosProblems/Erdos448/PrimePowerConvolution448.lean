import Mathlib

open scoped BigOperators
open Finset

namespace PrimePowerConvolution448

noncomputable def logPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n * Real.log (n : ℝ)

noncomputable def primePowerMass (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ (Q + 1).primesBelow,
    ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
      h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)

lemma log_eq_sum_primeFactors (n : ℕ) :
    Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  simp only [Finsupp.sum, Nat.support_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_pow, Real.log_pow]

lemma weighted_log_eq_sum_primeFactors
    (h : ℕ → ℝ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    {n : ℕ} (hn : n ≠ 0) :
    h n * Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by
  rw [log_eq_sum_primeFactors, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hcop : (ordProj[p] n).Coprime (ordCompl[p] n) :=
    (Nat.coprime_ordCompl hp hn).pow_left _
  have hdecomp : ordProj[p] n * ordCompl[p] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  calc
    h n * Real.log ((ordProj[p] n : ℕ) : ℝ) =
        h (ordProj[p] n * ordCompl[p] n) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hdecomp]
    _ = (h (ordProj[p] n) * h (ordCompl[p] n)) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hmul hcop]
    _ = h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by ring

private abbrev SourceIndex := Sigma fun _ : ℕ => ℕ
private abbrev TargetIndex := Sigma fun _ : ℕ => Sigma fun _ : ℕ => ℕ

private def sourceSet (N : ℕ) : Finset SourceIndex :=
  (Finset.Icc 1 N).sigma fun n => n.primeFactors

private def targetSet (N : ℕ) : Finset TargetIndex :=
  (Finset.Icc 1 N).sigma fun m =>
    ((N / m + 1).primesBelow).sigma fun p =>
      Finset.Icc 1 (Nat.log p (N / m))

private noncomputable def sourceWeight (h : ℕ → ℝ) (a : SourceIndex) : ℝ :=
  h (ordCompl[a.2] a.1) *
    (h (ordProj[a.2] a.1) * Real.log ((ordProj[a.2] a.1 : ℕ) : ℝ))

private noncomputable def targetWeight (h : ℕ → ℝ) (a : TargetIndex) : ℝ :=
  h a.1 * (h (a.2.1 ^ a.2.2) * Real.log ((a.2.1 ^ a.2.2 : ℕ) : ℝ))

private def sourceToTarget (a : SourceIndex) : TargetIndex :=
  ⟨ordCompl[a.2] a.1, ⟨a.2, a.1.factorization a.2⟩⟩

lemma sourceToTarget_injective_on (N : ℕ) :
    Set.InjOn sourceToTarget ↑(sourceSet N) := by
  intro a ha b hb hab
  rcases a with ⟨n, p⟩
  rcases b with ⟨n', p'⟩
  have hn : n = n' := by
    calc
      n = (sourceToTarget ⟨n, p⟩).2.1 ^ (sourceToTarget ⟨n, p⟩).2.2 *
          (sourceToTarget ⟨n, p⟩).1 :=
        (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      _ = (sourceToTarget ⟨n', p'⟩).2.1 ^ (sourceToTarget ⟨n', p'⟩).2.2 *
          (sourceToTarget ⟨n', p'⟩).1 := congrArg
            (fun z : TargetIndex => z.2.1 ^ z.2.2 * z.1) hab
      _ = n' := Nat.ordProj_mul_ordCompl_eq_self n' p'
  have hp : p = p' := congrArg (fun z : TargetIndex => z.2.1) hab
  subst n'
  subst p'
  rfl

lemma sourceToTarget_mem_targetSet {N : ℕ} {a : SourceIndex}
    (ha : a ∈ sourceSet N) : sourceToTarget a ∈ targetSet N := by
  rcases a with ⟨n, p⟩
  simp only [sourceSet, Finset.mem_sigma] at ha
  rcases ha with ⟨hnIcc, hp_mem⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn_one, hnN⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem).2.1
  have hnu : 0 < n.factorization p :=
    hp.factorization_pos_of_dvd hn0 hp_dvd
  have hmpos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hn0
  have hmN : ordCompl[p] n ≤ N :=
    (Nat.div_le_self n (ordProj[p] n)).trans hnN
  have hpow_mul : p ^ n.factorization p * ordCompl[p] n ≤ N := by
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact hnN
  have hpowQ : p ^ n.factorization p ≤ N / ordCompl[p] n := by
    rw [Nat.le_div_iff_mul_le hmpos]
    simpa [Nat.mul_comm] using hpow_mul
  have hpQ : p < N / ordCompl[p] n + 1 :=
    Nat.lt_succ_of_le ((Nat.le_self_pow hnu.ne' p).trans hpowQ)
  have hp_below : p ∈ (N / ordCompl[p] n + 1).primesBelow := by
    simpa [Nat.mem_primesBelow] using ⟨Nat.le_of_lt_succ hpQ, hp⟩
  have hnu_log : n.factorization p ≤ Nat.log p (N / ordCompl[p] n) :=
    Nat.le_log_of_pow_le hp.one_lt hpowQ
  simp only [sourceToTarget, targetSet, Finset.mem_sigma]
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmpos.ne', hmN⟩,
    hp_below, Finset.mem_Icc.mpr ⟨hnu, hnu_log⟩⟩

lemma sourceWeight_eq_targetWeight_sourceToTarget
    (h : ℕ → ℝ) (a : SourceIndex) :
    sourceWeight h a = targetWeight h (sourceToTarget a) := by
  rfl

lemma targetWeight_nonneg
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n)
    {N : ℕ} {a : TargetIndex} (ha : a ∈ targetSet N) :
    0 ≤ targetWeight h a := by
  rcases a with ⟨m, ⟨p, nu⟩⟩
  simp only [targetSet, Finset.mem_sigma] at ha
  rcases ha with ⟨hm, hp, hnu⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hnu_one : 1 ≤ nu := (Finset.mem_Icc.mp hnu).1
  have hpow_one : 1 ≤ p ^ nu := by
    exact one_le_pow₀ hp_prime.one_lt.le
  unfold targetWeight
  exact mul_nonneg (hnonneg m)
    (mul_nonneg (hnonneg (p ^ nu)) (Real.log_nonneg (by exact_mod_cast hpow_one)))

theorem logPartialSum_le_primePowerMass_convolution
    (h : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    (N : ℕ) :
    logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * primePowerMass h (N / m) := by
  let e : {a // a ∈ sourceSet N} ↪ TargetIndex :=
    ⟨fun a => sourceToTarget a.1,
      fun a b hab => Subtype.ext (sourceToTarget_injective_on N a.2 b.2 hab)⟩
  let U : Finset TargetIndex := (sourceSet N).attach.map e
  have hsource : logPartialSum h N = ∑ a ∈ sourceSet N, sourceWeight h a := by
    unfold logPartialSum sourceSet
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    exact weighted_log_eq_sum_primeFactors h hmul
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
  have himage :
      (∑ a ∈ sourceSet N, sourceWeight h a) =
        ∑ b ∈ U, targetWeight h b := by
    rw [← Finset.sum_attach]
    change (∑ a ∈ (sourceSet N).attach, sourceWeight h a.1) =
      ∑ b ∈ (sourceSet N).attach.map e, targetWeight h b
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun a ha =>
      sourceWeight_eq_targetWeight_sourceToTarget h a.1
  have hUT : U ⊆ targetSet N := by
    intro b hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨a, ha, rfl⟩
    exact sourceToTarget_mem_targetSet a.2
  have hsubsum :
      (∑ b ∈ U, targetWeight h b) ≤
        ∑ b ∈ targetSet N, targetWeight h b := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hUT fun b hbT hbU =>
      targetWeight_nonneg h hnonneg hbT
  have htarget :
      (∑ b ∈ targetSet N, targetWeight h b) =
        ∑ m ∈ Finset.Icc 1 N, h m * primePowerMass h (N / m) := by
    unfold targetSet primePowerMass targetWeight
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only
    rw [Finset.mul_sum]
  rw [hsource, himage]
  exact hsubsum.trans_eq htarget

#print axioms logPartialSum_le_primePowerMass_convolution

end PrimePowerConvolution448
