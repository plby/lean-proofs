import ErdosProblems.Erdos448.PrimePowerConvolution448

/-!
# Reindexing logarithmic prime-power convolutions

The finite bijection `(n,p,k) ↦ (n/p^k,p,k)` is adapted from the counting
infrastructure of Erdős 1081 and stated here for an arbitrary weight.
-/

namespace Bernays

private abbrev LocalLogSourceIndex :=
  Sigma fun _n : ℕ => Sigma fun _l : ℕ => ℕ

private abbrev LocalLogTargetIndex :=
  Sigma fun _m : ℕ => Sigma fun _l : ℕ => ℕ

/-- Indices `(n,l,k)` with `n ≤ N`, `l | n`, and
`1 ≤ k ≤ v_l(n)`. -/
private def localLogSourceSet (N : ℕ) : Finset LocalLogSourceIndex :=
  (Finset.Icc 1 N).sigma fun n =>
    n.primeFactors.sigma fun l => Finset.Icc 1 (n.factorization l)

/-- Convolution indices `(m,l,k)` with `m l^k ≤ N`. -/
private def localLogTargetSet (N : ℕ) : Finset LocalLogTargetIndex :=
  (Finset.Icc 1 N).sigma fun m =>
    ((N / m + 1).primesBelow).sigma fun l =>
      Finset.Icc 1 (Nat.log l (N / m))

/-- Removing `l^k` from a source integer produces its convolution index. -/
private def localLogSourceToTarget (z : LocalLogSourceIndex) :
    LocalLogTargetIndex :=
  ⟨z.1 / z.2.1 ^ z.2.2, z.2⟩

private theorem localLogSource_pow_dvd {N : ℕ} {z : LocalLogSourceIndex}
    (hz : z ∈ localLogSourceSet N) : z.2.1 ^ z.2.2 ∣ z.1 := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hz.2.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hz.1).1)
  exact (hl.pow_dvd_iff_le_factorization hn0).2
    (Finset.mem_Icc.mp hz.2.2).2

private theorem localLogSource_reconstruct {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    (localLogSourceToTarget z).1 *
        (localLogSourceToTarget z).2.1 ^
          (localLogSourceToTarget z).2.2 = z.1 := by
  rcases z with ⟨n, l, k⟩
  exact Nat.div_mul_cancel (localLogSource_pow_dvd hz)

private theorem localLogSourceToTarget_injOn (N : ℕ) :
    Set.InjOn localLogSourceToTarget
      (localLogSourceSet N : Set LocalLogSourceIndex) := by
  intro z hz w hw heq
  have htail : z.2 = w.2 := congrArg Sigma.snd heq
  have hhead : z.1 = w.1 := by
    calc
      z.1 = (localLogSourceToTarget z).1 *
          (localLogSourceToTarget z).2.1 ^
            (localLogSourceToTarget z).2.2 :=
        (localLogSource_reconstruct hz).symm
      _ = (localLogSourceToTarget w).1 *
          (localLogSourceToTarget w).2.1 ^
            (localLogSourceToTarget w).2.2 := by rw [heq]
      _ = w.1 := localLogSource_reconstruct hw
  cases z
  cases w
  simp_all

private theorem localLogSourceToTarget_mem {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    localLogSourceToTarget z ∈ localLogTargetSet N := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  rcases hz with ⟨hnIcc, hlmem, hkIcc⟩
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hpowpos : 0 < l ^ k := pow_pos hl.pos k
  have hpowdvd : l ^ k ∣ n :=
    (hl.pow_dvd_iff_le_factorization hn0).2 (Finset.mem_Icc.mp hkIcc).2
  have hmpos : 0 < n / l ^ k :=
    Nat.div_pos (Nat.le_of_dvd hnpos hpowdvd) hpowpos
  have hmN : n / l ^ k ≤ N := (Nat.div_le_self n _).trans (Finset.mem_Icc.mp hnIcc).2
  have hmul : l ^ k * (n / l ^ k) ≤ N := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hpowdvd]
    exact (Finset.mem_Icc.mp hnIcc).2
  have hpowQ : l ^ k ≤ N / (n / l ^ k) := by
    rw [Nat.le_div_iff_mul_le hmpos]
    exact hmul
  have hlQ : l < N / (n / l ^ k) + 1 :=
    Nat.lt_succ_of_le ((Nat.le_self_pow hkpos.ne' l).trans hpowQ)
  have hklog : k ≤ Nat.log l (N / (n / l ^ k)) :=
    Nat.le_log_of_pow_le hl.one_lt hpowQ
  simp only [localLogSourceToTarget, localLogTargetSet, Finset.mem_sigma]
  exact ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩,
    Nat.mem_primesBelow.mpr ⟨hlQ, hl⟩,
    Finset.mem_Icc.mpr ⟨hkpos, hklog⟩⟩

private theorem localLogSourceToTarget_surjOn (N : ℕ) :
    ∀ w ∈ localLogTargetSet N,
      ∃ z ∈ localLogSourceSet N, localLogSourceToTarget z = w := by
  intro w hw
  rcases w with ⟨m, l, k⟩
  simp only [localLogTargetSet, Finset.mem_sigma] at hw
  rcases hw with ⟨hmIcc, hlmem, hkIcc⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmIcc).1
  have hl : l.Prime := Nat.prime_of_mem_primesBelow hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hQ0 : N / m ≠ 0 := by
    intro hQ
    have : k ≤ 0 := by simpa [hQ] using (Finset.mem_Icc.mp hkIcc).2
    omega
  have hpowQ : l ^ k ≤ N / m :=
    Nat.pow_le_of_le_log hQ0 (Finset.mem_Icc.mp hkIcc).2
  have hmulN : m * l ^ k ≤ N := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hpowQ
  have hnpos : 0 < m * l ^ k := Nat.mul_pos hmpos (pow_pos hl.pos k)
  have hl_dvd : l ∣ m * l ^ k := by
    exact dvd_mul_of_dvd_right (dvd_pow_self l hkpos.ne') m
  have hlpf : l ∈ (m * l ^ k).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, hl_dvd, hnpos.ne'⟩
  have hkfac : k ≤ (m * l ^ k).factorization l := by
    apply (hl.pow_dvd_iff_le_factorization hnpos.ne').1
    exact dvd_mul_left (l ^ k) m
  let z : LocalLogSourceIndex := ⟨m * l ^ k, l, k⟩
  have hz : z ∈ localLogSourceSet N := by
    simp only [z, localLogSourceSet, Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hnpos, hmulN⟩, hlpf,
      Finset.mem_Icc.mpr ⟨hkpos, hkfac⟩⟩
  refine ⟨z, hz, ?_⟩
  simp only [z, localLogSourceToTarget]
  congr 1
  exact Nat.mul_div_left m (pow_pos hl.pos k)


theorem primePower_divisor_sum (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors,
      ∑ k ∈ Finset.Icc 1 (n.factorization p), w (n / p ^ k) p k) =
    ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ (N / m + 1).primesBelow,
      ∑ k ∈ Finset.Icc 1 (Nat.log p (N / m)), w m p k := by
  have hsum :
      (∑ z ∈ localLogSourceSet N, w (z.1 / z.2.1 ^ z.2.2) z.2.1 z.2.2) =
        ∑ z ∈ localLogTargetSet N, w z.1 z.2.1 z.2.2 := by
    apply Finset.sum_bij (fun z _ => localLogSourceToTarget z)
    · intro z hz
      exact localLogSourceToTarget_mem hz
    · intro z hz z' hz' hzz'
      exact localLogSourceToTarget_injOn N hz hz' hzz'
    · intro b hb
      obtain ⟨a, ha, hab⟩ := localLogSourceToTarget_surjOn N b hb
      exact ⟨a, ha, hab⟩
    · intro z _
      rfl
  simpa only [localLogSourceSet, localLogTargetSet, Finset.sum_sigma] using hsum

end Bernays
