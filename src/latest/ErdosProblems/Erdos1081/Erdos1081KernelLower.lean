import ErdosProblems.Erdos1081.Erdos1081Uniform
import ErdosProblems.Erdos1081.Erdos1081Mixing

namespace Erdos1081

open Filter Finset Set

noncomputable section

/-- Logarithmic mass of the unramified allowed primes. -/
noncomputable def specialRegularAllowedPrimeLog (p Q : ℕ) : ℝ :=
  ∑ q ∈ specialRegularAllowedPrimesFinite p Q, Real.log q

theorem squareUnitPrimeTail_subset_regularAllowed
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    squareUnitPrimeTail p N ⊆ specialRegularAllowedPrimesFinite p N := by
  classical
  intro q hq
  have hallowed := squareUnitPrimeTail_subset_allowed (p := p) (N := N) hp4 hq
  have hqdata := Finset.mem_filter.mp hallowed
  have hqprime := Nat.prime_of_mem_primesBelow hqdata.1
  have hqN : q ≤ N := by
    have := (Nat.mem_primesBelow.mp hqdata.1).1
    omega
  rw [squareUnitPrimeTail, Finset.mem_biUnion] at hq
  rcases hq with ⟨u, hu, hqu⟩
  have hinterval := Finset.mem_filter.mp hqu
  have hqgt2 : 2 < q := by
    simpa using (Finset.mem_Ioc.mp hinterval.1).1
  have hqmod := hinterval.2.2
  have hqp : q ≠ p := by
    intro heq
    subst q
    have huval0 : (u.1 : ZMod p).val = 0 := by simpa using hqmod.symm
    exact u.ne_zero ((ZMod.val_eq_zero _).mp huval0)
  rw [mem_specialRegularAllowedPrimesFinite]
  exact ⟨hqprime, hqN, by omega, hqp, hqdata.2⟩

theorem squareUnitPrimeTail_log_le_specialRegularAllowedPrimeLog
    {p N : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    (∑ q ∈ squareUnitPrimeTail p N, Real.log q) ≤
      specialRegularAllowedPrimeLog p N := by
  unfold specialRegularAllowedPrimeLog
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact squareUnitPrimeTail_subset_regularAllowed hp4
  · intro q hq hnot
    exact Real.log_nonneg (by exact_mod_cast
      (mem_specialRegularAllowedPrimesFinite.mp hq).1.one_le)

theorem eventually_specialRegularAllowedPrimeLog_lower
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∀ᶠ Q : ℕ in atTop,
      (1 / 8 : ℝ) * (Q : ℝ) ≤ specialRegularAllowedPrimeLog p Q := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let C : ℝ := squareUnitThetaSum p 2
  have hC : ∀ᶠ Q : ℕ in atTop, 8 * C ≤ (Q : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (8 * C))
  filter_upwards [eventually_squareUnitThetaSum_lower hp2, hC,
      eventually_ge_atTop 2] with Q htheta hCQ hQ2
  have htail := squareUnitThetaSum_sub_eq_tail_sum (p := p) hQ2
  calc
    (1 / 8 : ℝ) * (Q : ℝ) ≤ squareUnitThetaSum p Q - C := by
      dsimp [C] at hCQ ⊢
      linarith
    _ = ∑ q ∈ squareUnitPrimeTail p Q, Real.log q := htail
    _ ≤ specialRegularAllowedPrimeLog p Q :=
      squareUnitPrimeTail_log_le_specialRegularAllowedPrimeLog hp4

/-- The regular squarefree Euler products retain a uniform amount of
reciprocal mass below their natural cutoff. -/
theorem eventually_boundedSubsetEulerMass_regular_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ M : ℕ in atTop,
      regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
          Real.sqrt (Real.log (M : ℝ)) ≤
        boundedSubsetEulerMass
          (specialRegularAllowedPrimesFinite p M.sqrt) M := by
  have hEuler := eventually_squarefreeEulerMass_regular_lower hp4
  have hEulerSqrt := tendsto_nat_sqrt_atTop1081.eventually hEuler
  filter_upwards [hEulerSqrt,
      eventually_primeLogReciprocalMass_allowed_sqrt_le p,
      eventually_ge_atTop 16] with M hEulerM hmomentFull hM
  let P := specialRegularAllowedPrimesFinite p M.sqrt
  have hsqrt3 : 3 ≤ M.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_specialRegularAllowedPrimesFinite.mp hq).1
  have hmoment : primeLogReciprocalMass P ≤
      (3 / 4 : ℝ) * Real.log (M : ℝ) :=
    (primeLogReciprocalMass_regular_le p M.sqrt).trans hmomentFull
  have hretained := boundedSubsetEulerMass_lower_of_log_moment
    P M (3 / 4 : ℝ) hprime (by omega) (by norm_num) (by norm_num) hmoment
  have hsqrtCompare := half_sqrt_log_nat_le_sqrt_log_sqrt hM
  have hcpos := regularSquarefreeEulerLowerConstant_pos
  calc
    regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
          Real.sqrt (Real.log (M : ℝ)) ≤
        (1 / 4 : ℝ) *
          (regularSquarefreeEulerLowerConstant / (p : ℝ) *
            Real.sqrt (Real.log (M.sqrt : ℝ))) := by
      have hpR : (0 : ℝ) < p := by
        exact_mod_cast (Fact.out : p.Prime).pos
      have hmul := mul_le_mul_of_nonneg_left hsqrtCompare
        (div_nonneg hcpos.le hpR.le)
      have hmul4 := mul_le_mul_of_nonneg_left hmul
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      calc
        regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
            Real.sqrt (Real.log (M : ℝ)) =
          (1 / 4 : ℝ) *
            (regularSquarefreeEulerLowerConstant / (p : ℝ) *
              ((1 / 2 : ℝ) * Real.sqrt (Real.log (M : ℝ)))) := by
                field_simp [hpR.ne']
                <;> ring
        _ ≤ (1 / 4 : ℝ) *
            (regularSquarefreeEulerLowerConstant / (p : ℝ) *
              Real.sqrt (Real.log (M.sqrt : ℝ))) := hmul4
    _ ≤ (1 / 4 : ℝ) * squarefreeEulerMass P := by
      exact mul_le_mul_of_nonneg_left hEulerM (by norm_num)
    _ ≤ boundedSubsetEulerMass P M := by
      norm_num at hretained ⊢
      exact hretained

noncomputable def specialRegularKernelReciprocalSum (p M : ℕ) : ℝ :=
  ∑ m ∈ specialRegularSquarefreeKernels p M, (m : ℝ)⁻¹

theorem product_regular_allowed_mem_regularKernel
    {p Q M : ℕ} [Fact p.Prime] {S : Finset ℕ}
    (hS : S ⊆ specialRegularAllowedPrimesFinite p Q)
    (hprodM : ∏ q ∈ S, q ≤ M) :
    ∏ q ∈ S, q ∈ specialRegularSquarefreeKernels p M := by
  classical
  let n := ∏ q ∈ S, q
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact (mem_specialRegularAllowedPrimesFinite.mp (hS hq)).1
  have hnpos : 0 < n := by
    dsimp [n]
    exact Finset.prod_pos fun q hq ↦ (hprime q hq).pos
  have hsq : Squarefree n := by
    dsimp [n]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro q hq r hr hqr
      change IsRelPrime q r
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprime q hq) (hprime r hr)).mpr hqr
    · intro q hq
      exact (hprime q hq).squarefree
  have hsupport : ∀ l : ℕ, l.Prime →
      IsQuadraticObstruction (p ^ 3) l → ¬ l ∣ n := by
    intro l hl hobs hldiv
    dsimp [n] at hldiv
    obtain ⟨q, hqS, hlq⟩ :=
      (Prime.dvd_finsetProd_iff hl.prime (fun q : ℕ ↦ q)).mp hldiv
    have hqdata := mem_specialRegularAllowedPrimesFinite.mp (hS hqS)
    have heq : l = q :=
      (Nat.prime_dvd_prime_iff_eq hl hqdata.1).mp hlq
    exact hqdata.2.2.2.2 (heq ▸ hobs)
  have hcop : Nat.Coprime n (2 * p) := by
    dsimp [n]
    apply Nat.Coprime.prod_left
    intro q hq
    have hqdata := mem_specialRegularAllowedPrimesFinite.mp (hS hq)
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [hqdata.1.coprime_iff_not_dvd]
      intro hq2
      have := (Nat.prime_dvd_prime_iff_eq hqdata.1 (by decide : Nat.Prime 2)).mp hq2
      exact hqdata.2.2.1 this
    · rw [hqdata.1.coprime_iff_not_dvd]
      intro hqp
      have := (Nat.prime_dvd_prime_iff_eq hqdata.1
        (Fact.out : p.Prime)).mp hqp
      exact hqdata.2.2.2.1 this
  rw [mem_specialRegularSquarefreeKernels]
  exact ⟨Finset.mem_Icc.mpr ⟨hnpos, hprodM⟩, ⟨hsq, hsupport⟩, hcop⟩

theorem boundedSubsetEulerMass_le_regularKernelReciprocal
    (p Q M : ℕ) [Fact p.Prime] :
    boundedSubsetEulerMass (specialRegularAllowedPrimesFinite p Q) M ≤
      specialRegularKernelReciprocalSum p M := by
  classical
  let P := specialRegularAllowedPrimesFinite p Q
  let good : Finset (Finset ℕ) :=
    P.powerset.filter (fun S ↦ ∏ q ∈ S, q ≤ M)
  let prodMap : Finset ℕ → ℕ := fun S ↦ ∏ q ∈ S, q
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_specialRegularAllowedPrimesFinite.mp hq).1
  have hgoodSub : ∀ S ∈ good, S ⊆ P := by
    intro S hS
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hinj : Set.InjOn prodMap good := by
    intro A hA B hB
    exact prod_injOn_prime_subsets1081 hprime (hgoodSub A hA)
      (hgoodSub B hB)
  have himageSub : good.image prodMap ⊆
      specialRegularSquarefreeKernels p M := by
    intro n hn
    obtain ⟨S, hSgood, rfl⟩ := Finset.mem_image.mp hn
    exact product_regular_allowed_mem_regularKernel
      (hgoodSub S hSgood) (Finset.mem_filter.mp hSgood).2
  calc
    boundedSubsetEulerMass (specialRegularAllowedPrimesFinite p Q) M =
        ∑ S ∈ good, ((prodMap S : ℕ) : ℝ)⁻¹ := by
      dsimp [good, P, prodMap, boundedSubsetEulerMass]
      apply Finset.sum_congr rfl
      intro S hS
      exact subsetReciprocalWeight_eq_inv_prod S
    _ = ∑ n ∈ good.image prodMap, (n : ℝ)⁻¹ := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ n ∈ specialRegularSquarefreeKernels p M, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himageSub
      intro n hn hnot
      positivity
    _ = specialRegularKernelReciprocalSum p M := rfl

theorem sum_log_primeFactors_eq_log_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    ∑ q ∈ n.primeFactors, Real.log q = Real.log (n : ℝ) := by
  rw [PrimePowerConvolution448.log_eq_sum_primeFactors]
  apply Finset.sum_congr rfl
  intro q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqdvd := Nat.dvd_of_mem_primeFactors hq
  rw [Nat.factorization_eq_one_of_squarefree hn hqprime hqdvd]
  simp

noncomputable def specialFreshRegularAllowedPrimeLog
    (p m Q : ℕ) : ℝ :=
  ∑ q ∈ (specialRegularAllowedPrimesFinite p Q).filter
    (fun q ↦ ¬ q ∣ m), Real.log q

theorem specialRegularAllowedPrimeLog_sub_log_le_fresh
    {p m Q : ℕ} (hm : Squarefree m) :
    specialRegularAllowedPrimeLog p Q - Real.log (m : ℝ) ≤
      specialFreshRegularAllowedPrimeLog p m Q := by
  classical
  let P := specialRegularAllowedPrimesFinite p Q
  let fresh := P.filter (fun q ↦ ¬ q ∣ m)
  let old := P.filter (fun q ↦ q ∣ m)
  have hsplit : (∑ q ∈ fresh, Real.log q) +
      ∑ q ∈ old, Real.log q = ∑ q ∈ P, Real.log q := by
    dsimp [fresh, old]
    simpa [add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := P) (p := fun q ↦ ¬ q ∣ m) (f := fun q ↦ Real.log q))
  have holdSub : old ⊆ m.primeFactors := by
    intro q hq
    have hqdata := Finset.mem_filter.mp hq
    have hqprime := (mem_specialRegularAllowedPrimesFinite.mp hqdata.1).1
    exact Nat.mem_primeFactors.mpr ⟨hqprime, hqdata.2, hm.ne_zero⟩
  have hold : (∑ q ∈ old, Real.log q) ≤ Real.log (m : ℝ) := by
    calc
      (∑ q ∈ old, Real.log q) ≤
          ∑ q ∈ m.primeFactors, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg holdSub
        intro q hq hnot
        exact Real.log_nonneg (by exact_mod_cast
          (Nat.prime_of_mem_primeFactors hq).one_le)
      _ = Real.log (m : ℝ) := sum_log_primeFactors_eq_log_of_squarefree hm
  dsimp [specialRegularAllowedPrimeLog,
    specialFreshRegularAllowedPrimeLog, P, fresh, old] at hsplit ⊢
  linarith

theorem regularKernel_mul_fresh_prime_mem
    {p M Q N m q : ℕ} [Fact p.Prime]
    (hm : m ∈ specialRegularSquarefreeKernels p M)
    (hq : q ∈ specialRegularAllowedPrimesFinite p Q)
    (hqFresh : ¬ q ∣ m) (hmqN : m * q ≤ N) :
    m * q ∈ specialRegularSquarefreeKernels p N := by
  rw [mem_specialRegularSquarefreeKernels] at hm ⊢
  rcases hm with ⟨hmI, ⟨hmsq, hmsupport⟩, hmcop⟩
  have hqdata := mem_specialRegularAllowedPrimesFinite.mp hq
  have hmqpos : 0 < m * q := Nat.mul_pos
    (Finset.mem_Icc.mp hmI).1 hqdata.1.pos
  have hmqSq : Squarefree (m * q) := by
    rw [squarefree_mul_iff, ← Nat.coprime_iff_isRelPrime]
    exact ⟨(hqdata.1.coprime_iff_not_dvd.mpr hqFresh).symm,
      hmsq, hqdata.1.squarefree⟩
  have hmqSupport : ∀ l : ℕ, l.Prime →
      IsQuadraticObstruction (p ^ 3) l → ¬ l ∣ m * q := by
    intro l hl hobs hldiv
    rcases (Prime.dvd_mul hl.prime).mp hldiv with hlm | hlq
    · exact hmsupport l hl hobs hlm
    · have heq : l = q :=
        (Nat.prime_dvd_prime_iff_eq hl hqdata.1).mp hlq
      exact hqdata.2.2.2.2 (heq ▸ hobs)
  have hqcop : Nat.Coprime q (2 * p) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [hqdata.1.coprime_iff_not_dvd]
      intro hq2
      exact hqdata.2.2.1
        ((Nat.prime_dvd_prime_iff_eq hqdata.1
          (by decide : Nat.Prime 2)).mp hq2)
    · rw [hqdata.1.coprime_iff_not_dvd]
      intro hqp
      exact hqdata.2.2.2.1
        ((Nat.prime_dvd_prime_iff_eq hqdata.1
          (Fact.out : p.Prime)).mp hqp)
  exact ⟨Finset.mem_Icc.mpr ⟨hmqpos, hmqN⟩,
    ⟨hmqSq, hmqSupport⟩,
    (Nat.coprime_mul_iff_left.mpr ⟨hmcop, hqcop⟩)⟩

private abbrev FreshKernelSourceIndex := Sigma fun _ : ℕ ↦ ℕ
private abbrev FreshKernelTargetIndex := Sigma fun _ : ℕ ↦ ℕ

private noncomputable def freshKernelSourceSet
    (p N : ℕ) : Finset FreshKernelSourceIndex :=
  (specialRegularSquarefreeKernels p N.sqrt).sigma fun m ↦
    (specialRegularAllowedPrimesFinite p (N / m)).filter
      (fun q ↦ ¬ q ∣ m)

private noncomputable def freshKernelTargetSet
    (p N : ℕ) : Finset FreshKernelTargetIndex :=
  (specialRegularSquarefreeKernels p N).sigma fun n ↦ n.primeFactors

private def freshKernelSourceToTarget
    (z : FreshKernelSourceIndex) : FreshKernelTargetIndex :=
  ⟨z.1 * z.2, z.2⟩

private theorem freshKernelSourceToTarget_injOn (p N : ℕ) :
    Set.InjOn freshKernelSourceToTarget (freshKernelSourceSet p N) := by
  intro z hz w hw hzw
  rcases z with ⟨m, q⟩
  rcases w with ⟨m', q'⟩
  have hq : q = q' := congrArg Sigma.snd hzw
  subst q'
  have hprod : m * q = m' * q := congrArg Sigma.fst hzw
  have hqpos : 0 < q := by
    change ⟨m, q⟩ ∈ freshKernelSourceSet p N at hz
    simp only [freshKernelSourceSet, Finset.mem_sigma] at hz
    exact (mem_specialRegularAllowedPrimesFinite.mp
      (Finset.mem_filter.mp hz.2).1).1.pos
  have hm : m = m' := Nat.mul_right_cancel hqpos hprod
  subst m'
  rfl

private theorem freshKernelSourceToTarget_mem
    {p N : ℕ} [Fact p.Prime] {z : FreshKernelSourceIndex}
    (hz : z ∈ freshKernelSourceSet p N) :
    freshKernelSourceToTarget z ∈ freshKernelTargetSet p N := by
  rcases z with ⟨m, q⟩
  rw [freshKernelSourceSet, Finset.mem_sigma] at hz
  rcases hz with ⟨hm, hq⟩
  have hqdata := Finset.mem_filter.mp hq
  rw [freshKernelTargetSet, Finset.mem_sigma]
  have hmqN : m * q ≤ N := by
    have hmpos : 0 < m := (Finset.mem_Icc.mp
      (mem_specialRegularSquarefreeKernels.mp hm).1).1
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hmpos).mp
        (mem_specialRegularAllowedPrimesFinite.mp hqdata.1).2.1
  refine ⟨regularKernel_mul_fresh_prime_mem hm hqdata.1 hqdata.2 hmqN, ?_⟩
  exact Nat.mem_primeFactors.mpr
    ⟨(mem_specialRegularAllowedPrimesFinite.mp hqdata.1).1,
      dvd_mul_left q m, Nat.mul_ne_zero
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp
            (mem_specialRegularSquarefreeKernels.mp hm).1).1))
        (mem_specialRegularAllowedPrimesFinite.mp hqdata.1).1.ne_zero⟩

theorem freshRegularPrimeLog_sum_le_regularKernelLogSum
    (p N : ℕ) [Fact p.Prime] :
    (∑ m ∈ specialRegularSquarefreeKernels p N.sqrt,
        specialFreshRegularAllowedPrimeLog p m (N / m)) ≤
      ∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n := by
  classical
  let e : {z // z ∈ freshKernelSourceSet p N} ↪ FreshKernelTargetIndex :=
    ⟨fun z ↦ freshKernelSourceToTarget z.1,
      fun z w hzw ↦ Subtype.ext
        (freshKernelSourceToTarget_injOn p N z.2 w.2 hzw)⟩
  let U : Finset FreshKernelTargetIndex :=
    (freshKernelSourceSet p N).attach.map e
  have hsource :
      (∑ m ∈ specialRegularSquarefreeKernels p N.sqrt,
          specialFreshRegularAllowedPrimeLog p m (N / m)) =
        ∑ z ∈ freshKernelSourceSet p N, Real.log z.2 := by
    unfold freshKernelSourceSet specialFreshRegularAllowedPrimeLog
    rw [Finset.sum_sigma]
  have himage :
      (∑ z ∈ freshKernelSourceSet p N, Real.log z.2) =
        ∑ w ∈ U, Real.log w.2 := by
    rw [← Finset.sum_attach]
    change (∑ z ∈ (freshKernelSourceSet p N).attach, Real.log z.1.2) =
      ∑ w ∈ (freshKernelSourceSet p N).attach.map e, Real.log w.2
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro z hz
    rfl
  have hUT : U ⊆ freshKernelTargetSet p N := by
    intro w hw
    rw [Finset.mem_map] at hw
    rcases hw with ⟨z, hz, rfl⟩
    exact freshKernelSourceToTarget_mem z.2
  have htarget :
      (∑ w ∈ freshKernelTargetSet p N, Real.log w.2) =
        ∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n := by
    unfold freshKernelTargetSet
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    exact sum_log_primeFactors_eq_log_of_squarefree
      (mem_specialRegularSquarefreeKernels.mp hn).2.1.1
  rw [hsource, himage, ← htarget]
  apply Finset.sum_le_sum_of_subset_of_nonneg hUT
  intro w hw hnot
  exact Real.log_nonneg (by exact_mod_cast
    (Nat.prime_of_mem_primeFactors (Finset.mem_sigma.mp hw).2).one_le)

theorem eventually_log_nat_le_sixteenth :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) / 16 := by
  have hlogReal := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hlogNat, eventually_ge_atTop 1] with n hlog hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  simpa [id, Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hn0,
    div_eq_mul_inv, mul_comm] using hlog

theorem eventually_freshRegularAllowedPrimeLog_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ specialRegularSquarefreeKernels p N.sqrt,
      (1 / 32 : ℝ) * ((N : ℝ) / (m : ℝ)) ≤
        specialFreshRegularAllowedPrimeLog p m (N / m) := by
  have hprimeLog := eventually_specialRegularAllowedPrimeLog_lower
    (Fact.out : p.Prime) hp4
  rw [eventually_atTop] at hprimeLog
  obtain ⟨Q₀, hprimeLog⟩ := hprimeLog
  have hsmall := tendsto_nat_sqrt_atTop1081.eventually
    eventually_log_nat_le_sixteenth
  have hQ₀ := tendsto_nat_sqrt_atTop1081.eventually
    (eventually_ge_atTop Q₀)
  filter_upwards [hsmall, hQ₀, eventually_ge_atTop 1]
      with N hsmallN hsqrtQ₀ hN
  intro m hm
  have hmdata := mem_specialRegularSquarefreeKernels.mp hm
  have hmI := Finset.mem_Icc.mp hmdata.1
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmI.1
  have hsqrtN : N.sqrt ≤ N := Nat.sqrt_le_self N
  have hmN : m ≤ N := hmI.2.trans hsqrtN
  have hqge : N.sqrt ≤ N / m := by
    apply (Nat.le_div_iff_mul_le hmpos).2
    calc
      N.sqrt * m ≤ N.sqrt * N.sqrt := Nat.mul_le_mul_left _ hmI.2
      _ ≤ N := Nat.sqrt_le N
  have hmass := hprimeLog (N / m) (hsqrtQ₀.trans hqge)
  have hlogm : Real.log (m : ℝ) ≤ Real.log (N.sqrt : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hmI.2)
  have hlogq : Real.log (m : ℝ) ≤ ((N / m : ℕ) : ℝ) / 16 := by
    calc
      Real.log (m : ℝ) ≤ Real.log (N.sqrt : ℝ) := hlogm
      _ ≤ (N.sqrt : ℝ) / 16 := hsmallN
      _ ≤ ((N / m : ℕ) : ℝ) / 16 := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hqge) (by norm_num)
  have hfreshSub := specialRegularAllowedPrimeLog_sub_log_le_fresh
    (p := p) (Q := N / m) hmdata.2.1.1
  have hfresh : ((N / m : ℕ) : ℝ) / 16 ≤
      specialFreshRegularAllowedPrimeLog p m (N / m) := by
    linarith
  have hdiv := half_real_div_le_nat_div hmpos hmN
  calc
    (1 / 32 : ℝ) * ((N : ℝ) / (m : ℝ)) =
        (1 / 16 : ℝ) * ((N : ℝ) / (2 * (m : ℝ))) := by ring
    _ ≤ (1 / 16 : ℝ) * ((N / m : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = ((N / m : ℕ) : ℝ) / 16 := by ring
    _ ≤ specialFreshRegularAllowedPrimeLog p m (N / m) := hfresh

theorem eventually_regularKernelLogSum_lower_by_reciprocal
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 32 : ℝ) * (N : ℝ) *
          specialRegularKernelReciprocalSum p N.sqrt ≤
        ∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n := by
  have hfresh := eventually_freshRegularAllowedPrimeLog_lower hp4
  filter_upwards [hfresh] with N hfreshN
  calc
    (1 / 32 : ℝ) * (N : ℝ) *
          specialRegularKernelReciprocalSum p N.sqrt =
        ∑ m ∈ specialRegularSquarefreeKernels p N.sqrt,
          (1 / 32 : ℝ) * ((N : ℝ) / (m : ℝ)) := by
      unfold specialRegularKernelReciprocalSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [div_eq_mul_inv]
      ring
    _ ≤ ∑ m ∈ specialRegularSquarefreeKernels p N.sqrt,
        specialFreshRegularAllowedPrimeLog p m (N / m) :=
      Finset.sum_le_sum hfreshN
    _ ≤ ∑ n ∈ specialRegularSquarefreeKernels p N,
        Real.log n := freshRegularPrimeLog_sum_le_regularKernelLogSum p N

theorem regularKernelLogSum_le_log_mul_card
    (p : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n) ≤
      Real.log (N : ℝ) *
        ((specialRegularSquarefreeKernels p N).card : ℝ) := by
  calc
    (∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n) ≤
        ∑ _n ∈ specialRegularSquarefreeKernels p N,
          Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnI := Finset.mem_Icc.mp
        (mem_specialRegularSquarefreeKernels.mp hn).1
      exact Real.log_le_log (by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one hnI.1)) (by exact_mod_cast hnI.2)
    _ = Real.log (N : ℝ) *
        ((specialRegularSquarefreeKernels p N).card : ℝ) := by
      simp [mul_comm]

noncomputable def regularKernelLowerConstant : ℝ :=
  regularSquarefreeEulerLowerConstant / 1024

theorem regularKernelLowerConstant_pos :
    0 < regularKernelLowerConstant := by
  unfold regularKernelLowerConstant
  exact div_pos regularSquarefreeEulerLowerConstant_pos (by norm_num)

theorem eventually_specialRegularSquarefreeKernels_uniform_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∀ᶠ N : ℕ in atTop,
      2 * regularKernelLowerConstant * (p : ℝ)⁻¹ * landauScale N ≤
        ((specialRegularSquarefreeKernels p N).card : ℝ) := by
  have hrecBase := eventually_boundedSubsetEulerMass_regular_lower hp4
  have hrecSqrt := tendsto_nat_sqrt_atTop1081.eventually hrecBase
  have hlogLower := eventually_regularKernelLogSum_lower_by_reciprocal hp4
  filter_upwards [hrecSqrt, hlogLower, eventually_ge_atTop 16]
      with N hrec hlogLowerN hN
  have hbridge := boundedSubsetEulerMass_le_regularKernelReciprocal
    p N.sqrt.sqrt N.sqrt
  have hrec' :
      regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
          Real.sqrt (Real.log (N.sqrt : ℝ)) ≤
        specialRegularKernelReciprocalSum p N.sqrt := hrec.trans hbridge
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hcoefNonneg : (0 : ℝ) ≤ 1 / 32 * (N : ℝ) := by positivity
  have hweighted := mul_le_mul_of_nonneg_left hrec' hcoefNonneg
  have hlogsqrt := half_sqrt_log_nat_le_sqrt_log_sqrt hN
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hcR : (0 : ℝ) < regularSquarefreeEulerLowerConstant :=
    regularSquarefreeEulerLowerConstant_pos
  have hsqrtlog : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast
      (show 1 < N by omega)))
  have hmain :
      regularSquarefreeEulerLowerConstant / (512 * (p : ℝ)) *
          (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        ∑ n ∈ specialRegularSquarefreeKernels p N, Real.log n := by
    calc
      regularSquarefreeEulerLowerConstant / (512 * (p : ℝ)) *
          (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) =
        (1 / 32 : ℝ) * (N : ℝ) *
          (regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
            ((1 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ)))) := by
          field_simp [hpR.ne']
          <;> ring
      _ ≤ (1 / 32 : ℝ) * (N : ℝ) *
          (regularSquarefreeEulerLowerConstant / (8 * (p : ℝ)) *
            Real.sqrt (Real.log (N.sqrt : ℝ))) := by
        gcongr
      _ ≤ (1 / 32 : ℝ) * (N : ℝ) *
          specialRegularKernelReciprocalSum p N.sqrt := by
        exact hweighted
      _ ≤ ∑ n ∈ specialRegularSquarefreeKernels p N,
          Real.log n := hlogLowerN
  have hupper := regularKernelLogSum_le_log_mul_card p (show 1 ≤ N by omega)
  have hcombined := hmain.trans hupper
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsquare : Real.sqrt (Real.log (N : ℝ)) ^ 2 =
      Real.log (N : ℝ) := Real.sq_sqrt hlogpos.le
  unfold regularKernelLowerConstant landauScale
  rw [show 2 * (regularSquarefreeEulerLowerConstant / 1024) *
      (p : ℝ)⁻¹ * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) =
      (regularSquarefreeEulerLowerConstant / (512 * (p : ℝ)) *
        (N : ℝ)) / Real.sqrt (Real.log (N : ℝ)) by
        field_simp [hpR.ne'] <;> ring]
  apply (div_le_iff₀ hsqrtlog).2
  apply le_of_mul_le_mul_right ?_ hsqrtlog
  calc
    (regularSquarefreeEulerLowerConstant / (512 * (p : ℝ)) *
        (N : ℝ)) *
        Real.sqrt (Real.log (N : ℝ)) =
      regularSquarefreeEulerLowerConstant / (512 * (p : ℝ)) *
        (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by ring
    _ ≤ Real.log (N : ℝ) *
        ((specialRegularSquarefreeKernels p N).card : ℝ) := hcombined
    _ = Real.sqrt (Real.log (N : ℝ)) ^ 2 *
        ((specialRegularSquarefreeKernels p N).card : ℝ) :=
      congrArg (fun x : ℝ ↦ x *
        ((specialRegularSquarefreeKernels p N).card : ℝ)) hsquare.symm
    _ = (((specialRegularSquarefreeKernels p N).card : ℝ) *
        Real.sqrt (Real.log (N : ℝ))) *
        Real.sqrt (Real.log (N : ℝ)) := by ring

theorem specialRegularSquarefreeKernels_subset
    (p N : ℕ) :
    specialRegularSquarefreeKernels p N ⊆ specialSquarefreeKernels p N := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

theorem specialSquarefreeKernelLower : SpecialSquarefreeKernelLower := by
  refine ⟨regularKernelLowerConstant, regularKernelLowerConstant_pos, ?_⟩
  intro p hp hp4
  let : Fact p.Prime := ⟨hp⟩
  filter_upwards [eventually_specialRegularSquarefreeKernels_uniform_lower hp4]
      with N hN
  exact hN.trans (by
    exact_mod_cast Finset.card_le_card
      (specialRegularSquarefreeKernels_subset p N))

theorem eventually_specialFormCount_uniform_lower_of_squareSubgroup_top
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (hsqtop :
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤) :
    ∀ᶠ N : ℕ in atTop,
      regularKernelLowerConstant * (p : ℝ)⁻¹ * landauScale N ≤
        (specialFormCount p N : ℝ) := by
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have heta : 0 < regularKernelLowerConstant * (p : ℝ)⁻¹ :=
    mul_pos regularKernelLowerConstant_pos (inv_pos.mpr hpR)
  have hmiss := eventually_specialRegularKernelExceptions_negligible
    hp4 hsqtop heta
  have hlower := eventually_specialRegularSquarefreeKernels_uniform_lower hp4
  filter_upwards [hmiss, hlower] with N hmissN hlowerN
  have hcardNat :
      (specialRegularSquarefreeKernels p N).card ≤
        (specialRegularKernelExceptions p N).card +
          (specialFormValues p N).card := by
    exact Finset.card_le_card_sdiff_add_card
  have hcard :
      ((specialRegularSquarefreeKernels p N).card : ℝ) ≤
        ((specialRegularKernelExceptions p N).card : ℝ) +
          (specialFormCount p N : ℝ) := by
    exact_mod_cast hcardNat
  linarith

theorem specialBernaysLower_of_squareSubgroup_top
    (hsqtop : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤) :
    SpecialBernaysLower := by
  refine ⟨regularKernelLowerConstant, regularKernelLowerConstant_pos, ?_⟩
  intro p hp hp4
  let : Fact p.Prime := ⟨hp⟩
  exact eventually_specialFormCount_uniform_lower_of_squareSubgroup_top
    hp4 (hsqtop p hp4)

end

end Erdos1081
