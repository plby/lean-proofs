import ErdosProblems.Erdos1081.Erdos1081RingClass
import ErdosProblems.Erdos1081.Erdos1081Residues

namespace Erdos1081

open Filter Finset Set

noncomputable section

theorem tendsto_finsetSum_atTop_of_nonneg_of_exhaustive
    {ι : Type*} (E : ℕ → Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hmono : Monotone E)
    (hexhaust : ∀ F : Finset ι, ∃ N, F ⊆ E N)
    (hnot : ¬ Summable f) :
    Tendsto (fun N ↦ ∑ i ∈ E N, f i) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hlarge : ∃ F : Finset ι, b < ∑ i ∈ F, f i := by
    by_contra h
    push_neg at h
    exact hnot (summable_of_sum_le hf h)
  obtain ⟨F, hF⟩ := hlarge
  obtain ⟨N, hFN⟩ := hexhaust F
  refine ⟨N, ?_⟩
  intro M hNM
  exact hF.le.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (hFN.trans (hmono hNM)) (fun i hi hi' ↦ hf i))

theorem boundedSpecialSplitPrimeData_mono (p : ℕ) :
    Monotone (boundedSpecialSplitPrimeData p) := by
  intro N M hNM s hs
  rw [mem_boundedSpecialSplitPrimeData_iff] at hs ⊢
  exact hs.trans hNM

theorem boundedSpecialSplitPrimeData_exhaustive
    (p : ℕ) (F : Finset (SpecialSplitPrimeData p)) :
    ∃ N, F ⊆ boundedSpecialSplitPrimeData p N := by
  classical
  refine ⟨F.sup SpecialSplitPrimeData.q, ?_⟩
  intro s hs
  rw [mem_boundedSpecialSplitPrimeData_iff]
  exact Finset.le_sup hs

theorem tendsto_specialBadSplitPrimeWeight_bounded
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
    (hH : H ≠ ⊤) :
    Tendsto
      (fun N ↦ ∑ s ∈ boundedSpecialSplitPrimeData p N,
        specialBadSplitPrimeWeight H s) atTop atTop := by
  exact tendsto_finsetSum_atTop_of_nonneg_of_exhaustive
    (boundedSpecialSplitPrimeData p) (specialBadSplitPrimeWeight H)
    (specialBadSplitPrimeWeight_nonneg H)
    (boundedSpecialSplitPrimeData_mono p)
    (boundedSpecialSplitPrimeData_exhaustive p)
    (not_summable_specialBadSplitPrimeWeight H hH)

section SquareSubgroup

variable {G : Type*} [CommGroup G]

def classSquareMonoidHom : G →* (classSquareSubgroup : Subgroup G) where
  toFun := classSquareElement
  map_one' := by
    apply Subtype.ext
    simp [classSquareElement]
  map_mul' x y := by
    apply Subtype.ext
    simp [classSquareElement, mul_pow]

@[simp] theorem classSquareMonoidHom_apply (x : G) :
    classSquareMonoidHom x = classSquareElement x := rfl

def squarePreimageSubgroup
    (H : Subgroup (classSquareSubgroup : Subgroup G)) : Subgroup G :=
  H.comap classSquareMonoidHom

@[simp] theorem mem_squarePreimageSubgroup
    (H : Subgroup (classSquareSubgroup : Subgroup G)) (x : G) :
    x ∈ squarePreimageSubgroup H ↔ classSquareElement x ∈ H := Iff.rfl

theorem squarePreimageSubgroup_ne_top
    (H : Subgroup (classSquareSubgroup : Subgroup G)) (hH : H ≠ ⊤) :
    squarePreimageSubgroup H ≠ ⊤ := by
  intro htop
  apply hH
  ext y
  constructor
  · intro hy
    exact Subgroup.mem_top y
  · intro hy
    rcases y.2 with ⟨x, hx⟩
    have hxK : x ∈ squarePreimageSubgroup H := by
      rw [htop]
      exact Subgroup.mem_top x
    have hsq : classSquareElement x ∈ H := hxK
    have heq : classSquareElement x = y := by
      apply Subtype.ext
      exact hx
    simpa [heq] using hsq

end SquareSubgroup

noncomputable def specialSquareBadPrimes
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))))
    (N : ℕ) : Finset ℕ := by
  classical
  exact ((boundedSpecialSplitPrimeData p N).filter fun s ↦
    classSquareElement s.idealClass ∉ H).image SpecialSplitPrimeData.q

theorem mem_specialSquareBadPrimes_iff
    {p N q : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) :
    q ∈ specialSquareBadPrimes H N ↔
      ∃ s : SpecialSplitPrimeData p,
        s.q = q ∧ s.q ≤ N ∧ classSquareElement s.idealClass ∉ H := by
  classical
  simp only [specialSquareBadPrimes, Finset.mem_image, Finset.mem_filter,
    mem_boundedSpecialSplitPrimeData_iff]
  aesop

theorem specialSquareBadPrimes_prime
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) :
    ∀ N q, q ∈ specialSquareBadPrimes H N → q.Prime := by
  intro N q hq
  obtain ⟨s, rfl, _⟩ := (mem_specialSquareBadPrimes_iff H).mp hq
  exact s.prime

theorem specialObstructionPrimes_disjoint_specialSquareBadPrimes
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))))
    (N : ℕ) :
    Disjoint (specialObstructionPrimesFinite p N)
      (specialSquareBadPrimes H N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hqObs hqBad
  obtain ⟨s, hs, hsq, _hsH⟩ :=
    (mem_specialSquareBadPrimes_iff H).mp hqBad
  subst q
  exact s.split (mem_specialObstructionPrimesFinite.mp hqObs).2.2

theorem obstructionReciprocalMass_specialSquareBadPrimes
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))))
    (N : ℕ) :
    obstructionReciprocalMass (N + 1).primesBelow
        (specialSquareBadPrimes H N) =
      ∑ s ∈ boundedSpecialSplitPrimeData p N,
        specialBadSplitPrimeWeight (squarePreimageSubgroup H) s := by
  classical
  let T := (boundedSpecialSplitPrimeData p N).filter fun s ↦
    classSquareElement s.idealClass ∉ H
  have hinj : Set.InjOn SpecialSplitPrimeData.q
      (T : Set (SpecialSplitPrimeData p)) := by
    intro s hs t ht hst
    exact SpecialSplitPrimeData.ext hst
  have hsub : specialSquareBadPrimes H N ⊆ (N + 1).primesBelow := by
    intro q hq
    obtain ⟨s, rfl, hsq, _⟩ :=
      (mem_specialSquareBadPrimes_iff H).mp hq
    exact Nat.mem_primesBelow.mpr ⟨by omega, s.prime⟩
  calc
    obstructionReciprocalMass (N + 1).primesBelow
        (specialSquareBadPrimes H N) =
        ∑ q ∈ specialSquareBadPrimes H N, (q : ℝ)⁻¹ := by
      unfold obstructionReciprocalMass
      have hfilter : (N + 1).primesBelow.filter
          (fun q ↦ q ∈ specialSquareBadPrimes H N) =
          specialSquareBadPrimes H N := by
        ext q
        constructor
        · intro hq
          exact (Finset.mem_filter.mp hq).2
        · intro hq
          exact Finset.mem_filter.mpr ⟨hsub hq, hq⟩
      rw [hfilter]
    _ = ∑ s ∈ T, (s.q : ℝ)⁻¹ := by
      dsimp [specialSquareBadPrimes]
      rw [Finset.sum_image]
      exact hinj
    _ = ∑ s ∈ boundedSpecialSplitPrimeData p N,
        specialBadSplitPrimeWeight (squarePreimageSubgroup H) s := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hmem : classSquareElement s.idealClass ∈ H
      · simp [hmem, specialBadSplitPrimeWeight,
          squarePreimageSubgroup, classSquareMonoidHom]
      · simp [hmem, specialBadSplitPrimeWeight,
          squarePreimageSubgroup, classSquareMonoidHom]

theorem tendsto_obstructionReciprocalMass_specialSquareBadPrimes
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))))
    (hH : H ≠ ⊤) :
    Tendsto
      (fun N ↦ obstructionReciprocalMass (N + 1).primesBelow
        (specialSquareBadPrimes H N)) atTop atTop := by
  simpa only [obstructionReciprocalMass_specialSquareBadPrimes] using
    tendsto_specialBadSplitPrimeWeight_bounded
      (squarePreimageSubgroup H) (squarePreimageSubgroup_ne_top H hH)

noncomputable def specialRegularSquarefreeKernels
    (p N : ℕ) : Finset ℕ := by
  classical
  exact (specialSquarefreeKernels p N).filter fun a ↦
    Nat.Coprime a (2 * p)

@[simp] theorem mem_specialRegularSquarefreeKernels
    {p N a : ℕ} :
    a ∈ specialRegularSquarefreeKernels p N ↔
      a ∈ Finset.Icc 1 N ∧ IsSpecialSquarefreeKernel p a ∧
        Nat.Coprime a (2 * p) := by
  classical
  simp [specialRegularSquarefreeKernels, and_assoc]

noncomputable def specialRegularKernelExceptions
    (p N : ℕ) : Finset ℕ :=
  specialRegularSquarefreeKernels p N \ specialFormValues p N

theorem mem_specialFormValues_of_signed_primeFactors
    {p N a : ℕ} [Fact p.Prime]
    (ha1 : 1 < a) (haN : a ≤ N)
    (ha : IsSpecialSquarefreeKernel p a)
    (hacop : Nat.Coprime a (2 * p))
    (sigma : Fin a.primeFactors.card → Bool)
    (hclass :
      let e : Fin a.primeFactors.card ≃
          {q : ℕ // q ∈ a.primeFactors} :=
        (a.primeFactors.orderIsoOfFin rfl).toEquiv
      signedProduct sigma (fun i ↦
        specialSplitPrimeClass p (e i).1
          (Nat.prime_of_mem_primeFactors (e i).2)
          (by
            intro htwo
            have hdvd : 2 ∣ a := by
              rw [← htwo]
              exact Nat.dvd_of_mem_primeFactors (e i).2
            exact (by decide : (2 : ℕ) ≠ 1)
              (Nat.eq_one_of_dvd_coprimes hacop hdvd
                (by exact dvd_mul_right 2 p)))
          (by
            intro hpq
            have hdvd : p ∣ a := by
              rw [← hpq]
              exact Nat.dvd_of_mem_primeFactors (e i).2
            exact (Fact.out : p.Prime).ne_one
              (Nat.eq_one_of_dvd_coprimes hacop hdvd
                (by exact dvd_mul_left p 2)))
          (by
            intro hobs
            exact ha.2 (e i).1
              (Nat.prime_of_mem_primeFactors (e i).2) hobs
              (Nat.dvd_of_mem_primeFactors (e i).2))) = 1) :
    a ∈ specialFormValues p N := by
  classical
  let e : Fin a.primeFactors.card ≃
      {q : ℕ // q ∈ a.primeFactors} :=
    (a.primeFactors.orderIsoOfFin rfl).toEquiv
  let q : Fin a.primeFactors.card → ℕ := fun i ↦ (e i).1
  have hqprime : ∀ i, (q i).Prime := fun i ↦
    Nat.prime_of_mem_primeFactors (e i).2
  have hq2 : ∀ i, q i ≠ 2 := by
    intro i htwo
    have hdvd : 2 ∣ a := by
      rw [← htwo]
      exact Nat.dvd_of_mem_primeFactors (e i).2
    exact (by decide : (2 : ℕ) ≠ 1)
      (Nat.eq_one_of_dvd_coprimes hacop hdvd
        (by exact dvd_mul_right 2 p))
  have hqp : ∀ i, q i ≠ p := by
    intro i hpq
    have hdvd : p ∣ a := by
      rw [← hpq]
      exact Nat.dvd_of_mem_primeFactors (e i).2
    exact (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes hacop hdvd
        (by exact dvd_mul_left p 2))
  have hallowed : ∀ i, ¬ IsQuadraticObstruction (p ^ 3) (q i) := by
    intro i hobs
    exact ha.2 (q i) (hqprime i) hobs
      (Nat.dvd_of_mem_primeFactors (e i).2)
  have hqinj : Function.Injective q := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  have hprod : ∏ i, q i = a := by
    calc
      ∏ i, q i = ∏ z : {q : ℕ // q ∈ a.primeFactors}, z.1 :=
        Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
      _ = ∏ z ∈ a.primeFactors, z := by
        simpa only [Finset.univ_eq_attach] using
          (Finset.prod_attach a.primeFactors (fun z : ℕ ↦ z))
      _ = a := Nat.prod_primeFactors_of_squarefree ha.1
  have hclass' : signedProduct sigma (fun i ↦
      specialSplitPrimeClass p (q i) (hqprime i) (hq2 i) (hqp i)
        (hallowed i)) = 1 := by
    simpa [e, q] using hclass
  obtain ⟨x, y, hxy⟩ :=
    exists_specialForm_representation_of_signedClassProduct
      q hqprime hq2 hqp hallowed hqinj sigma hclass'
  rw [hprod] at hxy
  have hx : 0 < x := by
    by_contra hx0
    have hx0' : x = 0 := Nat.eq_zero_of_not_pos hx0
    rw [hx0', zero_pow (by decide : 2 ≠ 0), zero_add] at hxy
    have hpdiv : p ∣ a := by
      rw [hxy]
      simpa using ((pow_dvd_pow p (by omega : 1 ≤ 3)).trans
        (dvd_mul_right (p ^ 3) (y ^ 2)))
    exact (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes hacop hpdiv
        (by exact dvd_mul_left p 2))
  have hy : 0 < y := by
    by_contra hy0
    have hy0' : y = 0 := Nat.eq_zero_of_not_pos hy0
    rw [hy0', zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hxy
    by_cases hx1 : x = 1
    · rw [hx1] at hxy
      simp at hxy
      omega
    · have hsquare : Squarefree (x ^ 2) := by
        rw [← hxy]
        exact ha.1
      have := (Nat.squarefree_pow_iff hx1 (by decide : 2 ≠ 0)).mp hsquare
      omega
  rw [mem_specialFormValues]
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, haN⟩,
    x, Finset.mem_Icc.mpr ⟨hx, ?_⟩,
    y, Finset.mem_Icc.mpr ⟨hy, ?_⟩, hxy⟩
  · calc
      x ≤ x ^ 2 := by nlinarith
      _ ≤ x ^ 2 + p ^ 3 * y ^ 2 := Nat.le_add_right _ _
      _ = a := hxy.symm
      _ ≤ N := haN
  · calc
      y ≤ y ^ 2 := by nlinarith
      _ ≤ p ^ 3 * y ^ 2 := by
        have hp3 : 1 ≤ p ^ 3 := pow_pos (Fact.out : p.Prime).pos 3
        nlinarith
      _ ≤ x ^ 2 + p ^ 3 * y ^ 2 := Nat.le_add_left _ _
      _ = a := hxy.symm
      _ ≤ N := haN

theorem countOutsideSubgroup_ofFn_eq_card_filter
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {k : ℕ} (H : Subgroup G) [DecidablePred (· ∈ H)]
    (x : Fin k → G) :
    countOutsideSubgroup H (List.ofFn x) =
      (Finset.univ.filter fun i ↦ x i ∉ H).card := by
  classical
  induction k with
  | zero => simp [countOutsideSubgroup]
  | succ k ih =>
      rw [List.ofFn_succ]
      by_cases h0 : x 0 ∈ H
      · rw [countOutsideSubgroup_cons_of_mem H _ _ h0]
        rw [ih (fun i : Fin k ↦ x i.succ)]
        simpa [Finset.card_filter, Fin.sum_univ_succ, h0]
      · rw [countOutsideSubgroup_cons_of_not_mem H _ _ h0]
        rw [ih (fun i : Fin k ↦ x i.succ)]
        simpa [Finset.card_filter, Fin.sum_univ_succ, h0, Nat.add_comm]

theorem exists_squareSubgroup_with_few_primeDivisors_of_exception
    {p N a : ℕ} [Fact p.Prime]
    (hsqtop :
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤)
    (ha : a ∈ specialRegularKernelExceptions p N)
    (ha1 : 1 < a) :
    ∃ H : Subgroup
        (classSquareSubgroup : Subgroup
          (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))),
      H ≠ ⊤ ∧
        primeDivisorCount (specialSquareBadPrimes H N) a <
          Nat.card
            (classSquareSubgroup : Subgroup
              (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) := by
  classical
  rw [specialRegularKernelExceptions, Finset.mem_sdiff] at ha
  rw [mem_specialRegularSquarefreeKernels] at ha
  let e : Fin a.primeFactors.card ≃
      {q : ℕ // q ∈ a.primeFactors} :=
    (a.primeFactors.orderIsoOfFin rfl).toEquiv
  let q : Fin a.primeFactors.card → ℕ := fun i ↦ (e i).1
  have hqprime : ∀ i, (q i).Prime := fun i ↦
    Nat.prime_of_mem_primeFactors (e i).2
  have hq2 : ∀ i, q i ≠ 2 := by
    intro i htwo
    have hdvd : 2 ∣ a := by
      rw [← htwo]
      exact Nat.dvd_of_mem_primeFactors (e i).2
    exact (by decide : (2 : ℕ) ≠ 1)
      (Nat.eq_one_of_dvd_coprimes ha.1.2.2 hdvd
        (by exact dvd_mul_right 2 p))
  have hqp : ∀ i, q i ≠ p := by
    intro i hpq
    have hdvd : p ∣ a := by
      rw [← hpq]
      exact Nat.dvd_of_mem_primeFactors (e i).2
    exact (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes ha.1.2.2 hdvd
        (by exact dvd_mul_left p 2))
  have hallowed : ∀ i, ¬ IsQuadraticObstruction (p ^ 3) (q i) := by
    intro i hobs
    exact ha.1.2.1.2 (q i) (hqprime i) hobs
      (Nat.dvd_of_mem_primeFactors (e i).2)
  have hqinj : Function.Injective q := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  let s : Fin a.primeFactors.card → SpecialSplitPrimeData p := fun i ↦
    ⟨q i, hqprime i, hq2 i, hqp i, hallowed i⟩
  let x : Fin a.primeFactors.card →
      ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)) := fun i ↦ (s i).idealClass
  have hclass :
      (QuotientGroup.mk'
        (classSquareSubgroup : Subgroup
          (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) (∏ i, x i)) =
      QuotientGroup.mk'
        (classSquareSubgroup : Subgroup
          (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem, hsqtop]
    exact Subgroup.mem_top _
  have hmiss : ∀ sigma : Fin a.primeFactors.card → Bool,
      signedProduct sigma x ≠ 1 := by
    intro sigma hsigma
    apply ha.2
    apply mem_specialFormValues_of_signed_primeFactors
      ha1 (Finset.mem_Icc.mp ha.1.1).2 ha.1.2.1 ha.1.2.2 sigma
    simpa [e, q, s, x, SpecialSplitPrimeData.idealClass] using hsigma
  let : Fintype (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :=
    zsqrtdClassGroupFintype (-(p : ℤ) ^ 3)
      (specialDiscriminant_neg p Fact.out)
  obtain ⟨H, hH, hfew⟩ :=
    exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
      x 1 hclass hmiss
  refine ⟨H, hH, ?_⟩
  let Bfilter := (specialSquareBadPrimes H N).filter fun r ↦ r ∣ a
  let Ifilter := (Finset.univ : Finset (Fin a.primeFactors.card)).filter
    fun i ↦ classSquareElement (x i) ∉ H
  let f : {r : ℕ // r ∈ Bfilter} →
      {i : Fin a.primeFactors.card // i ∈ Ifilter} := fun r ↦ by
    have hrB : r.1 ∈ specialSquareBadPrimes H N :=
      (Finset.mem_filter.mp r.2).1
    have hrdvd : r.1 ∣ a := (Finset.mem_filter.mp r.2).2
    have hrprime : r.1.Prime :=
      specialSquareBadPrimes_prime H N r.1 hrB
    have hrpf : r.1 ∈ a.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrprime, hrdvd, by omega⟩
    let i : Fin a.primeFactors.card := e.symm ⟨r.1, hrpf⟩
    have hqi : q i = r.1 := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨r.1, hrpf⟩)
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    obtain ⟨t, htq, _htN, htH⟩ :=
      (mem_specialSquareBadPrimes_iff H).mp hrB
    have hts : t = s i := by
      apply SpecialSplitPrimeData.ext
      simpa [s] using htq.trans hqi.symm
    simpa [x, hts] using htH
  have hf : Function.Injective f := by
    intro r t hrt
    apply Subtype.ext
    have hi := congrArg (fun z ↦ (e z.1).1) hrt
    simpa [f] using hi
  have hcard : Bfilter.card ≤ Ifilter.card := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective f hf)
  have hcount : primeDivisorCount (specialSquareBadPrimes H N) a =
      Bfilter.card := by rfl
  have hout : Ifilter.card =
      countOutsideSubgroup H
        (List.ofFn fun i ↦ classSquareElement (x i)) := by
    rw [countOutsideSubgroup_ofFn_eq_card_filter]
  rw [hcount]
  exact hcard.trans_lt (hout.trans_lt hfew)

noncomputable def specialProperSquareSubgroups
    (p : ℕ) [Fact p.Prime] :
    Finset (Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) := by
  classical
  letI : Fintype (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :=
    zsqrtdClassGroupFintype (-(p : ℤ) ^ 3)
      (specialDiscriminant_neg p Fact.out)
  exact Finset.univ.filter (· ≠ ⊤)

@[simp] theorem mem_specialProperSquareSubgroups
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) :
    H ∈ specialProperSquareSubgroups p ↔ H ≠ ⊤ := by
  classical
  let : Fintype (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))) :=
    zsqrtdClassGroupFintype (-(p : ℤ) ^ 3)
      (specialDiscriminant_neg p Fact.out)
  simp [specialProperSquareSubgroups]

theorem specialRegularKernelException_mem_cover
    {p N a : ℕ} [Fact p.Prime]
    (hsqtop :
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤)
    (ha : a ∈ specialRegularKernelExceptions p N) :
    a = 1 ∨
      ∃ H : Subgroup
          (classSquareSubgroup : Subgroup
            (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))),
        H ∈ specialProperSquareSubgroups p ∧
          a ∈ parityFewPrimeDivisorValues
            (specialObstructionPrimesFinite p N)
            (specialSquareBadPrimes H N)
            (Nat.card
              (classSquareSubgroup : Subgroup
                (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) N := by
  classical
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  right
  have ha1lt : 1 < a := by
    rw [specialRegularKernelExceptions, Finset.mem_sdiff,
      mem_specialRegularSquarefreeKernels] at ha
    have haone := (Finset.mem_Icc.mp ha.1.1).1
    omega
  obtain ⟨H, hH, hfew⟩ :=
    exists_squareSubgroup_with_few_primeDivisors_of_exception
      hsqtop ha ha1lt
  refine ⟨H, (mem_specialProperSquareSubgroups H).mpr hH, ?_⟩
  rw [parityFewPrimeDivisorValues, Finset.mem_filter]
  rw [specialRegularKernelExceptions, Finset.mem_sdiff,
    mem_specialRegularSquarefreeKernels] at ha
  refine ⟨ha.1.1, ?_, hfew.le⟩
  have hadm : SpecialLocallyAdmissible p a := by
    simpa using (specialLocallyAdmissible_sq_mul_squarefree_iff
      (p := p) (a := a) (b := 1)
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha.1.1).1)
      (by decide) ha.1.2.1.1).mpr ha.1.2.1.2
  intro l hl
  have hldata := mem_specialObstructionPrimesFinite.mp hl
  exact hadm l hldata.1 hldata.2.2

theorem specialRegularKernelExceptions_card_le_cover
    {p N : ℕ} [Fact p.Prime]
    (hsqtop :
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤) :
    (specialRegularKernelExceptions p N).card ≤ 1 +
      ∑ H ∈ specialProperSquareSubgroups p,
        (parityFewPrimeDivisorValues
          (specialObstructionPrimesFinite p N)
          (specialSquareBadPrimes H N)
          (Nat.card
            (classSquareSubgroup : Subgroup
              (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) N).card := by
  classical
  let U := (specialProperSquareSubgroups p).biUnion fun H ↦
    parityFewPrimeDivisorValues
      (specialObstructionPrimesFinite p N)
      (specialSquareBadPrimes H N)
      (Nat.card
        (classSquareSubgroup : Subgroup
          (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) N
  have hsub : specialRegularKernelExceptions p N ⊆ {1} ∪ U := by
    intro a ha
    rcases specialRegularKernelException_mem_cover hsqtop ha with ha1 | haH
    · exact Finset.mem_union_left _ (by simpa [ha1])
    · obtain ⟨H, hHP, haH⟩ := haH
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨H, hHP, haH⟩)
  calc
    (specialRegularKernelExceptions p N).card ≤ ({1} ∪ U).card :=
      Finset.card_le_card hsub
    _ ≤ ({1} : Finset ℕ).card + U.card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ H ∈ specialProperSquareSubgroups p,
        (parityFewPrimeDivisorValues
          (specialObstructionPrimesFinite p N)
          (specialSquareBadPrimes H N)
          (Nat.card
            (classSquareSubgroup : Subgroup
              (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))) N).card := by
      simp only [Finset.card_singleton, U]
      exact Nat.add_le_add_left (Finset.card_biUnion_le) 1

theorem tendsto_landauScale_atTop :
    Tendsto landauScale atTop atTop := by
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop (eventually_ge_atTop 3 |>.mono ?_) hsqrt
  intro N hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hNone : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hNone
  have hsqrtlog : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have hlogle : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hsqrtle : Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hlogle
  rw [landauScale]
  apply (le_div_iff₀ hsqrtlog).2
  calc
    Real.sqrt (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsqrtle (Real.sqrt_nonneg _)
    _ = (N : ℝ) := Real.mul_self_sqrt (by positivity)

theorem eventually_specialRegularKernelExceptions_negligible
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (hsqtop :
      (classSquareSubgroup : Subgroup
        (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3)))) = ⊤)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ((specialRegularKernelExceptions p N).card : ℝ) ≤
        eta * landauScale N := by
  classical
  let P := specialProperSquareSubgroups p
  let R := Nat.card
    (classSquareSubgroup : Subgroup
      (ClassGroup (Zsqrtd (-(p : ℤ) ^ 3))))
  let eta' : ℝ := eta / (2 * (P.card + 1))
  have heta' : 0 < eta' := by
    dsimp [eta']
    positivity
  obtain ⟨C, hC, hmassL⟩ :=
    eventually_specialObstructionReciprocalMass_half_lower
      (Fact.out : p.Prime) hp4
  have hEach : ∀ᶠ N : ℕ in atTop, ∀ H ∈ P,
      ((parityFewPrimeDivisorValues
        (specialObstructionPrimesFinite p N)
        (specialSquareBadPrimes H N) R N).card : ℝ) ≤
          eta' * landauScale N := by
    rw [Finset.eventually_all]
    intro H hHP
    have hH : H ≠ ⊤ := by
      exact (mem_specialProperSquareSubgroups H).mp hHP
    exact eventually_parityFewPrimeDivisorValues_le_landauScale_mul_of_tendstoMass
      (fun N ↦ specialObstructionPrimesFinite p N)
      (fun N ↦ specialSquareBadPrimes H N)
      (fun N l hl ↦ (mem_specialObstructionPrimesFinite.mp hl).1)
      (specialSquareBadPrimes_prime H)
      (specialObstructionPrimes_disjoint_specialSquareBadPrimes H)
      R heta' hmassL
      (tendsto_obstructionReciprocalMass_specialSquareBadPrimes H hH)
  have hOne : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ eta / 2 * landauScale N := by
    have hlarge := tendsto_landauScale_atTop.eventually_ge_atTop (2 / eta)
    filter_upwards [hlarge] with N hN
    have h := mul_le_mul_of_nonneg_left hN (le_of_lt (half_pos heta))
    field_simp [heta.ne'] at h ⊢
    nlinarith
  filter_upwards [hEach, hOne, eventually_ge_atTop 3] with N hEachN hOneN hN
  have hcoverNat := specialRegularKernelExceptions_card_le_cover
    (p := p) (N := N) hsqtop
  have hcover : ((specialRegularKernelExceptions p N).card : ℝ) ≤
      1 + ∑ H ∈ P,
        ((parityFewPrimeDivisorValues
          (specialObstructionPrimesFinite p N)
          (specialSquareBadPrimes H N) R N).card : ℝ) := by
    exact_mod_cast hcoverNat
  have hsum : (∑ H ∈ P,
      ((parityFewPrimeDivisorValues
        (specialObstructionPrimesFinite p N)
        (specialSquareBadPrimes H N) R N).card : ℝ)) ≤
      (P.card : ℝ) * eta' * landauScale N := by
    calc
      (∑ H ∈ P,
          ((parityFewPrimeDivisorValues
            (specialObstructionPrimesFinite p N)
            (specialSquareBadPrimes H N) R N).card : ℝ)) ≤
          ∑ H ∈ P, eta' * landauScale N :=
        Finset.sum_le_sum hEachN
      _ = (P.card : ℝ) * eta' * landauScale N := by
        simp [mul_assoc]
  have hcoef : (P.card : ℝ) * eta' ≤ eta / 2 := by
    dsimp [eta']
    have hcard : (P.card : ℝ) < P.card + 1 := by norm_num
    have hden : (0 : ℝ) < 2 * (P.card + 1) := by positivity
    rw [div_eq_mul_inv]
    calc
      (P.card : ℝ) *
          (eta * ((2 : ℝ) * ((P.card : ℝ) + 1))⁻¹) =
          eta / 2 * ((P.card : ℝ) / ((P.card : ℝ) + 1)) := by
        field_simp
      _ ≤ eta / 2 * 1 := by
        gcongr
        exact (div_le_one (by positivity)).2 (by linarith)
      _ = eta / 2 := by ring
  have hscale : 0 ≤ landauScale N := by
    have hNone : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    dsimp [landauScale]
    positivity
  have hsum' : (∑ H ∈ P,
      ((parityFewPrimeDivisorValues
        (specialObstructionPrimesFinite p N)
        (specialSquareBadPrimes H N) R N).card : ℝ)) ≤
      eta / 2 * landauScale N :=
    hsum.trans (mul_le_mul_of_nonneg_right hcoef hscale)
  linarith

end

end Erdos1081
