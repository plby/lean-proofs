import ErdosProblems.Erdos220.Basic
import ErdosProblems.Erdos220.LargePrime
import ErdosProblems.Erdos220.MomentExpansion
import ErdosProblems.Erdos220.SmallMoment

/-!
# The smooth--rough decomposition for Erdős problem 220

This file contains the arithmetic assembly surrounding the Montgomery--
Vaughan smooth--rough argument.  In particular, it proves that all the
quantities entering the empty-window estimate may be reduced, without any
loss, to the squarefree kernel, and records the canonical factorisation of
that kernel at the interval length.
-/

open scoped BigOperators

namespace Erdos220

/-! ## Reduction to the squarefree kernel -/

/-- The squarefree kernel (radical) of a positive natural number. -/
def squarefreeKernel (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

@[simp] lemma squarefreeKernel_primeFactors (n : ℕ) :
    (squarefreeKernel n).primeFactors = n.primeFactors := by
  exact Nat.primeFactors_prod_primeFactors n

lemma squarefree_squarefreeKernel (n : ℕ) : Squarefree (squarefreeKernel n) := by
  rw [squarefreeKernel]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq ↦ ?_)
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq)

lemma squarefreeKernel_dvd (n : ℕ) : squarefreeKernel n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

lemma squarefreeKernel_pos {n : ℕ} (hn : 0 < n) : 0 < squarefreeKernel n := by
  rw [squarefreeKernel]
  exact Finset.prod_pos fun p hp ↦ Nat.pos_of_mem_primeFactors hp

lemma squarefreeKernel_ne_zero {n : ℕ} (hn : 0 < n) : squarefreeKernel n ≠ 0 :=
  (squarefreeKernel_pos hn).ne'

/-- Coprimality depends only on the squarefree kernel. -/
lemma coprime_squarefreeKernel_iff {n m : ℕ} (hn : 0 < n) :
    (squarefreeKernel n).Coprime m ↔ n.Coprime m := by
  rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd,
    Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨p, hp, hpk, hpm⟩
    exact ⟨p, hp, hpk.trans (squarefreeKernel_dvd n), hpm⟩
  · rintro ⟨p, hp, hpn, hpm⟩
    have hpf : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
    exact ⟨p, hp, Finset.dvd_prod_of_mem id hpf, hpm⟩

lemma unitCount_squarefreeKernel {n h x : ℕ} (hn : 0 < n) :
    unitCount (squarefreeKernel n) h x = unitCount n h x := by
  unfold unitCount
  congr 1
  ext t
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _ht
  exact coprime_squarefreeKernel_iff hn

/-- `unitCount k h` is periodic in the starting point, with period `k`. -/
lemma unitCount_periodic (k h : ℕ) :
    Function.Periodic (unitCount k h) k := by
  intro x
  unfold unitCount
  congr 1
  ext t
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _ht
  exact eq_iff_iff.mp (by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.periodic_coprime k (x + t))

/-- A periodic predicate has the expected number of solutions in an
integral number of periods. -/
lemma card_filter_range_mul_of_periodic (p : ℕ → Prop) [DecidablePred p]
    (d m : ℕ) (hp : Function.Periodic p d) :
    ((Finset.range (m * d)).filter p).card =
      m * ((Finset.range d).filter p).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
      have hshift : (fun k ↦ p (m * d + k)) = p := by
        funext k
        have hh := hp.nsmul m k
        change p (k + m * d) = p k at hh
        simpa only [Nat.add_comm] using hh
      simpa only [hshift]

lemma emptyWindows_squarefreeKernel_pred {n h x : ℕ} (hn : 0 < n) :
    (unitCount (squarefreeKernel n) h x = 0) ↔ (unitCount n h x = 0) := by
  rw [unitCount_squarefreeKernel hn]

/-- Empty windows scale exactly through repeated periods of the squarefree
kernel. -/
lemma card_emptyWindows_eq_kernel_mul {n h : ℕ} (hn : 0 < n) :
    (emptyWindows n h).card =
      (n / squarefreeKernel n) * (emptyWindows (squarefreeKernel n) h).card := by
  let r := squarefreeKernel n
  let q := n / r
  have hr : 0 < r := squarefreeKernel_pos hn
  have hnqr : n = q * r := by
    dsimp [q, r]
    exact (Nat.div_mul_cancel (squarefreeKernel_dvd n)).symm
  have hperiod : Function.Periodic (fun x ↦ unitCount r h x = 0) r :=
    (unitCount_periodic r h).comp (fun z ↦ z = 0)
  have hcard := card_filter_range_mul_of_periodic
    (fun x ↦ unitCount r h x = 0) r q hperiod
  have hpred : (fun x ↦ unitCount n h x = 0) =
      (fun x ↦ unitCount r h x = 0) := by
    funext x
    exact propext (emptyWindows_squarefreeKernel_pred hn).symm
  change (emptyWindows n h).card = q * (emptyWindows r h).card
  simp only [emptyWindows, hpred]
  rw [hnqr]
  exact hcard

/-- Euler's totient scales by the same repetition factor as the window
count. -/
lemma totient_eq_kernel_mul {n : ℕ} (hn : 0 < n) :
    n.totient = (n / squarefreeKernel n) * (squarefreeKernel n).totient := by
  let r := squarefreeKernel n
  have hr : 0 < r := squarefreeKernel_pos hn
  let F := ∏ p ∈ n.primeFactors, (p - 1)
  have hφn : n.totient = (n / r) * F := by
    simpa only [r, F, squarefreeKernel] using
      Nat.totient_eq_div_primeFactors_mul n
  have hφr : r.totient = F := by
    rw [Nat.totient_eq_div_primeFactors_mul r]
    have hpf : r.primeFactors = n.primeFactors := by
      simpa only [r] using squarefreeKernel_primeFactors n
    rw [hpf]
    have hprod : (∏ p ∈ n.primeFactors, p) = r := by rfl
    rw [hprod, Nat.div_self hr]
    simp [F]
  rw [hφn, hφr]

lemma density_squarefreeKernel {n : ℕ} (hn : 0 < n) :
    density (squarefreeKernel n) = density n := by
  let r := squarefreeKernel n
  let q := n / r
  have hr : 0 < r := squarefreeKernel_pos hn
  have hq : 0 < q := Nat.div_pos
    (Nat.le_of_dvd hn (squarefreeKernel_dvd n)) hr
  have hnqr : n = q * r := by
    dsimp [q, r]
    exact (Nat.div_mul_cancel (squarefreeKernel_dvd n)).symm
  have hphi : n.totient = q * r.totient := by
    simpa only [q, r] using totient_eq_kernel_mul hn
  change density r = density n
  rw [density, density, hphi]
  conv_rhs => rw [hnqr]
  push_cast
  field_simp

/-- A division-free empty-window estimate for the squarefree kernel scales
to the original modulus with exactly the same constant. -/
lemma emptyWindows_bound_of_kernel {B : ℝ} {n h : ℕ} (hn : 0 < n)
    (H : ((emptyWindows (squarefreeKernel n) h).card : ℝ) * (h : ℝ) ^ 2 *
      ((squarefreeKernel n).totient : ℝ) ^ 2 ≤
        B * (squarefreeKernel n : ℝ) ^ 3) :
    ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
      B * (n : ℝ) ^ 3 := by
  let r := squarefreeKernel n
  let q := n / r
  have hnqr : n = q * r := by
    dsimp [q, r]
    exact (Nat.div_mul_cancel (squarefreeKernel_dvd n)).symm
  have hE : (emptyWindows n h).card = q * (emptyWindows r h).card := by
    simpa only [q, r] using card_emptyWindows_eq_kernel_mul (n := n) (h := h) hn
  have hphi : n.totient = q * r.totient := by
    simpa only [q, r] using totient_eq_kernel_mul hn
  rw [hE, hphi, hnqr]
  push_cast
  calc
    (↑q * ↑(emptyWindows r h).card) * (h : ℝ) ^ 2 *
          (↑q * ↑r.totient) ^ 2 =
        (q : ℝ) ^ 3 *
          ((↑(emptyWindows r h).card) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2) := by
            ring
    _ ≤ (q : ℝ) ^ 3 * (B * (r : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ = B * (↑q * ↑r) ^ 3 := by ring

/-! ## The small-prime/large-prime factorisation -/

/-- Product of the prime factors of `r` which do not exceed `h`. -/
def smoothPart (r h : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p ↦ p ≤ h), p

/-- Product of the prime factors of `r` which exceed `h`. -/
def roughPart (r h : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p ↦ h < p), p

lemma smoothPart_pos (r h : ℕ) : 0 < smoothPart r h := by
  rw [smoothPart]
  exact Finset.prod_pos fun p hp ↦
    Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma roughPart_pos (r h : ℕ) : 0 < roughPart r h := by
  rw [roughPart]
  exact Finset.prod_pos fun p hp ↦
    Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    smoothPart r h * roughPart r h = r := by
  rw [smoothPart, roughPart, ← Finset.prod_union]
  · rw [show r.primeFactors.filter (fun p ↦ p ≤ h) ∪
        r.primeFactors.filter (fun p ↦ h < p) = r.primeFactors by
      ext p
      by_cases hp : p ≤ h
      · simp [hp]
      · have hhp : h < p := Nat.lt_of_not_ge hp
        simp [hp, hhp]]
    exact Nat.prod_primeFactors_of_squarefree hr
  · rw [Finset.disjoint_left]
    intro p hpSmall hpLarge
    have hs := (Finset.mem_filter.mp hpSmall).2
    have hl := (Finset.mem_filter.mp hpLarge).2
    omega

lemma smoothPart_coprime_roughPart {r h : ℕ} (hr : Squarefree r) :
    (smoothPart r h).Coprime (roughPart r h) := by
  apply Nat.coprime_of_squarefree_mul
  rw [smoothPart_mul_roughPart hr]
  exact hr

lemma squarefree_smoothPart {r h : ℕ} (hr : Squarefree r) :
    Squarefree (smoothPart r h) := by
  have hd : smoothPart r h ∣ r :=
    ⟨roughPart r h, (smoothPart_mul_roughPart (h := h) hr).symm⟩
  exact Squarefree.squarefree_of_dvd hd hr

lemma squarefree_roughPart {r h : ℕ} (hr : Squarefree r) :
    Squarefree (roughPart r h) := by
  have hd : roughPart r h ∣ r :=
    ⟨smoothPart r h, by
      rw [mul_comm]
      exact (smoothPart_mul_roughPart (h := h) hr).symm⟩
  exact Squarefree.squarefree_of_dvd hd hr

lemma primeFactors_smoothPart_subset {r h : ℕ} :
    (smoothPart r h).primeFactors ⊆ r.primeFactors.filter (fun p ↦ p ≤ h) := by
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ smoothPart r h := (Nat.mem_primeFactors.mp hp).2.1
  rw [smoothPart, hpPrime.prime.dvd_finsetProd_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqPrime : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hpqeq : p = q := ((hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq).symm
  simpa [hpqeq] using hq

lemma smoothPart_prime_le {r h p : ℕ} (hp : p ∈ (smoothPart r h).primeFactors) :
    p ≤ h := by
  exact (Finset.mem_filter.mp (primeFactors_smoothPart_subset hp)).2

lemma roughPart_prime_gt {r h p : ℕ} (hp : p ∈ (roughPart r h).primeFactors) :
    h < p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ roughPart r h := (Nat.mem_primeFactors.mp hp).2.1
  rw [roughPart, hpPrime.prime.dvd_finsetProd_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqPrime : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hpqeq : p = q := ((hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq).symm
  simpa [hpqeq] using (Finset.mem_filter.mp hq).2

lemma totient_smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    r.totient = (smoothPart r h).totient * (roughPart r h).totient := by
  rw [← Nat.totient_mul (smoothPart_coprime_roughPart hr),
    smoothPart_mul_roughPart hr]

lemma density_smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    density r = density (smoothPart r h) * density (roughPart r h) := by
  let s := smoothPart r h
  let v := roughPart r h
  have hrv : r = s * v := by
    simpa only [s, v] using (smoothPart_mul_roughPart hr).symm
  have hphi : r.totient = s.totient * v.totient := by
    simpa only [s, v] using totient_smoothPart_mul_roughPart hr
  change density r = density s * density v
  rw [density, density, density, hphi]
  conv_lhs => rw [hrv]
  push_cast
  field_simp [Nat.ne_of_gt (smoothPart_pos r h), Nat.ne_of_gt (roughPart_pos r h)]

/-! ## Exact CRT decomposition of empty windows -/

open LargePrime

/-- Empty windows are the simultaneous shifted-nonunit event used by the
large-prime lemma. -/
lemma card_emptyWindows_eq_shiftedNonunitCount {m : ℕ} (hm : 0 < m) (h : ℕ) :
    (emptyWindows m h).card = shiftedNonunitCount m (Finset.Icc 1 h) := by
  rw [shiftedNonunitCount_eq_noncoprime hm]
  apply congrArg Finset.card
  ext x
  simp only [emptyWindows, shiftedNoncoprimeResidueCount, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hx, hempty⟩
    refine ⟨hx, ?_⟩
    rw [unitCount_eq_zero_iff] at hempty
    intro t
    exact (hempty t.1 (Finset.mem_Icc.mp t.2).1
      (Finset.mem_Icc.mp t.2).2) ∘ Nat.Coprime.symm
  · rintro ⟨hx, hempty⟩
    refine ⟨hx, ?_⟩
    rw [unitCount_eq_zero_iff]
    intro t ht1 hth ht
    exact hempty ⟨t, Finset.mem_Icc.mpr ⟨ht1, hth⟩⟩ ht.symm

/-- Shifts which survive the small-prime coordinate `u`. -/
def survivingShifts (s h : ℕ) [NeZero s] (u : ZMod s) : Finset ℕ :=
  (Finset.Icc 1 h).filter fun t ↦ IsUnit (u + (t : ZMod s))

lemma survivingShifts_subset (s h : ℕ) [NeZero s] (u : ZMod s) :
    survivingShifts s h u ⊆ Finset.Icc 1 h := by
  classical
  exact Finset.filter_subset _ _

lemma card_survivingShifts_eq_unitCount {s : ℕ} [NeZero s]
    (h : ℕ) (u : ZMod s) :
    (survivingShifts s h u).card = unitCount s h u.val := by
  classical
  apply congrArg Finset.card
  ext t
  simp only [survivingShifts, unitCount, Finset.mem_filter, Finset.mem_Icc]
  rw [shifted_isUnit_iff_coprime]
  simp only [Nat.coprime_comm]

lemma crt_shift_isUnit_iff {s v : ℕ} (hcop : s.Coprime v)
    (x : ZMod (s * v)) (t : ℕ) :
    IsUnit (x + (t : ZMod (s * v))) ↔
      IsUnit (((ZMod.chineseRemainder hcop) x).1 + (t : ZMod s)) ∧
        IsUnit (((ZMod.chineseRemainder hcop) x).2 + (t : ZMod v)) := by
  let cr : ZMod (s * v) ≃+* ZMod s × ZMod v := ZMod.chineseRemainder hcop
  have hmap : cr (x + (t : ZMod (s * v))) =
      ((cr x).1 + (t : ZMod s), (cr x).2 + (t : ZMod v)) := by
    rw [map_add, map_natCast]
    rfl
  calc
    IsUnit (x + (t : ZMod (s * v))) ↔
        IsUnit (cr (x + (t : ZMod (s * v)))) :=
      (MulEquiv.isUnit_map cr.toMulEquiv).symm
    _ ↔ IsUnit ((cr x).1 + (t : ZMod s)) ∧
        IsUnit ((cr x).2 + (t : ZMod v)) := by
      rw [hmap, Prod.isUnit_iff]

/-- The simultaneous shifted-nonunit event modulo `s*v`, written as a
dependent sum over the small CRT coordinate. -/
noncomputable def emptyCrtEquiv (s v h : ℕ) [NeZero s] [NeZero v]
    (hcop : s.Coprime v) :
    {x : ZMod (s * v) //
      ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} ≃
      Σ u : ZMod s,
        {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
          ¬IsUnit (z + (t.1 : ZMod v))} := by
  classical
  let cr : ZMod (s * v) ≃+* ZMod s × ZMod v := ZMod.chineseRemainder hcop
  refine
    { toFun := fun x ↦
        ⟨(cr x.1).1, ⟨(cr x.1).2, fun t ht ↦ ?_⟩⟩
      invFun := fun y ↦
        ⟨cr.symm (y.1, y.2.1), fun t ht ↦ ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htmem : t.1 ∈ (Finset.Icc 1 h).filter
        (fun a : ℕ ↦ IsUnit ((cr x.1).1 + (a : ZMod s))) := by
      simpa only [survivingShifts] using t.2
    have hu : IsUnit ((cr x.1).1 + (t.1 : ZMod s)) :=
      (Finset.mem_filter.mp htmem).2
    have hboth : IsUnit (x.1 + (t.1 : ZMod (s * v))) :=
      (crt_shift_isUnit_iff hcop x.1 t.1).mpr ⟨hu, ht⟩
    exact x.2 ⟨t.1, (Finset.mem_filter.mp t.2).1⟩ hboth
  · have hboth := (crt_shift_isUnit_iff hcop (cr.symm (y.1, y.2.1)) t.1).mp ht
    have heq : (ZMod.chineseRemainder hcop) (cr.symm (y.1, y.2.1)) =
        (y.1, y.2.1) := by
      exact cr.apply_symm_apply (y.1, y.2.1)
    rw [heq] at hboth
    have hboth' : IsUnit (y.1 + (t.1 : ZMod s)) ∧
        IsUnit (y.2.1 + (t.1 : ZMod v)) := hboth
    let t' : ↑(survivingShifts s h y.1) :=
      ⟨t.1, by
        change t.1 ∈ (Finset.Icc 1 h).filter
          (fun a : ℕ ↦ IsUnit (y.1 + (a : ZMod s)))
        exact Finset.mem_filter.mpr ⟨t.2, hboth'.1⟩⟩
    exact y.2.2 t' hboth'.2
  · intro x
    apply Subtype.ext
    exact cr.symm_apply_apply x.1
  · rintro ⟨u, z⟩
    have hp := cr.apply_symm_apply (u, z.1)
    have hp1 : (cr (cr.symm (u, z.1))).1 = u := congrArg Prod.fst hp
    have hp2 : (cr (cr.symm (u, z.1))).2 = z.1 := congrArg Prod.snd hp
    apply Sigma.ext hp1
    refine (Subtype.heq_iff_coe_eq ?_).2 hp2
    intro x
    simp only [survivingShifts]
    have hset :
        (Finset.Icc 1 h).filter (fun t : ℕ ↦
          IsUnit ((cr (cr.symm (u, z.1))).1 + (t : ZMod s))) =
        (Finset.Icc 1 h).filter (fun t : ℕ ↦ IsUnit (u + (t : ZMod s))) := by
      exact congrArg (fun w : ZMod s ↦
        (Finset.Icc 1 h).filter (fun t : ℕ ↦ IsUnit (w + (t : ZMod s)))) hp1
    exact eq_iff_iff.mp (congrArg (fun U : Finset ℕ ↦
      ∀ t : ↑U, ¬IsUnit (x + (t.1 : ZMod v))) hset)

theorem shiftedNonunitCount_mul_eq_sum (s v h : ℕ) [NeZero s] [NeZero v]
    (hs : 0 < s) (hv : 0 < v) (hcop : s.Coprime v) :
    shiftedNonunitCount (s * v) (Finset.Icc 1 h) =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
  change Nat.card {x : ZMod (s * v) //
      ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} = _
  calc
    Nat.card {x : ZMod (s * v) //
        ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} =
        Nat.card (Σ u : ZMod s,
          {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
            ¬IsUnit (z + (t.1 : ZMod v))}) :=
      Nat.card_congr (emptyCrtEquiv s v h hcop)
    _ = ∑ u : ZMod s, Nat.card
        {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
          ¬IsUnit (z + (t.1 : ZMod v))} := Nat.card_sigma
    _ = ∑ u : ZMod s, shiftedNonunitCount v
        (survivingShifts s h u) := rfl

/-- Exact conditional-count identity behind the smooth--rough argument. -/
theorem card_emptyWindows_mul_eq_sum {s v : ℕ} (hs : 0 < s) (hv : 0 < v)
    [NeZero s] [NeZero v] (hcop : s.Coprime v) (h : ℕ) :
    (emptyWindows (s * v) h).card =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
  rw [card_emptyWindows_eq_shiftedNonunitCount (mul_pos hs hv),
    shiftedNonunitCount_mul_eq_sum s v h hs hv hcop]

/-! ## Two elementary analytic inequalities used in the good/bad split -/

lemma one_sub_pow_le_exp_neg_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a : ℕ) :
    (1 - x) ^ a ≤ Real.exp (-(a * x)) := by
  have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbase : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  calc
    (1 - x) ^ a ≤ Real.exp (-x) ^ a := pow_le_pow_left₀ hbase0 hbase a
    _ = Real.exp (-(a * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- The uniform polynomial form of exponential decay used for good smooth
residue classes. -/
lemma sq_mul_exp_neg_le_two (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 2 := by
  have hseries := Real.pow_div_factorial_le_exp x hx 2
  norm_num [Nat.factorial] at hseries
  have hexp : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ hexp]
  nlinarith

lemma pow_decay_mul_sq_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a : ℕ) :
    (1 - x) ^ a * ((a : ℝ) * x) ^ 2 ≤ 2 := by
  have hdecay := one_sub_pow_le_exp_neg_mul hx0 hx1 a
  have hax0 : 0 ≤ (a : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0
  calc
    (1 - x) ^ a * ((a : ℝ) * x) ^ 2 ≤
        Real.exp (-((a : ℝ) * x)) * ((a : ℝ) * x) ^ 2 := by
      gcongr
    _ ≤ 2 := by
      simpa [mul_comm] using sq_mul_exp_neg_le_two ((a : ℝ) * x) hax0

/-! ## The large-prime pointwise estimate -/

lemma shiftedNonunitCount_le_modulus {v : ℕ} (hv : 0 < v) (A : Finset ℕ) :
    shiftedNonunitCount v A ≤ v := by
  rw [shiftedNonunitCount_eq_noncoprime hv, shiftedNoncoprimeResidueCount]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range v)

/-- Multiplying the large-prime density estimate by the square of its
conditional mean removes all dependence on the number of surviving shifts. -/
lemma largePrime_count_mean_sq_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hv : 0 < v) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    (shiftedNonunitCount v A : ℝ) *
        ((A.card : ℝ) * density v) ^ 2 ≤ 2 * v := by
  have hdQ := squarefree_largePrime_density_le A hA hsq hlarge
  have hdR : (shiftedNonunitCount v A : ℝ) / v ≤
      (1 - (v.totient : ℝ) / v) ^ A.card := by
    have hdCast :
        ((((shiftedNonunitCount v A : ℚ) / v : ℚ) : ℝ)) ≤
          ((((1 - (v.totient : ℚ) / v) ^ A.card : ℚ) : ℝ)) := by
      exact_mod_cast hdQ
    norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow] at hdCast
    exact hdCast
  have hdR' : (shiftedNonunitCount v A : ℝ) / v ≤
      (1 - density v) ^ A.card := by
    simpa only [density] using hdR
  have hdecay := pow_decay_mul_sq_le_two
    (x := density v) (density_pos hv).le (density_le_one v) A.card
  have hprob : (shiftedNonunitCount v A : ℝ) / v *
      ((A.card : ℝ) * density v) ^ 2 ≤ 2 :=
    (mul_le_mul_of_nonneg_right hdR' (sq_nonneg _)).trans hdecay
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  calc
    (shiftedNonunitCount v A : ℝ) * ((A.card : ℝ) * density v) ^ 2 =
        (v : ℝ) * ((shiftedNonunitCount v A : ℝ) / v *
          ((A.card : ℝ) * density v) ^ 2) := by field_simp
    _ ≤ (v : ℝ) * 2 := mul_le_mul_of_nonneg_left hprob hvR.le
    _ = 2 * v := by ring

/-- A smooth residue with at least half the expected number of surviving
shifts contributes at most `8*v` after the natural mean-square weighting. -/
lemma largePrime_good_residue_le {s v h : ℕ} [NeZero s]
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 h) (hv : 0 < v)
    (hsq : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p)
    (hgood : (h : ℝ) * density s / 2 ≤ A.card) :
    (shiftedNonunitCount v A : ℝ) *
        ((h : ℝ) * (density s * density v)) ^ 2 ≤ 8 * v := by
  have hpoint := largePrime_count_mean_sq_le A hA hv hsq hlarge
  have hds0 : 0 ≤ density s := (density_pos (NeZero.pos s)).le
  have hdv0 : 0 ≤ density v := (density_pos hv).le
  have hleft0 : 0 ≤ (h : ℝ) * (density s * density v) := by positivity
  have hright0 : 0 ≤ 2 * ((A.card : ℝ) * density v) := by positivity
  have hmean : (h : ℝ) * (density s * density v) ≤
      2 * ((A.card : ℝ) * density v) := by
    have hm := mul_le_mul_of_nonneg_right hgood hdv0
    nlinarith
  have hsquare : ((h : ℝ) * (density s * density v)) ^ 2 ≤
      (2 * ((A.card : ℝ) * density v)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmean) (add_nonneg hright0 hleft0)]
  calc
    (shiftedNonunitCount v A : ℝ) *
          ((h : ℝ) * (density s * density v)) ^ 2 ≤
        (shiftedNonunitCount v A : ℝ) *
          (2 * ((A.card : ℝ) * density v)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 4 * ((shiftedNonunitCount v A : ℝ) *
          ((A.card : ℝ) * density v) ^ 2) := by ring
    _ ≤ 4 * (2 * v) := mul_le_mul_of_nonneg_left hpoint (by norm_num)
    _ = 8 * v := by ring

/-! ## Good/bad residue summation -/

/-- Canonical representatives identify a filtered set of residues modulo
`s` with the corresponding filter of `range s`. -/
lemma card_filter_zmod_val_eq_range {s : ℕ} [NeZero s]
    (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (ZMod s)).filter (fun u ↦ P u.val)).card =
      ((Finset.range s).filter P).card := by
  classical
  refine Finset.card_bij (fun u _hu ↦ u.val) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.val_lt, hu⟩
  · intro u₁ hu₁ u₂ hu₂ heq
    exact ZMod.val_injective s heq
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    refine ⟨(a : ZMod s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp ha'.1)]
      exact ha'.2
    · exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha'.1)

lemma bad_residue_sum_le {α : Type*} [Fintype α] {B d : ℝ} {s v h : ℕ}
    (hv : 0 < v) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (bad : Finset α)
    (A : α → Finset ℕ)
    (htail : (bad.card : ℝ) * (h : ℝ) ^ 2 ≤ B * s) :
    (∑ u ∈ bad, (shiftedNonunitCount v (A u) : ℝ) *
      ((h : ℝ) * d) ^ 2) ≤ B * s * v := by
  have hweight0 : 0 ≤ ((h : ℝ) * d) ^ 2 := sq_nonneg _
  have hweight : ((h : ℝ) * d) ^ 2 ≤ (h : ℝ) ^ 2 := by
    have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
    have hmul : (h : ℝ) * d ≤ (h : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hd1 hh0
    simpa using pow_le_pow_left₀ (mul_nonneg hh0 hd0) hmul 2
  calc
    (∑ u ∈ bad, (shiftedNonunitCount v (A u) : ℝ) *
        ((h : ℝ) * d) ^ 2) ≤
        ∑ _u ∈ bad, (v : ℝ) * (h : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul
        (by exact_mod_cast shiftedNonunitCount_le_modulus hv (A u))
        hweight hweight0 (Nat.cast_nonneg _)
    _ = (v : ℝ) * ((bad.card : ℝ) * (h : ℝ) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ (v : ℝ) * (B * s) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = B * s * v := by ring

lemma good_residue_sum_le {s v h : ℕ} [NeZero s] (hv : 0 < v)
    (vsquare : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p)
    (good : Finset (ZMod s))
    (hgood : ∀ u ∈ good, (h : ℝ) * density s / 2 ≤
      (survivingShifts s h u).card) :
    (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
      ((h : ℝ) * (density s * density v)) ^ 2) ≤ 8 * s * v := by
  calc
    (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * (density s * density v)) ^ 2) ≤
        ∑ _u ∈ good, (8 : ℝ) * v := by
      apply Finset.sum_le_sum
      intro u hu
      exact largePrime_good_residue_le (s := s) (survivingShifts s h u)
        (survivingShifts_subset s h u) hv vsquare hlarge (hgood u hu)
    _ = (good.card : ℝ) * ((8 : ℝ) * v) := by simp
    _ ≤ (s : ℝ) * ((8 : ℝ) * v) := by
      gcongr
      exact_mod_cast (Finset.card_le_univ good).trans_eq (by simp)
    _ = 8 * s * v := by ring

/-- The complete smooth--rough assembly for a squarefree modulus, assuming
only the lower-tail consequence of the small-prime moment estimate. -/
theorem squarefree_emptyWindows_bound_of_lowerTail {B : ℝ} (hB0 : 0 ≤ B)
    (hLower : ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) * h ^ 2 ≤
          B * s)
    {r h : ℕ} (hr : 0 < r) (hrsq : Squarefree r) (hh : 1 ≤ h) :
    ((emptyWindows r h).card : ℝ) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2 ≤
      (B + 8) * (r : ℝ) ^ 3 := by
  classical
  let s := smoothPart r h
  let v := roughPart r h
  have hs : 0 < s := by simpa only [s] using smoothPart_pos r h
  have hv : 0 < v := by simpa only [v] using roughPart_pos r h
  let : NeZero s := ⟨hs.ne'⟩
  let : NeZero v := ⟨hv.ne'⟩
  have hsquare : Squarefree s := by
    simpa only [s] using squarefree_smoothPart (h := h) hrsq
  have vsquare : Squarefree v := by
    simpa only [v] using squarefree_roughPart (h := h) hrsq
  have hcop : s.Coprime v := by
    simpa only [s, v] using smoothPart_coprime_roughPart (h := h) hrsq
  have hrprod : s * v = r := by
    simpa only [s, v] using smoothPart_mul_roughPart (h := h) hrsq
  have hsmooth : ∀ p ∈ s.primeFactors, p ≤ h := by
    intro p hp
    simpa only [s] using smoothPart_prime_le (h := h) hp
  have hlarge : ∀ p ∈ v.primeFactors, h < p := by
    intro p hp
    simpa only [v] using roughPart_prime_gt (h := h) hp
  have hdensity : density r = density s * density v := by
    simpa only [s, v] using density_smoothPart_mul_roughPart (h := h) hrsq
  let bad : Finset (ZMod s) := Finset.univ.filter fun u ↦
    (unitCount s h u.val : ℝ) < (h : ℝ) * density s / 2
  let good : Finset (ZMod s) := Finset.univ.filter fun u ↦ u ∉ bad
  have hbadCard : bad.card =
      ((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card := by
    dsimp only [bad]
    exact card_filter_zmod_val_eq_range (s := s)
      (fun u : ℕ ↦ (unitCount s h u : ℝ) < (h : ℝ) * density s / 2)
  have htail : (bad.card : ℝ) * (h : ℝ) ^ 2 ≤ B * s := by
    rw [hbadCard]
    exact hLower hs hsquare hh hsmooth
  have hbadSum := bad_residue_sum_le hv (density_pos hr).le
    (density_le_one r) bad (fun u ↦ survivingShifts s h u) htail
  have hgoodPoint : ∀ u ∈ good, (h : ℝ) * density s / 2 ≤
      (survivingShifts s h u).card := by
    intro u hu
    have hubad : u ∉ bad := (Finset.mem_filter.mp hu).2
    rw [card_survivingShifts_eq_unitCount]
    exact le_of_not_gt (by
      simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hubad)
  have hgoodSum := good_residue_sum_le hv vsquare hlarge good hgoodPoint
  have hgoodSum' :
      (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * density r) ^ 2) ≤ 8 * s * v := by
    simpa only [hdensity] using hgoodSum
  have hcount : (emptyWindows r h).card =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
    rw [← hrprod]
    exact card_emptyWindows_mul_eq_sum hs hv hcop h
  have hsplit :
      (∑ u : ZMod s,
        (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2) =
      (∑ u ∈ bad, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2) +
      ∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (ZMod s)))
      (p := fun u ↦ u ∈ bad)
      (f := fun u ↦ (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * density r) ^ 2)]
    have hfilterBad : (Finset.univ : Finset (ZMod s)).filter
        (fun u ↦ u ∈ bad) = bad := by ext u; simp
    rw [hfilterBad]
  have hprob : ((emptyWindows r h).card : ℝ) *
      ((h : ℝ) * density r) ^ 2 ≤ (B + 8) * r := by
    calc
      ((emptyWindows r h).card : ℝ) * ((h : ℝ) * density r) ^ 2 =
          (∑ u : ZMod s,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ)) *
              ((h : ℝ) * density r) ^ 2 := by
        simp only [hcount, Nat.cast_sum]
      _ = ∑ u : ZMod s,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2 := by rw [Finset.sum_mul]
      _ = (∑ u ∈ bad,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2) +
          ∑ u ∈ good,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2 := hsplit
      _ ≤ B * s * v + 8 * s * v := add_le_add hbadSum hgoodSum'
      _ = (B + 8) * r := by rw [← hrprod]; push_cast; ring
  have hscaled := mul_le_mul_of_nonneg_right hprob (sq_nonneg (r : ℝ))
  calc
    ((emptyWindows r h).card : ℝ) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2 =
        (((emptyWindows r h).card : ℝ) *
          ((h : ℝ) * density r) ^ 2) * (r : ℝ) ^ 2 := by
      rw [density]
      field_simp
    _ ≤ ((B + 8) * (r : ℝ)) * (r : ℝ) ^ 2 := hscaled
    _ = (B + 8) * (r : ℝ) ^ 3 := by ring

/-- The small-prime sixth-moment estimate, together with the finite
smooth--rough argument above, gives the desired empty-window estimate for
every positive modulus. -/
theorem exists_emptyWindows_bound_of_sixthMomentBound {A : ℝ}
    (hA : SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 := by
  obtain ⟨C, hC, hLower⟩ := smallPrime_lowerTail_of_sixthMomentBound hA
  refine ⟨C + 8, by positivity, ?_⟩
  intro n h hn hh
  apply emptyWindows_bound_of_kernel hn
  exact squarefree_emptyWindows_bound_of_lowerTail hC.le hLower
    (squarefreeKernel_pos hn) (squarefree_squarefreeKernel n) hh

theorem exists_emptyWindows_bound_of_exists_sixthMomentBound
    (hMoment : ∃ A : ℝ, SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 := by
  obtain ⟨A, hA⟩ := hMoment
  exact exists_emptyWindows_bound_of_sixthMomentBound hA

/-- The unconditional uniform empty-window estimate used in the gap
deduction. -/
theorem exists_emptyWindows_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 :=
  exists_emptyWindows_bound_of_exists_sixthMomentBound
    exists_smallPrimeSixthMomentBound

end Erdos220
