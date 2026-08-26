/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionKernelTransform
import BoundedGaps.Maynard.ImprovedGPY.S2TauMean

/-!
# Prime-edge majorants for the transformed collision kernel

Every squarefree matching auxiliary matrix is determined by the finite set
of pairs `(p, ba)` saying that the prime `p` occurs on the matrix edge `ba`.
This file makes that encoding injective and bounds an arbitrary nonnegative
multiplicative matrix weight by the corresponding finite Euler product.
The argument deliberately enlarges the image to the whole powerset; allowing
the same prime on several edges only makes the upper bound larger.
-/

namespace Erdos4b

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

noncomputable local instance generalCollisionKernelBoundDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- All prime/edge labels available below the scalar cutoff `Q`. -/
def crossAuxiliaryPrimeEdgeUniverse
    (H : Finset ℕ) (Q : ℕ) : Finset (ℕ × (H × H)) :=
  Nat.primesLE Q ×ˢ (Finset.univ : Finset (H × H))

/-- Prime/edge incidence set of one auxiliary value matrix. -/
def crossAuxiliaryPrimeIncidence
    {H : Finset ℕ} (Q : ℕ) (A : CrossAuxiliaryValueMatrix H) :
    Finset (ℕ × (H × H)) :=
  (crossAuxiliaryPrimeEdgeUniverse H Q).filter fun x ↦ x.1 ∣ A x.2

@[simp] theorem mem_crossAuxiliaryPrimeEdgeUniverse_iff
    {H : Finset ℕ} {Q p : ℕ} {ba : H × H} :
    (p, ba) ∈ crossAuxiliaryPrimeEdgeUniverse H Q ↔
      p ≤ Q ∧ p.Prime := by
  simp [crossAuxiliaryPrimeEdgeUniverse, Nat.mem_primesLE]

@[simp] theorem mem_crossAuxiliaryPrimeIncidence_iff
    {H : Finset ℕ} {Q p : ℕ} {A : CrossAuxiliaryValueMatrix H}
    {ba : H × H} :
    (p, ba) ∈ crossAuxiliaryPrimeIncidence Q A ↔
      p ≤ Q ∧ p.Prime ∧ p ∣ A ba := by
  simp [crossAuxiliaryPrimeIncidence, and_assoc]

theorem crossAuxiliaryPrimeIncidence_subset_universe
    {H : Finset ℕ} (Q : ℕ) (A : CrossAuxiliaryValueMatrix H) :
    crossAuxiliaryPrimeIncidence Q A ⊆
      crossAuxiliaryPrimeEdgeUniverse H Q := by
  exact Finset.filter_subset _ _

/-- Every prime factor of a positive entry strictly below `Q` occurs in the
prime-edge universe with cutoff `Q`. -/
theorem prime_le_cutoff_of_dvd_crossAuxiliary_entry
    {H : Finset ℕ} {Q p : ℕ} {A : CrossAuxiliaryValueMatrix H}
    {ba : H × H} (hpos : 0 < A ba) (hle : A ba ≤ Q)
    (hp : p.Prime) (hpA : p ∣ A ba) : p ≤ Q := by
  exact (Nat.le_of_dvd hpos hpA).trans hle

/-- The incidence encoding is injective on the squarefree matrix box. -/
theorem crossAuxiliaryPrimeIncidence_injOn_squarefreeBox
    (H : Finset ℕ) (Q : ℕ) :
    Set.InjOn (crossAuxiliaryPrimeIncidence (H := H) Q)
      (crossAuxiliarySquarefreeValueMatrixBox H Q :
        Set (CrossAuxiliaryValueMatrix H)) := by
  intro A hA B hB hinc
  have hAData := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA
  have hBData := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hB
  funext ba
  rw [Nat.Squarefree.ext_iff (hAData.2 ba) (hBData.2 ba)]
  intro p hp
  constructor
  · intro hpA
    have hpQ := prime_le_cutoff_of_dvd_crossAuxiliary_entry
      (hAData.1 ba).1 (hAData.1 ba).2 hp hpA
    have hmemA : (p, ba) ∈ crossAuxiliaryPrimeIncidence Q A :=
      mem_crossAuxiliaryPrimeIncidence_iff.mpr ⟨hpQ, hp, hpA⟩
    have hmemB : (p, ba) ∈ crossAuxiliaryPrimeIncidence Q B := by
      rw [← hinc]
      exact hmemA
    exact (mem_crossAuxiliaryPrimeIncidence_iff.mp hmemB).2.2
  · intro hpB
    have hpQ := prime_le_cutoff_of_dvd_crossAuxiliary_entry
      (hBData.1 ba).1 (hBData.1 ba).2 hp hpB
    have hmemB : (p, ba) ∈ crossAuxiliaryPrimeIncidence Q B :=
      mem_crossAuxiliaryPrimeIncidence_iff.mpr ⟨hpQ, hp, hpB⟩
    have hmemA : (p, ba) ∈ crossAuxiliaryPrimeIncidence Q A := by
      rw [hinc]
      exact hmemB
    exact (mem_crossAuxiliaryPrimeIncidence_iff.mp hmemA).2.2

/-- The incidence encoding remains injective after restriction to matching
matrices. -/
theorem crossAuxiliaryPrimeIncidence_injOn_matchingBox
    (H : Finset ℕ) (Q : ℕ) :
    Set.InjOn (crossAuxiliaryPrimeIncidence (H := H) Q)
      (crossAuxiliaryMatchingValueMatrixBox H Q :
        Set (CrossAuxiliaryValueMatrix H)) := by
  apply (crossAuxiliaryPrimeIncidence_injOn_squarefreeBox H Q).mono
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- A prime-product over all entries is exactly the product over the
prime-edge incidence set. -/
theorem prod_entryPrimeFactors_eq_prod_primeIncidence
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (f : ℕ → H × H → ℝ) :
    (∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p ba) =
      ∏ x ∈ crossAuxiliaryPrimeIncidence Q A, f x.1 x.2 := by
  classical
  have hAData := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA
  have hfactorSet : ∀ ba : H × H,
      (A ba).primeFactors =
        (Nat.primesLE Q).filter (fun p ↦ p ∣ A ba) := by
    intro ba
    ext p
    constructor
    · intro hpMem
      have hp := Nat.prime_of_mem_primeFactors hpMem
      have hpA := Nat.dvd_of_mem_primeFactors hpMem
      have hpQ := prime_le_cutoff_of_dvd_crossAuxiliary_entry
        (hAData.1 ba).1 (hAData.1 ba).2 hp hpA
      simp [Nat.mem_primesLE, hpQ, hp, hpA]
    · intro hpMem
      have hpData := Finset.mem_filter.mp hpMem
      exact Nat.mem_primeFactors.mpr ⟨
        (Nat.mem_primesLE.mp hpData.1).2, hpData.2, (hAData.1 ba).1.ne'⟩
  simp_rw [hfactorSet]
  unfold crossAuxiliaryPrimeIncidence crossAuxiliaryPrimeEdgeUniverse
  rw [Finset.prod_filter]
  rw [Finset.prod_product]
  simp only [Finset.mem_product, Finset.mem_univ, and_true]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro ba hba
  rw [Finset.prod_filter]

/-- Weight of an arbitrary finite set of prime-edge labels. -/
noncomputable def crossPrimeEdgeSetWeight
    {H : Finset ℕ} (f : ℕ → H × H → ℝ)
    (S : Finset (ℕ × (H × H))) : ℝ :=
  ∏ x ∈ S, f x.1 x.2

theorem crossPrimeEdgeSetWeight_nonneg
    {H : Finset ℕ} {f : ℕ → H × H → ℝ}
    (hf : ∀ p ba, 0 ≤ f p ba)
    (S : Finset (ℕ × (H × H))) :
    0 ≤ crossPrimeEdgeSetWeight f S := by
  unfold crossPrimeEdgeSetWeight
  exact Finset.prod_nonneg fun x hx ↦ hf x.1 x.2

/-- Generic finite Euler-product majorant for matching squarefree matrices.
No arithmetic property of `f` is required beyond nonnegativity. -/
theorem sum_matchingMatrix_primeProducts_le_eulerProduct
    {H : Finset ℕ} {Q : ℕ} (f : ℕ → H × H → ℝ)
    (hf : ∀ p ba, 0 ≤ f p ba) :
    (∑ A ∈ crossAuxiliaryMatchingValueMatrixBox H Q,
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p ba) ≤
      ∏ x ∈ crossAuxiliaryPrimeEdgeUniverse H Q,
        (1 + f x.1 x.2) := by
  classical
  let box := crossAuxiliaryMatchingValueMatrixBox H Q
  let U := crossAuxiliaryPrimeEdgeUniverse H Q
  let incidence : CrossAuxiliaryValueMatrix H →
      Finset (ℕ × (H × H)) := crossAuxiliaryPrimeIncidence Q
  let weight : Finset (ℕ × (H × H)) → ℝ :=
    crossPrimeEdgeSetWeight f
  have hinj : Set.InjOn incidence box :=
    crossAuxiliaryPrimeIncidence_injOn_matchingBox H Q
  have himage : box.image incidence ⊆ U.powerset := by
    intro S hS
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.mem_powerset]
    exact crossAuxiliaryPrimeIncidence_subset_universe Q A
  calc
    (∑ A ∈ box,
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p ba) =
        ∑ A ∈ box, weight (incidence A) := by
      apply Finset.sum_congr rfl
      intro A hA
      dsimp [weight, incidence]
      have hAsq : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q := by
        exact (Finset.mem_filter.mp (show A ∈
          crossAuxiliaryMatchingValueMatrixBox H Q by simpa [box] using hA)).1
      exact prod_entryPrimeFactors_eq_prod_primeIncidence hAsq f
    _ = ∑ S ∈ box.image incidence, weight S := by
      exact (Finset.sum_image (f := weight) hinj).symm
    _ ≤ ∑ S ∈ U.powerset, weight S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro S hS hSNot
      exact crossPrimeEdgeSetWeight_nonneg hf S
    _ = ∏ x ∈ U, (f x.1 x.2 + 1) := by
      rw [Finset.prod_add (fun x ↦ f x.1 x.2) (fun _ ↦ (1 : ℝ)) U]
      apply Finset.sum_congr rfl
      intro S hS
      unfold weight crossPrimeEdgeSetWeight
      simp
    _ = ∏ x ∈ U, (1 + f x.1 x.2) := by
      apply Finset.prod_congr rfl
      intro x hx
      ring

/-- Product of all ordinary off-diagonal cross variables. -/
def crossTupleValueProduct
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) : ℕ :=
  ∏ x ∈ (BoundedGaps.Maynard.offDiagonalPairs H).attach, s x.1 x.2

/-! ## Prime incidence for the ordinary common/cross base -/

/-- A label is either one common coordinate or one off-diagonal cross
coordinate. -/
abbrev CrossBaseLabel (H : Finset ℕ) :=
  Sum H ↑(BoundedGaps.Maynard.offDiagonalPairs H)

/-- Value carried by a common/cross base label. -/
def crossBaseLabelValue
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : CrossBaseLabel H → ℕ
  | Sum.inl h => u h
  | Sum.inr ab => s ab.1 ab.2

/-- The product over the disjoint label type is exactly the ordinary base
product used by the prime charge. -/
theorem prod_crossBaseLabelValue
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) :
    (∏ i : CrossBaseLabel H, crossBaseLabelValue s u i) =
      (∏ h : H, u h) * crossTupleValueProduct s := by
  rw [Fintype.prod_sum_type]
  congr 1

/-- Finite box of ordinary base tuples whose complete value product is
squarefree.  This is precisely the support retained by the transformed
kernel bound. -/
def squarefreeCrossBaseTupleBox (H : Finset ℕ) (R : ℕ) :
    Finset
      ((∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)) :=
  (BoundedGaps.Maynard.crossMoebiusTupleBox H R ×ˢ
      BoundedGaps.Maynard.maynardDivisorTupleBox H R).filter fun su ↦
    Squarefree ((∏ h : H, su.2 h) * crossTupleValueProduct su.1)

@[simp] theorem mem_squarefreeCrossBaseTupleBox_iff
    {H : Finset ℕ} {R : ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {u : H → ℕ} :
    (s, u) ∈ squarefreeCrossBaseTupleBox H R ↔
      s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R ∧
      u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R ∧
      Squarefree ((∏ h : H, u h) * crossTupleValueProduct s) := by
  simp only [squarefreeCrossBaseTupleBox, Finset.mem_filter,
    Finset.mem_product]
  tauto

/-- Prime/label universe for the ordinary base. -/
def crossBasePrimeLabelUniverse
    (H : Finset ℕ) (Q : ℕ) : Finset (ℕ × CrossBaseLabel H) :=
  Nat.primesLE Q ×ˢ (Finset.univ : Finset (CrossBaseLabel H))

/-- Prime incidence set of one ordinary base tuple. -/
def crossBasePrimeIncidence
    {H : Finset ℕ} (Q : ℕ)
    (su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)) : Finset (ℕ × CrossBaseLabel H) :=
  (crossBasePrimeLabelUniverse H Q).filter fun pi ↦
    pi.1 ∣ crossBaseLabelValue su.1 su.2 pi.2

@[simp] theorem mem_crossBasePrimeIncidence_iff
    {H : Finset ℕ} {Q p : ℕ} {i : CrossBaseLabel H}
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)} :
    (p, i) ∈ crossBasePrimeIncidence Q su ↔
      p ≤ Q ∧ p.Prime ∧ p ∣ crossBaseLabelValue su.1 su.2 i := by
  simp [crossBasePrimeIncidence, crossBasePrimeLabelUniverse,
    Nat.mem_primesLE, and_assoc]

theorem crossBasePrimeIncidence_subset_universe
    {H : Finset ℕ} (Q : ℕ)
    (su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)) :
    crossBasePrimeIncidence Q su ⊆ crossBasePrimeLabelUniverse H Q :=
  Finset.filter_subset _ _

theorem crossBaseLabelValue_pos_of_mem_squarefreeBox
    {H : Finset ℕ} {R : ℕ}
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsu : su ∈ squarefreeCrossBaseTupleBox H R)
    (i : CrossBaseLabel H) :
    0 < crossBaseLabelValue su.1 su.2 i := by
  have hdata := mem_squarefreeCrossBaseTupleBox_iff.mp hsu
  rcases i with h | ab
  · exact (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp
      hdata.2.1 h).1
  · have hsab := (Finset.mem_pi.mp hdata.1) ab.1 ab.2
    exact (Finset.mem_Icc.mp hsab).1

theorem crossBaseLabelValue_le_of_mem_squarefreeBox
    {H : Finset ℕ} {R : ℕ}
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsu : su ∈ squarefreeCrossBaseTupleBox H R)
    (i : CrossBaseLabel H) :
    crossBaseLabelValue su.1 su.2 i ≤ R := by
  have hdata := mem_squarefreeCrossBaseTupleBox_iff.mp hsu
  rcases i with h | ab
  · exact (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp
      hdata.2.1 h).2.le
  · have hsab := (Finset.mem_pi.mp hdata.1) ab.1 ab.2
    exact (Finset.mem_Icc.mp hsab).2

theorem crossBaseLabelValue_dvd_baseProduct
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) (i : CrossBaseLabel H) :
    crossBaseLabelValue s u i ∣
      (∏ h : H, u h) * crossTupleValueProduct s := by
  rw [← prod_crossBaseLabelValue s u]
  exact Finset.dvd_prod_of_mem (crossBaseLabelValue s u)
    (Finset.mem_univ i)

/-- On the squarefree base box, the prime-incidence encoding determines all
common and cross values. -/
theorem crossBasePrimeIncidence_injOn_squarefreeBox
    (H : Finset ℕ) {R Q : ℕ} (hRQ : R ≤ Q) :
    Set.InjOn (crossBasePrimeIncidence (H := H) Q)
      (squarefreeCrossBaseTupleBox H R : Set
        ((∀ ab : H × H,
            ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
          (H → ℕ))) := by
  intro su hsu tv htv hinc
  have hval : ∀ i : CrossBaseLabel H,
      crossBaseLabelValue su.1 su.2 i =
        crossBaseLabelValue tv.1 tv.2 i := by
    intro i
    have hsuData := mem_squarefreeCrossBaseTupleBox_iff.mp hsu
    have htvData := mem_squarefreeCrossBaseTupleBox_iff.mp htv
    have hsqSu := hsuData.2.2.squarefree_of_dvd
      (crossBaseLabelValue_dvd_baseProduct su.1 su.2 i)
    have hsqTv := htvData.2.2.squarefree_of_dvd
      (crossBaseLabelValue_dvd_baseProduct tv.1 tv.2 i)
    rw [Nat.Squarefree.ext_iff hsqSu hsqTv]
    intro p hp
    constructor
    · intro hpSu
      have hpQ : p ≤ Q :=
        (Nat.le_of_dvd
          (crossBaseLabelValue_pos_of_mem_squarefreeBox hsu i) hpSu).trans
            ((crossBaseLabelValue_le_of_mem_squarefreeBox hsu i).trans hRQ)
      have hmemSu : (p, i) ∈ crossBasePrimeIncidence Q su :=
        mem_crossBasePrimeIncidence_iff.mpr ⟨hpQ, hp, hpSu⟩
      have hmemTv : (p, i) ∈ crossBasePrimeIncidence Q tv := by
        rw [← hinc]
        exact hmemSu
      exact (mem_crossBasePrimeIncidence_iff.mp hmemTv).2.2
    · intro hpTv
      have hpQ : p ≤ Q :=
        (Nat.le_of_dvd
          (crossBaseLabelValue_pos_of_mem_squarefreeBox htv i) hpTv).trans
            ((crossBaseLabelValue_le_of_mem_squarefreeBox htv i).trans hRQ)
      have hmemTv : (p, i) ∈ crossBasePrimeIncidence Q tv :=
        mem_crossBasePrimeIncidence_iff.mpr ⟨hpQ, hp, hpTv⟩
      have hmemSu : (p, i) ∈ crossBasePrimeIncidence Q su := by
        rw [hinc]
        exact hmemTv
      exact (mem_crossBasePrimeIncidence_iff.mp hmemSu).2.2
  apply Prod.ext
  · funext ab hab
    exact hval (Sum.inr ⟨ab, hab⟩)
  · funext h
    exact hval (Sum.inl h)

/-- Prime-local reciprocal weight of one ordinary base label.  Common
variables occur once in the denominator; cross variables occur twice. -/
noncomputable def crossBasePrimeWeight
    {H : Finset ℕ} (p : ℕ) : CrossBaseLabel H → ℝ
  | Sum.inl _ => (1 : ℝ) / Nat.totient p
  | Sum.inr _ => (1 : ℝ) / (Nat.totient p : ℝ) ^ 2

/-- Reciprocal weight of an ordinary common/cross tuple after the two base
totient copies have been simplified. -/
noncomputable def crossBaseReciprocalWeight
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : ℝ :=
  (1 : ℝ) /
    ((∏ h : H, (Nat.totient (u h) : ℝ)) *
      (BoundedGaps.Maynard.crossTotientProduct H s : ℝ) ^ 2)

/-- Squarefree ordinary-base weight with the totient of every constraint
prime absent from that base. -/
noncomputable def crossBaseConstraintWeight
    {H : Finset ℕ} (A : H → ℕ)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : ℝ :=
  let b := (∏ h : H, u h) * crossTupleValueProduct s
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  if Squarefree b then
    crossBaseReciprocalWeight s u *
      ((1 : ℝ) / Nat.totient (a / Nat.gcd a b))
  else 0

theorem inv_totient_eq_primeFactors_product
    {n : ℕ} (hn : Squarefree n) :
    (1 : ℝ) / Nat.totient n =
      ∏ p ∈ n.primeFactors, (1 : ℝ) / Nat.totient p := by
  rw [BoundedGaps.Maynard.totient_eq_prod_primeFactors_of_squarefree hn]
  push_cast
  simp only [one_div, Finset.prod_inv_distrib]

/-- The ordinary base reciprocal weight is the product of the prime-local
label weights over all prime incidences. -/
theorem crossBaseReciprocalWeight_eq_primeIncidenceProduct
    {H : Finset ℕ} {R Q : ℕ} (hRQ : R ≤ Q)
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {u : H → ℕ}
    (hsu : (s, u) ∈ squarefreeCrossBaseTupleBox H R) :
    crossBaseReciprocalWeight s u =
      ∏ pi ∈ crossBasePrimeIncidence Q (s, u),
        crossBasePrimeWeight pi.1 pi.2 := by
  have hdata := mem_squarefreeCrossBaseTupleBox_iff.mp hsu
  have hsqValue : ∀ i : CrossBaseLabel H,
      Squarefree (crossBaseLabelValue s u i) := fun i ↦
    hdata.2.2.squarefree_of_dvd
      (crossBaseLabelValue_dvd_baseProduct s u i)
  have hfactorSet : ∀ i : CrossBaseLabel H,
      (crossBaseLabelValue s u i).primeFactors =
        (Nat.primesLE Q).filter
          (fun p ↦ p ∣ crossBaseLabelValue s u i) := by
    intro i
    ext p
    constructor
    · intro hpMem
      have hp := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
      have hpQ := (Nat.le_of_dvd
        (crossBaseLabelValue_pos_of_mem_squarefreeBox hsu i) hpDvd).trans
          ((crossBaseLabelValue_le_of_mem_squarefreeBox hsu i).trans hRQ)
      simp [Nat.mem_primesLE, hpQ, hp, hpDvd]
    · intro hpMem
      have hpData := Finset.mem_filter.mp hpMem
      exact Nat.mem_primeFactors.mpr ⟨
        (Nat.mem_primesLE.mp hpData.1).2, hpData.2,
        (crossBaseLabelValue_pos_of_mem_squarefreeBox hsu i).ne'⟩
  have hprimeProduct :
      (∏ i : CrossBaseLabel H,
        ∏ p ∈ (crossBaseLabelValue s u i).primeFactors,
          crossBasePrimeWeight p i) =
        ∏ pi ∈ crossBasePrimeIncidence Q (s, u),
          crossBasePrimeWeight pi.1 pi.2 := by
    simp_rw [hfactorSet]
    unfold crossBasePrimeIncidence crossBasePrimeLabelUniverse
    rw [Finset.prod_filter, Finset.prod_product]
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.prod_filter]
  rw [← hprimeProduct]
  unfold crossBaseReciprocalWeight
  rw [Fintype.prod_sum_type]
  have hcommon :
      (∏ h : H,
        ∏ p ∈ (u h).primeFactors, crossBasePrimeWeight p (Sum.inl h)) =
        (1 : ℝ) / ∏ h : H, (Nat.totient (u h) : ℝ) := by
    calc
      _ = ∏ h : H, (1 : ℝ) / Nat.totient (u h) := by
        apply Finset.prod_congr rfl
        intro h hh
        change (∏ p ∈ (u h).primeFactors,
            (1 : ℝ) / Nat.totient p) = _
        exact (inv_totient_eq_primeFactors_product
          (hsqValue (Sum.inl h))).symm
      _ = _ := by
        simp only [one_div, Finset.prod_inv_distrib]
  have hcross :
      (∏ ab : ↑(BoundedGaps.Maynard.offDiagonalPairs H),
        ∏ p ∈ (s ab.1 ab.2).primeFactors,
          crossBasePrimeWeight p (Sum.inr ab)) =
        (1 : ℝ) /
          (BoundedGaps.Maynard.crossTotientProduct H s : ℝ) ^ 2 := by
    calc
      _ = ∏ ab : ↑(BoundedGaps.Maynard.offDiagonalPairs H),
          (1 : ℝ) / (Nat.totient (s ab.1 ab.2) : ℝ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro ab hab
        change (∏ p ∈ (s ab.1 ab.2).primeFactors,
            (1 : ℝ) / (Nat.totient p : ℝ) ^ 2) = _
        exact (BoundedGaps.Maynard.inv_totient_sq_eq_primeFactors_product
          (hsqValue (Sum.inr ab))).symm
      _ = _ := by
        unfold BoundedGaps.Maynard.crossTotientProduct
        push_cast
        simp only [Finset.univ_eq_attach]
        rw [← Finset.prod_pow]
        simp only [one_div, Finset.prod_inv_distrib]
  change (1 : ℝ) /
      ((∏ h : H, (Nat.totient (u h) : ℝ)) *
        (BoundedGaps.Maynard.crossTotientProduct H s : ℝ) ^ 2) =
    (∏ h : H,
      ∏ p ∈ (u h).primeFactors, crossBasePrimeWeight p (Sum.inl h)) *
    ∏ ab : ↑(BoundedGaps.Maynard.offDiagonalPairs H),
      ∏ p ∈ (s ab.1 ab.2).primeFactors,
        crossBasePrimeWeight p (Sum.inr ab)
  rw [hcommon, hcross]
  field_simp

theorem finset_pair_mul_dvd_prod_nat
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {f : ι → ℕ}
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    f i * f j ∣ ∏ x ∈ S, f x := by
  let T := S.erase i
  have hjT : j ∈ T := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hjDvd : f j ∣ ∏ x ∈ T, f x :=
    Finset.dvd_prod_of_mem f hjT
  obtain ⟨c, hc⟩ := hjDvd
  refine ⟨c, ?_⟩
  calc
    (∏ x ∈ S, f x) = (∏ x ∈ S.erase i, f x) * f i :=
      (Finset.prod_erase_mul S f hi).symm
    _ = f i * f j * c := by
      rw [show S.erase i = T by rfl, hc]
      ac_rfl

/-- Squarefreeness of the complete base product makes the totient fully
multiplicative across every common and cross label. -/
theorem totient_crossTupleBase_eq
    {H : Finset ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {u : H → ℕ}
    (hsq : Squarefree
      ((∏ h : H, u h) * crossTupleValueProduct s)) :
    Nat.totient ((∏ h : H, u h) * crossTupleValueProduct s) =
      (∏ h : H, Nat.totient (u h)) *
        BoundedGaps.Maynard.crossTotientProduct H s := by
  have hpair : Set.Pairwise
      ((Finset.univ : Finset (CrossBaseLabel H)) : Set (CrossBaseLabel H))
      (Function.onFun Nat.Coprime (crossBaseLabelValue s u)) := by
    intro i hi j hj hij
    apply Nat.coprime_of_squarefree_mul
    apply hsq.squarefree_of_dvd
    rw [← prod_crossBaseLabelValue s u]
    exact finset_pair_mul_dvd_prod_nat
      (Finset.mem_univ i) (Finset.mem_univ j) hij
  calc
    Nat.totient ((∏ h : H, u h) * crossTupleValueProduct s) =
        Nat.totient (∏ i : CrossBaseLabel H,
          crossBaseLabelValue s u i) := by
      rw [prod_crossBaseLabelValue]
    _ = ∏ i : CrossBaseLabel H,
          Nat.totient (crossBaseLabelValue s u i) := by
      exact BoundedGaps.Maynard.totient_finsetProd_of_pairwise_coprime
        Finset.univ (crossBaseLabelValue s u) hpair
    _ = (∏ h : H, Nat.totient (u h)) *
          BoundedGaps.Maynard.crossTotientProduct H s := by
      rw [Fintype.prod_sum_type]
      congr 1

/-- A squarefree base contains any fixed prime on at most one label. -/
theorem crossBasePrimeIncidence_fst_injOn
    {H : Finset ℕ} {Q : ℕ}
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsq : Squarefree
      ((∏ h : H, su.2 h) * crossTupleValueProduct su.1)) :
    Set.InjOn Prod.fst
      (crossBasePrimeIncidence Q su : Set (ℕ × CrossBaseLabel H)) := by
  rintro ⟨p, i⟩ hpi ⟨q, j⟩ hqj hpq
  dsimp only at hpq
  subst q
  have hpiData := mem_crossBasePrimeIncidence_iff.mp hpi
  have hpjData := mem_crossBasePrimeIncidence_iff.mp hqj
  have hij : i = j := by
    by_contra hij
    have hpairDvd :
        crossBaseLabelValue su.1 su.2 i *
            crossBaseLabelValue su.1 su.2 j ∣
          (∏ h : H, su.2 h) * crossTupleValueProduct su.1 := by
      rw [← prod_crossBaseLabelValue su.1 su.2]
      exact finset_pair_mul_dvd_prod_nat
        (Finset.mem_univ i) (Finset.mem_univ j) hij
    have hcop : (crossBaseLabelValue su.1 su.2 i).Coprime
        (crossBaseLabelValue su.1 su.2 j) :=
      Nat.coprime_of_squarefree_mul (hsq.squarefree_of_dvd hpairDvd)
    exact hpiData.2.1.ne_one
      (Nat.eq_one_of_dvd_coprimes hcop hpiData.2.2 hpjData.2.2)
  subst j
  rfl

/-- Incidences whose prime also divides a scalar constraint. -/
def crossBaseConstraintIncidence
    {H : Finset ℕ} (a Q : ℕ)
    (su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)) : Finset (ℕ × CrossBaseLabel H) :=
  (crossBasePrimeIncidence Q su).filter fun pi ↦ pi.1 ∣ a

/-- The prime projection of the constraint incidences is exactly the prime
support of `gcd(a,b)`. -/
theorem image_fst_crossBaseConstraintIncidence
    {H : Finset ℕ} {R Q a : ℕ} (hRQ : R ≤ Q) (ha : a ≠ 0)
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsu : su ∈ squarefreeCrossBaseTupleBox H R) :
    (crossBaseConstraintIncidence a Q su).image Prod.fst =
      (Nat.gcd a
        ((∏ h : H, su.2 h) * crossTupleValueProduct su.1)).primeFactors := by
  let b := (∏ h : H, su.2 h) * crossTupleValueProduct su.1
  have hsq := (mem_squarefreeCrossBaseTupleBox_iff.mp hsu).2.2
  have hb : b ≠ 0 := hsq.ne_zero
  ext p
  constructor
  · intro hpMem
    obtain ⟨pi, hpi, hpEq⟩ := Finset.mem_image.mp hpMem
    have hpiFilter := Finset.mem_filter.mp hpi
    have hpiData := mem_crossBasePrimeIncidence_iff.mp hpiFilter.1
    subst p
    have hpB : pi.1 ∣ b := by
      exact hpiData.2.2.trans
        (crossBaseLabelValue_dvd_baseProduct su.1 su.2 pi.2)
    exact Nat.mem_primeFactors.mpr
      ⟨hpiData.2.1, Nat.dvd_gcd hpiFilter.2 hpB,
        (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne'⟩
  · intro hpMem
    have hpData := Nat.mem_primeFactors.mp hpMem
    have hp := hpData.1
    have hpA : p ∣ a := hpData.2.1.trans (Nat.gcd_dvd_left a b)
    have hpB : p ∣ b := hpData.2.1.trans (Nat.gcd_dvd_right a b)
    change p ∣ (∏ h : H, su.2 h) * crossTupleValueProduct su.1 at hpB
    rw [← prod_crossBaseLabelValue su.1 su.2] at hpB
    obtain ⟨i, hi, hpVal⟩ := (hp.prime.dvd_finsetProd_iff
      (crossBaseLabelValue su.1 su.2)).mp hpB
    have hpQ : p ≤ Q :=
      (Nat.le_of_dvd
        (crossBaseLabelValue_pos_of_mem_squarefreeBox hsu i) hpVal).trans
          ((crossBaseLabelValue_le_of_mem_squarefreeBox hsu i).trans hRQ)
    have hpi : (p, i) ∈ crossBaseConstraintIncidence a Q su := by
      rw [crossBaseConstraintIncidence, Finset.mem_filter]
      exact ⟨mem_crossBasePrimeIncidence_iff.mpr
        ⟨hpQ, hp, hpVal⟩, hpA⟩
    exact Finset.mem_image.mpr ⟨(p, i), hpi, rfl⟩

/-- At a constraint prime, remove the outer reciprocal-totient factor from
the label weight. -/
noncomputable def crossBaseModifiedPrimeWeight
    {H : Finset ℕ} (a p : ℕ) (i : CrossBaseLabel H) : ℝ :=
  if p ∣ a then
    (Nat.totient p : ℝ) * crossBasePrimeWeight p i
  else crossBasePrimeWeight p i

/-- The modified incidence product is the ordinary reciprocal base weight
times the totient of the overlap with the constraint. -/
theorem prod_crossBaseModifiedPrimeWeight_eq
    {H : Finset ℕ} {R Q a : ℕ} (hRQ : R ≤ Q)
    (ha : Squarefree a)
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsu : su ∈ squarefreeCrossBaseTupleBox H R) :
    (∏ pi ∈ crossBasePrimeIncidence Q su,
        crossBaseModifiedPrimeWeight a pi.1 pi.2) =
      crossBaseReciprocalWeight su.1 su.2 *
        (Nat.totient (Nat.gcd a
          ((∏ h : H, su.2 h) * crossTupleValueProduct su.1)) : ℝ) := by
  let S := crossBasePrimeIncidence Q su
  let T := crossBaseConstraintIncidence a Q su
  let b := (∏ h : H, su.2 h) * crossTupleValueProduct su.1
  have hsq := (mem_squarefreeCrossBaseTupleBox_iff.mp hsu).2.2
  have hinj : Set.InjOn Prod.fst (T : Set (ℕ × CrossBaseLabel H)) := by
    apply (crossBasePrimeIncidence_fst_injOn hsq).mono
    exact Finset.filter_subset _ _
  have himage : T.image Prod.fst = (Nat.gcd a b).primeFactors := by
    exact image_fst_crossBaseConstraintIncidence hRQ ha.ne_zero hsu
  have hbase := crossBaseReciprocalWeight_eq_primeIncidenceProduct
    hRQ hsu
  have hgSq : Squarefree (Nat.gcd a b) :=
    ha.squarefree_of_dvd (Nat.gcd_dvd_left a b)
  have htotG : (Nat.totient (Nat.gcd a b) : ℝ) =
      ∏ p ∈ (Nat.gcd a b).primeFactors, (Nat.totient p : ℝ) := by
    exact_mod_cast
      BoundedGaps.Maynard.totient_eq_prod_primeFactors_of_squarefree hgSq
  calc
    (∏ pi ∈ S, crossBaseModifiedPrimeWeight a pi.1 pi.2) =
        ∏ pi ∈ S,
          (crossBasePrimeWeight pi.1 pi.2 *
            if pi.1 ∣ a then (Nat.totient pi.1 : ℝ) else 1) := by
      apply Finset.prod_congr rfl
      intro pi hpi
      unfold crossBaseModifiedPrimeWeight
      split_ifs
      · ring
      · ring
    _ = (∏ pi ∈ S, crossBasePrimeWeight pi.1 pi.2) *
          ∏ pi ∈ S,
            (if pi.1 ∣ a then (Nat.totient pi.1 : ℝ) else 1) := by
      exact Finset.prod_mul_distrib
    _ = (∏ pi ∈ S, crossBasePrimeWeight pi.1 pi.2) *
          ∏ pi ∈ T, (Nat.totient pi.1 : ℝ) := by
      congr 1
      rw [Finset.prod_ite]
      simp [T, crossBaseConstraintIncidence, S]
    _ = (∏ pi ∈ S, crossBasePrimeWeight pi.1 pi.2) *
          ∏ p ∈ T.image Prod.fst, (Nat.totient p : ℝ) := by
      rw [Finset.prod_image hinj]
    _ = crossBaseReciprocalWeight su.1 su.2 *
          (Nat.totient (Nat.gcd a b) : ℝ) := by
      rw [← hbase, himage, ← htotG]

theorem crossBaseModifiedPrimeWeight_nonneg
    {H : Finset ℕ} (a p : ℕ) (i : CrossBaseLabel H) :
    0 ≤ crossBaseModifiedPrimeWeight a p i := by
  unfold crossBaseModifiedPrimeWeight crossBasePrimeWeight
  rcases i with h | ab <;> split_ifs <;> positivity

/-- Exact cancellation of the overlap totient: the constraint weight is
`1/φ(a)` times the modified prime-incidence product. -/
theorem crossBaseConstraintWeight_eq_modifiedPrimeProduct
    {H : Finset ℕ} {A : H → ℕ} {R Q : ℕ} (hRQ : R ≤ Q)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A))
    {su :
      (∀ ab : H × H,
          ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) ×
        (H → ℕ)}
    (hsu : su ∈ squarefreeCrossBaseTupleBox H R) :
    crossBaseConstraintWeight A su.1 su.2 =
      ((1 : ℝ) /
        Nat.totient (BoundedGaps.Maynard.divisorTupleProduct H A)) *
      ∏ pi ∈ crossBasePrimeIncidence Q su,
        crossBaseModifiedPrimeWeight
          (BoundedGaps.Maynard.divisorTupleProduct H A) pi.1 pi.2 := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  let b := (∏ h : H, su.2 h) * crossTupleValueProduct su.1
  let g := Nat.gcd a b
  let c := a / g
  have hsq := (mem_squarefreeCrossBaseTupleBox_iff.mp hsu).2.2
  have haPos : 0 < a := Nat.pos_of_ne_zero hAtotal.ne_zero
  have hb : b ≠ 0 := hsq.ne_zero
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_left b haPos
  have hcPos : 0 < c := Nat.div_pos
    (Nat.le_of_dvd haPos (Nat.gcd_dvd_left a b)) hgPos
  have hcg : c.Coprime g := by
    apply Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right a b)
    exact Nat.coprime_div_gcd_of_squarefree hAtotal hb
  have hcgMul : c * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hphiA : Nat.totient a = Nat.totient c * Nat.totient g := by
    rw [← hcgMul, Nat.totient_mul hcg]
  have hphiAPos : 0 < (Nat.totient a : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr haPos
  have hphiCPos : 0 < (Nat.totient c : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hcPos
  have hphiGPos : 0 < (Nat.totient g : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hgPos
  have hmodified := prod_crossBaseModifiedPrimeWeight_eq
    hRQ hAtotal hsu
  unfold crossBaseConstraintWeight
  dsimp only
  rw [if_pos hsq]
  change crossBaseReciprocalWeight su.1 su.2 *
      ((1 : ℝ) / Nat.totient c) = _
  rw [show (∏ pi ∈ crossBasePrimeIncidence Q su,
      crossBaseModifiedPrimeWeight a pi.1 pi.2) =
      crossBaseReciprocalWeight su.1 su.2 * (Nat.totient g : ℝ) by
    simpa [a, b, g] using hmodified]
  have hphiAReal : (Nat.totient a : ℝ) =
      (Nat.totient c : ℝ) * Nat.totient g := by
    exact_mod_cast hphiA
  rw [hphiAReal]
  field_simp [hphiAPos.ne', hphiCPos.ne', hphiGPos.ne']
  <;> ring

noncomputable def crossBaseModifiedSetWeight
    {H : Finset ℕ} (a : ℕ)
    (S : Finset (ℕ × CrossBaseLabel H)) : ℝ :=
  ∏ pi ∈ S, crossBaseModifiedPrimeWeight a pi.1 pi.2

theorem crossBaseModifiedSetWeight_nonneg
    {H : Finset ℕ} (a : ℕ)
    (S : Finset (ℕ × CrossBaseLabel H)) :
    0 ≤ crossBaseModifiedSetWeight a S := by
  unfold crossBaseModifiedSetWeight
  exact Finset.prod_nonneg fun pi hpi ↦
    crossBaseModifiedPrimeWeight_nonneg a pi.1 pi.2

/-- Generic Euler-product majorant for squarefree ordinary base tuples with
the constraint-overlap modification. -/
theorem sum_squarefreeCrossBase_modifiedPrimeProducts_le_eulerProduct
    (H : Finset ℕ) (R a : ℕ) :
    (∑ su ∈ squarefreeCrossBaseTupleBox H R,
        ∏ pi ∈ crossBasePrimeIncidence R su,
          crossBaseModifiedPrimeWeight a pi.1 pi.2) ≤
      ∏ pi ∈ crossBasePrimeLabelUniverse H R,
        (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2) := by
  let box := squarefreeCrossBaseTupleBox H R
  let U := crossBasePrimeLabelUniverse H R
  let incidence := crossBasePrimeIncidence (H := H) R
  let weight := crossBaseModifiedSetWeight (H := H) a
  have hinj : Set.InjOn incidence box :=
    crossBasePrimeIncidence_injOn_squarefreeBox H le_rfl
  have himage : box.image incidence ⊆ U.powerset := by
    intro S hS
    obtain ⟨su, hsu, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.mem_powerset]
    exact crossBasePrimeIncidence_subset_universe R su
  calc
    (∑ su ∈ box,
        ∏ pi ∈ incidence su,
          crossBaseModifiedPrimeWeight a pi.1 pi.2) =
        ∑ su ∈ box, weight (incidence su) := by
      rfl
    _ = ∑ S ∈ box.image incidence, weight S := by
      exact (Finset.sum_image (f := weight) hinj).symm
    _ ≤ ∑ S ∈ U.powerset, weight S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro S hS hSNot
      exact crossBaseModifiedSetWeight_nonneg a S
    _ = ∏ pi ∈ U,
          (crossBaseModifiedPrimeWeight a pi.1 pi.2 + 1) := by
      rw [Finset.prod_add
        (fun pi ↦ crossBaseModifiedPrimeWeight a pi.1 pi.2)
        (fun _ ↦ (1 : ℝ)) U]
      apply Finset.sum_congr rfl
      intro S hS
      unfold weight crossBaseModifiedSetWeight
      simp
    _ = ∏ pi ∈ U,
          (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2) := by
      apply Finset.prod_congr rfl
      intro pi hpi
      ring

/-- The nested common/cross sum is the same sum over the filtered product
box; terms off the squarefree locus vanish by definition. -/
theorem sum_crossBaseConstraintWeight_eq_squarefreeBox
    {H : Finset ℕ} (A : H → ℕ) (R : ℕ) :
    (∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossBaseConstraintWeight A s u) =
      ∑ su ∈ squarefreeCrossBaseTupleBox H R,
        crossBaseConstraintWeight A su.1 su.2 := by
  calc
    _ = ∑ su ∈
          (BoundedGaps.Maynard.crossMoebiusTupleBox H R ×ˢ
            BoundedGaps.Maynard.maynardDivisorTupleBox H R),
          crossBaseConstraintWeight A su.1 su.2 :=
      (Finset.sum_product _ _ _).symm
    _ = _ := by
      unfold squarefreeCrossBaseTupleBox
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro su hsu
      unfold crossBaseConstraintWeight
      dsimp only
      by_cases hsq : Squarefree
          ((∏ h : H, su.2 h) * crossTupleValueProduct su.1)
      · rw [if_pos hsq, if_pos hsq]
      · rw [if_neg hsq, if_neg hsq]

/-- Complete finite Euler-product bound for the common/cross base sum with
one squarefree lcm-constraint tuple. -/
theorem sum_crossBaseConstraintWeight_le_eulerProduct
    {H : Finset ℕ} {A : H → ℕ} (R : ℕ)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    (∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossBaseConstraintWeight A s u) ≤
      ((1 : ℝ) /
        Nat.totient (BoundedGaps.Maynard.divisorTupleProduct H A)) *
      ∏ pi ∈ crossBasePrimeLabelUniverse H R,
        (1 + crossBaseModifiedPrimeWeight
          (BoundedGaps.Maynard.divisorTupleProduct H A) pi.1 pi.2) := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  let box := squarefreeCrossBaseTupleBox H R
  have houter : 0 ≤ (1 : ℝ) / Nat.totient a := by positivity
  rw [sum_crossBaseConstraintWeight_eq_squarefreeBox]
  calc
    (∑ su ∈ box, crossBaseConstraintWeight A su.1 su.2) =
        ((1 : ℝ) / Nat.totient a) *
          ∑ su ∈ box,
            ∏ pi ∈ crossBasePrimeIncidence R su,
              crossBaseModifiedPrimeWeight a pi.1 pi.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro su hsu
      exact crossBaseConstraintWeight_eq_modifiedPrimeProduct
        le_rfl hAtotal hsu
    _ ≤ ((1 : ℝ) / Nat.totient a) *
          ∏ pi ∈ crossBasePrimeLabelUniverse H R,
            (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2) := by
      apply mul_le_mul_of_nonneg_left _ houter
      exact sum_squarefreeCrossBase_modifiedPrimeProducts_le_eulerProduct
        H R a

/-! ## Comparing modified and ordinary base Euler products -/

noncomputable def crossBaseEulerProduct (H : Finset ℕ) (R : ℕ) : ℝ :=
  ∏ pi ∈ crossBasePrimeLabelUniverse H R,
    (1 + crossBasePrimeWeight pi.1 pi.2)

theorem crossBasePrimeWeight_nonneg
    {H : Finset ℕ} (p : ℕ) (i : CrossBaseLabel H) :
    0 ≤ crossBasePrimeWeight p i := by
  unfold crossBasePrimeWeight
  rcases i with h | ab <;> positivity

theorem crossBasePrimeWeight_le_one_of_prime
    {H : Finset ℕ} {p : ℕ} (hp : p.Prime) (i : CrossBaseLabel H) :
    crossBasePrimeWeight p i ≤ 1 := by
  have hphiNat : 1 ≤ Nat.totient p := by
    rw [Nat.totient_prime hp]
    have hp2 := hp.two_le
    omega
  have hphi : (1 : ℝ) ≤ Nat.totient p := by exact_mod_cast hphiNat
  have hphiPos : (0 : ℝ) < Nat.totient p := lt_of_lt_of_le zero_lt_one hphi
  rcases i with h | ab
  · unfold crossBasePrimeWeight
    exact (div_le_iff₀ hphiPos).mpr (by simpa using hphi)
  · unfold crossBasePrimeWeight
    apply (div_le_iff₀ (sq_pos_of_pos hphiPos)).mpr
    nlinarith

theorem crossBaseModifiedPrimeWeight_le_one_of_prime
    {H : Finset ℕ} (a : ℕ) {p : ℕ} (hp : p.Prime)
    (i : CrossBaseLabel H) :
    crossBaseModifiedPrimeWeight a p i ≤ 1 := by
  have hphiPos : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hphiOne : (1 : ℝ) ≤ Nat.totient p := by
    have hphiNat : 1 ≤ Nat.totient p := by
      rw [Nat.totient_prime hp]
      have hp2 := hp.two_le
      omega
    exact_mod_cast hphiNat
  unfold crossBaseModifiedPrimeWeight
  by_cases hpa : p ∣ a
  · rw [if_pos hpa]
    rcases i with h | ab
    · unfold crossBasePrimeWeight
      change (Nat.totient p : ℝ) *
          ((1 : ℝ) / Nat.totient p) ≤ 1
      field_simp [hphiPos.ne']
      norm_num
    · unfold crossBasePrimeWeight
      change (Nat.totient p : ℝ) *
          ((1 : ℝ) / (Nat.totient p : ℝ) ^ 2) ≤ 1
      rw [show (Nat.totient p : ℝ) *
          ((1 : ℝ) / (Nat.totient p : ℝ) ^ 2) =
          (1 : ℝ) / Nat.totient p by
        field_simp [hphiPos.ne']]
      exact (div_le_iff₀ hphiPos).mpr (by simpa using hphiOne)
  · rw [if_neg hpa]
    exact crossBasePrimeWeight_le_one_of_prime hp i

theorem modifiedEulerFactor_le_two_mul_baseEulerFactor
    {H : Finset ℕ} (a : ℕ) {p : ℕ} (hp : p.Prime)
    (i : CrossBaseLabel H) :
    1 + crossBaseModifiedPrimeWeight a p i ≤
      (if p ∣ a then 2 else 1) * (1 + crossBasePrimeWeight p i) := by
  by_cases hpa : p ∣ a
  · rw [if_pos hpa]
    have hmod := crossBaseModifiedPrimeWeight_le_one_of_prime a hp i
    have hbase := crossBasePrimeWeight_nonneg p i
    linarith
  · rw [if_neg hpa]
    unfold crossBaseModifiedPrimeWeight
    rw [if_neg hpa]
    simpa using
      (le_refl (1 + crossBasePrimeWeight p i))

theorem crossBaseEulerProduct_nonneg (H : Finset ℕ) (R : ℕ) :
    0 ≤ crossBaseEulerProduct H R := by
  unfold crossBaseEulerProduct
  exact Finset.prod_nonneg fun pi hpi ↦ by
    have := crossBasePrimeWeight_nonneg pi.1 pi.2
    linarith

/-- Modifying the local factors at the primes of `a` costs at most a fixed
power of two per prime and otherwise leaves the ordinary Euler product
unchanged. -/
theorem modifiedCrossBaseEulerProduct_le
    (H : Finset ℕ) (R : ℕ) {a : ℕ} (ha : Squarefree a) :
    (∏ pi ∈ crossBasePrimeLabelUniverse H R,
        (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2)) ≤
      (((2 ^ Fintype.card (CrossBaseLabel H)) ^ ω a : ℕ) : ℝ) *
        crossBaseEulerProduct H R := by
  let U := crossBasePrimeLabelUniverse H R
  let T := U.filter fun pi ↦ pi.1 ∣ a
  have hpoint : ∀ pi ∈ U,
      1 + crossBaseModifiedPrimeWeight a pi.1 pi.2 ≤
        (if pi.1 ∣ a then 2 else 1) *
          (1 + crossBasePrimeWeight pi.1 pi.2) := by
    intro pi hpi
    have hp : pi.1.Prime := by
      have hmem := Finset.mem_product.mp hpi
      exact (Nat.mem_primesLE.mp hmem.1).2
    exact modifiedEulerFactor_le_two_mul_baseEulerFactor a hp pi.2
  have hTsub : T ⊆
      a.primeFactors ×ˢ (Finset.univ : Finset (CrossBaseLabel H)) := by
    intro pi hpi
    have hdata := Finset.mem_filter.mp hpi
    have hU := Finset.mem_product.mp hdata.1
    have hp := (Nat.mem_primesLE.mp hU.1).2
    exact Finset.mem_product.mpr ⟨
      Nat.mem_primeFactors.mpr ⟨hp, hdata.2, ha.ne_zero⟩,
      Finset.mem_univ _⟩
  have hcard : T.card ≤ ω a * Fintype.card (CrossBaseLabel H) := by
    calc
      T.card ≤ (a.primeFactors ×ˢ
          (Finset.univ : Finset (CrossBaseLabel H))).card :=
        Finset.card_le_card hTsub
      _ = _ := by
        rw [Finset.card_product, Finset.card_univ]
        rfl
  have hpowNat : 2 ^ T.card ≤
      (2 ^ Fintype.card (CrossBaseLabel H)) ^ ω a := by
    calc
      2 ^ T.card ≤ 2 ^ (ω a * Fintype.card (CrossBaseLabel H)) :=
        Nat.pow_le_pow_right (by omega) hcard
      _ = _ := by
        rw [← pow_mul]
        congr 1
        ac_rfl
  have hpow : ((2 ^ T.card : ℕ) : ℝ) ≤
      (((2 ^ Fintype.card (CrossBaseLabel H)) ^ ω a : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hbaseNonneg := crossBaseEulerProduct_nonneg H R
  calc
    (∏ pi ∈ U,
        (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2)) ≤
        ∏ pi ∈ U,
          ((if pi.1 ∣ a then 2 else 1) *
            (1 + crossBasePrimeWeight pi.1 pi.2)) := by
      apply Finset.prod_le_prod
      · intro pi hpi
        have hmod := crossBaseModifiedPrimeWeight_nonneg a pi.1 pi.2
        linarith
      · exact hpoint
    _ = (∏ pi ∈ U, (if pi.1 ∣ a then (2 : ℝ) else 1)) *
          crossBaseEulerProduct H R := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ((2 ^ T.card : ℕ) : ℝ) * crossBaseEulerProduct H R := by
      congr 1
      rw [Finset.prod_ite]
      simp [T]
    _ ≤ (((2 ^ Fintype.card (CrossBaseLabel H)) ^ ω a : ℕ) : ℝ) *
          crossBaseEulerProduct H R :=
      mul_le_mul_of_nonneg_right hpow hbaseNonneg

/-! ## Products of matching-matrix row and column lcms -/

theorem crossAuxiliaryColumnLcm_eq_prod_of_matching
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A) (j : H) :
    crossAuxiliaryColumnLcm A j = ∏ i : H, A (i, j) := by
  unfold crossAuxiliaryColumnLcm
  apply Finset.lcm_eq_prod
  intro i hi i' hi' hii'
  apply crossAuxiliary_entries_coprime_of_matching hmatch
  intro hpair
  exact hii' (congrArg Prod.fst hpair)

theorem crossAuxiliaryRowLcm_eq_prod_of_matching
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A) (i : H) :
    crossAuxiliaryRowLcm A i = ∏ j : H, A (i, j) := by
  unfold crossAuxiliaryRowLcm
  apply Finset.lcm_eq_prod
  intro j hj j' hj' hjj'
  apply crossAuxiliary_entries_coprime_of_matching hmatch
  intro hpair
  exact hjj' (congrArg Prod.snd hpair)

theorem divisorTupleProduct_crossAuxiliaryColumnLcm_eq_entryProduct
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A) :
    BoundedGaps.Maynard.divisorTupleProduct H
        (crossAuxiliaryColumnLcm A) =
      ∏ ba : H × H, A ba := by
  unfold BoundedGaps.Maynard.divisorTupleProduct
  simp_rw [crossAuxiliaryColumnLcm_eq_prod_of_matching hmatch]
  exact (Fintype.prod_prod_type_right A).symm

theorem divisorTupleProduct_crossAuxiliaryRowLcm_eq_entryProduct
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A) :
    BoundedGaps.Maynard.divisorTupleProduct H
        (crossAuxiliaryRowLcm A) =
      ∏ ba : H × H, A ba := by
  unfold BoundedGaps.Maynard.divisorTupleProduct
  simp_rw [crossAuxiliaryRowLcm_eq_prod_of_matching hmatch]
  exact (Fintype.prod_prod_type A).symm

/-! ## Absolute majorants for one fixed-lcm `Y` value -/

/-- On the starred locus, the product of the left lower tuple is the
product of all common variables and all cross variables. -/
theorem divisorTupleProduct_leftCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    (hstar : BoundedGaps.Maynard.IsStarredCrossTuple H u s) :
    BoundedGaps.Maynard.divisorTupleProduct H
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) =
      (∏ h : H, u h) * crossTupleValueProduct s := by
  unfold BoundedGaps.Maynard.divisorTupleProduct
  simp_rw [BoundedGaps.Maynard.leftCrossLowerTuple,
    BoundedGaps.Maynard.outgoingCrossLcm_eq_product hstar,
    Nat.Coprime.lcm_eq_mul
      (BoundedGaps.Maynard.u_coprime_outgoingCrossProduct hstar _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  unfold crossTupleValueProduct BoundedGaps.Maynard.outgoingCrossProduct
    BoundedGaps.Maynard.outgoingCrossIndices
  exact Finset.prod_fiberwise
    (BoundedGaps.Maynard.offDiagonalPairs H).attach
    (fun x ↦ x.1.1) (fun x ↦ s x.1 x.2)

/-- The corresponding product identity for the right lower tuple. -/
theorem divisorTupleProduct_rightCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    (hstar : BoundedGaps.Maynard.IsStarredCrossTuple H u s) :
    BoundedGaps.Maynard.divisorTupleProduct H
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) =
      (∏ h : H, u h) * crossTupleValueProduct s := by
  unfold BoundedGaps.Maynard.divisorTupleProduct
  simp_rw [BoundedGaps.Maynard.rightCrossLowerTuple,
    BoundedGaps.Maynard.incomingCrossLcm_eq_product hstar,
    Nat.Coprime.lcm_eq_mul
      (BoundedGaps.Maynard.u_coprime_incomingCrossProduct hstar _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  unfold crossTupleValueProduct BoundedGaps.Maynard.incomingCrossProduct
    BoundedGaps.Maynard.incomingCrossIndices
  exact Finset.prod_fiberwise
    (BoundedGaps.Maynard.offDiagonalPairs H).attach
    (fun x ↦ x.1.2) (fun x ↦ s x.1 x.2)

/-- If two squarefree lower values both contain `u` and their lcm contains
the squarefree constraint `A`, their two totients contain two copies of
`φ(u)` and one copy of the part of `φ(A)` not already supplied by `u`.
This is the prime-local charging identity used below; it remains valid when
`A` and `u` overlap. -/
theorem totient_common_squarefree_lcm_charge
    {A u L R : ℕ} (hA : Squarefree A) (hL : Squarefree L)
    (hR : Squarefree R) (huL : u ∣ L) (huR : u ∣ R)
    (hA_lcm : A ∣ Nat.lcm L R) :
    Nat.totient u * Nat.totient u *
        Nat.totient (A / Nat.gcd A u) ∣
      Nat.totient L * Nat.totient R := by
  have huPos : 0 < u := Nat.pos_of_dvd_of_pos huL
    (Nat.pos_of_ne_zero hL.ne_zero)
  have hquotCoprime : (A / Nat.gcd A u).Coprime u :=
    Nat.coprime_div_gcd_of_squarefree hA huPos.ne'
  have hquotDvdA : A / Nat.gcd A u ∣ A :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left A u)
  have hquotDvdLcm : A / Nat.gcd A u ∣ Nat.lcm L R :=
    hquotDvdA.trans hA_lcm
  have huDvdLcm : u ∣ Nat.lcm L R :=
    huL.trans (Nat.dvd_lcm_left L R)
  have hprodDvdLcm : (A / Nat.gcd A u) * u ∣ Nat.lcm L R :=
    hquotCoprime.mul_dvd_of_dvd_of_dvd hquotDvdLcm huDvdLcm
  have hphiGcd : Nat.totient u ∣ Nat.totient (Nat.gcd L R) :=
    Nat.totient_dvd_of_dvd (Nat.dvd_gcd huL huR)
  have hphiLcm : Nat.totient (A / Nat.gcd A u) * Nat.totient u ∣
      Nat.totient (Nat.lcm L R) := by
    rw [← Nat.totient_mul hquotCoprime]
    exact Nat.totient_dvd_of_dvd hprodDvdLcm
  have hproduct := mul_dvd_mul hphiGcd hphiLcm
  rw [BoundedGaps.Maynard.totient_gcd_mul_totient_lcm_of_squarefree
    hL hR] at hproduct
  simpa [mul_assoc, mul_comm, mul_left_comm] using hproduct

theorem cast_totient_common_squarefree_lcm_charge_le
    {A u L R : ℕ} (hA : Squarefree A) (hL : Squarefree L)
    (hR : Squarefree R) (huL : u ∣ L) (huR : u ∣ R)
    (hA_lcm : A ∣ Nat.lcm L R) :
    (Nat.totient u : ℝ) ^ 2 * Nat.totient (A / Nat.gcd A u) ≤
      (Nat.totient L : ℝ) * Nat.totient R := by
  have hdvd := totient_common_squarefree_lcm_charge
    hA hL hR huL huR hA_lcm
  have hrightPos : 0 < Nat.totient L * Nat.totient R :=
    Nat.mul_pos (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hL.ne_zero))
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hR.ne_zero))
  rw [pow_two]
  exact_mod_cast Nat.le_of_dvd hrightPos hdvd

/-- Every scalar constraint is present in the lcm of the two lower values
chosen by an allocation. -/
theorem tupleLcmAllocation_constraint_dvd_lcm_lowers
    {H : Finset ℕ} {A : H → ℕ} (hA : ∀ h : H, Squarefree (A h))
    (x : TupleLcmAllocation A) (h : H) :
    A h ∣ Nat.lcm (tupleLcmAllocationFirstLower x h)
      (tupleLcmAllocationSecondLower x h) := by
  have hx : (x h).1.1 ∈ (A h).divisors ∧
      (x h).1.2 ∈ (A h / (x h).1.1).divisors := by
    simpa only [lcmAllocationSupport, Finset.mem_sigma] using (x h).property
  have htDvd : (x h).1.1 ∣ A h := (Nat.mem_divisors.mp hx.1).1
  have hmul : (A h / (x h).1.1) * (x h).1.1 = A h :=
    Nat.div_mul_cancel htDvd
  have hcop : (A h / (x h).1.1).Coprime (x h).1.1 := by
    apply Nat.coprime_of_squarefree_mul
    simpa [hmul] using hA h
  have hquot : A h / (x h).1.1 ∣
      Nat.lcm (tupleLcmAllocationFirstLower x h)
        (tupleLcmAllocationSecondLower x h) := by
    exact Nat.dvd_lcm_right _ _
  have ht : (x h).1.1 ∣
      Nat.lcm (tupleLcmAllocationFirstLower x h)
        (tupleLcmAllocationSecondLower x h) := by
    apply dvd_trans (Nat.dvd_lcm_left (x h).1.1 (x h).1.2)
    exact Nat.dvd_lcm_left _ _
  rw [← hmul]
  exact hcop.mul_dvd_of_dvd_of_dvd hquot ht

/-- Adjoining arbitrary common lower values can only enlarge the lcm, so
the allocation constraint remains present. -/
theorem tupleLcmAllocation_constraint_dvd_lcm_commonLowers
    {H : Finset ℕ} {A : H → ℕ} (hA : ∀ h : H, Squarefree (A h))
    (u v : H → ℕ) (x : TupleLcmAllocation A) (h : H) :
    A h ∣ Nat.lcm (tupleLcmAllocationCommonFirstLower u x h)
      (tupleLcmAllocationCommonSecondLower v x h) := by
  apply dvd_trans (tupleLcmAllocation_constraint_dvd_lcm_lowers hA x h)
  apply Nat.lcm_dvd
  · exact (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
  · exact (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)

theorem tupleLcmAllocationCommonFirstYFactor_ne_zero_y_ne_zero
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ}
    {u : H → ℕ} {x : TupleLcmAllocation A}
    (h : tupleLcmAllocationCommonFirstYFactor y u x ≠ 0) :
    y (tupleLcmAllocationCommonFirstLower u x) ≠ 0 := by
  intro hy
  apply h
  simp [tupleLcmAllocationCommonFirstYFactor, hy]

theorem tupleLcmAllocationCommonSecondYFactor_ne_zero_y_ne_zero
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ}
    {u : H → ℕ} {x : TupleLcmAllocation A}
    (h : tupleLcmAllocationCommonSecondYFactor y u x ≠ 0) :
    y (tupleLcmAllocationCommonSecondLower u x) ≠ 0 := by
  intro hy
  apply h
  simp [tupleLcmAllocationCommonSecondYFactor, hy]

/-- Nonzero allocated factors still force the ordinary common/cross tuple to
be starred: all of its variables divide the corresponding allocated lower
coordinates, so the usual support coprimality argument survives unchanged. -/
theorem isStarredCrossTuple_of_allocatedYFactors_ne_zero
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {x : TupleLcmAllocation A}
    (hl : tupleLcmAllocationCommonFirstYFactor y
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x ≠ 0)
    (hr : tupleLcmAllocationCommonSecondYFactor y
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x ≠ 0) :
    BoundedGaps.Maynard.IsStarredCrossTuple H u s := by
  have hlSupport := hy _
    (tupleLcmAllocationCommonFirstYFactor_ne_zero_y_ne_zero hl)
  have hrSupport := hy _
    (tupleLcmAllocationCommonSecondYFactor_ne_zero_y_ne_zero hr)
  have huLeft (h : H) : u h ∣
      tupleLcmAllocationCommonFirstLower
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x h :=
    (BoundedGaps.Maynard.u_dvd_leftCrossLowerTuple H u s h).trans
      (Nat.dvd_lcm_left _ _)
  have huRight (h : H) : u h ∣
      tupleLcmAllocationCommonSecondLower
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x h :=
    (BoundedGaps.Maynard.u_dvd_rightCrossLowerTuple H u s h).trans
      (Nat.dvd_lcm_left _ _)
  have hsLeft (ab : H × H)
      (hab : ab ∈ BoundedGaps.Maynard.offDiagonalPairs H) :
      s ab hab ∣ tupleLcmAllocationCommonFirstLower
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x ab.1 :=
    (BoundedGaps.Maynard.cross_dvd_leftCrossLowerTuple u s ab hab).trans
      (Nat.dvd_lcm_left _ _)
  have hsRight (ab : H × H)
      (hab : ab ∈ BoundedGaps.Maynard.offDiagonalPairs H) :
      s ab hab ∣ tupleLcmAllocationCommonSecondLower
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x ab.2 :=
    (BoundedGaps.Maynard.cross_dvd_rightCrossLowerTuple u s ab hab).trans
      (Nat.dvd_lcm_left _ _)
  constructor
  · intro ab hab
    have habNe : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hab).2
    have hright := hrSupport.coordinates_coprime habNe
    have hleft := hlSupport.coordinates_coprime habNe
    exact ⟨
      Nat.Coprime.of_dvd (hsRight ab hab) (huRight ab.1) hright.symm,
      Nat.Coprime.of_dvd (hsLeft ab hab) (huLeft ab.2) hleft⟩
  · intro ab cd hab hcd habcd hshared
    rcases hshared with hfirst | hsecond
    · have hne : ab.2 ≠ cd.2 := by
        intro h
        apply habcd
        exact Prod.ext hfirst h
      exact Nat.Coprime.of_dvd (hsRight ab hab) (hsRight cd hcd)
        (hrSupport.coordinates_coprime hne)
    · have hne : ab.1 ≠ cd.1 := by
        intro h
        apply habcd
        exact Prod.ext h hsecond
      exact Nat.Coprime.of_dvd (hsLeft ab hab) (hsLeft cd hcd)
        (hlSupport.coordinates_coprime hne)

/-- A surviving allocation forces the product of every ordinary common and
cross variable to be squarefree.  Indeed that base product is the product
of the unallocated left lower tuple, hence divides the supported allocated
lower tuple. -/
theorem squarefree_crossTupleBase_of_allocatedYFactors_ne_zero
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {x : TupleLcmAllocation A}
    (hl : tupleLcmAllocationCommonFirstYFactor y
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x ≠ 0)
    (hr : tupleLcmAllocationCommonSecondYFactor y
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x ≠ 0) :
    Squarefree ((∏ h : H, u h) * crossTupleValueProduct s) := by
  have hlSupport := hy _
    (tupleLcmAllocationCommonFirstYFactor_ne_zero_y_ne_zero hl)
  have hstar := isStarredCrossTuple_of_allocatedYFactors_ne_zero hy hl hr
  rw [← divisorTupleProduct_leftCrossLowerTuple hstar]
  apply hlSupport.2.2.squarefree_of_dvd
  unfold BoundedGaps.Maynard.divisorTupleProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro h hh
  exact Nat.dvd_lcm_left _ _

theorem finset_prod_dvd_of_pairwise_natCoprime
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {f : ι → ℕ} {z : ℕ}
    (hpair : Set.Pairwise (S : Set ι) (Function.onFun Nat.Coprime f))
    (hdiv : ∀ i ∈ S, f i ∣ z) :
    (∏ i ∈ S, f i) ∣ z := by
  induction S using Finset.cons_induction with
  | empty => simp
  | @cons a S ha ih =>
      rw [Finset.coe_cons, Set.pairwise_insert] at hpair
      rw [Finset.prod_cons]
      apply (Nat.Coprime.prod_right fun i hi ↦
        hpair.2 i (by simp [hi]) (fun hai ↦ ha (hai ▸ hi)) |>.1).mul_dvd_of_dvd_of_dvd
      · exact hdiv a (by simp)
      · apply ih hpair.1
        intro i hi
        exact hdiv i (by simp [hi])

/-! ## The finite cost of the lcm allocations -/

/-- Every coordinate allocation embeds into two divisors of the total
constraint product.  This intentionally crude common codomain makes the
cardinality estimate independent of how primes are distributed among the
coordinates. -/
noncomputable def tupleLcmAllocationDivisorEmbedding
    {H : Finset ℕ} (A : H → ℕ)
    (ha : BoundedGaps.Maynard.divisorTupleProduct H A ≠ 0) :
    TupleLcmAllocation A →
      (H →
        (↑(BoundedGaps.Maynard.divisorTupleProduct H A).divisors ×
          ↑(BoundedGaps.Maynard.divisorTupleProduct H A).divisors)) :=
  fun x h ↦
    let a := BoundedGaps.Maynard.divisorTupleProduct H A
    let hx : (x h).1.1 ∈ (A h).divisors ∧
        (x h).1.2 ∈ (A h / (x h).1.1).divisors := by
      simpa only [lcmAllocationSupport, Finset.mem_sigma] using (x h).property
    let hAprod : A h ∣ a :=
      BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product A h
    let htA : (x h).1.1 ∣ A h := (Nat.mem_divisors.mp hx.1).1
    let hsA : (x h).1.2 ∣ A h :=
      (Nat.mem_divisors.mp hx.2).1.trans (Nat.div_dvd_of_dvd htA)
    (⟨(x h).1.1, Nat.mem_divisors.mpr
        ⟨htA.trans hAprod, ha⟩⟩,
      ⟨(x h).1.2, Nat.mem_divisors.mpr
        ⟨hsA.trans hAprod, ha⟩⟩)

theorem tupleLcmAllocationDivisorEmbedding_injective
    {H : Finset ℕ} (A : H → ℕ)
    (ha : BoundedGaps.Maynard.divisorTupleProduct H A ≠ 0) :
    Function.Injective (tupleLcmAllocationDivisorEmbedding A ha) := by
  intro x z hxz
  funext h
  have hh := congrFun hxz h
  apply Subtype.ext
  have hpair : ((x h).1.1, (x h).1.2) =
      ((z h).1.1, (z h).1.2) := by
    simpa [tupleLcmAllocationDivisorEmbedding] using congrArg
      (fun w ↦ (w.1.1, w.2.1)) hh
  rcases xh : (x h).1 with ⟨xt, xs⟩
  rcases zh : (z h).1 with ⟨zt, zs⟩
  simp only [xh, zh] at hpair ⊢
  cases hpair
  rfl

/-- The simultaneous allocation set costs at most two choices of a divisor
of the total constraint product in each coordinate. -/
theorem card_tupleLcmAllocation_le_divisors_sq_pow
    {H : Finset ℕ} (A : H → ℕ)
    (ha : BoundedGaps.Maynard.divisorTupleProduct H A ≠ 0) :
    Fintype.card (TupleLcmAllocation A) ≤
      (((BoundedGaps.Maynard.divisorTupleProduct H A).divisors.card) ^ 2) ^
        Fintype.card H := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  have hcard := Fintype.card_le_of_injective
    (tupleLcmAllocationDivisorEmbedding A ha)
    (tupleLcmAllocationDivisorEmbedding_injective A ha)
  rw [Fintype.card_pi] at hcard
  simp only [Fintype.card_prod, Fintype.card_coe,
    Finset.prod_const, pow_two] at hcard
  simpa [a, pow_two] using hcard

/-- For a squarefree constraint product the preceding allocation cost is a
fixed constant per prime. -/
theorem card_tupleLcmAllocation_le_four_pow_card_pow_omega
    {H : Finset ℕ} {A : H → ℕ}
    (hA : Squarefree (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    Fintype.card (TupleLcmAllocation A) ≤
      (4 ^ Fintype.card H) ^
        ω (BoundedGaps.Maynard.divisorTupleProduct H A) := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  calc
    Fintype.card (TupleLcmAllocation A) ≤
        (a.divisors.card ^ 2) ^ Fintype.card H := by
      simpa [a] using card_tupleLcmAllocation_le_divisors_sq_pow A hA.ne_zero
    _ = ((2 ^ ω a) ^ 2) ^ Fintype.card H := by
      rw [BoundedGaps.Maynard.card_divisors_eq_two_pow_omega hA]
    _ = (4 ^ Fintype.card H) ^ ω a := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      simp only [← pow_mul]
      congr 1
      ac_rfl

/-- Aggregate form of the prime charge.  For a surviving allocated term,
the product of all ordinary common and cross variables divides both final
lower-tuple products.  The squarefree constraint product divides their lcm.
Consequently the two complete totient denominators contain two copies of
the base totient and one copy of every new constraint prime. -/
theorem allocatedCross_totientProduct_charge
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree (BoundedGaps.Maynard.divisorTupleProduct H A))
    {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {x : TupleLcmAllocation A}
    (hl : tupleLcmAllocationCommonFirstYFactor y
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x ≠ 0)
    (hr : tupleLcmAllocationCommonSecondYFactor y
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x ≠ 0) :
    let b := (∏ h : H, u h) * crossTupleValueProduct s
    let a := BoundedGaps.Maynard.divisorTupleProduct H A
    Nat.totient b * Nat.totient b * Nat.totient (a / Nat.gcd a b) ∣
      (∏ h : H, Nat.totient
        (tupleLcmAllocationCommonFirstLower
          (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x h)) *
      (∏ h : H, Nat.totient
        (tupleLcmAllocationCommonSecondLower
          (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x h)) := by
  dsimp only
  let l : H → ℕ := tupleLcmAllocationCommonFirstLower
    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x
  let r : H → ℕ := tupleLcmAllocationCommonSecondLower
    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x
  let L := BoundedGaps.Maynard.divisorTupleProduct H l
  let R' := BoundedGaps.Maynard.divisorTupleProduct H r
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  let b := (∏ h : H, u h) * crossTupleValueProduct s
  have hlSupport : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W l :=
    hy _ (tupleLcmAllocationCommonFirstYFactor_ne_zero_y_ne_zero hl)
  have hrSupport : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r :=
    hy _ (tupleLcmAllocationCommonSecondYFactor_ne_zero_y_ne_zero hr)
  have hstar := isStarredCrossTuple_of_allocatedYFactors_ne_zero hy hl hr
  have hbL : b ∣ L := by
    rw [show b = BoundedGaps.Maynard.divisorTupleProduct H
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) by
      exact (divisorTupleProduct_leftCrossLowerTuple hstar).symm]
    unfold L BoundedGaps.Maynard.divisorTupleProduct l
    apply Finset.prod_dvd_prod_of_dvd
    intro h hh
    exact Nat.dvd_lcm_left _ _
  have hbR : b ∣ R' := by
    rw [show b = BoundedGaps.Maynard.divisorTupleProduct H
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) by
      exact (divisorTupleProduct_rightCrossLowerTuple hstar).symm]
    unfold R' BoundedGaps.Maynard.divisorTupleProduct r
    apply Finset.prod_dvd_prod_of_dvd
    intro h hh
    exact Nat.dvd_lcm_left _ _
  have hAcoord : ∀ h : H, Squarefree (A h) := fun h ↦
    hAtotal.squarefree_of_dvd
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product A h)
  have hAeach : ∀ h : H, A h ∣ Nat.lcm L R' := by
    intro h
    apply dvd_trans
      (tupleLcmAllocation_constraint_dvd_lcm_commonLowers
        hAcoord
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s)
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x h)
    apply Nat.lcm_dvd
    · exact (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product l h).trans
        (Nat.dvd_lcm_left L R')
    · exact (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product r h).trans
        (Nat.dvd_lcm_right L R')
  have haLcm : a ∣ Nat.lcm L R' := by
    unfold a BoundedGaps.Maynard.divisorTupleProduct
    apply finset_prod_dvd_of_pairwise_natCoprime
    · intro i hi j hj hij
      exact BoundedGaps.Maynard.divisorTupleCoordinates_coprime_of_squarefree_product
        hAtotal hij
    · intro h hh
      exact hAeach h
  have hcharge := totient_common_squarefree_lcm_charge
    hAtotal hlSupport.2.2 hrSupport.2.2 hbL hbR haLcm
  rw [BoundedGaps.Maynard.totient_divisorTupleProduct_eq_prod
      hlSupport.2.2,
    BoundedGaps.Maynard.totient_divisorTupleProduct_eq_prod
      hrSupport.2.2] at hcharge
  exact hcharge

/-- The denominator occurring in the first allocated `Y` factor. -/
noncomputable def tupleLcmAllocationFirstTotientProduct
    {H : Finset ℕ} {A : H → ℕ} (u : H → ℕ)
    (x : TupleLcmAllocation A) : ℝ :=
  ∏ h : H, (Nat.totient
    (tupleLcmAllocationCommonFirstLower u x h) : ℝ)

/-- The denominator occurring in the second allocated `Y` factor. -/
noncomputable def tupleLcmAllocationSecondTotientProduct
    {H : Finset ℕ} {A : H → ℕ} (u : H → ℕ)
    (x : TupleLcmAllocation A) : ℝ :=
  ∏ h : H, (Nat.totient
    (tupleLcmAllocationCommonSecondLower u x h) : ℝ)

theorem tupleLcmAllocationFirstTotientProduct_pos
    {H : Finset ℕ} {A u : H → ℕ}
    (hu : ∀ h : H, 0 < u h) (hA : ∀ h : H, 0 < A h)
    (x : TupleLcmAllocation A) :
    0 < tupleLcmAllocationFirstTotientProduct u x := by
  unfold tupleLcmAllocationFirstTotientProduct
  apply Finset.prod_pos
  intro h hh
  exact_mod_cast Nat.totient_pos.mpr
    (tupleLcmAllocationCommonFirstLower_pos_of_pos hu hA x h)

theorem tupleLcmAllocationSecondTotientProduct_pos
    {H : Finset ℕ} {A u : H → ℕ}
    (hu : ∀ h : H, 0 < u h) (hA : ∀ h : H, 0 < A h)
    (x : TupleLcmAllocation A) :
    0 < tupleLcmAllocationSecondTotientProduct u x := by
  unfold tupleLcmAllocationSecondTotientProduct
  apply Finset.prod_pos
  intro h hh
  exact_mod_cast Nat.totient_pos.mpr
    (tupleLcmAllocationCommonSecondLower_pos_of_pos hu hA x h)

/-- Pointwise absolute bound for the first allocated `Y` factor.  It keeps
the full allocated totient denominator, which is where every auxiliary
matrix prime will subsequently be charged. -/
theorem abs_tupleLcmAllocationCommonFirstYFactor_le
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : ∀ r, |y r| ≤ B) {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h) (hA : ∀ h : H, 0 < A h)
    (x : TupleLcmAllocation A) :
    |tupleLcmAllocationCommonFirstYFactor y u x| ≤
      B / tupleLcmAllocationFirstTotientProduct u x := by
  have hden := tupleLcmAllocationFirstTotientProduct_pos hu hA x
  unfold tupleLcmAllocationCommonFirstYFactor
  change
    |(∏ h : H, (ArithmeticFunction.moebius
        (tupleLcmAllocationCommonFirstLower u x h) : ℝ)) *
        y (tupleLcmAllocationCommonFirstLower u x) /
          tupleLcmAllocationFirstTotientProduct u x| ≤
      B / tupleLcmAllocationFirstTotientProduct u x
  rw [abs_div, abs_mul, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  have hmul := mul_le_mul
    (BoundedGaps.Maynard.abs_moebiusTupleProduct_le_one
      (tupleLcmAllocationCommonFirstLower u x))
    (hy (tupleLcmAllocationCommonFirstLower u x))
    (abs_nonneg _) zero_le_one
  simpa only [one_mul] using hmul

/-- Pointwise absolute bound for the second allocated `Y` factor. -/
theorem abs_tupleLcmAllocationCommonSecondYFactor_le
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : ∀ r, |y r| ≤ B) {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h) (hA : ∀ h : H, 0 < A h)
    (x : TupleLcmAllocation A) :
    |tupleLcmAllocationCommonSecondYFactor y u x| ≤
      B / tupleLcmAllocationSecondTotientProduct u x := by
  have hden := tupleLcmAllocationSecondTotientProduct_pos hu hA x
  unfold tupleLcmAllocationCommonSecondYFactor
  change
    |(∏ h : H, (ArithmeticFunction.moebius
        (tupleLcmAllocationCommonSecondLower u x h) : ℝ)) *
        y (tupleLcmAllocationCommonSecondLower u x) /
          tupleLcmAllocationSecondTotientProduct u x| ≤
      B / tupleLcmAllocationSecondTotientProduct u x
  rw [abs_div, abs_mul, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  have hmul := mul_le_mul
    (BoundedGaps.Maynard.abs_moebiusTupleProduct_le_one
      (tupleLcmAllocationCommonSecondLower u x))
    (hy (tupleLcmAllocationCommonSecondLower u x))
    (abs_nonneg _) zero_le_one
  simpa only [one_mul] using hmul

theorem abs_tupleLcmAllocationMobiusWeight_le_one
    {H : Finset ℕ} {A : H → ℕ} (x : TupleLcmAllocation A) :
    |tupleLcmAllocationMobiusWeight x| ≤ 1 := by
  unfold tupleLcmAllocationMobiusWeight
  exact BoundedGaps.Maynard.abs_moebiusTupleProduct_le_one
    (fun h ↦ (x h).1.2)

/-- The ordinary cross/common coefficient is bounded by its positive
common-totient factor. -/
theorem abs_crossCommonTupleWeight_le
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) :
    |crossCommonTupleWeight s u| ≤
      ∏ h : H, (Nat.totient (u h) : ℝ) := by
  unfold crossCommonTupleWeight
  rw [abs_mul, abs_of_nonneg (by positivity :
    0 ≤ ∏ h : H, (Nat.totient (u h) : ℝ))]
  exact mul_le_of_le_one_left (by positivity)
    (BoundedGaps.Maynard.abs_crossMoebiusTupleTerm_le_one s)

/-- A completely explicit nonnegative majorant for one allocation term. -/
noncomputable def fixedLcmAllocationMajorant
    {H : Finset ℕ} {A : H → ℕ} (B : ℝ)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ)
    (x : TupleLcmAllocation A) : ℝ :=
  (∏ h : H, (Nat.totient (u h) : ℝ)) *
    (B / tupleLcmAllocationFirstTotientProduct
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x) *
    (B / tupleLcmAllocationSecondTotientProduct
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)

/-- The allocation-independent majorant obtained by charging both final
totient products to the ordinary common/cross base and to the part of the
constraint product not already present in that base. -/
noncomputable def fixedLcmPrimeChargedMajorant
    {H : Finset ℕ} (A : H → ℕ) (B : ℝ)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : ℝ :=
  let b := (∏ h : H, u h) * crossTupleValueProduct s
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  (∏ h : H, (Nat.totient (u h) : ℝ)) * B ^ 2 /
    ((Nat.totient b : ℝ) ^ 2 *
      (Nat.totient (a / Nat.gcd a b) : ℝ))

/-- Prime-charged majorant restricted to the squarefree ordinary base.
This indicator is not an artificial restriction: every nonzero transformed
allocation lies on this locus. -/
noncomputable def fixedLcmSupportedPrimeChargedMajorant
    {H : Finset ℕ} (A : H → ℕ) (B : ℝ)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : ℝ :=
  if Squarefree ((∏ h : H, u h) * crossTupleValueProduct s) then
    fixedLcmPrimeChargedMajorant A B s u
  else 0

theorem fixedLcmPrimeChargedMajorant_nonneg
    {H : Finset ℕ} (A : H → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) :
    0 ≤ fixedLcmPrimeChargedMajorant A B s u := by
  unfold fixedLcmPrimeChargedMajorant
  positivity

theorem fixedLcmSupportedPrimeChargedMajorant_nonneg
    {H : Finset ℕ} (A : H → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) :
    0 ≤ fixedLcmSupportedPrimeChargedMajorant A B s u := by
  unfold fixedLcmSupportedPrimeChargedMajorant
  split
  · exact fixedLcmPrimeChargedMajorant_nonneg A hB s u
  · exact le_rfl

theorem crossBaseConstraintWeight_nonneg
    {H : Finset ℕ} (A : H → ℕ)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) :
    0 ≤ crossBaseConstraintWeight A s u := by
  unfold crossBaseConstraintWeight
  dsimp only
  by_cases hsq : Squarefree
      ((∏ h : H, u h) * crossTupleValueProduct s)
  · rw [if_pos hsq]
    unfold crossBaseReciprocalWeight
    positivity
  · rw [if_neg hsq]

/-- On the finite boxes the charged majorant is exactly `B²` times the
squarefree base weight with its new-constraint-prime factor. -/
theorem fixedLcmSupportedPrimeChargedMajorant_eq
    {H : Finset ℕ} {A : H → ℕ} (B : ℝ)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A))
    {R : ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R) :
    fixedLcmSupportedPrimeChargedMajorant A B s u =
      B ^ 2 * crossBaseConstraintWeight A s u := by
  let b := (∏ h : H, u h) * crossTupleValueProduct s
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  by_cases hsq : Squarefree b
  · have hphiNat := totient_crossTupleBase_eq hsq
    have hphi : (Nat.totient b : ℝ) =
        (∏ h : H, (Nat.totient (u h) : ℝ)) *
          (BoundedGaps.Maynard.crossTotientProduct H s : ℝ) := by
      exact_mod_cast hphiNat
    have hUPos : 0 < ∏ h : H, (Nat.totient (u h) : ℝ) := by
      apply Finset.prod_pos
      intro h hh
      exact_mod_cast Nat.totient_pos.mpr
        (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp hu h).1
    have hSPos : 0 <
        (BoundedGaps.Maynard.crossTotientProduct H s : ℝ) := by
      have hSnat : 0 < BoundedGaps.Maynard.crossTotientProduct H s := by
        unfold BoundedGaps.Maynard.crossTotientProduct
        apply Finset.prod_pos
        intro ab hab
        exact Nat.totient_pos.mpr
          ((Finset.mem_Icc.mp ((Finset.mem_pi.mp hs) ab.1 ab.2)).1)
      exact_mod_cast hSnat
    have haPos : 0 < a := Nat.pos_of_ne_zero hAtotal.ne_zero
    have hgcdPos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b haPos
    have hquotPos : 0 < a / Nat.gcd a b := Nat.div_pos
      (Nat.le_of_dvd haPos (Nat.gcd_dvd_left a b)) hgcdPos
    have hqPhiPos : 0 < (Nat.totient (a / Nat.gcd a b) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hquotPos
    unfold fixedLcmSupportedPrimeChargedMajorant
      fixedLcmPrimeChargedMajorant crossBaseConstraintWeight
      crossBaseReciprocalWeight
    rw [if_pos hsq, if_pos hsq]
    dsimp only
    rw [hphi]
    field_simp [hUPos.ne', hSPos.ne', hqPhiPos.ne']
    <;> ring
  · unfold fixedLcmSupportedPrimeChargedMajorant crossBaseConstraintWeight
    rw [if_neg hsq, if_neg hsq]
    ring

theorem fixedLcmAllocationMajorant_nonneg
    {H : Finset ℕ} {A : H → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ h : H, 0 < A h)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    {R : ℕ} (u : H → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R)
    (x : TupleLcmAllocation A) :
    0 ≤ fixedLcmAllocationMajorant B s u x := by
  have hleftPos : ∀ h : H,
      0 < BoundedGaps.Maynard.leftCrossLowerTuple H u s h :=
    BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs
  have hrightPos : ∀ h : H,
      0 < BoundedGaps.Maynard.rightCrossLowerTuple H u s h :=
    BoundedGaps.Maynard.rightCrossLowerTuple_pos hu hs
  have hfirstDen := tupleLcmAllocationFirstTotientProduct_pos
    hleftPos hA x
  have hsecondDen := tupleLcmAllocationSecondTotientProduct_pos
    hrightPos hA x
  unfold fixedLcmAllocationMajorant
  exact mul_nonneg
    (mul_nonneg (by positivity) (div_nonneg hB hfirstDen.le))
    (div_nonneg hB hsecondDen.le)

/-- Absolute value of one transformed fixed-lcm summand, before summing the
ordinary cross/common tuple and the lcm allocation. -/
theorem abs_fixedLcm_transformed_summand_le
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hy : ∀ r, |y r| ≤ B)
    (hA : ∀ h : H, 0 < A h)
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    {R : ℕ}
    (u : H → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R)
    (x : TupleLcmAllocation A) :
    |crossCommonTupleWeight s u *
        (tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationCommonSecondYFactor y
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| ≤
      fixedLcmAllocationMajorant B s u x := by
  have hleftPos : ∀ h : H,
      0 < BoundedGaps.Maynard.leftCrossLowerTuple H u s h :=
    BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs
  have hrightPos : ∀ h : H,
      0 < BoundedGaps.Maynard.rightCrossLowerTuple H u s h :=
    BoundedGaps.Maynard.rightCrossLowerTuple_pos hu hs
  have hcommon := abs_crossCommonTupleWeight_le s u
  have hmob := abs_tupleLcmAllocationMobiusWeight_le_one x
  have hfirst := abs_tupleLcmAllocationCommonFirstYFactor_le
    hy hleftPos hA x
  have hsecond := abs_tupleLcmAllocationCommonSecondYFactor_le
    hy hrightPos hA x
  unfold fixedLcmAllocationMajorant
  rw [abs_mul, abs_mul, abs_mul]
  have hphi : 0 ≤ ∏ h : H, (Nat.totient (u h) : ℝ) := by positivity
  have hfirstNonneg : 0 ≤ B /
      tupleLcmAllocationFirstTotientProduct
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x := by
    exact div_nonneg hB
      (tupleLcmAllocationFirstTotientProduct_pos hleftPos hA x).le
  have hsecondNonneg : 0 ≤ B /
      tupleLcmAllocationSecondTotientProduct
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x := by
    exact div_nonneg hB
      (tupleLcmAllocationSecondTotientProduct_pos hrightPos hA x).le
  calc
    |crossCommonTupleWeight s u| *
          (|tupleLcmAllocationMobiusWeight x| *
            |tupleLcmAllocationCommonFirstYFactor y
              (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x| *
            |tupleLcmAllocationCommonSecondYFactor y
              (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x|) ≤
        (∏ h : H, (Nat.totient (u h) : ℝ)) *
          (1 * (B / tupleLcmAllocationFirstTotientProduct
              (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x) *
            (B / tupleLcmAllocationSecondTotientProduct
              (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)) := by
      gcongr
    _ = _ := by ring

/-- The overlap-safe prime charge converted to the real-valued bound needed
for the Euler product.  A vanished allocated factor contributes zero.  For
a surviving allocation, the aggregate divisibility theorem above replaces
the two final totient denominators by two copies of the ordinary base and
one copy of every genuinely new constraint prime. -/
theorem abs_fixedLcm_transformed_summand_le_primeCharged
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A))
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R)
    (x : TupleLcmAllocation A) :
    |crossCommonTupleWeight s u *
        (tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationCommonSecondYFactor y
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| ≤
      fixedLcmPrimeChargedMajorant A B s u := by
  let yl := tupleLcmAllocationCommonFirstYFactor y
    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x
  let yr := tupleLcmAllocationCommonSecondYFactor y
    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x
  by_cases hl : yl = 0
  · simp [yl, hl, fixedLcmPrimeChargedMajorant_nonneg A hB s u]
  by_cases hr : yr = 0
  · simp [yr, hr, fixedLcmPrimeChargedMajorant_nonneg A hB s u]
  have hstar := isStarredCrossTuple_of_allocatedYFactors_ne_zero
    hySupport hl hr
  let b := (∏ h : H, u h) * crossTupleValueProduct s
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  have hAPos : ∀ h : H, 0 < A h := by
    intro h
    have hsq := hAtotal.squarefree_of_dvd
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product A h)
    exact Nat.pos_of_ne_zero hsq.ne_zero
  have hbPos : 0 < b := by
    rw [show b = BoundedGaps.Maynard.divisorTupleProduct H
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) by
      exact (divisorTupleProduct_leftCrossLowerTuple hstar).symm]
    unfold BoundedGaps.Maynard.divisorTupleProduct
    exact Finset.prod_pos fun h hh ↦
      BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs h
  have haPos : 0 < a := by
    exact Nat.pos_of_ne_zero hAtotal.ne_zero
  have hgcdPos : 0 < Nat.gcd a b :=
    Nat.gcd_pos_of_pos_left b haPos
  have hquotPos : 0 < a / Nat.gcd a b := by
    exact Nat.div_pos
      (Nat.le_of_dvd haPos (Nat.gcd_dvd_left a b)) hgcdPos
  have hchargeNat := allocatedCross_totientProduct_charge
    hySupport hAtotal hl hr
  have hfirstNatPos : 0 < ∏ h : H, Nat.totient
      (tupleLcmAllocationCommonFirstLower
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x h) := by
    exact Finset.prod_pos fun h hh ↦ Nat.totient_pos.mpr
      (tupleLcmAllocationCommonFirstLower_pos_of_pos
        (BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs) hAPos x h)
  have hsecondNatPos : 0 < ∏ h : H, Nat.totient
      (tupleLcmAllocationCommonSecondLower
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x h) := by
    exact Finset.prod_pos fun h hh ↦ Nat.totient_pos.mpr
      (tupleLcmAllocationCommonSecondLower_pos_of_pos
        (BoundedGaps.Maynard.rightCrossLowerTuple_pos hu hs) hAPos x h)
  have hchargeNatLe := Nat.le_of_dvd
    (Nat.mul_pos hfirstNatPos hsecondNatPos) hchargeNat
  have hchargeReal :
      (Nat.totient b : ℝ) ^ 2 *
          (Nat.totient (a / Nat.gcd a b) : ℝ) ≤
        tupleLcmAllocationFirstTotientProduct
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationSecondTotientProduct
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x := by
    have hchargeCast :
        ((Nat.totient
            ((∏ h : H, u h) * crossTupleValueProduct s) : ℝ) *
              Nat.totient
                ((∏ h : H, u h) * crossTupleValueProduct s) *
              Nat.totient
                (BoundedGaps.Maynard.divisorTupleProduct H A /
                  Nat.gcd (BoundedGaps.Maynard.divisorTupleProduct H A)
                    ((∏ h : H, u h) * crossTupleValueProduct s)) : ℝ) ≤
          (∏ h : H, (Nat.totient
            (tupleLcmAllocationCommonFirstLower
              (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x h) : ℝ)) *
          ∏ h : H, (Nat.totient
            (tupleLcmAllocationCommonSecondLower
              (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x h) : ℝ) := by
      exact_mod_cast hchargeNatLe
    simpa [a, b, pow_two, tupleLcmAllocationFirstTotientProduct,
      tupleLcmAllocationSecondTotientProduct, mul_assoc] using hchargeCast
  have hchargePos : 0 <
      (Nat.totient b : ℝ) ^ 2 *
        (Nat.totient (a / Nat.gcd a b) : ℝ) := by
    positivity
  have hfirstPos := tupleLcmAllocationFirstTotientProduct_pos
    (BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs) hAPos x
  have hsecondPos := tupleLcmAllocationSecondTotientProduct_pos
    (BoundedGaps.Maynard.rightCrossLowerTuple_pos hu hs) hAPos x
  have hnumNonneg : 0 ≤
      (∏ h : H, (Nat.totient (u h) : ℝ)) * B ^ 2 := by
    positivity
  calc
    |crossCommonTupleWeight s u *
        (tupleLcmAllocationMobiusWeight x * yl * yr)| ≤
        fixedLcmAllocationMajorant B s u x := by
      exact abs_fixedLcm_transformed_summand_le
        hB hyBound hAPos s u hu hs x
    _ = (∏ h : H, (Nat.totient (u h) : ℝ)) * B ^ 2 /
        (tupleLcmAllocationFirstTotientProduct
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationSecondTotientProduct
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x) := by
      unfold fixedLcmAllocationMajorant
      field_simp [hfirstPos.ne', hsecondPos.ne']
      <;> ring
    _ ≤ (∏ h : H, (Nat.totient (u h) : ℝ)) * B ^ 2 /
        ((Nat.totient b : ℝ) ^ 2 *
          (Nat.totient (a / Nat.gcd a b) : ℝ)) :=
      div_le_div_of_nonneg_left hnumNonneg hchargePos hchargeReal
    _ = fixedLcmPrimeChargedMajorant A B s u := by
      rfl

theorem abs_fixedLcm_transformed_summand_le_supportedPrimeCharged
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A))
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R)
    (x : TupleLcmAllocation A) :
    |crossCommonTupleWeight s u *
        (tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationCommonSecondYFactor y
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| ≤
      fixedLcmSupportedPrimeChargedMajorant A B s u := by
  unfold fixedLcmSupportedPrimeChargedMajorant
  split_ifs with hsq
  · exact abs_fixedLcm_transformed_summand_le_primeCharged
      hB hyBound hySupport hAtotal s u hu hs x
  · let yl := tupleLcmAllocationCommonFirstYFactor y
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x
    let yr := tupleLcmAllocationCommonSecondYFactor y
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x
    by_cases hl : yl = 0
    · simp [yl, hl]
    by_cases hr : yr = 0
    · simp [yr, hr]
    exact (hsq
      (squarefree_crossTupleBase_of_allocatedYFactors_ne_zero
        hySupport hl hr)).elim

/-- After summing the finite allocation family, its only cost is its
cardinality.  Crucially, the squarefree-base indicator and the new-prime
totient denominator are retained. -/
theorem abs_fixedLcmCompatiblePairYValue_le_supportedPrimeChargedSum
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      (Fintype.card (TupleLcmAllocation A) : ℝ) *
        ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            fixedLcmSupportedPrimeChargedMajorant A B s u := by
  unfold fixedLcmCompatiblePairYValue
  calc
    |∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (∑ x : TupleLcmAllocation A,
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| ≤
        ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            ∑ x : TupleLcmAllocation A,
              |crossCommonTupleWeight s u *
                (tupleLcmAllocationMobiusWeight x *
                  tupleLcmAllocationCommonFirstYFactor y
                    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                  tupleLcmAllocationCommonSecondYFactor y
                    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| := by
      calc
        _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            |∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              crossCommonTupleWeight s u *
                (∑ x : TupleLcmAllocation A,
                  tupleLcmAllocationMobiusWeight x *
                    tupleLcmAllocationCommonFirstYFactor y
                      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                    tupleLcmAllocationCommonSecondYFactor y
                      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              |crossCommonTupleWeight s u *
                (∑ x : TupleLcmAllocation A,
                  tupleLcmAllocationMobiusWeight x *
                    tupleLcmAllocationCommonFirstYFactor y
                      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                    tupleLcmAllocationCommonSecondYFactor y
                      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| := by
          gcongr with s hs
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          gcongr with s hs u hu
          rw [abs_mul]
          calc
            |crossCommonTupleWeight s u| *
                |∑ x : TupleLcmAllocation A,
                  tupleLcmAllocationMobiusWeight x *
                    tupleLcmAllocationCommonFirstYFactor y
                      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                    tupleLcmAllocationCommonSecondYFactor y
                      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x| ≤
                |crossCommonTupleWeight s u| *
                  ∑ x : TupleLcmAllocation A,
                    |tupleLcmAllocationMobiusWeight x *
                      tupleLcmAllocationCommonFirstYFactor y
                        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                      tupleLcmAllocationCommonSecondYFactor y
                        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
                (abs_nonneg _)
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              simp only [abs_mul]
    _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            ∑ _x : TupleLcmAllocation A,
              fixedLcmSupportedPrimeChargedMajorant A B s u := by
      gcongr with s hs u hu x hx
      exact abs_fixedLcm_transformed_summand_le_supportedPrimeCharged
        hB hyBound hySupport hAtotal s u hu hs x
    _ = (Fintype.card (TupleLcmAllocation A) : ℝ) *
          ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              fixedLcmSupportedPrimeChargedMajorant A B s u := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      push_cast
      simp_rw [← Finset.mul_sum]

theorem abs_fixedLcmCompatiblePairYValue_le_primeMultiplicitySum
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      (((4 ^ Fintype.card H) ^
        ω (BoundedGaps.Maynard.divisorTupleProduct H A) : ℕ) : ℝ) *
        ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            fixedLcmSupportedPrimeChargedMajorant A B s u := by
  have hsumNonneg : 0 ≤
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          fixedLcmSupportedPrimeChargedMajorant A B s u := by
    apply Finset.sum_nonneg
    intro s hs
    apply Finset.sum_nonneg
    intro u hu
    exact fixedLcmSupportedPrimeChargedMajorant_nonneg A hB s u
  calc
    |fixedLcmCompatiblePairYValue R y A| ≤
        (Fintype.card (TupleLcmAllocation A) : ℝ) *
          ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              fixedLcmSupportedPrimeChargedMajorant A B s u :=
      abs_fixedLcmCompatiblePairYValue_le_supportedPrimeChargedSum
        hB hyBound hySupport hAtotal
    _ ≤ (((4 ^ Fintype.card H) ^
          ω (BoundedGaps.Maynard.divisorTupleProduct H A) : ℕ) : ℝ) *
          ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              fixedLcmSupportedPrimeChargedMajorant A B s u := by
      apply mul_le_mul_of_nonneg_right _ hsumNonneg
      exact_mod_cast
        card_tupleLcmAllocation_le_four_pow_card_pow_omega hAtotal

/-- Final fixed-constraint estimate: allocation multiplicity, the common
`B²` scale, the new-prime factor `1/φ(a)`, and a completely explicit finite
Euler product. -/
theorem abs_fixedLcmCompatiblePairYValue_le_eulerProduct
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      (((4 ^ Fintype.card H) ^
        ω (BoundedGaps.Maynard.divisorTupleProduct H A) : ℕ) : ℝ) *
      (B ^ 2 *
        (((1 : ℝ) /
          Nat.totient (BoundedGaps.Maynard.divisorTupleProduct H A)) *
        ∏ pi ∈ crossBasePrimeLabelUniverse H R,
          (1 + crossBaseModifiedPrimeWeight
            (BoundedGaps.Maynard.divisorTupleProduct H A) pi.1 pi.2))) := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  let M : ℝ := (((4 ^ Fintype.card H) ^ ω a : ℕ) : ℝ)
  let S : ℝ :=
    ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
      ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
        crossBaseConstraintWeight A s u
  let E : ℝ := ((1 : ℝ) / Nat.totient a) *
    ∏ pi ∈ crossBasePrimeLabelUniverse H R,
      (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2)
  have hsumEq :
      (∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          fixedLcmSupportedPrimeChargedMajorant A B s u) = B ^ 2 * S := by
    unfold S
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    exact fixedLcmSupportedPrimeChargedMajorant_eq
      B hAtotal s u hs hu
  have hSE : S ≤ E := by
    exact sum_crossBaseConstraintWeight_le_eulerProduct R hAtotal
  have hM : 0 ≤ M := by positivity
  have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
  calc
    |fixedLcmCompatiblePairYValue R y A| ≤
        M *
          ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
            ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
              fixedLcmSupportedPrimeChargedMajorant A B s u := by
      exact abs_fixedLcmCompatiblePairYValue_le_primeMultiplicitySum
        hB hyBound hySupport hAtotal
    _ = M * (B ^ 2 * S) := by rw [hsumEq]
    _ ≤ M * (B ^ 2 * E) := by
      gcongr
    _ = _ := by rfl

/-- The fixed-lcm estimate with all constraint-dependent losses collected
into one constant per prime of the squarefree constraint product. -/
theorem abs_fixedLcmCompatiblePairYValue_le_baseEulerProduct
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      ((((4 ^ Fintype.card H) *
          (2 ^ Fintype.card (CrossBaseLabel H))) ^
        ω (BoundedGaps.Maynard.divisorTupleProduct H A) : ℕ) : ℝ) *
      (B ^ 2 *
        (((1 : ℝ) /
          Nat.totient (BoundedGaps.Maynard.divisorTupleProduct H A)) *
          crossBaseEulerProduct H R)) := by
  let a := BoundedGaps.Maynard.divisorTupleProduct H A
  let C₁ : ℕ := 4 ^ Fintype.card H
  let C₂ : ℕ := 2 ^ Fintype.card (CrossBaseLabel H)
  let E₀ : ℝ := crossBaseEulerProduct H R
  let E₁ : ℝ := ∏ pi ∈ crossBasePrimeLabelUniverse H R,
    (1 + crossBaseModifiedPrimeWeight a pi.1 pi.2)
  have hE : E₁ ≤ ((C₂ ^ ω a : ℕ) : ℝ) * E₀ := by
    exact modifiedCrossBaseEulerProduct_le H R hAtotal
  have houter : 0 ≤ ((C₁ ^ ω a : ℕ) : ℝ) := by positivity
  have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
  have hinv : 0 ≤ (1 : ℝ) / Nat.totient a := by positivity
  calc
    |fixedLcmCompatiblePairYValue R y A| ≤
        ((C₁ ^ ω a : ℕ) : ℝ) *
          (B ^ 2 * (((1 : ℝ) / Nat.totient a) * E₁)) := by
      exact abs_fixedLcmCompatiblePairYValue_le_eulerProduct
        hB hyBound hySupport hAtotal
    _ ≤ ((C₁ ^ ω a : ℕ) : ℝ) *
          (B ^ 2 * (((1 : ℝ) / Nat.totient a) *
            (((C₂ ^ ω a : ℕ) : ℝ) * E₀))) := by
      gcongr
    _ = ((((C₁ * C₂) ^ ω a : ℕ) : ℝ) *
          (B ^ 2 * (((1 : ℝ) / Nat.totient a) * E₀))) := by
      push_cast
      rw [mul_pow]
      ring
    _ = _ := by rfl

/-- The complete fixed-lcm transformed value is bounded by the sum of its
explicit nonnegative allocation majorants. -/
theorem abs_fixedLcmCompatiblePairYValue_le_majorantSum
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hy : ∀ r, |y r| ≤ B)
    (hA : ∀ h : H, 0 < A h) (R : ℕ) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          ∑ x : TupleLcmAllocation A,
            fixedLcmAllocationMajorant B s u x := by
  unfold fixedLcmCompatiblePairYValue
  calc
    |∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (∑ x : TupleLcmAllocation A,
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| ≤
        ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          |∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            crossCommonTupleWeight s u *
              (∑ x : TupleLcmAllocation A,
                tupleLcmAllocationMobiusWeight x *
                  tupleLcmAllocationCommonFirstYFactor y
                    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                  tupleLcmAllocationCommonSecondYFactor y
                    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            |crossCommonTupleWeight s u *
              (∑ x : TupleLcmAllocation A,
                tupleLcmAllocationMobiusWeight x *
                  tupleLcmAllocationCommonFirstYFactor y
                    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                  tupleLcmAllocationCommonSecondYFactor y
                    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| := by
      gcongr with s hs
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            ∑ x : TupleLcmAllocation A,
              |crossCommonTupleWeight s u *
                (tupleLcmAllocationMobiusWeight x *
                  tupleLcmAllocationCommonFirstYFactor y
                    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                  tupleLcmAllocationCommonSecondYFactor y
                    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)| := by
      gcongr with s hs u hu
      rw [abs_mul]
      calc
        |crossCommonTupleWeight s u| *
            |∑ x : TupleLcmAllocation A,
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x| ≤
            |crossCommonTupleWeight s u| *
              ∑ x : TupleLcmAllocation A,
                |tupleLcmAllocationMobiusWeight x *
                  tupleLcmAllocationCommonFirstYFactor y
                    (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                  tupleLcmAllocationCommonSecondYFactor y
                    (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (abs_nonneg _)
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          simp only [abs_mul]
    _ ≤ ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
          ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
            ∑ x : TupleLcmAllocation A,
              fixedLcmAllocationMajorant B s u x := by
      gcongr with s hs u hu x hx
      exact abs_fixedLcm_transformed_summand_le hB hy hA s u hu hs x

end

end Erdos4b
