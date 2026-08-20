import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve

/-!
# Integral coordinates in a fixed ideal lattice

This file records the compatibility which is implicit in the geometric
congruence-cell count.  The chosen real chart of a nonzero ideal lattice
sends the standard integral lattice onto that ideal lattice.  Consequently
every element of the ideal has a unique integral coordinate vector.  Its
reduction modulo `m` is exactly the label of the generator congruence cell
containing the element.

Keeping this bridge explicit is important in the odd-prime application: the
power-residue condition lives in the quotient ring of the cyclotomic integer
ring, whereas the lattice estimate is indexed by coordinate vectors.
-/

open scoped NumberField nonZeroDivisors Pointwise

namespace Erdos980.ElliottTail.OddMediumCoordinateBridge

noncomputable section

open NumberField
open NumberField.mixedEmbedding
open IdealGeneratorCongruenceCount

variable (K : Type*) [Field K] [NumberField K]
variable (J : (Ideal (RingOfIntegers K))⁰)

/-- Every element of a fixed nonzero ideal has integral coordinates in the
chosen ideal-lattice chart. -/
theorem exists_integralCoordinates
    (b : (J : Ideal (RingOfIntegers K))) :
    ∃ z : mixedEmbedding.index K → ℤ,
      idealLatticeChart J (fun i ↦ (z i : ℝ)) =
        (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K ((b.1 : RingOfIntegers K) : K)) := by
  classical
  have hbLattice :
      mixedEmbedding K ((b.1 : RingOfIntegers K) : K) ∈
        mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) := by
    rw [mixedEmbedding.mem_idealLattice]
    refine ⟨(b.1 : K), ?_, rfl⟩
    simp only [FractionalIdeal.coe_mk0]
    exact ⟨b.1, b.2, rfl⟩
  have hx :
      (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K ((b.1 : RingOfIntegers K) : K)) ∈
        (mixedEmbedding.stdBasis K).equivFunL ''
          (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) :
            Set (mixedEmbedding.mixedSpace K)) :=
    ⟨_, hbLattice, rfl⟩
  rw [← idealLatticeChart_image J] at hx
  obtain ⟨x, hxint, hxeq⟩ := hx
  have hxcoords : ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
    letI := Fintype.ofFinite (mixedEmbedding.index K)
    change x ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (mixedEmbedding.index K))) at hxint
    simpa only [
      (Pi.basisFun ℝ (mixedEmbedding.index K)).mem_span_iff_repr_mem ℤ x,
      Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm] using hxint
  choose z hz using hxcoords
  refine ⟨z, ?_⟩
  rw [← hxeq]
  congr 1
  funext i
  exact hz i

/-- The unique integral coordinate vector of an element of `J`. -/
def integralCoordinates (b : (J : Ideal (RingOfIntegers K))) :
    mixedEmbedding.index K → ℤ :=
  Classical.choose (exists_integralCoordinates K J b)

theorem idealLatticeChart_integralCoordinates
    (b : (J : Ideal (RingOfIntegers K))) :
    idealLatticeChart J (fun i ↦ (integralCoordinates K J b i : ℝ)) =
      (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K ((b.1 : RingOfIntegers K) : K)) :=
  Classical.choose_spec (exists_integralCoordinates K J b)

/-- Integral ideal-lattice coordinates determine the ideal element. -/
theorem integralCoordinates_injective :
    Function.Injective (integralCoordinates K J) := by
  intro a b hab
  apply Subtype.ext
  apply RingOfIntegers.coe_injective (K := K)
  apply mixedEmbedding_injective K
  apply (mixedEmbedding.stdBasis K).equivFunL.injective
  rw [← idealLatticeChart_integralCoordinates K J a,
    ← idealLatticeChart_integralCoordinates K J b, hab]

theorem integralCoordinates_zero :
    integralCoordinates K J (0 : (J : Ideal (RingOfIntegers K))) = 0 := by
  apply funext
  intro i
  have h := idealLatticeChart_integralCoordinates K J
    (0 : (J : Ideal (RingOfIntegers K)))
  have hz : idealLatticeChart J (0 : mixedEmbedding.index K → ℝ) = 0 :=
    map_zero _
  have : (fun i ↦ (integralCoordinates K J
      (0 : (J : Ideal (RingOfIntegers K))) i : ℝ)) = 0 := by
    apply (idealLatticeChart J).injective
    rw [h]
    simp
  have hi : (integralCoordinates K J
      (0 : (J : Ideal (RingOfIntegers K))) i : ℝ) = (0 : ℤ) := by
    simpa only [Int.cast_zero, Pi.zero_apply] using congrFun this i
  exact Int.cast_injective hi

theorem integralCoordinates_add
    (a b : (J : Ideal (RingOfIntegers K))) :
    integralCoordinates K J (a + b) =
      integralCoordinates K J a + integralCoordinates K J b := by
  apply funext
  intro i
  have hsum :
      (fun i ↦ (integralCoordinates K J (a + b) i : ℝ)) =
        (fun i ↦ (integralCoordinates K J a i : ℝ)) +
          (fun i ↦ (integralCoordinates K J b i : ℝ)) := by
    apply (idealLatticeChart J).injective
    rw [map_add, idealLatticeChart_integralCoordinates K J,
      idealLatticeChart_integralCoordinates K J,
      idealLatticeChart_integralCoordinates K J]
    change (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (((a.1 + b.1 : RingOfIntegers K)) : K)) =
      (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K ((a.1 : RingOfIntegers K) : K)) +
        (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K ((b.1 : RingOfIntegers K) : K))
    simp only [map_add]
  have hi : (integralCoordinates K J (a + b) i : ℝ) =
      ((integralCoordinates K J a + integralCoordinates K J b) i : ℤ) := by
    simpa only [Int.cast_add, Pi.add_apply] using congrFun hsum i
  exact Int.cast_injective hi

theorem integralCoordinates_neg
    (a : (J : Ideal (RingOfIntegers K))) :
    integralCoordinates K J (-a) = -integralCoordinates K J a := by
  apply funext
  intro i
  have hneg :
      (fun i ↦ (integralCoordinates K J (-a) i : ℝ)) =
        -(fun i ↦ (integralCoordinates K J a i : ℝ)) := by
    apply (idealLatticeChart J).injective
    rw [map_neg, idealLatticeChart_integralCoordinates K J,
      idealLatticeChart_integralCoordinates K J]
    change (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (((-a.1 : RingOfIntegers K)) : K)) =
      -(mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K ((a.1 : RingOfIntegers K) : K))
    simp only [map_neg]
  have hi : (integralCoordinates K J (-a) i : ℝ) =
      ((-integralCoordinates K J a) i : ℤ) := by
    simpa only [Int.cast_neg, Pi.neg_apply] using congrFun hneg i
  exact Int.cast_injective hi

theorem integralCoordinates_sub
    (a b : (J : Ideal (RingOfIntegers K))) :
    integralCoordinates K J (a - b) =
      integralCoordinates K J a - integralCoordinates K J b := by
  rw [sub_eq_add_neg, integralCoordinates_add, integralCoordinates_neg]
  rfl

theorem integralCoordinates_nsmul (n : ℕ)
    (a : (J : Ideal (RingOfIntegers K))) :
    integralCoordinates K J (n • a) = n • integralCoordinates K J a := by
  induction n with
  | zero => simp [integralCoordinates_zero]
  | succ n ih =>
      rw [succ_nsmul, integralCoordinates_add, ih, succ_nsmul]

theorem integralCoordinates_surjective :
    Function.Surjective (integralCoordinates K J) := by
  classical
  intro z
  let zr : mixedEmbedding.index K → ℝ := fun i ↦ (z i : ℝ)
  have hzmem : zr ∈
      (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (mixedEmbedding.index K))) :
          Set (mixedEmbedding.index K → ℝ)) := by
    letI := Fintype.ofFinite (mixedEmbedding.index K)
    change zr ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (mixedEmbedding.index K)))
    simp only [
      (Pi.basisFun ℝ (mixedEmbedding.index K)).mem_span_iff_repr_mem ℤ zr,
      Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm]
    exact fun i ↦ ⟨z i, rfl⟩
  have hchart : idealLatticeChart J zr ∈
      (mixedEmbedding.stdBasis K).equivFunL ''
        (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) :
          Set (mixedEmbedding.mixedSpace K)) := by
    rw [← idealLatticeChart_image J]
    exact ⟨zr, hzmem, rfl⟩
  obtain ⟨v, hv, hvchart⟩ := hchart
  rw [SetLike.mem_coe, mixedEmbedding.mem_idealLattice] at hv
  obtain ⟨y, hy, hyemb⟩ := hv
  simp only [FractionalIdeal.coe_mk0] at hy
  obtain ⟨b, hb, hby⟩ := hy
  let bJ : (J : Ideal (RingOfIntegers K)) := ⟨b, hb⟩
  refine ⟨bJ, ?_⟩
  funext i
  have hreal :
      (fun i ↦ (integralCoordinates K J bJ i : ℝ)) = zr := by
    apply (idealLatticeChart J).injective
    rw [idealLatticeChart_integralCoordinates K J]
    calc
      (mixedEmbedding.stdBasis K).equivFunL
          (mixedEmbedding K ((bJ.1 : RingOfIntegers K) : K)) =
          (mixedEmbedding.stdBasis K).equivFunL (mixedEmbedding K y) := by
            congr 2
      _ = (mixedEmbedding.stdBasis K).equivFunL v := by rw [hyemb]
      _ = idealLatticeChart J zr := hvchart
  have hi : (integralCoordinates K J bJ i : ℝ) = (z i : ℤ) := by
    simpa only [zr] using congrFun hreal i
  exact Int.cast_injective hi

/-- The chosen lattice chart induces an additive equivalence between the
fixed ideal and the standard integral coordinate lattice. -/
def integralCoordinatesAddEquiv :
    (J : Ideal (RingOfIntegers K)) ≃+ (mixedEmbedding.index K → ℤ) := by
  let f : (J : Ideal (RingOfIntegers K)) →+
      (mixedEmbedding.index K → ℤ) :=
    { toFun := integralCoordinates K J
      map_zero' := integralCoordinates_zero K J
      map_add' := integralCoordinates_add K J }
  exact AddEquiv.ofBijective f
    ⟨integralCoordinates_injective K J,
      integralCoordinates_surjective K J⟩

/-- Reduction of the integral ideal-lattice coordinates modulo `m`. -/
def coordinateResidue (m : ℕ)
    (b : (J : Ideal (RingOfIntegers K))) :
    mixedEmbedding.index K → ZMod m :=
  fun i ↦ (integralCoordinates K J b i : ZMod m)

theorem coordinateResidue_add (m : ℕ)
    (a b : (J : Ideal (RingOfIntegers K))) :
    coordinateResidue K J m (a + b) =
      coordinateResidue K J m a + coordinateResidue K J m b := by
  funext i
  simp [coordinateResidue, integralCoordinates_add]

theorem coordinateResidue_sub (m : ℕ)
    (a b : (J : Ideal (RingOfIntegers K))) :
    coordinateResidue K J m (a - b) =
      coordinateResidue K J m a - coordinateResidue K J m b := by
  funext i
  simp [coordinateResidue, integralCoordinates_sub]

theorem coordinateResidue_nsmul_self (m : ℕ)
    (a : (J : Ideal (RingOfIntegers K))) :
    coordinateResidue K J m (m • a) = 0 := by
  funext i
  simp [coordinateResidue, integralCoordinates_nsmul]

/-- The representative already used by the geometric cell count, packaged
as an element of the fixed ideal. -/
def coordinateRepresentative {m : ℕ}
    (k : mixedEmbedding.index K → ZMod m) :
    (J : Ideal (RingOfIntegers K)) :=
  ⟨RayNormPrimeSieve.generatorOfCoordinate K J k,
    RayNormPrimeSieve.generatorOfCoordinate_mem K J k⟩

theorem integralCoordinates_coordinateRepresentative {m : ℕ}
    (k : mixedEmbedding.index K → ZMod m) (i : mixedEmbedding.index K) :
    integralCoordinates K J (coordinateRepresentative K J k) i = (k i).val := by
  have hcoords := idealLatticeChart_integralCoordinates K J
    (coordinateRepresentative K J k)
  have hrep := RayNormPrimeSieve.embedding_generatorOfCoordinate K J k
  have hreal :
      (fun i ↦ (integralCoordinates K J
        (coordinateRepresentative K J k) i : ℝ)) =
        fun i ↦ ((k i).val : ℝ) := by
    apply (idealLatticeChart J).injective
    rw [hcoords]
    simpa only [coordinateRepresentative, generatorCongruenceTranslate] using hrep
  exact_mod_cast congrFun hreal i

@[simp] theorem coordinateResidue_coordinateRepresentative {m : ℕ}
    [NeZero m]
    (k : mixedEmbedding.index K → ZMod m) :
    coordinateResidue K J m (coordinateRepresentative K J k) = k := by
  funext i
  rw [coordinateResidue, integralCoordinates_coordinateRepresentative]
  simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (k i)

theorem coordinateResidue_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (coordinateResidue K J m) := by
  intro k
  exact ⟨coordinateRepresentative K J k,
    coordinateResidue_coordinateRepresentative K J k⟩

/-- Equality of coordinate residues is equivalent to coordinatewise
divisibility of the integral-coordinate difference. -/
theorem coordinateResidue_eq_iff_dvd_sub {m : ℕ}
    {a b : (J : Ideal (RingOfIntegers K))} :
    coordinateResidue K J m a = coordinateResidue K J m b ↔
      ∀ i, (m : ℤ) ∣
        integralCoordinates K J a i - integralCoordinates K J b i := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [coordinateResidue, coordinateResidue,
      ← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    exact hi
  · intro h
    funext i
    rw [coordinateResidue, coordinateResidue,
      ← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h i

/-- Coordinate congruence is literal congruence modulo the subideal `mJ`. -/
theorem coordinateResidue_eq_iff_exists_sub_eq_nsmul {m : ℕ}
    {a b : (J : Ideal (RingOfIntegers K))} :
    coordinateResidue K J m a = coordinateResidue K J m b ↔
      ∃ c : (J : Ideal (RingOfIntegers K)), a - b = m • c := by
  constructor
  · intro h
    have hdvd := (coordinateResidue_eq_iff_dvd_sub K J).mp h
    choose z hz using hdvd
    obtain ⟨c, hc⟩ := integralCoordinates_surjective K J z
    refine ⟨c, ?_⟩
    apply integralCoordinates_injective K J
    rw [integralCoordinates_sub, integralCoordinates_nsmul, hc]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul]
    exact hz i
  · rintro ⟨c, h⟩
    have := congrArg (coordinateResidue K J m) h
    rw [coordinateResidue_sub, coordinateResidue_nsmul_self] at this
    exact sub_eq_zero.mp this

/-- Send a coordinate vector to the residue class of its fixed-ideal
representative. -/
def coordinateToIdealQuotient (Q : Ideal (RingOfIntegers K)) (m : ℕ) :
    (mixedEmbedding.index K → ZMod m) →
      RingOfIntegers K ⧸ Q :=
  fun k ↦ Ideal.Quotient.mk Q (coordinateRepresentative K J k).1

/-- If the fixed ideal is coprime to the scalar ideal `(m)`, coordinate
vectors modulo `m` are exactly the residue classes modulo `(m)`. -/
theorem coordinateToIdealQuotient_bijective (m : ℕ)
    [NeZero m]
    (Q : Ideal (RingOfIntegers K))
    (hQ : Q = Ideal.span ({(m : RingOfIntegers K)} : Set (RingOfIntegers K)))
    (hcop : IsCoprime (J : Ideal (RingOfIntegers K)) Q) :
    Function.Bijective (coordinateToIdealQuotient K J Q m) := by
  classical
  constructor
  · intro k l hkl
    have hmem :
        (coordinateRepresentative K J k).1 -
            (coordinateRepresentative K J l).1 ∈ Q :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hkl
    have hmemJ :
        (coordinateRepresentative K J k).1 -
            (coordinateRepresentative K J l).1 ∈
          (J : Ideal (RingOfIntegers K)) :=
      (J : Ideal (RingOfIntegers K)).sub_mem
        (coordinateRepresentative K J k).2
        (coordinateRepresentative K J l).2
    have hprod :
        (coordinateRepresentative K J k).1 -
            (coordinateRepresentative K J l).1 ∈
          (J : Ideal (RingOfIntegers K)) * Q := by
      rw [Ideal.mul_eq_inf_of_isCoprime hcop]
      exact ⟨hmemJ, hmem⟩
    rw [hQ, Ideal.mem_mul_span_singleton] at hprod
    obtain ⟨c, hcJ, hc⟩ := hprod
    let cJ : (J : Ideal (RingOfIntegers K)) := ⟨c, hcJ⟩
    have hsub : coordinateRepresentative K J k -
        coordinateRepresentative K J l = m • cJ := by
      apply Subtype.ext
      simpa [cJ, nsmul_eq_mul, mul_comm] using hc.symm
    have hres := congrArg (coordinateResidue K J m) hsub
    rw [coordinateResidue_sub, coordinateResidue_nsmul_self,
      coordinateResidue_coordinateRepresentative,
      coordinateResidue_coordinateRepresentative] at hres
    exact sub_eq_zero.mp hres
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha : a ∈
        (J : Ideal (RingOfIntegers K)) ⊔ Q := by
      rw [hcop.sup_eq]
      trivial
    rw [Submodule.mem_sup] at ha
    obtain ⟨b, hbJ, c, hcQ, hbc⟩ := ha
    let bJ : (J : Ideal (RingOfIntegers K)) := ⟨b, hbJ⟩
    let k := coordinateResidue K J m bJ
    refine ⟨k, ?_⟩
    have hsame : coordinateResidue K J m
        (coordinateRepresentative K J k) = coordinateResidue K J m bJ := by
      simp [k]
    obtain ⟨d, hd⟩ :=
      (coordinateResidue_eq_iff_exists_sub_eq_nsmul K J).mp hsame
    apply Ideal.Quotient.eq.mpr
    have hrepb :
        (coordinateRepresentative K J k).1 - b ∈ Q := by
      rw [hQ]
      apply Ideal.mem_span_singleton.mpr
      refine ⟨d.1, ?_⟩
      simpa [nsmul_eq_mul, mul_comm] using congrArg Subtype.val hd
    have hba : b - a ∈ Q := by
      have : b + c = a := hbc
      rw [← this]
      simpa using Q.neg_mem hcQ
    simpa [sub_eq_add_neg, add_assoc] using Q.add_mem hrepb hba

/-- Coordinate residues and the scalar quotient ring are equivalent whenever
the fixed ideal is coprime to the scalar ideal. -/
def coordinateIdealQuotientEquiv (m : ℕ)
    [NeZero m]
    (Q : Ideal (RingOfIntegers K))
    (hQ : Q = Ideal.span ({(m : RingOfIntegers K)} : Set (RingOfIntegers K)))
    (hcop : IsCoprime (J : Ideal (RingOfIntegers K)) Q) :
    (mixedEmbedding.index K → ZMod m) ≃ (RingOfIntegers K ⧸ Q) :=
  Equiv.ofBijective (coordinateToIdealQuotient K J Q m)
    (coordinateToIdealQuotient_bijective K J m Q hQ hcop)

theorem coordinateIdealQuotientEquiv_apply (m : ℕ)
    [NeZero m]
    (Q : Ideal (RingOfIntegers K))
    (hQ : Q = Ideal.span ({(m : RingOfIntegers K)} : Set (RingOfIntegers K)))
    (hcop : IsCoprime (J : Ideal (RingOfIntegers K)) Q)
    (k : mixedEmbedding.index K → ZMod m) :
    coordinateIdealQuotientEquiv K J m Q hQ hcop k =
      Ideal.Quotient.mk Q (coordinateRepresentative K J k).1 := rfl

/-- The unit residues of the quotient ring embed as the full-unit coordinate
cells modulo the scalar modulus. -/
def quotientUnitsCoordinateEmbedding (m : ℕ)
    [NeZero m]
    (Q : Ideal (RingOfIntegers K))
    (hQ : Q = Ideal.span ({(m : RingOfIntegers K)} : Set (RingOfIntegers K)))
    (hcop : IsCoprime (J : Ideal (RingOfIntegers K)) Q) :
    (RingOfIntegers K ⧸ Q)ˣ ↪
      (mixedEmbedding.index K → ZMod m) where
  toFun u := (coordinateIdealQuotientEquiv K J m Q hQ hcop).symm u.1
  inj' := by
    intro u v huv
    apply Units.ext
    exact (coordinateIdealQuotientEquiv K J m Q hQ hcop).symm.injective huv

end

end Erdos980.ElliottTail.OddMediumCoordinateBridge
