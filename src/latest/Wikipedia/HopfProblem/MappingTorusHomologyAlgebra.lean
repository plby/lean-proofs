import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# The signed two-arc algebra of the Wang sequence

For an integral endomorphism `F`, the signed two-arc Mayer--Vietoris map is
`(a,b) ↦ (a+b, -(a+F b))`.  This file identifies its kernel and extracts
the Wang difference `id-F` and the signed boundary `-fst ∘ d` from actual
range/kernel equalities supplied by a Mayer--Vietoris sequence.

Only linear algebra is asserted here.  The topological application must
supply the endomorphisms, maps, and exactness proofs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology.Algebra

open PeriodTorusHigherHomology

variable {M N P : Type*}
  [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N]
  [AddCommGroup P] [Module ℤ P]

/-- The Wang difference, with the sign fixed by the two-arc convention. -/
def difference (F : M →ₗ[ℤ] M) : M →ₗ[ℤ] M := LinearMap.id - F

@[simp] theorem difference_apply (F : M →ₗ[ℤ] M) (b : M) :
    difference F b = b - F b := rfl

/-- The first two-arc map with its actual Mayer--Vietoris minus sign. -/
def twoArcMap (F : M →ₗ[ℤ] M) : (M × M) →ₗ[ℤ] (M × M) :=
  intLinearMapOfAddHom
    { toFun p := (p.1 + p.2, -(p.1 + F p.2))
      map_zero' := by simp
      map_add' p q := by
        apply Prod.ext
        · exact add_add_add_comm p.1 q.1 p.2 q.2
        · change -((p.1 + q.1) + F (p.2 + q.2)) =
            -(p.1 + F p.2) + -(q.1 + F q.2)
          rw [map_add]
          abel }

@[simp] theorem twoArcMap_apply (F : M →ₗ[ℤ] M) (p : M × M) :
    twoArcMap F p = (p.1 + p.2, -(p.1 + F p.2)) := rfl

theorem pairSum_twoArcMap (F : M →ₗ[ℤ] M) (p : M × M) :
    pairSumMap M (twoArcMap F p) = difference F p.2 := by
  change (p.1 + p.2) + -(p.1 + F p.2) = p.2 - F p.2
  abel

/-- The kernel is precisely the antidiagonal on vectors fixed by `F`. -/
theorem twoArcMap_kernel_iff (F : M →ₗ[ℤ] M) (p : M × M) :
    twoArcMap F p = 0 ↔ p.1 = -p.2 ∧ difference F p.2 = 0 := by
  constructor
  · intro hp
    have hsum : p.1 + p.2 = 0 := congrArg Prod.fst hp
    refine ⟨eq_neg_of_add_eq_zero_left hsum, ?_⟩
    rw [← pairSum_twoArcMap F p, hp, map_zero]
  · rintro ⟨hfst, hfix⟩
    have hF : F p.2 = p.2 := (sub_eq_zero.mp hfix).symm
    rw [twoArcMap_apply, hfst, hF, neg_add_cancel, neg_zero]
    rfl

theorem twoArcMap_kernel_param (F : M →ₗ[ℤ] M) (p : M × M) :
    p ∈ LinearMap.ker (twoArcMap F) ↔
      ∃ b : LinearMap.ker (difference F), p = (-(b : M), (b : M)) := by
  change twoArcMap F p = 0 ↔ _
  rw [twoArcMap_kernel_iff]
  constructor
  · rintro ⟨hp, hb⟩
    exact ⟨⟨p.2, hb⟩, Prod.ext hp rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨rfl, b.property⟩

/-- The actual linear antidiagonal parametrization of the two-arc kernel. -/
def fixedAntidiagonal (F : M →ₗ[ℤ] M) :
    LinearMap.ker (difference F) →ₗ[ℤ] (M × M) :=
  intLinearMapOfAddHom
    { toFun b := (-(b : M), (b : M))
      map_zero' := by simp
      map_add' b c := by
        apply Prod.ext
        · exact neg_add (b : M) (c : M)
        · rfl }

@[simp] theorem fixedAntidiagonal_apply (F : M →ₗ[ℤ] M)
    (b : LinearMap.ker (difference F)) : fixedAntidiagonal F b = (-(b : M), (b : M)) := rfl

theorem range_fixedAntidiagonal (F : M →ₗ[ℤ] M) :
    LinearMap.range (fixedAntidiagonal F) = LinearMap.ker (twoArcMap F) := by
  ext p
  rw [twoArcMap_kernel_param]
  change (∃ b : LinearMap.ker (difference F), fixedAntidiagonal F b = p) ↔
    ∃ b : LinearMap.ker (difference F), p = (-(b : M), (b : M))
  simp only [fixedAntidiagonal_apply, eq_comm]

/-- Exactness of the actual two-arc maps gives the image/kernel equality for `id-F`. -/
theorem range_difference_eq_ker (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M))) :
    LinearMap.range (difference F) = LinearMap.ker i := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    have hb : twoArcMap F (0, b) ∈ LinearMap.range (twoArcMap F) := ⟨(0, b), rfl⟩
    rw [hJ] at hb
    change i (pairSumMap M (twoArcMap F (0, b))) = 0 at hb
    rw [pairSum_twoArcMap] at hb
    exact hb
  · intro hx
    have hix : i x = 0 := LinearMap.mem_ker.mp hx
    have hp : (x, 0) ∈ LinearMap.ker (i.comp (pairSumMap M)) := by
      change i (x + 0) = 0
      simpa only [add_zero] using hix
    rw [← hJ] at hp
    obtain ⟨p, hp⟩ := hp
    refine ⟨p.2, ?_⟩
    calc
      difference F p.2 = pairSumMap M (twoArcMap F p) := (pairSum_twoArcMap F p).symm
      _ = x := by rw [hp, pairSumMap_apply, add_zero]

/-- The Wang boundary is the negative first component of the actual connecting map. -/
def boundary (d : N →ₗ[ℤ] (P × P)) : N →ₗ[ℤ] P := (negativeFirstMap P).comp d

@[simp] theorem boundary_apply (d : N →ₗ[ℤ] (P × P)) (n : N) :
    boundary d n = -(d n).1 := rfl

theorem connecting_mem_kernel (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n ∈ LinearMap.ker (twoArcMap F) := by
  rw [← hd]
  exact ⟨n, rfl⟩

/-- On the actual connecting image, the negative first component equals the second. -/
theorem boundary_eq_snd (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    boundary d n = (d n).2 := by
  have hp := (twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)
  rw [boundary_apply, hp.1, neg_neg]

theorem connecting_eq_antidiagonal (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n = (-boundary d n, boundary d n) := by
  apply Prod.ext
  · simp only [boundary_apply, neg_neg]
  · exact (boundary_eq_snd F d hd n).symm

theorem boundary_mem_kernel (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    boundary d n ∈ LinearMap.ker (difference F) := by
  rw [boundary_eq_snd F d hd n]
  exact ((twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)).2

/-- Exactness at the next pair gives surjectivity onto the invariant kernel. -/
theorem boundary_range (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range (boundary d) = LinearMap.ker (difference F) := by
  ext b
  constructor
  · rintro ⟨n, rfl⟩
    exact boundary_mem_kernel F d hd n
  · intro hb
    have hp : (-b, b) ∈ LinearMap.ker (twoArcMap F) :=
      (twoArcMap_kernel_iff F (-b, b)).mpr ⟨rfl, hb⟩
    rw [← hd] at hp
    obtain ⟨n, hn⟩ := hp
    refine ⟨n, ?_⟩
    rw [boundary_apply, hn]
    exact neg_neg b

/-- The signed boundary loses no kernel information from the connecting map. -/
theorem boundary_ker (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (boundary d) = LinearMap.ker d := by
  ext n
  change boundary d n = 0 ↔ d n = 0
  constructor
  · intro hn
    rw [connecting_eq_antidiagonal F d hd n, hn, neg_zero]
    rfl
  · intro hn
    rw [boundary_apply, hn]
    exact neg_zero

/-- The unreduced Wang sequence is exact at its middle term. -/
theorem range_inclusion_eq_ker_boundary (F : P →ₗ[ℤ] P)
    (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range i = LinearMap.ker (boundary d) :=
  hi.trans (boundary_ker F d hd).symm

end Wikipedia.HopfProblem.MappingTorusHomology.Algebra
