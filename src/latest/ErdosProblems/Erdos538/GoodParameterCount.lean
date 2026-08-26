import ErdosProblems.Erdos538.FiniteFieldCounts
import ErdosProblems.Erdos538.GeneratedGood

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

/-- The coefficient vector of the normalized relation enters the diagonal
isotropy equation through its coordinatewise square. -/
def squaredNormalizedNull {K ι : Type*} [Monoid K]
    (tail : ι → Kˣ) : Option ι → K :=
  fun o => (normalizedNull (fun i => (tail i : K)) o) ^ 2

/-- The squared normalized relation is nonzero (its `none` coordinate is one). -/
theorem squaredNormalizedNull_ne_zero
    {K ι : Type*} [MonoidWithZero K] [Nontrivial K] (tail : ι → Kˣ) :
    squaredNormalizedNull tail ≠ 0 := by
  intro h
  have := congrFun h none
  simp [squaredNormalizedNull, normalizedNull] at this

/-- Nonzero diagonal coefficient vectors satisfying isotropy for one
normalized relation. -/
abbrev IsotropicCoeffParam {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (tail : ι → Kˣ) :=
  {c : LinearMap.ker ((dotProductEquiv K (Option ι))
      (squaredNormalizedNull tail)) // c ≠ 0}

/-- For a `d+1`-coordinate normalized full-support relation, the admissible
nonzero diagonal coefficient vectors number `q^d-1`. -/
theorem natCard_isotropicCoeffParam
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (d : ℕ) (tail : Fin d → Kˣ) :
    Nat.card (IsotropicCoeffParam tail) = Nat.card K ^ d - 1 := by
  rw [natCard_ne_zero]
  rw [natCard_ker_dotProduct (squaredNormalizedNull_ne_zero tail)]
  simp

/-- Independent basis rows, indexed by `Fin d`. -/
abbrev BasisParam (K : Type*) [Field K] (d : ℕ) :=
  {b : Fin d → (Fin d → K) // LinearIndependent K b}

/-- The favorable fixed-child parameter space: a nonzero normalized tail, an
independent basis row family, and a nonzero isotropic diagonal coefficient
vector. -/
abbrev GoodParam (K : Type*) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) :=
  Σ tail : Fin d → Kˣ, BasisParam K d × IsotropicCoeffParam tail

/-- Exact count of independent basis row families. -/
theorem natCard_basisParam
    {K : Type*} [Field K] [Fintype K] (d : ℕ) :
    Nat.card (BasisParam K d) =
      ∏ i : Fin d, (Fintype.card K ^ d - Fintype.card K ^ i.val) := by
  simpa [BasisParam, Module.finrank_fintype_fun_eq_card] using
    (card_linearIndependent (K := K) (V := Fin d → K) (k := d) (by simp))

/-- There are `(q-1)^d` normalized full-support tails. -/
theorem natCard_unit_tails
    {K : Type*} [Field K] [Fintype K] (d : ℕ) :
    Nat.card (Fin d → Kˣ) = (Nat.card K - 1) ^ d := by
  rw [Nat.card_fun, Nat.card_units]
  simp

/-- Exact favorable-parameter count for one ordered child. -/
theorem natCard_goodParam
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (d : ℕ) :
    Nat.card (GoodParam K d) =
      (Nat.card K - 1) ^ d *
        (∏ i : Fin d, (Fintype.card K ^ d - Fintype.card K ^ i.val)) *
        (Nat.card K ^ d - 1) := by
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod, natCard_basisParam, natCard_isotropicCoeffParam]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_unit_tails]
  simp [Nat.mul_assoc]

/-- Cross-term coefficient vector controlling whether an outside row extends
the child null line orthogonally. -/
def crossVector
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) : Fin d → K :=
  fun i => p.2.2.1.1 (some i) * (p.1 i : K)

/-- The cross-term functional is nonzero.  Otherwise every `some` coefficient
vanishes (the tail is full support), and isotropy then forces the `none`
coefficient to vanish too, contradicting the nonzero coefficient condition. -/
theorem crossVector_ne_zero
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) : crossVector p ≠ 0 := by
  intro hcross
  have hsome : ∀ i, p.2.2.1.1 (some i) = 0 := by
    intro i
    have hi := congrFun hcross i
    simp only [crossVector, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_right (p.1 i).ne_zero
  have hiso := p.2.2.1.2
  change ((dotProductEquiv K (Option (Fin d))) (squaredNormalizedNull p.1))
    p.2.2.1.1 = 0 at hiso
  rw [dotProductEquiv_apply_apply] at hiso
  simp only [dotProduct, Fintype.sum_option, squaredNormalizedNull,
    normalizedNull, one_pow, one_mul] at hiso
  have hnone : p.2.2.1.1 none = 0 := by
    simpa [hsome] using hiso
  apply p.2.2.2
  apply Subtype.ext
  funext o
  cases o with
  | none => exact hnone
  | some i => exact hsome i

/-- Quadratic self-term in basis coordinates for an outside row. -/
def outsideQuad
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) (a : Fin d → K) : K :=
  ∑ i, p.2.2.1.1 (some i) * a i ^ 2

/-- Exact coordinate count of outside labels making the generated child's
parent relation plane totally isotropic. -/
theorem natCard_badOutsideCoords
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) :
    Nat.card {z : (Fin d → K) × K //
      (dotProductEquiv K (Fin d)) (crossVector p) z.1 = 0 ∧
      z.2 = -outsideQuad p z.1} = Nat.card K ^ (d - 1) := by
  simpa [Module.finrank_fintype_fun_eq_card] using
    natCard_bad_pairs ((dotProductEquiv K (Fin d)) (crossVector p))
      (dotProductEquiv_ne_zero (crossVector_ne_zero p))
      (fun a => -outsideQuad p a)

/-- All row/coefficient data on one ordered `d+1`-point child. -/
abbrev ChildSample (K : Type*) (d : ℕ) :=
  (Option (Fin d) → (Fin d → K)) × (Option (Fin d) → K)

/-- Forget a favorable parameterization to its generated row/coefficient
sample. -/
def goodParamToSample
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ} :
    GoodParam K d → ChildSample K d := fun p =>
  (generatedRows (fun i => (p.1 i : K)) p.2.1.1, p.2.2.1.1)

/-- Favorable parameterizations never overcount a child sample. -/
theorem goodParamToSample_injective
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ} :
    Function.Injective (@goodParamToSample K _ _ _ d) := by
  rintro ⟨pt, pb, pc⟩ ⟨qt, qb, qc⟩ hpq
  have hrows : generatedRows (fun i => (pt i : K)) pb.1 =
      generatedRows (fun i => (qt i : K)) qb.1 := congrArg Prod.fst hpq
  have htb := generatedRows_pair_injective pb.2 hrows
  have htail : pt = qt := by
    funext i
    apply Units.ext
    exact congrFun htb.1 i
  subst qt
  have hbasis : pb = qb := by
    apply Subtype.ext
    exact htb.2
  subst qb
  have hcoeff : pc = qc := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Prod.snd hpq
  subst qc
  rfl

/-- The image of a favorable parameter has a spanning row family, a
full-support isotropic relation, and a nonzero coefficient vector. -/
theorem goodParamToSample_properties
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (hd : 0 < d) (p : GoodParam K d) :
    let sample := goodParamToSample p
    let lam := normalizedNull (fun i => (p.1 i : K))
    (∀ o, lam o ≠ 0) ∧
    (∑ o, lam o • sample.1 o = 0) ∧
    Function.Surjective (Fintype.linearCombination K sample.1) ∧
    (dotProductEquiv K (Option (Fin d))) (fun o => lam o ^ 2) sample.2 = 0 ∧
    sample.2 ≠ 0 := by
  dsimp [goodParamToSample]
  have hcne : p.2.2.1.1 ≠ 0 := by
    intro h
    apply p.2.2.2
    apply Subtype.ext
    exact h
  refine ⟨normalizedNull_fullSupport one_ne_zero _ (fun i => (p.1 i).ne_zero),
    normalizedNull_generatedRows_relation _ _, ?_, ?_, hcne⟩
  · letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    exact generatedRows_surjective _ _ p.2.1.2
  · exact p.2.2.1.2

/-- Intrinsic good-child predicate on row/coefficient samples. -/
def IsGoodChildSample
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (sample : ChildSample K d) : Prop :=
  ∃ lam : Option (Fin d) → K,
    (∀ o, lam o ≠ 0) ∧
    (∑ o, lam o • sample.1 o = 0) ∧
    Function.Surjective (Fintype.linearCombination K sample.1) ∧
    (dotProductEquiv K (Option (Fin d))) (fun o => lam o ^ 2) sample.2 = 0 ∧
    sample.2 ≠ 0

/-- Every favorable parameter gives a distinct intrinsically good child
sample, so the exact parameter count is a rigorous lower bound. -/
theorem goodParam_card_le_goodSamples
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} (hd : 0 < d) :
    Nat.card (GoodParam K d) ≤
      Nat.card {sample : ChildSample K d // IsGoodChildSample sample} := by
  let f : GoodParam K d → {sample : ChildSample K d // IsGoodChildSample sample} :=
    fun p => ⟨goodParamToSample p,
      ⟨normalizedNull (fun i => (p.1 i : K)), goodParamToSample_properties hd p⟩⟩
  apply Nat.card_le_card_of_injective f
  intro p q hpq
  apply goodParamToSample_injective
  exact congrArg Subtype.val hpq

/-- Exact total number of child row/coefficient samples. -/
theorem natCard_childSample
    {K : Type*} [Field K] [Fintype K] (d : ℕ) :
    Nat.card (ChildSample K d) = Nat.card K ^ ((d + 1) * (d + 1)) := by
  simp only [ChildSample, Nat.card_prod, Nat.card_fun]
  simp
  ring_nf

end Erdos538.IsotropicKernel
