import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ZMod
import ErdosProblems.Erdos920.Mixing

/-!
# Finite projective orthogonality for Erdős 920

This file isolates the finite-geometric input used in the algebraic construction
behind the lower bound for Erdős problem 920.  Points are honest one-dimensional
subspaces (Mathlib's `Projectivization`), rather than a choice of normalised
coordinates.  Consequently all incidence predicates are independent of choices
of representatives by construction.
-/

namespace Erdos920.Projective

open scoped BigOperators LinearAlgebra.Projectivization

noncomputable section

/-- The last term is a lower bound for a nonempty geometric sum. -/
theorem pow_pred_le_geomSum (q d : ℕ) (hd : 1 ≤ d) :
    q ^ (d - 1) ≤ ∑ i ∈ Finset.range d, q ^ i := by
  apply Finset.single_le_sum
  · intro i hi
    exact Nat.zero_le _
  · simp only [Finset.mem_range]
    omega

/-- For base at least two, a finite geometric sum is at most twice its
largest term.  The statement deliberately includes the empty-sum edge case. -/
theorem geomSum_le_two_mul_pow_pred (q d : ℕ) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range d, q ^ i) ≤ 2 * q ^ (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      cases d with
      | zero => simp
      | succ n =>
          rw [Finset.sum_range_succ]
          have hstep : 2 * q ^ n ≤ q ^ (n + 1) := by
            calc
              2 * q ^ n ≤ q * q ^ n := Nat.mul_le_mul_right (q ^ n) hq
              _ = q ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
          have ih' : (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ 2 * q ^ n := by
            simpa using ih
          have hold : (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ q ^ (n + 1) :=
            ih'.trans hstep
          simp only [Nat.add_sub_cancel]
          omega

/-- Monotonicity of finite geometric sums in their number of terms. -/
theorem geomSum_mono (q : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.range a, q ^ i) ≤ ∑ i ∈ Finset.range b, q ^ i :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

/-- Points of projective `(d - 1)`-space over `F`. -/
abbrev Point (F : Type*) [Field F] (d : ℕ) := ℙ F (Fin d → F)

/-- The dot-product polarity on finite projective space. -/
abbrev Orthogonal {F : Type*} [Field F] {d : ℕ} :
    Point F d → Point F d → Prop :=
  Projectivization.orthogonal

lemma orthogonal_comm {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    Orthogonal x y ↔ Orthogonal y x :=
  Projectivization.orthogonal_comm

/-- Projective space over a finite field is finite. -/
instance pointFinite (F : Type*) [Field F] [Finite F] (d : ℕ) :
    Finite (Point F d) := inferInstance

/-- The number of points in projective `(d - 1)`-space is the geometric sum
`1 + |F| + ⋯ + |F|^(d-1)`. -/
theorem natCard_point (F : Type*) [Field F] [Finite F] (d : ℕ) :
    Nat.card (Point F d) = ∑ i ∈ Finset.range d, Nat.card F ^ i := by
  apply Projectivization.card_of_finrank
  exact Module.finrank_fin_fun F

/-- The preceding cardinality formula for a prime field. -/
theorem natCard_point_zmod (q d : ℕ) [Fact q.Prime] :
    Nat.card (Point (ZMod q) d) = ∑ i ∈ Finset.range d, q ^ i := by
  simpa [Nat.card_zmod] using natCard_point (ZMod q) d

/-- The leading-term lower bound for projective `(d - 1)`-space. -/
theorem pow_pred_le_natCard_point_zmod (q d : ℕ) [Fact q.Prime]
    (hd : 1 ≤ d) :
    q ^ (d - 1) ≤ Nat.card (Point (ZMod q) d) := by
  rw [natCard_point_zmod]
  exact pow_pred_le_geomSum q d hd

/-- The leading-term upper bound for projective `(d - 1)`-space. -/
theorem natCard_point_zmod_le_two_mul_pow_pred (q d : ℕ) [Fact q.Prime] :
    Nat.card (Point (ZMod q) d) ≤ 2 * q ^ (d - 1) := by
  rw [natCard_point_zmod]
  exact geomSum_le_two_mul_pow_pred q d (Fact.out : q.Prime).two_le

/-- The point-count estimate in the `d = t + 1` indexing used by the
Erdős--Rogers construction. -/
theorem point_zmod_bounds (q t : ℕ) [Fact q.Prime] :
    q ^ t ≤ Nat.card (Point (ZMod q) (t + 1)) ∧
      Nat.card (Point (ZMod q) (t + 1)) ≤ 2 * q ^ t := by
  constructor
  · simpa using pow_pred_le_natCard_point_zmod q (t + 1) (by omega)
  · simpa using natCard_point_zmod_le_two_mul_pow_pred q (t + 1)

/-- Evaluation against a projective representative under the standard dot
product, bundled as a linear functional. -/
def dotFunctional {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    (Fin d → F) →ₗ[F] F :=
  (dotProductBilin F F) x.rep

@[simp] lemma dotFunctional_apply {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) (v : Fin d → F) :
    dotFunctional x v = x.rep ⬝ᵥ v := rfl

/-- The vector hyperplane polar to a projective point. -/
def orthSpace {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    Submodule F (Fin d → F) :=
  LinearMap.ker (dotFunctional x)

@[simp] lemma mem_orthSpace_iff {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) (v : Fin d → F) :
    v ∈ orthSpace x ↔ x.rep ⬝ᵥ v = 0 := by
  rfl

/-- The dot-product functional associated to a projective point is nonzero. -/
theorem dotFunctional_ne_zero {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    dotFunctional x ≠ 0 := by
  intro h
  have hz : ∀ v : Fin d → F, x.rep ⬝ᵥ v = 0 := by
    intro v
    have := LinearMap.congr_fun h v
    simpa using this
  exact x.rep_nonzero (dotProduct_eq_zero x.rep hz)

/-- Every polar hyperplane has codimension one.  This subtraction-free form is
convenient even in dimension zero (which in fact has no projective points). -/
theorem finrank_orthSpace_add_one {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) :
    Module.finrank F (orthSpace x) + 1 = d := by
  calc
    Module.finrank F (orthSpace x) + 1 = Module.finrank F (Fin d → F) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero (dotFunctional_ne_zero x)
    _ = d := Module.finrank_fin_fun F

/-- In positive dimension the polar hyperplane has dimension `d - 1`. -/
theorem finrank_orthSpace {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) :
    Module.finrank F (orthSpace x) = d - 1 := by
  have h := finrank_orthSpace_add_one x
  omega

/-- The dot-product polarity is nondegenerate: a point is determined by its
polar hyperplane. -/
theorem orthSpace_injective {F : Type*} [Field F] {d : ℕ} :
    Function.Injective (orthSpace : Point F d → Submodule F (Fin d → F)) := by
  intro x y hker
  obtain ⟨v, hfv⟩ : ∃ v : Fin d → F, dotFunctional x v ≠ 0 := by
    by_contra h
    push Not at h
    apply dotFunctional_ne_zero x
    apply LinearMap.ext
    intro w
    simpa using h w
  have hgv : dotFunctional y v ≠ 0 := by
    intro hzero
    have hvy : v ∈ orthSpace y := hzero
    have hvx : v ∈ orthSpace x := by rwa [hker]
    exact hfv hvx
  let c : F := dotFunctional x v / dotFunctional y v
  have hc : c ≠ 0 := div_ne_zero hfv hgv
  have hker' : LinearMap.ker (dotFunctional x) =
      LinearMap.ker (c • dotFunctional y) := by
    calc
      LinearMap.ker (dotFunctional x) = LinearMap.ker (dotFunctional y) := hker
      _ = LinearMap.ker (c • dotFunctional y) :=
        (LinearMap.ker_smul (dotFunctional y) c hc).symm
  have happ : dotFunctional x v = (c • dotFunctional y) v := by
    rw [LinearMap.smul_apply]
    change dotFunctional x v = c * dotFunctional y v
    exact (div_mul_cancel₀ (dotFunctional x v) hgv).symm
  have hfun : dotFunctional x = c • dotFunctional y :=
    Module.Dual.eq_of_ker_eq_of_apply_eq v hker' happ hfv
  have hrep : x.rep = c • y.rep := by
    apply dotProduct_eq
    intro w
    have hw := LinearMap.congr_fun hfun w
    simpa [dotFunctional, smul_dotProduct] using hw
  rw [← x.mk_rep, ← y.mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨c, hrep.symm⟩

/-- Orthogonality is membership in the polar hyperplane, expressed without a
choice of representative for the second point. -/
theorem orthogonal_iff_submodule_le {F : Type*} [Field F] {d : ℕ}
    (x y : Point F d) :
    Orthogonal x y ↔ y.submodule ≤ orthSpace x := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    mem_orthSpace_iff]
  conv_lhs =>
    rw [← x.mk_rep, ← y.mk_rep]
  exact Projectivization.orthogonal_mk x.rep_nonzero y.rep_nonzero

section ProjectivizeSubmodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The inclusion of a vector subspace induces an inclusion of its projective
space into the ambient projective space. -/
def projectivizeInclusion (S : Submodule F V) : ℙ F S → ℙ F V :=
  Projectivization.map S.subtype S.injective_subtype

theorem projectivizeInclusion_injective (S : Submodule F V) :
    Function.Injective (projectivizeInclusion S) :=
  Projectivization.map_injective S.subtype S.injective_subtype

/-- The image of `ℙ(S)` consists exactly of the projective points whose
one-dimensional vector subspace is contained in `S`. -/
theorem mem_range_projectivizeInclusion_iff (S : Submodule F V) (p : ℙ F V) :
    p ∈ Set.range (projectivizeInclusion S) ↔ p.submodule ≤ S := by
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Projectivization.ind with
    | h v hv =>
        rw [projectivizeInclusion, Projectivization.map_mk,
          Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
        exact v.property
  · intro hp
    have hrep : p.rep ∈ S := by
      apply hp
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self p.rep
    let v : S := ⟨p.rep, hrep⟩
    have hv : v ≠ 0 := by
      intro h
      exact p.rep_nonzero (congr_arg Subtype.val h)
    refine ⟨Projectivization.mk F v hv, ?_⟩
    rw [projectivizeInclusion, Projectivization.map_mk]
    exact p.mk_rep

/-- Projectivizing a submodule is equivalent to the subtype of ambient
projective points which it contains. -/
def pointsInEquiv (S : Submodule F V) :
    ℙ F S ≃ {p : ℙ F V // p.submodule ≤ S} :=
  (Equiv.ofInjective (projectivizeInclusion S)
      (projectivizeInclusion_injective S)).trans
    (Equiv.setCongr (Set.ext fun p ↦ mem_range_projectivizeInclusion_iff S p))

/-- Cardinality of the projective points contained in a finite-dimensional
submodule over a finite field. -/
theorem natCard_pointsIn [Finite F] [Finite V] (S : Submodule F V) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} =
      ∑ i ∈ Finset.range (Module.finrank F S), Nat.card F ^ i := by
  calc
    Nat.card {p : ℙ F V // p.submodule ≤ S} = Nat.card (ℙ F S) :=
      Nat.card_congr (pointsInEquiv S).symm
    _ = ∑ i ∈ Finset.range (Module.finrank F S), Nat.card F ^ i :=
      Projectivization.card_of_finrank F S rfl

/-- Leading-term lower bound for the projective points of a nonzero vector
subspace over a prime field. -/
theorem pow_pred_le_natCard_pointsIn_zmod
    {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] (S : Submodule (ZMod q) V) (hS : 1 ≤ Module.finrank (ZMod q) S) :
    q ^ (Module.finrank (ZMod q) S - 1) ≤
      Nat.card {p : ℙ (ZMod q) V // p.submodule ≤ S} := by
  rw [natCard_pointsIn]
  simpa [Nat.card_zmod] using
    pow_pred_le_geomSum q (Module.finrank (ZMod q) S) hS

/-- Leading-term upper bound for the projective points of any vector subspace
over a prime field, including the zero-dimensional edge case. -/
theorem natCard_pointsIn_zmod_le_two_mul_pow_pred
    {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] (S : Submodule (ZMod q) V) :
    Nat.card {p : ℙ (ZMod q) V // p.submodule ≤ S} ≤
      2 * q ^ (Module.finrank (ZMod q) S - 1) := by
  rw [natCard_pointsIn]
  simpa [Nat.card_zmod] using geomSum_le_two_mul_pow_pred q
    (Module.finrank (ZMod q) S) (Fact.out : q.Prime).two_le

/-- A zero-dimensional vector subspace contains no projective point. -/
theorem natCard_pointsIn_eq_zero_of_finrank_eq_zero
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    (S : Submodule F V) (hS : Module.finrank F S = 0) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} = 0 := by
  rw [natCard_pointsIn, hS]
  simp

/-- A one-dimensional vector subspace contains exactly one projective point. -/
theorem natCard_pointsIn_eq_one_of_finrank_eq_one
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    (S : Submodule F V) (hS : Module.finrank F S = 1) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} = 1 := by
  rw [natCard_pointsIn, hS]
  simp

end ProjectivizeSubmodule

/-- The projective neighbors of a point under the dot-product polarity.  A
self-orthogonal point belongs to its own neighborhood; this is the incidence
relation needed by the polarity construction, not yet a loopless graph. -/
abbrev Neighbors {F : Type*} [Field F] {d : ℕ} (x : Point F d) :=
  {y : Point F d // Orthogonal x y}

/-- The neighbors of `x` form the projectivization of its polar hyperplane. -/
def neighborsEquiv {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    ℙ F (orthSpace x) ≃ Neighbors x :=
  (pointsInEquiv (orthSpace x)).trans
    (Equiv.setCongr (Set.ext fun y ↦ (orthogonal_iff_submodule_le x y).symm))

/-- Every projective point has the same polarity degree. -/
theorem natCard_neighbors {F : Type*} [Field F] [Finite F] {d : ℕ}
    (x : Point F d) :
    Nat.card (Neighbors x) =
      ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
  calc
    Nat.card (Neighbors x) = Nat.card (ℙ F (orthSpace x)) :=
      Nat.card_congr (neighborsEquiv x).symm
    _ = ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
      apply Projectivization.card_of_finrank
      exact finrank_orthSpace x

/-- Uniform polarity degree over a prime field. -/
theorem natCard_neighbors_zmod (q : ℕ) [Fact q.Prime] {d : ℕ}
    (x : Point (ZMod q) d) :
    Nat.card (Neighbors x) = ∑ i ∈ Finset.range (d - 1), q ^ i := by
  simpa [Nat.card_zmod] using natCard_neighbors x

/-- The polarity degree estimates in the `d = t + 1` indexing. -/
theorem neighbor_zmod_bounds (q : ℕ) [Fact q.Prime] {t : ℕ} (ht : 1 ≤ t)
    (x : Point (ZMod q) (t + 1)) :
    q ^ (t - 1) ≤ Nat.card (Neighbors x) ∧
      Nat.card (Neighbors x) ≤ 2 * q ^ (t - 1) := by
  rw [natCard_neighbors_zmod]
  have hdim : t + 1 - 1 = t := by omega
  rw [hdim]
  exact ⟨pow_pred_le_geomSum q t ht,
    geomSum_le_two_mul_pow_pred q t (Fact.out : q.Prime).two_le⟩

/-- The common vector hyperplane cut out by two projective points. -/
def commonOrthSpace {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    Submodule F (Fin d → F) :=
  orthSpace x ⊓ orthSpace y

/-- Common projective neighbors for the polarity incidence relation. -/
abbrev CommonNeighbors {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :=
  {z : Point F d // Orthogonal x z ∧ Orthogonal y z}

/-- The common neighbors of two points projectivize the intersection of their
polar hyperplanes. -/
def commonNeighborsEquiv {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    ℙ F (commonOrthSpace x y) ≃ CommonNeighbors x y :=
  (pointsInEquiv (commonOrthSpace x y)).trans
    (Equiv.setCongr (Set.ext fun z ↦ by
      change z.submodule ≤ orthSpace x ⊓ orthSpace y ↔
        Orthogonal x z ∧ Orthogonal y z
      rw [le_inf_iff, ← orthogonal_iff_submodule_le x z,
        ← orthogonal_iff_submodule_le y z]))

/-- Distinct polar hyperplanes span the full coordinate space. -/
theorem sup_orthSpace_eq_top {F : Type*} [Field F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    orthSpace x ⊔ orthSpace y = ⊤ := by
  have hne : orthSpace x ≠ orthSpace y := by
    intro h
    exact hxy (orthSpace_injective h)
  have hnotle : ¬ orthSpace y ≤ orthSpace x := by
    intro hle
    apply hne
    symm
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_orthSpace y, finrank_orthSpace x]
  have hlt : orthSpace x < orthSpace x ⊔ orthSpace y := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    apply hnotle
    rw [heq]
    exact le_sup_right
  have hrank_lt := Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_le := Submodule.finrank_le (orthSpace x ⊔ orthSpace y)
  have hrank_eq : Module.finrank F ↑(orthSpace x ⊔ orthSpace y) = d := by
    rw [finrank_orthSpace x] at hrank_lt
    rw [Module.finrank_fin_fun] at hrank_le
    omega
  apply Submodule.eq_top_of_finrank_eq
  simpa [Module.finrank_fin_fun] using hrank_eq

/-- Two distinct polar hyperplanes meet in codimension two. -/
theorem finrank_commonOrthSpace {F : Type*} [Field F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    Module.finrank F (commonOrthSpace x y) = d - 2 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (orthSpace x) (orthSpace y)
  have htop : Module.finrank F (⊤ : Submodule F (Fin d → F)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  rw [sup_orthSpace_eq_top hxy, htop,
    finrank_orthSpace x, finrank_orthSpace y] at hdim
  change Module.finrank F ↑(orthSpace x ⊓ orthSpace y) = d - 2
  omega

/-- Distinct projective points have the same number of common polarity
neighbors. -/
theorem natCard_commonNeighbors {F : Type*} [Field F] [Finite F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) =
      ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
  calc
    Nat.card (CommonNeighbors x y) = Nat.card (ℙ F (commonOrthSpace x y)) :=
      Nat.card_congr (commonNeighborsEquiv x y).symm
    _ = ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
      apply Projectivization.card_of_finrank
      exact finrank_commonOrthSpace hxy

/-- Uniform distinct-pair common-neighbor count over a prime field. -/
theorem natCard_commonNeighbors_zmod (q : ℕ) [Fact q.Prime] {d : ℕ}
    {x y : Point (ZMod q) d} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) =
      ∑ i ∈ Finset.range (d - 2), q ^ i := by
  simpa [Nat.card_zmod] using natCard_commonNeighbors hxy

/-- The distinct-pair codegree estimates in the `d = t + 1` indexing. -/
theorem commonNeighbor_zmod_bounds (q : ℕ) [Fact q.Prime] {t : ℕ}
    (ht : 2 ≤ t) {x y : Point (ZMod q) (t + 1)} (hxy : x ≠ y) :
    q ^ (t - 2) ≤ Nat.card (CommonNeighbors x y) ∧
      Nat.card (CommonNeighbors x y) ≤ 2 * q ^ (t - 2) := by
  rw [natCard_commonNeighbors_zmod q hxy]
  have hdim : t + 1 - 2 = t - 1 := by omega
  have hpred : t - 1 - 1 = t - 2 := by omega
  rw [hdim]
  constructor
  · simpa [hpred] using pow_pred_le_geomSum q (t - 1) (by omega)
  · simpa [hpred] using geomSum_le_two_mul_pow_pred q (t - 1)
      (Fact.out : q.Prime).two_le

/-- The codegree upper bound remains valid without a dimension hypothesis. -/
theorem natCard_commonNeighbors_zmod_le (q : ℕ) [Fact q.Prime] {t : ℕ}
    {x y : Point (ZMod q) (t + 1)} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) ≤ 2 * q ^ (t - 2) := by
  rw [natCard_commonNeighbors_zmod q hxy]
  have hdim : t + 1 - 2 = t - 1 := by omega
  have hpred : t - 1 - 1 = t - 2 := by omega
  rw [hdim]
  simpa [hpred] using geomSum_le_two_mul_pow_pred q (t - 1)
    (Fact.out : q.Prime).two_le

section Mixing

/-- Convert a filtered-universe cardinality to the `Nat.card` of the
corresponding subtype.  This is the bridge from projective cardinality lemmas
to finite-relation hypotheses. -/
theorem card_filter_univ_eq_natCard_subtype
    {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x : X // p x} := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- `Finset` form of the uniform projective polarity degree. -/
theorem card_filter_orthogonal
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    (x : Point F d) :
    (Finset.univ.filter (Orthogonal x)).card =
      ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
  rw [card_filter_univ_eq_natCard_subtype]
  exact natCard_neighbors x

/-- `Finset` form of the uniform off-diagonal projective polarity codegree. -/
theorem card_filter_commonOrthogonal
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    {x y : Point F d} (hxy : x ≠ y) :
    (Finset.univ.filter fun z ↦ Orthogonal x z ∧ Orthogonal y z).card =
      ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
  rw [card_filter_univ_eq_natCard_subtype]
  exact natCard_commonNeighbors hxy

/-- A cleared-denominator, squared expander-mixing inequality for projective
orthogonality.  It follows from the exact degree and codegree counts above and
the finite second-moment calculation in `Erdos920.Mixing`; loops at isotropic
points are allowed and counted once. -/
theorem orthogonal_orderedEdges_deviation_sq_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    (((Fintype.card (Point F d) : ℝ) *
          Mixing.orderedEdges Orthogonal A B -
        (D : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) *
        ((Fintype.card (Point F d) : ℝ) ^ 2 *
            (D * B.card + C * B.card * (B.card - 1) : ℕ) -
          (Fintype.card (Point F d) : ℝ) * (D * B.card : ℕ) ^ 2)) := by
  dsimp only
  apply Mixing.orderedEdges_deviation_sq_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy

/-- The simpler design-form mixing estimate.  The hypothesis `C ≤ D` is
kept explicit so the statement also covers the small-dimensional edge cases
without hidden arithmetic assumptions. -/
theorem orthogonal_scaled_mixing_sq_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [Nonempty (Point F d)]
    [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    (((Fintype.card (Point F d) : ℝ) *
          Mixing.orderedEdges Orthogonal A B -
        (D : ℝ) * A.card * B.card) ^ 2 ≤
      (Fintype.card (Point F d) : ℝ) ^ 2 * ((D : ℝ) - C) *
        A.card * B.card) := by
  dsimp only
  apply Mixing.scaled_orderedEdges_deviation_sq_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy
  · exact geomSum_mono (Nat.card F) (by omega)

/-- Absolute-value form of projective expander mixing:
`|e(A,B) - D|A||B|/N| ≤ √((D-C)|A||B|)`. -/
theorem orthogonal_abs_orderedEdges_sub_expected_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [Nonempty (Point F d)]
    [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    |(Mixing.orderedEdges Orthogonal A B : ℝ) -
        (D : ℝ) / Fintype.card (Point F d) * A.card * B.card| ≤
      Real.sqrt (((D : ℝ) - C) * A.card * B.card) := by
  dsimp only
  apply Mixing.abs_orderedEdges_sub_expected_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy
  · exact geomSum_mono (Nat.card F) (by omega)

end Mixing

end

end Erdos920.Projective
