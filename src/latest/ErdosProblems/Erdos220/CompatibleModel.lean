import ErdosProblems.Erdos220.CompatibleFundamental
import ErdosProblems.Erdos220.CompatiblePrimeCoordinate
import ErdosProblems.Erdos220.CompatibleStateEquiv

/-!
# The prime-by-prime compatible fundamental model

This file realizes the abstract `CompatibleFundamentalModel` by iterating the
prime-local compatible coordinates over exactly the primes used by one of the
six supports.  Omitting unused prime factors is essential: their local
compatibility equation is identically zero, and introducing them into the
tensor product would create a spurious cardinality loss.
-/

open scoped BigOperators

namespace Erdos220

noncomputable section

/-- The set of the six factors in whose frequency support `p` occurs. -/
def primeSupport (U : Fin 6 → Finset ℕ) (p : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ p ∈ U i

@[simp] lemma mem_primeSupport {U : Fin 6 → Finset ℕ} {p : ℕ} {i : Fin 6} :
    i ∈ primeSupport U p ↔ p ∈ U i := by
  simp [primeSupport]

/-- The union of the six frequency supports. -/
def usedPrimes (U : Fin 6 → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion U

lemma mem_usedPrimes {U : Fin 6 → Finset ℕ} {p : ℕ} :
    p ∈ usedPrimes U ↔ ∃ i : Fin 6, p ∈ U i := by
  simp [usedPrimes]

abbrev UsedPrimeIndex (U : Fin 6 → Finset ℕ) := {p : ℕ // p ∈ usedPrimes U}

/-- The ordered list of used primes.  Its order only fixes nested product
types and has no mathematical significance. -/
def usedPrimeIndexList (U : Fin 6 → Finset ℕ) : List (UsedPrimeIndex U) :=
  (usedPrimes U).attach.toList

@[simp] lemma mem_usedPrimeIndexList {U : Fin 6 → Finset ℕ}
    (p : UsedPrimeIndex U) : p ∈ usedPrimeIndexList U := by
  simp [usedPrimeIndexList]

/-- Iteration of the compatible prime coordinate over a list of used primes. -/
noncomputable def compatibleSystemList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    List (UsedPrimeIndex U) → FundamentalSystem
  | [] => .nil
  | p :: ps => by
      letI : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      exact .cons
        (compatiblePrimeCoordinate p.1 (primeSupport U p.1) (hmult p.1 p.2))
        (compatibleSystemList s U hsub hmult ps)

/-- The full tensor system over the used primes. -/
noncomputable def compatibleSystem (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    FundamentalSystem :=
  compatibleSystemList s U hsub hmult (usedPrimeIndexList U)

/-- The residue in the `p`-coordinate belonging to a primitive-frequency
tuple, with zero inserted outside its support. -/
def primitiveResidue {T : Finset ℕ} (a : PrimitiveFrequencyTuple T) (p : ℕ) :
    ZMod p :=
  if hp : p ∈ T then ((a ⟨p, hp⟩).1 : ZMod p) else 0

@[simp] lemma primitiveResidue_of_mem {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) {p : ℕ} (hp : p ∈ T) :
    primitiveResidue a p = ((a ⟨p, hp⟩).1 : ZMod p) := by
  simp [primitiveResidue, hp]

@[simp] lemma primitiveResidue_of_not_mem {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) {p : ℕ} (hp : p ∉ T) :
    primitiveResidue a p = 0 := by
  simp [primitiveResidue, hp]

/-- Encode one primitive-frequency tuple into a nested value product. -/
def compatibleValueEncodeList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (L : List (UsedPrimeIndex U)) → (i : Fin 6) →
      PrimitiveFrequencyTuple (U i) →
        (compatibleSystemList s U hsub hmult L).Value i
  | [], _, _ => ()
  | p :: ps, i, a =>
      (primitiveResidue a p.1,
        compatibleValueEncodeList s U hsub hmult ps i a)

def compatibleValueEncode (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    (compatibleSystem s U hsub hmult).Value i :=
  compatibleValueEncodeList s U hsub hmult (usedPrimeIndexList U) i a

private lemma natCast_injective_below {p a b : ℕ} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h

private lemma compatibleValueEncodeList_component
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (i : Fin 6) (q : U i)
    (hmem : ∃ p ∈ L, p.1 = q.1)
    {a b : PrimitiveFrequencyTuple (U i)}
    (hab : compatibleValueEncodeList s U hsub hmult L i a =
      compatibleValueEncodeList s U hsub hmult L i b) : a q = b q := by
  induction L with
  | nil =>
      obtain ⟨p, hp, _⟩ := hmem
      simp at hp
  | cons p ps ih =>
      let : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      by_cases hqp : q.1 = p.1
      · have hpU : p.1 ∈ U i := by simpa [hqp] using q.2
        have hqeq : q = ⟨p.1, hpU⟩ := Subtype.ext hqp
        have hfst := congrArg Prod.fst hab
        simp only [compatibleValueEncodeList] at hfst
        have hcast : ((a ⟨p.1, hpU⟩).1 : ZMod p.1) =
            ((b ⟨p.1, hpU⟩).1 : ZMod p.1) := by
          rw [primitiveResidue_of_mem a hpU, primitiveResidue_of_mem b hpU] at hfst
          exact hfst
        apply Subtype.ext
        rw [hqeq]
        apply natCast_injective_below (p := p.1) _ _ hcast
        · exact Finset.mem_range.mp (Finset.mem_filter.mp (a ⟨p.1, hpU⟩).2).1
        · exact Finset.mem_range.mp (Finset.mem_filter.mp (b ⟨p.1, hpU⟩).2).1
      · apply ih
        · obtain ⟨t, htL, htr⟩ := hmem
          simp only [List.mem_cons] at htL
          rcases htL with rfl | ht
          · exact (hqp htr.symm).elim
          · exact ⟨t, ht, htr⟩
        · exact congrArg Prod.snd hab

lemma compatibleValueEncodeList_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (i : Fin 6)
    (hcover : ∀ q ∈ U i, ∃ p ∈ L, p.1 = q) :
    Function.Injective (compatibleValueEncodeList s U hsub hmult L i) := by
  intro a b hab
  funext q
  exact compatibleValueEncodeList_component s U hsub hmult L i q
    (hcover q.1 q.2) hab

lemma compatibleValueEncode_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) : Function.Injective (compatibleValueEncode s U hsub hmult i) := by
  apply compatibleValueEncodeList_injective
  intro q hq
  let p : UsedPrimeIndex U := ⟨q, mem_usedPrimes.mpr ⟨i, hq⟩⟩
  exact ⟨p, mem_usedPrimeIndexList p, rfl⟩

lemma sixLocalFrequency_eq_sum_primitiveResidue
    {U : Fin 6 → Finset ℕ} (a : SixPrimitiveFrequencyTuple U) (p : ℕ) :
    sixLocalFrequency a p = ∑ i, primitiveResidue (a i) p := by
  unfold sixLocalFrequency sixLocalFrequencyNat primitiveResidue
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p ∈ U i <;> simp [hpi]

/-- The local compatible residue vector supplied by a globally compatible
primitive tuple. -/
def compatibleLocalState (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (a : CompatiblePrimitiveTuple s U) (p : UsedPrimeIndex U) :
    CompatiblePrimeState p.1 (primeSupport U p.1) := by
  refine ⟨fun i ↦ primitiveResidue (a.1 i) p.1, ?_, ?_⟩
  · intro i hi
    exact primitiveResidue_of_not_mem _ (by simpa using hi)
  · have hp : p.1 ∈ s.primeFactors := hsub p.2
    rw [← sixLocalFrequency_eq_sum_primitiveResidue]
    exact a.2 p.1 hp

/-- Encode a compatible primitive tuple in the nested state product. -/
def compatibleStateEncodeList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (L : List (UsedPrimeIndex U)) → CompatiblePrimitiveTuple s U →
      (compatibleSystemList s U hsub hmult L).State
  | [], _ => ()
  | p :: ps, a =>
      (compatibleLocalState s U hsub a p,
        compatibleStateEncodeList s U hsub hmult ps a)

def compatibleStateEncode (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) :
    (compatibleSystem s U hsub hmult).State :=
  compatibleStateEncodeList s U hsub hmult (usedPrimeIndexList U) a

lemma project_compatibleStateEncodeList
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (a : CompatiblePrimitiveTuple s U) (i : Fin 6) :
    (compatibleSystemList s U hsub hmult L).project i
        (compatibleStateEncodeList s U hsub hmult L a) =
      compatibleValueEncodeList s U hsub hmult L i (a.1 i) := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
      apply Prod.ext
      · rfl
      · exact ih

lemma project_compatibleStateEncode
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) (i : Fin 6) :
    (compatibleSystem s U hsub hmult).project i
        (compatibleStateEncode s U hsub hmult a) =
      compatibleValueEncode s U hsub hmult i (a.1 i) :=
  project_compatibleStateEncodeList s U hsub hmult _ a i

/-- Every element of a system's explicit value finset is present. -/
lemma mem_valueElements (t : FundamentalSystem) (i : Fin 6) (x : t.Value i) :
    x ∈ t.valueElements i := by
  induction t with
  | nil => simp [FundamentalSystem.valueElements]
  | cons c t ih =>
      exact Finset.mem_product.mpr ⟨(c.valueFintype i).complete x.1, ih x.2⟩

/-- Every state is present in a system's explicit state finset. -/
lemma mem_stateElements (t : FundamentalSystem) (x : t.State) :
    x ∈ t.stateElements := by
  induction t with
  | nil => simp [FundamentalSystem.stateElements]
  | cons c t ih =>
      exact Finset.mem_product.mpr ⟨c.stateFintype.complete x.1, ih x.2⟩

/-- Jointly, the six projections of the compatible prime system determine
its state. -/
lemma compatibleSystemList_project_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) :
    Function.Injective
      (fun x : (compatibleSystemList s U hsub hmult L).State ↦
        fun i ↦ (compatibleSystemList s U hsub hmult L).project i x) := by
  induction L with
  | nil =>
      intro x y h
      cases x
      cases y
      rfl
  | cons p ps ih =>
      intro x y h
      apply Prod.ext
      · apply Subtype.ext
        funext i
        exact congrArg Prod.fst (congrFun h i)
      · apply ih
        funext i
        exact congrArg Prod.snd (congrFun h i)

lemma compatibleStateEncode_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    Function.Injective (compatibleStateEncode s U hsub hmult) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply compatibleValueEncode_injective s U hsub hmult i
  rw [← project_compatibleStateEncode s U hsub hmult a i,
    ← project_compatibleStateEncode s U hsub hmult b i, hab]

/-- The selected value domain is precisely the image of primitive
frequencies. -/
def compatibleValueDomain (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) : Finset ((compatibleSystem s U hsub hmult).Value i) := by
  classical
  exact Finset.univ.image (compatibleValueEncode s U hsub hmult i)

noncomputable def compatibleValueEquiv
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) :
    PrimitiveFrequencyTuple (U i) ≃
      {x : (compatibleSystem s U hsub hmult).Value i //
        x ∈ compatibleValueDomain s U hsub hmult i} :=
  (Equiv.ofInjective _ (compatibleValueEncode_injective s U hsub hmult i)).trans
    (Equiv.setCongr (by
      ext x
      simp [compatibleValueDomain]))

@[simp] lemma compatibleValueEquiv_apply_val
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    ((compatibleValueEquiv s U hsub hmult i) a).1 =
      compatibleValueEncode s U hsub hmult i a := rfl

/-- Local sum-zero states imply all compatibility equations belonging to
coordinates present in the list. -/
lemma compatible_of_project_eq_list
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (a : SixPrimitiveFrequencyTuple U)
    (x : (compatibleSystemList s U hsub hmult L).State)
    (hproject : ∀ i,
      (compatibleSystemList s U hsub hmult L).project i x =
        compatibleValueEncodeList s U hsub hmult L i (a i)) :
    ∀ p ∈ L, sixLocalFrequency a p.1 = 0 := by
  induction L with
  | nil => simp
  | cons head tail ih =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with hpEq | hp
      · have peq : p = head := by exact hpEq
        subst p
        rw [sixLocalFrequency_eq_sum_primitiveResidue]
        calc
          ∑ i, primitiveResidue (a i) head.1 = ∑ i, x.1.1 i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (congrArg Prod.fst (hproject i)).symm
          _ = 0 := x.1.2.2
      · apply ih x.2 (fun i ↦ congrArg Prod.snd (hproject i)) p hp

/-- Decode a good system state into primitive tuples and prove all the
prime-compatibility equations, including the tautological equations at
unused prime factors. -/
lemma decoded_is_compatible
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (x : (compatibleSystem s U hsub hmult).State)
    (hx : ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
      compatibleValueDomain s U hsub hmult i) :
    sixPrimeCompatible s (fun i ↦
      (compatibleValueEquiv s U hsub hmult i).symm
        ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩) := by
  let a : SixPrimitiveFrequencyTuple U := fun i ↦
    (compatibleValueEquiv s U hsub hmult i).symm
      ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩
  have hencode (i : Fin 6) :
      compatibleValueEncode s U hsub hmult i (a i) =
        (compatibleSystem s U hsub hmult).project i x := by
    exact congrArg Subtype.val
      ((compatibleValueEquiv s U hsub hmult i).apply_symm_apply
        ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩)
  intro p hp
  by_cases hpused : p ∈ usedPrimes U
  · let q : UsedPrimeIndex U := ⟨p, hpused⟩
    exact compatible_of_project_eq_list s U hsub hmult
      (usedPrimeIndexList U) a x (fun i ↦ (hencode i).symm)
      q (mem_usedPrimeIndexList q)
  · rw [sixLocalFrequency_eq_sum_primitiveResidue]
    apply Finset.sum_eq_zero
    intro i hi
    apply primitiveResidue_of_not_mem
    intro hpi
    exact hpused (mem_usedPrimes.mpr ⟨i, hpi⟩)

/-- The range of the state encoding is exactly the filtered state domain
selected by the primitive value finsets. -/
lemma range_compatibleStateEncode
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    Set.range (compatibleStateEncode s U hsub hmult) =
      {x | x ∈ (compatibleSystem s U hsub hmult).stateElements ∧
        ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
          compatibleValueDomain s U hsub hmult i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨mem_stateElements _ _, ?_⟩
    intro i
    simp [compatibleValueDomain, project_compatibleStateEncode]
  · intro hx
    let a : SixPrimitiveFrequencyTuple U := fun i ↦
      (compatibleValueEquiv s U hsub hmult i).symm
        ⟨(compatibleSystem s U hsub hmult).project i x, hx.2 i⟩
    have ha : sixPrimeCompatible s a :=
      decoded_is_compatible s U hsub hmult x hx.2
    let A : CompatiblePrimitiveTuple s U := ⟨a, ha⟩
    refine ⟨A, ?_⟩
    apply compatibleSystemList_project_injective s U hsub hmult
      (usedPrimeIndexList U)
    funext i
    change (compatibleSystemList s U hsub hmult (usedPrimeIndexList U)).project i
        (compatibleStateEncodeList s U hsub hmult (usedPrimeIndexList U) A) = _
    rw [project_compatibleStateEncodeList]
    exact congrArg Subtype.val
      ((compatibleValueEquiv s U hsub hmult i).apply_symm_apply
        ⟨(compatibleSystem s U hsub hmult).project i x, hx.2 i⟩)

noncomputable def compatibleStateEquiv
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    CompatiblePrimitiveTuple s U ≃
      {x : (compatibleSystem s U hsub hmult).State //
        x ∈ (compatibleSystem s U hsub hmult).stateElements ∧
          ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
            compatibleValueDomain s U hsub hmult i} :=
  (Equiv.ofInjective _ (compatibleStateEncode_injective s U hsub hmult)).trans
    (Equiv.setCongr (range_compatibleStateEncode s U hsub hmult))

@[simp] lemma compatibleStateEquiv_apply_val
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) :
    ((compatibleStateEquiv s U hsub hmult) a).1 =
      compatibleStateEncode s U hsub hmult a := rfl

/-- The actual finite compatible-frequency model. -/
noncomputable def compatibleFundamentalModel
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    CompatibleFundamentalModel s U where
  system := compatibleSystem s U hsub hmult
  valueDomain := compatibleValueDomain s U hsub hmult
  valueDomain_subset := fun i x hx ↦ mem_valueElements _ _ x
  valueEquiv := compatibleValueEquiv s U hsub hmult
  stateEquiv := compatibleStateEquiv s U hsub hmult
  project_encode := by
    intro a i
    rw [compatibleValueEquiv_apply_val, compatibleStateEquiv_apply_val,
      project_compatibleStateEncode]

/-- The no-singleton formulation used after support-factor bookkeeping. -/
noncomputable def compatibleFundamentalModelOfNoSingleton
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    CompatibleFundamentalModel s U :=
  compatibleFundamentalModel s U hsub (by
    intro p hp
    have hpos : 0 < (primeSupport U p).card := by
      obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
      exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩
    have hne0 : (primeSupport U p).card ≠ 0 := Nat.ne_of_gt hpos
    have hne1 : (primeSupport U p).card ≠ 1 := hnoone p hp
    omega)

@[simp] theorem compatibleSystemList_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) :
    (compatibleSystemList s U hsub hmult L).scale =
      (L.map fun p ↦ Real.sqrt p.1 ^ ((primeSupport U p.1).card - 2)).prod := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
      let : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      simp only [compatibleSystemList, FundamentalSystem.scale,
        List.map_cons, List.prod_cons, compatiblePrimeCoordinate_scale, ih]

@[simp] theorem compatibleSystem_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (compatibleSystem s U hsub hmult).scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) := by
  rw [compatibleSystem, compatibleSystemList_scale, usedPrimeIndexList,
    Finset.prod_map_toList]
  exact Finset.prod_attach (usedPrimes U)
    (fun p ↦ Real.sqrt p ^ ((primeSupport U p).card - 2))

@[simp] theorem compatibleFundamentalModel_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (compatibleFundamentalModel s U hsub hmult).system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) :=
  compatibleSystem_scale s U hsub hmult

@[simp] theorem compatibleFundamentalModelOfNoSingleton_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    (compatibleFundamentalModelOfNoSingleton s U hsub hnoone).system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) := by
  unfold compatibleFundamentalModelOfNoSingleton
  apply compatibleFundamentalModel_scale

/-- The concrete arbitrary-support compatible-frequency estimate in the
exact form needed by the sixth-moment expansion. -/
theorem compatibleIntervalContraction_le_of_noSingleton
    (s h : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    ‖compatibleIntervalContraction s h U‖ ≤
      (∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2)) *
        ∏ i, Real.sqrt
          (∑ a : PrimitiveFrequencyTuple (U i),
            ‖primitiveIntervalFourier h a‖ ^ 2) := by
  let M := compatibleFundamentalModelOfNoSingleton s U hsub hnoone
  have hbound := M.compatibleIntervalContraction_le h
  rw [show M.system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) by
    simpa [M] using compatibleFundamentalModelOfNoSingleton_scale
      s U hsub hnoone] at hbound
  exact hbound

end

end Erdos220
