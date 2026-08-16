import ErdosProblems.Erdos920.Averaging

/-!
# The factorial-saving ordering lemma for Erdős 920

This file proves the deterministic double-counting form of the random-ordering
lemma used in Bradač's proof.  A transitive-tournament-free digraph is turned
into a clique-free graph by retaining the arcs which point forwards in a
linear order.  Averaging over all permutations of the vertex set saves the
factor `m!` when forward-independent tuples are converted to independent
sets.
-/

open scoped BigOperators

namespace Erdos920

section

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Forward-independent tuples which are increasing in the order induced by
`π`.  These are in bijection with the independent sets of `forwardGraph D π`.
-/
noncomputable def increasingForwardFinset (D : V → V → Prop)
    (π : Equiv.Perm V) (k : ℕ) : Finset (Fin k → V) := by
  classical
  exact (forwardIndependentFinset D k).filter
    (fun x ↦ StrictMono (fun i ↦ π (x i)))

@[simp]
lemma mem_increasingForwardFinset {D : V → V → Prop}
    {π : Equiv.Perm V} {k : ℕ} {x : Fin k → V} :
    x ∈ increasingForwardFinset D π k ↔
      ForwardIndependent D x ∧ StrictMono (fun i ↦ π (x i)) := by
  classical
  simp [increasingForwardFinset]

private lemma image_univ_card_of_strictMono {k : ℕ} {π : Equiv.Perm V}
    {x : Fin k → V} (hx : StrictMono (fun i ↦ π (x i))) :
    (Finset.univ.image x).card = k := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    exact hx.injective (congrArg π hij)

private lemma image_univ_independent {D : V → V → Prop}
    {π : Equiv.Perm V} {k : ℕ} {x : Fin k → V}
    (hforward : ForwardIndependent D x)
    (hmono : StrictMono (fun i ↦ π (x i))) :
    (forwardGraph D π).IsIndepSet (Finset.univ.image x : Set V) := by
  intro u hu v hv huv hadj
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hu hv
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hv
  rcases lt_trichotomy i j with hij | hij | hij
  · rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
    · exact hforward hij h.2
    · exact (lt_asymm (hmono hij) h.1).elim
  · exact huv (congrArg x hij)
  · rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
    · exact (lt_asymm (hmono hij) h.1).elim
    · exact hforward hij h.2

private lemma strictMono_eq_of_image_eq {k : ℕ} {x y : Fin k → V}
    (hx : StrictMono x) (hy : StrictMono y)
    (hxy : Finset.univ.image x = Finset.univ.image y) : x = y := by
  have hcard : (Finset.univ.image x).card = k := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i hi j hj hij
      exact hx.injective hij
  have hxeq : x = (Finset.univ.image x).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (by simp) hx
  have hyeq : y = (Finset.univ.image x).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (by simp [hxy]) hy
  exact hxeq.trans hyeq.symm

private lemma increasing_tuple_eq_of_image_eq {k : ℕ} {π : Equiv.Perm V}
    {x y : Fin k → V}
    (hx : StrictMono (fun i ↦ π (x i)))
    (hy : StrictMono (fun i ↦ π (y i)))
    (hxy : Finset.univ.image x = Finset.univ.image y) : x = y := by
  apply π.injective.comp_left
  apply strictMono_eq_of_image_eq hx hy
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : x i ∈ Finset.univ.image y := by
      rw [← hxy]
      simp
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, by simpa [hji]⟩
  · rintro ⟨i, rfl⟩
    have hi : y i ∈ Finset.univ.image x := by
      rw [hxy]
      simp
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, by simpa [hji]⟩

/-- Independent `k`-sets of a forward graph are exactly its increasing
forward-independent `k`-tuples. -/
lemma indepSetFinset_card_forwardGraph_eq_increasing
    (D : V → V → Prop) (π : Equiv.Perm V) (k : ℕ) :
    ((forwardGraph D π).indepSetFinset k).card =
      (increasingForwardFinset D π k).card := by
  classical
  let A := (forwardGraph D π).indepSetFinset k
  let B := increasingForwardFinset D π k
  apply Nat.le_antisymm
  · rw [← Finset.card_attach (s := A)]
    let f : {S // S ∈ A} → (Fin k → V) := fun S ↦
      orderedTuple π S.1 <| (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq
    exact Finset.card_le_card_of_injOn f (by
      intro S hS
      have hNS := SimpleGraph.mem_indepSetFinset_iff.mp S.2
      exact mem_increasingForwardFinset.mpr ⟨
        orderedTuple_forwardIndependent π S.1 hNS.card_eq hNS.isIndepSet,
        orderedTuple_strictMono_after π S.1 hNS.card_eq⟩) (by
      intro S hS T hT hST
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_orderedTuple π S.1
            (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq,
        ← range_orderedTuple π T.1
            (SimpleGraph.mem_indepSetFinset_iff.mp T.2).card_eq]
      exact congrArg Set.range hST)
  · rw [← Finset.card_attach (s := B)]
    let g : {x // x ∈ B} → Finset V := fun x ↦ Finset.univ.image x.1
    exact Finset.card_le_card_of_injOn g (by
      intro x hx
      have hx' := mem_increasingForwardFinset.mp x.2
      exact SimpleGraph.mem_indepSetFinset_iff.mpr ⟨
        image_univ_independent hx'.1 hx'.2,
        image_univ_card_of_strictMono hx'.2⟩) (by
      intro x hx y hy hxy
      apply Subtype.ext
      exact increasing_tuple_eq_of_image_eq
        (mem_increasingForwardFinset.mp x.2).2
        (mem_increasingForwardFinset.mp y.2).2 hxy)

/-- Permutations which put a fixed tuple in increasing order. -/
noncomputable def increasingPermFinset {k : ℕ} (x : Fin k → V) :
    Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter (fun π ↦ StrictMono (fun i ↦ π (x i)))

@[simp]
lemma mem_increasingPermFinset {k : ℕ} {x : Fin k → V}
    {π : Equiv.Perm V} :
    π ∈ increasingPermFinset x ↔ StrictMono (fun i ↦ π (x i)) := by
  classical
  simp [increasingPermFinset]

/-- A fixed injective `k`-tuple is increasing in precisely at most a
`1 / k!` fraction of all vertex permutations.  The proof explicitly injects
an increasing permutation together with a permutation of the tuple's indices
into the full permutation group. -/
lemma increasingPermFinset_card_mul_factorial_le {k : ℕ}
    (x : Fin k → V) (hx : Function.Injective x) :
    (increasingPermFinset x).card * k.factorial ≤
      Fintype.card (Equiv.Perm V) := by
  classical
  let A : Finset (Equiv.Perm V) := increasingPermFinset x
  let e : Fin k ↪ V := ⟨x, hx⟩
  let twist : Equiv.Perm (Fin k) → Equiv.Perm V :=
    fun σ ↦ σ.viaFintypeEmbedding e
  let F : Equiv.Perm V × Equiv.Perm (Fin k) → Equiv.Perm V :=
    fun p ↦ (twist p.2).trans p.1
  have hF : Set.InjOn F
      (↑(A ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k)))) :
        Set (Equiv.Perm V × Equiv.Perm (Fin k))) := by
    rintro ⟨π, σ⟩ hp ⟨π', σ'⟩ hp' heq
    have hpA : π ∈ A := (Finset.mem_product.mp hp).1
    have hpA' : π' ∈ A := (Finset.mem_product.mp hp').1
    have hπ : StrictMono (fun i ↦ π (x i)) :=
      mem_increasingPermFinset.mp hpA
    have hπ' : StrictMono (fun i ↦ π' (x i)) :=
      mem_increasingPermFinset.mp hpA'
    have himage :
        Finset.univ.image (fun i ↦ π (x i)) =
          Finset.univ.image (fun i ↦ π' (x i)) := by
      ext v
      constructor
      · intro hv
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨i, rfl⟩ := hv
        refine ⟨σ' (σ.symm i), ?_⟩
        have happ := DFunLike.congr_fun heq (x (σ.symm i))
        dsimp only [F] at happ
        change π ((twist σ) (e (σ.symm i))) =
          π' ((twist σ') (e (σ.symm i))) at happ
        simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
        simpa [e] using happ.symm
      · intro hv
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨i, rfl⟩ := hv
        refine ⟨σ (σ'.symm i), ?_⟩
        have happ := DFunLike.congr_fun heq (x (σ'.symm i))
        dsimp only [F] at happ
        change π ((twist σ) (e (σ'.symm i))) =
          π' ((twist σ') (e (σ'.symm i))) at happ
        simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
        simpa [e] using happ
    have hordered : (fun i ↦ π (x i)) = (fun i ↦ π' (x i)) :=
      strictMono_eq_of_image_eq hπ hπ' himage
    have hσσ' : σ = σ' := by
      apply Equiv.ext
      intro i
      apply hπ.injective
      have happ := DFunLike.congr_fun heq (x i)
      dsimp only [F] at happ
      change π ((twist σ) (e i)) = π' ((twist σ') (e i)) at happ
      simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
      have hord := congrFun hordered (σ' i)
      exact happ.trans hord.symm
    subst σ'
    have hππ' : π = π' := by
      ext v
      have happ := DFunLike.congr_fun heq ((twist σ).symm v)
      simpa [F] using happ
    subst π'
    rfl
  calc
    (increasingPermFinset x).card * k.factorial =
        (A ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k)))).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
    _ ≤ (Finset.univ : Finset (Equiv.Perm V)).card :=
      Finset.card_le_card_of_injOn F (by simp) hF
    _ = Fintype.card (Equiv.Perm V) := Finset.card_univ

/-- Double-count the pairs `(π,x)` for which the forward-independent tuple
`x` is increasing in the order induced by `π`. -/
lemma sum_increasingForwardFinset_card (D : V → V → Prop) (k : ℕ) :
    (∑ π : Equiv.Perm V, (increasingForwardFinset D π k).card) =
      ∑ x ∈ forwardIndependentFinset D k, (increasingPermFinset x).card := by
  classical
  simp only [increasingForwardFinset, increasingPermFinset, Finset.card_filter]
  rw [Finset.sum_comm]

/-- The total number of independent sets over all vertex orderings satisfies
the factorial-saving bound. -/
lemma sum_indepSetFinset_card_forwardGraph_mul_factorial_le
    (D : V → V → Prop) (k : ℕ) :
    (∑ π : Equiv.Perm V, ((forwardGraph D π).indepSetFinset k).card) *
        k.factorial ≤
      (forwardIndependentFinset D k).card *
        Fintype.card (Equiv.Perm V) := by
  classical
  rw [Finset.sum_congr rfl (fun π _ ↦
    indepSetFinset_card_forwardGraph_eq_increasing D π k)]
  rw [sum_increasingForwardFinset_card D k, Finset.sum_mul]
  calc
    ∑ x ∈ forwardIndependentFinset D k,
        (increasingPermFinset x).card * k.factorial ≤
        ∑ _x ∈ forwardIndependentFinset D k,
          Fintype.card (Equiv.Perm V) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hinj : Function.Injective x
      · exact increasingPermFinset_card_mul_factorial_le x hinj
      · have hempty : increasingPermFinset x = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro π hπ
          apply hinj
          intro i j hij
          apply (mem_increasingPermFinset.mp hπ).injective
          exact congrArg π hij
        simp [hempty]
    _ = (forwardIndependentFinset D k).card *
          Fintype.card (Equiv.Perm V) := by simp

/-- **Factorial-saving ordering lemma.**  Some ordering of the vertices turns
the digraph into a forward graph with at most the number of
forward-independent ordered `k`-tuples divided by `k!` independent `k`-sets.
-/
theorem exists_forwardGraph_factorial_bound
    (D : V → V → Prop) (k : ℕ) :
    ∃ π : Equiv.Perm V,
      ((forwardGraph D π).indepSetFinset k).card * k.factorial ≤
        (forwardIndependentFinset D k).card := by
  classical
  by_contra! hbad
  have hstrict :
      (∑ _π : Equiv.Perm V, (forwardIndependentFinset D k).card) <
        ∑ π : Equiv.Perm V,
          ((forwardGraph D π).indepSetFinset k).card * k.factorial := by
    apply Finset.sum_lt_sum_of_nonempty (by simp)
    intro π hπ
    exact hbad π
  have htotal := sum_indepSetFinset_card_forwardGraph_mul_factorial_le D k
  rw [Finset.sum_mul] at htotal
  have :
      (∑ π : Equiv.Perm V,
          ((forwardGraph D π).indepSetFinset k).card * k.factorial) ≤
        ∑ _π : Equiv.Perm V, (forwardIndependentFinset D k).card := by
    simpa [Nat.mul_comm] using htotal
  exact (not_lt_of_ge this) hstrict

/-- The graph supplied by the factorial-saving ordering lemma is
clique-free whenever the original digraph has no transitive tournament. -/
theorem exists_cliqueFree_forwardGraph_factorial_bound
    {D : V → V → Prop} {s : ℕ} (hD : TransitiveTournamentFree D s)
    (k : ℕ) :
    ∃ π : Equiv.Perm V, (forwardGraph D π).CliqueFree s ∧
      ((forwardGraph D π).indepSetFinset k).card * k.factorial ≤
        (forwardIndependentFinset D k).card := by
  obtain ⟨π, hπ⟩ := exists_forwardGraph_factorial_bound D k
  exact ⟨π, forwardGraph_cliqueFree hD π, hπ⟩

end

end Erdos920
