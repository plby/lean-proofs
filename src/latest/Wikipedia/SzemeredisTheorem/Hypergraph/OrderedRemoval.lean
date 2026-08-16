import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedGoodAtoms
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedEnergy
import Wikipedia.SzemeredisTheorem.Hypergraph.FullOrderedRegularity

/-!
# Bad-base cleaning for ordered hypergraph complexes

For each upper tuple, the frozen fine upper partition chooses a unique
genuine atom.  The tuple is bad when its coarse boundary lies in the bad
base attached to that very atom.  Summing over the disjoint upper atoms gives
the sharp
cleaning estimate

```
mass(own-atom bad base) ≤
  complexity(upper) * densityThreshold
    + atomEnergyGap / defectThreshold.
```

The second half of the file pulls these bad sets back to every subface of a
top ordered edge.  Exact finite Fubini preserves normalized density, and a
finite union bound gives the deletion-cost estimate needed by ordered
hypergraph removal.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Finite union bounds -/

/-- The indicator of a finite union is bounded by the sum of the
indicators. -/
theorem finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (s : Finset ι) (F : ι → Finset Ω) (x : Ω) :
    finsetIndicator (s.biUnion F) x ≤
      ∑ i ∈ s, finsetIndicator (F i) x := by
  by_cases hx : x ∈ s.biUnion F
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    rw [finsetIndicator_of_mem hx]
    calc
      1 = finsetIndicator (F i) x :=
        (finsetIndicator_of_mem hxi).symm
      _ ≤ ∑ j ∈ s, finsetIndicator (F j) x := by
        apply Finset.single_le_sum
          (s := s)
          (f := fun j => finsetIndicator (F j) x)
        · intro j hj
          by_cases hxj : x ∈ F j <;> simp [hxj]
        · exact hi
  · rw [finsetIndicator_of_not_mem hx]
    exact Finset.sum_nonneg fun i _ => by
      by_cases hxi : x ∈ F i <;> simp [hxi]

/-- Normalized finite union bound. -/
theorem mean_finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    [Fintype ι] [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (finsetIndicator (s.biUnion F)) ≤
      ∑ i ∈ s, mean (finsetIndicator (F i)) := by
  calc
    mean (finsetIndicator (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          finsetIndicator (F i) x) :=
      mean_mono (finsetIndicator_biUnion_le_sum s F)
    _ = ∑ i ∈ s, mean (finsetIndicator (F i)) :=
      mean_finset_sum s (fun i => finsetIndicator (F i))

/-! ## The bad base attached to the tuple's own upper atom -/

/-- Union, over all genuine upper atoms, of the part of that atom lying
above its own bad boundary base. -/
noncomputable def ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) : Finset Ω := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ atomBadBaseSupport fine coarse upper a α β

@[simp]
theorem mem_ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) (x : Ω) :
    x ∈ ownAtomBadBaseSupport fine coarse upper α β ↔
      x ∈ atomBadBaseSupport fine coarse upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [ownAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ atomBadBaseSupport
          fine coarse upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical :
        partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [ownAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine
      ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_inter.mpr
    exact
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

/-- Per-atom bad-base estimate charged to that atom's own square-defect
mass, before summing over atoms. -/
theorem mean_indicator_atom_inter_badBaseSupport_le_local
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport
          fine coarse upper a α β)) ≤
      α + mean
        (atomBoundaryDefectSq fine coarse upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport
          fine coarse upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩ smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)) +
        mean (finsetIndicator
          (largeDefectBaseSupport
            fine coarse upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)
          (largeDefectBaseSupport fine coarse upper a β)
    _ ≤
        α + mean
          (atomBoundaryDefectSq fine coarse upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          coarse a.1 hα)
        (mean_indicator_largeAverageBaseSupport_le
          coarse
          (atomBoundaryDefectSq fine coarse upper a)
          (atomBoundaryDefectSq_nonneg
            fine coarse upper a) hβ)

/-- **Summed own-atom bad-base estimate.**  Low-density bases cost one
`α` per upper atom, while all excessive-defect bases together cost only the
single aggregate atom-energy gap divided by `β`. -/
theorem mean_indicator_ownAtomBadBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (ownAtomBadBaseSupport fine coarse upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (partitionAtomEnergy fine upper -
          partitionAtomEnergy coarse upper) / β := by
  calc
    mean (finsetIndicator
        (ownAtomBadBaseSupport fine coarse upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ atomBadBaseSupport
              fine coarse upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ atomBadBaseSupport
              fine coarse upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α +
            mean (atomBoundaryDefectSq
              fine coarse upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        mean_indicator_atom_inter_badBaseSupport_le_local
          fine coarse upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (partitionAtomEnergy fine upper -
            partitionAtomEnergy coarse upper) / β := by
      rw [partitionAtomEnergy_sub_eq_sum_mean_sq hfc upper]
      unfold atomBoundaryDefectSq atomBoundaryDefect
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.sum_div]
      rw [Fintype.card_coe]
      rfl

/-! ## Ordered specialization -/

/-- Tuples whose boundary lies in the bad base attached to their own
genuine upper atom. -/
noncomputable def orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  ownAtomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper α β

@[simp]
theorem mem_orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) (x : Fin (j + 1) → G) :
    x ∈ orderedOwnAtomBadBaseSupport
        fine coarse e upper α β ↔
      x ∈ orderedAtomBadBaseSupport
        fine coarse e upper
          (partitionAtomAt upper x) α β := by
  exact
    mem_ownAtomBadBaseSupport
      (orderedBoundaryPartition fine e)
      (orderedBoundaryPartition coarse e)
      upper α β x

/-- Ordered summed own-atom cleaning estimate. -/
theorem mean_indicator_orderedOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (orderedOwnAtomBadBaseSupport
          fine coarse e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy fine e upper -
          orderedAtomEnergy coarse e upper) / β := by
  exact
    mean_indicator_ownAtomBadBaseSupport_le
      (orderedBoundaryPartition_mono hfc e)
      upper hα hβ

/-! ## Pullback to top faces -/

/-- A positive-rank ordered subface of an `r`-tuple.  The first component
stores one less than its arity. -/
abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)

/-- Every smaller ordered face factors through an ordered face of any
intermediate admissible rank.  This is the exact extension lemma used to
turn survival of all top-face deletions into avoidance on every lower
face. -/
theorem exists_orderedFace_factor_through
    {k s r : ℕ} (hsr : s ≤ r) (hrk : r ≤ k)
    (f : OrderedFace k s) :
    ∃ e : OrderedFace k r, ∃ d : OrderedFace r s,
      d.trans e = f := by
  classical
  let sf : Finset (Fin k) :=
    Finset.univ.map f.toEmbedding
  have hsf_card : sf.card = s := by
    rw [show sf.card =
        (Finset.univ : Finset (Fin s)).card by
      exact Finset.card_map f.toEmbedding]
    simp
  have hsf_univ : sf ⊆ Finset.univ :=
    Finset.subset_univ sf
  obtain ⟨t, hsf_t, _ht_univ, ht⟩ :=
    Finset.exists_subsuperset_card_eq
      hsf_univ
      (by simpa [hsf_card] using hsr)
      (by simpa using hrk)
  let e : OrderedFace k r :=
    t.orderEmbOfFin ht
  have hf_mem (i : Fin s) : f i ∈ t := by
    apply hsf_t
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_univ i, rfl⟩
  let ft : Fin s ↪o t :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨f i, hf_mem i⟩)
      (fun _ _ hij => f.strictMono hij)
  let d : OrderedFace r s :=
    ft.trans (t.orderIsoOfFin ht).symm.toOrderEmbedding
  refine ⟨e, d, ?_⟩
  apply RelEmbedding.ext
  intro i
  change
    t.orderEmbOfFin ht
        ((t.orderIsoOfFin ht).symm
          ⟨f i, hf_mem i⟩) =
      f i
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp

/-- Pull a finite set on one ordered face back to the full tuple space. -/
noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]

/-- Pullback along an ordered coordinate face preserves normalized
density. -/
theorem mean_indicator_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    mean (finsetIndicator
        (orderedFacePullbackFinset d S)) =
      mean (finsetIndicator S) := by
  rw [show
      finsetIndicator (orderedFacePullbackFinset d S) =
        fun y => finsetIndicator S
          (orderedFaceTuple d y) by
    funext y
    by_cases hy : orderedFaceTuple d y ∈ S
    · rw [finsetIndicator_of_mem hy,
        finsetIndicator_of_mem]
      exact
        (mem_orderedFacePullbackFinset d S y).2 hy
    · rw [finsetIndicator_of_not_mem hy,
        finsetIndicator_of_not_mem]
      exact fun h =>
        hy ((mem_orderedFacePullbackFinset d S y).1 h)]
  exact mean_comp_orderedFaceTuple d
    (finsetIndicator S)

/-- Delete a top tuple when any of its positive-rank ordered subfaces lies
in the bad base attached to its own frozen fine upper atom. -/
noncomputable def orderedTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (orderedOwnAtomBadBaseSupport
          (fine.layer q.1.1
            (Nat.le_of_lt q.1.2))
          (coarse.layer q.1.1
            (Nat.le_of_lt q.1.2))
          (q.2.trans e)
          (fine.partition q.1.succ
            (q.2.trans e))
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

/-- Explicit union-bound cost of the top-face bad-base deletion. -/
theorem mean_indicator_orderedTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (orderedTopBadBaseDeletion fine coarse e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (fine.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          (orderedAtomEnergy
              (fine.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e)) -
            orderedAtomEnergy
              (coarse.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e))) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (orderedTopBadBaseDeletion fine coarse e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (orderedOwnAtomBadBaseSupport
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ :
            Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (orderedOwnAtomBadBaseSupport
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            (orderedAtomEnergy
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e)) -
              orderedAtomEnergy
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      have hlayer :
          OrderedFacePartitionRefines
            (fine.layer q.1.1
              (Nat.le_of_lt q.1.2))
            (coarse.layer q.1.1
              (Nat.le_of_lt q.1.2)) := by
        intro g
        exact hfc
          ⟨q.1.1,
            Nat.lt_succ_iff.mpr
              (Nat.le_of_lt q.1.2)⟩ g
      exact
        mean_indicator_orderedOwnAtomBadBaseSupport_le
          hlayer
          (q.2.trans e)
          (fine.partition q.1.succ
            (q.2.trans e))
          (hα q.1.1) (hβ q.1.1)

/-- The bad-base top deletions, one for every top ordered face. -/
noncomputable def orderedBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => orderedTopBadBaseDeletion fine coarse e α β

/-- Per-top-face density bound for the bad-base deletion family. -/
theorem faceDeletionDensity_orderedBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          fine coarse α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (fine.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          (orderedAtomEnergy
              (fine.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e)) -
            orderedAtomEnergy
              (coarse.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e))) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (orderedBadBaseDeletionFamily
            fine coarse α β) e =
        mean (finsetIndicator
          (orderedTopBadBaseDeletion
            fine coarse e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      orderedBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    mean_indicator_orderedTopBadBaseDeletion_le
      hfc e α β hα hβ

/-- A coarse but convenient constant-threshold deletion estimate.  If all
fine atoms have complexity at most `M`, every local energy loss is bounded
by the total all-rank frozen-upper gap. -/
theorem faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcomplex :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ M)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((M : ℝ) * α + P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            (orderedAtomEnergy
                (P.fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (P.fine.partition q.1.succ
                  (q.2.trans e)) -
              orderedAtomEnergy
                (P.coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (P.fine.partition q.1.succ
                  (q.2.trans e))) / β) := by
      exact
        faceDeletionDensity_orderedBadBaseDeletionFamily_le
          P.refines (fun _ => α) (fun _ => β)
          (fun _ => hα) (fun _ => hβ) e
    _ ≤
        ∑ _q : OrderedPositiveSubface r,
          ((M : ℝ) * α +
            P.totalAtomEnergyGap / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ hα
        exact_mod_cast
          hcomplex q.1.succ (q.2.trans e)
      · apply div_le_div_of_nonneg_right _ hβ.le
        have hfineLayer :
            P.fine.layer q.1.1
                (Nat.le_of_lt q.1.2) =
              P.fine.partition q.1.castSucc := by
          rfl
        have hcoarseLayer :
            P.coarse.layer q.1.1
                (Nat.le_of_lt q.1.2) =
              P.coarse.partition q.1.castSucc := by
          rfl
        rw [hfineLayer, hcoarseLayer]
        change
          P.faceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.totalAtomEnergyGap
        exact
          P.faceAtomEnergyGap_le_total
            q.1 (q.2.trans e)
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((M : ℝ) * α +
            P.totalAtomEnergyGap / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

/-- Parameter-ready form of the constant-threshold estimate. -/
theorem faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le_of_bound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcomplex :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ M)
    {α β ε : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hparameters :
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((M : ℝ) * α + P.totalAtomEnergyGap / β) ≤
        ε)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
      ε :=
  (faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le
    P hcomplex hα hβ e).trans hparameters

/-! ## Surviving tuples induce good closed configurations -/

/-- If a full tuple avoids the bad-base deletion on every top face, then
its canonical fine atom configuration is good at every positive rank.
The proof extends each lower face to a top face and reads the corresponding
pullback component of the deletion union. -/
theorem ClosedOrderedAtomConfiguration.isGood_of_avoids_topBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (fine coarse : OrderedPartitionComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          orderedTopBadBaseDeletion
            fine coarse e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple fine x).IsGood
      fine coarse α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple fine x).isGood_of_avoids_badBases
      fine coarse α β
  intro j hj f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr hj) hrk f
  apply havoid e
  rw [orderedTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine
    ⟨⟨⟨j, hj⟩, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  have htuple :
      orderedFaceTuple d (orderedFaceTuple e x) =
        orderedFaceTuple f x := by
    rw [show
        orderedFaceTuple d (orderedFaceTuple e x) =
          orderedFaceTuple (d.trans e) x by rfl,
      hde]
  rw [htuple, hde]
  exact
    (mem_orderedOwnAtomBadBaseSupport
      (fine.layer j (Nat.le_of_lt hj))
      (coarse.layer j (Nat.le_of_lt hj))
      f
      (fine.partition
        ⟨j + 1, Nat.succ_lt_succ hj⟩ f)
      (α (j + 1)) (β (j + 1))
      (orderedFaceTuple f x)).2 hbad

end Wikipedia.SzemeredisTheorem
