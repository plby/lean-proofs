import Wikipedia.SzemeredisTheorem.Hypergraph.FacePartition

/-!
# Energy under refinement of finite face partitions

For mathlib's refinement order, `P ≤ Q` means that `P` is finer than `Q`.
This file proves both finite tower identities and the corresponding
monotonicity of `partitionEnergy`.  The stronger Pythagorean identity records
the energy increment exactly as the mean-square difference of the two
conditional averages.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Fine conditional averaging preserves the sum on each atom of every
coarser partition. -/
theorem sum_conditionalMean_on_coarser_part
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  let fineParts : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have hUnion : fineParts.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 hxt
    · intro hxs
      obtain ⟨t, ht, hxt⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, htu⟩ := hPQ ht
      have hus : u = s :=
        Q.eq_of_mem_parts hu hs (htu hxt) hxs
      have hts : t ⊆ s := by
        simpa [hus] using htu
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩, hxt⟩
  have hdisjoint :
      (↑fineParts : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ fineParts.biUnion id,
          conditionalMean P f x := by
      exact Finset.sum_congr hUnion.symm fun _ _ => rfl
    _ =
        ∑ t ∈ fineParts,
          ∑ x ∈ t, conditionalMean P f x :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ fineParts, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_conditionalMean_on_part P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ fineParts.biUnion id, f x :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr hUnion fun _ _ => rfl

/-- Coarse-after-fine tower identity. -/
@[simp]
theorem conditionalMean_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean Q (conditionalMean P f) x =
      conditionalMean Q f x := by
  change
    Finset.expect (Q.part x) (conditionalMean P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    sum_conditionalMean_on_coarser_part P Q hPQ f
      (Q.part_mem.2 (Finset.mem_univ x))]

/-- Fine-after-coarse tower identity.  A function constant on coarse atoms is
already constant on every finer atom. -/
@[simp]
theorem conditionalMean_reverse_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean Q f) x =
      conditionalMean Q f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean Q f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part Q f
        (FacePartition.part_subset_of_le hPQ x hy)
    _ = conditionalMean Q f x :=
      Finset.expect_const (by simp) _

/-- A factor constant on the current atom can be pulled out of a conditional
average. -/
theorem conditionalMean_mul_right_of_constant_on_part
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    conditionalMean P (fun y => u y * v y) x =
      conditionalMean P u x * v x := by
  calc
    conditionalMean P (fun y => u y * v y) x =
        conditionalMean P (fun y => v x * u y) x := by
      rw [conditionalMean, conditionalMean]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * conditionalMean P u x :=
      conditionalMean_smul P (v x) u x
    _ = conditionalMean P u x * v x := by
      ring

/-- A conditional average is measurable with respect to its own partition,
so it can be pulled out of another conditional average over that partition. -/
theorem conditionalMean_mul_conditionalMean_right
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => u y * conditionalMean P v y) x =
      conditionalMean P u x * conditionalMean P v x := by
  apply conditionalMean_mul_right_of_constant_on_part
  intro y hy
  exact conditionalMean_eq_of_mem_part P v hy

/-- The fine and coarse conditional averages have the same mixed second
moment as the coarse conditional average has second moment. -/
theorem mean_conditionalMean_mul_eq_sq_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      conditionalMean P f x * conditionalMean Q f x) =
      mean (fun x => conditionalMean Q f x ^ 2) := by
  calc
    mean (fun x =>
        conditionalMean P f x * conditionalMean Q f x) =
        mean (conditionalMean Q (fun x =>
          conditionalMean P f x * conditionalMean Q f x)) :=
      (mean_conditionalMean Q _).symm
    _ =
        mean (fun x =>
          conditionalMean Q (conditionalMean P f) x *
            conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_conditionalMean_right
        Q (conditionalMean P f) f x
    _ =
        mean (fun x =>
          conditionalMean Q f x * conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      rw [conditionalMean_tower_of_le P Q hPQ]
    _ = mean (fun x => conditionalMean Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]

/-- Exact Pythagorean identity for refinement: the energy increment is the
mean-square distance between the fine and coarse conditional averages. -/
theorem partitionEnergy_pythagorean
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f =
      partitionEnergy Q f +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) := by
  have hcross :=
    mean_conditionalMean_mul_eq_sq_of_le P Q hPQ f
  have hdiff :
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) =
        mean (fun x => conditionalMean P f x ^ 2) -
          2 * mean (fun x =>
            conditionalMean P f x * conditionalMean Q f x) +
          mean (fun x => conditionalMean Q f x ^ 2) := by
    calc
      mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) =
          mean (fun x =>
            conditionalMean P f x ^ 2 -
              2 * (conditionalMean P f x *
                conditionalMean Q f x) +
              conditionalMean Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => conditionalMean P f x ^ 2) -
            2 * mean (fun x =>
              conditionalMean P f x * conditionalMean Q f x) +
            mean (fun x => conditionalMean Q f x ^ 2) := by
        rw [mean_add, mean_sub, mean_smul]
  change
    mean (fun x => conditionalMean P f x ^ 2) =
      mean (fun x => conditionalMean Q f x ^ 2) +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2)
  rw [hdiff, hcross]
  ring

/-- Equivalent variance form of the Pythagorean identity. -/
theorem partitionEnergy_sub_eq_mean_sq
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f - partitionEnergy Q f =
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  ring

/-- Refinement can only increase partition energy. -/
theorem partitionEnergy_mono
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy Q f ≤ partitionEnergy P f := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  exact le_add_of_nonneg_right
    (mean_nonneg fun x => sq_nonneg _)

/-- The standard `[0,1]` energy bounds packaged as interval membership. -/
theorem partitionEnergy_mem_Icc [Nonempty Ω]
    (P : FacePartition Ω) {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    partitionEnergy P f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨partitionEnergy_nonneg P f,
    partitionEnergy_le_one P hf0 hf1⟩

/-- For a `[0,1]`-valued function, energies along a refinement lie in the
expected monotone chain. -/
theorem partitionEnergy_refinement_bounds [Nonempty Ω]
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ partitionEnergy Q f ∧
      partitionEnergy Q f ≤ partitionEnergy P f ∧
      partitionEnergy P f ≤ 1 :=
  ⟨partitionEnergy_nonneg Q f,
    partitionEnergy_mono P Q hPQ f,
    partitionEnergy_le_one P hf0 hf1⟩

end Wikipedia.SzemeredisTheorem
