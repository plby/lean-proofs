import StackExchange.Puzzling139335.FiniteBoundaryPartition.Breakpoints
import StackExchange.Puzzling139335.FiniteBoundaryPartition.ClosedCover

/-!
# Finite boundary partitions

A Jordan curve covered by finitely many closed sets, with distinct labels
overlapping only at finitely many points of the curve, admits a finite ordered
parameter partition.  Each closed interval image belongs to one cover set.
The midpoint is always a breakpoint, so no interval traverses the whole loop.
-/

open Set

namespace Puzzling139335

/-- A continuous path with finitely many exceptional parameters has a finite
partition subordinate to a closed cover which is disjoint off the exceptions. -/
theorem continuousOn_exists_finite_closed_cover_partition
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {f : ℝ → X} (hf : ContinuousOn f (Icc 0 1))
    (T : ι → Set X) (hclosed : ∀ i, IsClosed (T i))
    (hcover : f '' Icc 0 1 ⊆ ⋃ i, T i) (E : Set X)
    (hfinite : (Icc 0 1 ∩ f ⁻¹' E).Finite)
    (hoverlap : ∀ i j, i ≠ j → (f '' Icc 0 1) ∩ T i ∩ T j ⊆ E) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧
      ∀ k : Fin n, ∃ j, f '' Icc (t k.castSucc) (t k.succ) ⊆ T j := by
  obtain ⟨n, hn, t, ht, ht0, ht1, hhalf, havoid⟩ :=
    exists_partition_avoiding_finite hfinite inter_subset_left
  refine ⟨n, hn, t, ht, ht0, ht1, hhalf, ?_⟩
  intro k
  have ha := partition_mem_unitInterval ht ht0 ht1 k.castSucc
  have hb := partition_mem_unitInterval ht ht0 ht1 k.succ
  have hab : t k.castSucc < t k.succ := ht k.castSucc_lt_succ
  have hclosedI : Icc (t k.castSucc) (t k.succ) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc ha.1 hb.2
  have hopenI : Ioo (t k.castSucc) (t k.succ) ⊆ Icc (0 : ℝ) 1 :=
    Ioo_subset_Icc_self.trans hclosedI
  have hS : IsConnected (f '' Ioo (t k.castSucc) (t k.succ)) :=
    (isConnected_Ioo hab).image f (hf.mono hopenI)
  have hsub : f '' Ioo (t k.castSucc) (t k.succ) ⊆ f '' Icc 0 1 :=
    image_mono hopenI
  have hdisE : Disjoint (f '' Ioo (t k.castSucc) (t k.succ)) E := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hfx
    exact Set.disjoint_left.mp (havoid k) hx ⟨hopenI hx, hfx⟩
  have hdis : Pairwise fun i j =>
      Disjoint ((f '' Ioo (t k.castSucc) (t k.succ)) ∩ T i)
        ((f '' Ioo (t k.castSucc) (t k.succ)) ∩ T j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp hdisE hxi.1
      (hoverlap i j hij ⟨⟨hsub hxi.1, hxi.2⟩, hxj.2⟩)
  obtain ⟨j, hj⟩ := exists_subset_of_finite_closed_cover hS hclosed (hsub.trans hcover) hdis
  refine ⟨j, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcl : x ∈ closure (Ioo (t k.castSucc) (t k.succ)) := by
    rwa [closure_Ioo hab.ne]
  have hfxcl : f x ∈ closure (f '' Ioo (t k.castSucc) (t k.succ)) :=
    ((hf x (hclosedI hx)).mono hopenI).mem_closure_image hxcl
  exact closure_minimal hj (hclosed j) hfxcl

end Puzzling139335

namespace Schoenflies

/-- A Jordan-loop parametrization meets a finite set at only finitely many
parameters in the closed unit interval. -/
theorem IsLoop.finite_preimage_inter_unitInterval {f : ℝ → Plane}
    (hf : IsLoop f) {E : Set Plane} (hE : E.Finite) :
    (Icc 0 1 ∩ f ⁻¹' E).Finite := by
  have hhalf : (Ico 0 1 ∩ f ⁻¹' E).Finite :=
    hE.of_injOn (f := f) (fun _ hx => hx.2) (hf.injOn.mono inter_subset_left)
  apply (hhalf.insert 1).subset
  rintro x ⟨hx, hfx⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr ⟨⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩, hfx⟩

/-- Finite pairwise overlap of a closed cover along a Jordan curve gives a
finite consecutive partition whose closed interval images have single labels. -/
theorem IsLoop.exists_finite_closed_cover_partition {ι : Type*} [Finite ι]
    {f : ℝ → Plane} (hf : IsLoop f) (T : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : f '' Icc 0 1 ⊆ ⋃ i, T i)
    (E : Set Plane) (hE : E.Finite)
    (hoverlap : ∀ i j, i ≠ j → (f '' Icc 0 1) ∩ T i ∩ T j ⊆ E) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧
      ∀ k : Fin n, ∃ j, f '' Icc (t k.castSucc) (t k.succ) ⊆ T j :=
  Puzzling139335.continuousOn_exists_finite_closed_cover_partition hf.continuousOn
    T hclosed hcover E (hf.finite_preimage_inter_unitInterval hE) hoverlap

/-- Set-level form: choose a Jordan parametrization together with the finite
partition subordinate to the closed cover. -/
theorem IsJordanCurve.exists_finite_closed_cover_partition {ι : Type*} [Finite ι]
    {C : Set Plane} (hC : IsJordanCurve C) (T : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : C ⊆ ⋃ i, T i)
    (E : Set Plane) (hE : E.Finite)
    (hoverlap : ∀ i j, i ≠ j → C ∩ T i ∩ T j ⊆ E) :
    ∃ f : ℝ → Plane, IsLoop f ∧ f '' Icc 0 1 = C ∧
      ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
        StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
        (1 / 2 : ℝ) ∈ range t ∧
        ∀ k : Fin n, ∃ j, f '' Icc (t k.castSucc) (t k.succ) ⊆ T j := by
  obtain ⟨f, hf, hfC⟩ := hC
  refine ⟨f, hf, hfC, hf.exists_finite_closed_cover_partition T hclosed ?_ E hE ?_⟩
  · rwa [hfC]
  · rwa [hfC]

end Schoenflies
