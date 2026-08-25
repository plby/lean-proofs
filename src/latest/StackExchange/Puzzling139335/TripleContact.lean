import StackExchange.Puzzling139335.JordanAccessibility
import StackExchange.Puzzling139335.WeightedMass.Family
import Wikipedia.SchoenfliesTheorem.Graph.K33Land
import Mathlib.Data.Set.Card

/-!
# Three Jordan pieces have at most two common points

Three common points would give nine access spokes, forming an embedded
`K₃,₃`.  The existing nonplanarity theorem rules this out.  The access spokes
are arbitrary Jordan arcs, so no polygonality assumption is needed.
-/

open Set

namespace Puzzling139335

/-- Three closed Jordan regions with pairwise disjoint interiors cannot
contain three distinct common points. -/
theorem jordan_regions_no_three_common_points (P : Fin 3 → Set Plane)
    (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (b : Fin 3 → Plane) (hb : ∀ i j, b j ∈ P i) (hinj : Function.Injective b) : False := by
  classical
  have hdisIQ {i j : Fin 3} (hij : i ≠ j) : Disjoint (interior (P i)) (P j) :=
    (hP j).disjoint_interior_left (hdis hij)
  have hfront (i j : Fin 3) : b j ∈ frontier (P i) := by
    apply (mem_frontier_iff_notMem_interior (hb i j)).mpr
    intro hint
    obtain ⟨k, hki⟩ := exists_ne i
    exact Set.disjoint_left.mp (hdisIQ hki.symm) hint (hb k j)
  choose x hx using fun i => (hP i).interior_nonempty
  choose A hAarc hAint hAmeet using fun i =>
    (hP i).exists_disjoint_arcs_to_frontier (hx i) b (hfront i) hinj
  have hAsub (i j : Fin 3) : A i j ⊆ P i := by
    intro z hz
    by_cases hzb : z = b j
    · exact hzb ▸ hb i j
    · exact interior_subset (hAint i j ⟨hz, hzb⟩)
  have hK : _root_.Graph.IsArcK33 x b A := by
    refine ⟨hAarc, ?_, hinj, ?_, ?_⟩
    · intro i k hik
      by_contra hine
      exact Set.disjoint_left.mp (hdis hine) (hx i) (by simpa only [hik] using hx k)
    · intro i j hij
      exact (hfront i j).2 (hij ▸ hx i)
    · intro i j k l hne z hz
      by_cases hik : i = k
      · subst k
        have hjl : j ≠ l := fun h => hne (Prod.ext rfl h)
        have hzx : z = x i := mem_singleton_iff.mp (hAmeet i j l hjl ▸ hz)
        subst z
        simp
      · have hzbj : z = b j := by
          by_contra hzne
          exact Set.disjoint_left.mp (hdisIQ hik) (hAint i j ⟨hz.1, hzne⟩)
            (hAsub k l hz.2)
        have hzbl : z = b l := by
          by_contra hzne
          exact Set.disjoint_left.mp (hdisIQ (Ne.symm hik)) (hAint k l ⟨hz.2, hzne⟩)
            (hAsub i j hz.1)
        exact ⟨Or.inr hzbj, Or.inr hzbl⟩
  exact hK.elim

/-- The extended cardinal bound includes the finiteness assertion. -/
theorem jordan_regions_triple_intersection_encard_le_two (P : Fin 3 → Set Plane)
    (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))) :
    (⋂ i, P i).encard ≤ 2 := by
  classical
  by_cases hs : (⋂ i, P i).Subsingleton
  · exact (encard_le_one_iff_subsingleton.mpr hs).trans (by norm_num)
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hs
  have hsub : (⋂ i, P i) ⊆ {a, b} := by
    intro c hc
    by_contra hnot
    have hca : c ≠ a := fun h => hnot (Or.inl h)
    have hcb : c ≠ b := fun h => hnot (Or.inr h)
    apply jordan_regions_no_three_common_points P hP hdis ![a, b, c]
    · intro i j
      fin_cases j
      · exact mem_iInter.mp ha i
      · exact mem_iInter.mp hb i
      · exact mem_iInter.mp hc i
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  exact (encard_mono hsub).trans_eq (encard_pair hab)

/-- In particular, three such pieces have a finite common intersection. -/
theorem jordan_regions_triple_intersection_finite (P : Fin 3 → Set Plane)
    (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))) :
    (⋂ i, P i).Finite :=
  finite_of_encard_le_coe (jordan_regions_triple_intersection_encard_le_two P hP hdis)

/-- The finite triple-intersection statement in a larger indexed family. -/
theorem jordan_regions_triple_intersection_finite_of_distinct {ι : Type*}
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (P i ∩ P j ∩ P k).Finite := by
  classical
  let q : Fin 3 → ι := ![i, j, k]
  have hq : Function.Injective q := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [q]
  have hdisq : Pairwise fun a b : Fin 3 =>
      Disjoint (interior (P (q a))) (interior (P (q b))) := by
    intro a b hab
    exact hdis (fun h => hab (hq h))
  have hfinite := jordan_regions_triple_intersection_finite
    (fun a => P (q a)) (fun a => hP (q a)) hdisq
  have heq : (⋂ a : Fin 3, P (q a)) = P i ∩ P j ∩ P k := by
    ext z
    simp [q, Fin.forall_fin_succ, and_assoc]
  rwa [heq] at hfinite

/-- All triple contacts in a finite Jordan family form a finite set. -/
theorem jordan_regions_tripleContactSet_finite {ι : Type*} [Finite ι]
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))) :
    (tripleContactSet P).Finite := by
  classical
  let T := {q : ι × ι × ι // q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2}
  have hfinite (q : T) : (P q.val.1 ∩ P q.val.2.1 ∩ P q.val.2.2).Finite :=
    jordan_regions_triple_intersection_finite_of_distinct P hP hdis
      q.property.1 q.property.2.1 q.property.2.2
  apply (Set.finite_iUnion hfinite).subset
  rintro z ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
  exact mem_iUnion.mpr ⟨⟨(i, j, k), hij, hik, hjk⟩, ⟨⟨hi, hj⟩, hk⟩⟩

/-- This supplies the finiteness input to the dissection's weighted-mass
identities, with no additional geometric hypothesis. -/
theorem SquareDissection.tripleContactSet_finite (d : SquareDissection) :
    (tripleContactSet d.piece).Finite :=
  jordan_regions_tripleContactSet_finite d.piece d.jordan d.disjoint_interiors

end Puzzling139335
