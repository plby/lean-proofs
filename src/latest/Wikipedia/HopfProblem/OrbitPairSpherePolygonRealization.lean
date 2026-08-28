import Wikipedia.HopfProblem.OrbitPairSphereCanonicalSegment
import Wikipedia.HopfProblem.OrbitPairOrderedSums
import Wikipedia.NoExoticSixSphere.RealIntervalProgress

/-!
# Actual continuous broken-geodesic realization of sphere polygons

Sum the displacements of clamped geodesic segments in the original ambient
Euclidean space. On every partition interval the completed prefix telescopes,
the tail vanishes, and the sum is exactly the active geodesic. Consequently
the sum has unit norm, hits every specified vertex, and is jointly continuous
in the admissible vertices and real time. It is constant outside the partition.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereCanonicalGeodesic
  RealIntervalProgress OrderedSums

variable {n m : ℕ}

def edgeDisplacement (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) (i : Fin (m + 1)) : Vector (n + 1) :=
  (segment (vertices a b v i.castSucc) (vertices a b v i.succ)
    (progress (τ i.castSucc) (τ i.succ) t)).val - (vertices a b v i.castSucc).val

def ambientPath (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) : Vector (n + 1) :=
  a.val + Fin.partialSum (edgeDisplacement a b τ v t) (Fin.last (m + 1))

theorem continuous_edgeDisplacement (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : Continuous (fun p : admissible (costDomain n) a b m × ℝ =>
      edgeDisplacement a b τ p.1.val p.2 i) := by
  let left : admissible (costDomain n) a b m → Sphere n :=
    fun v => vertices a b v.val i.castSucc
  let right : admissible (costDomain n) a b m → Sphere n :=
    fun v => vertices a b v.val i.succ
  have hl : Continuous left := (contMDiff_vertices a b i.castSucc).continuous.comp
    continuous_subtype_val
  have hr : Continuous right := (contMDiff_vertices a b i.succ).continuous.comp
    continuous_subtype_val
  have hs := continuous_segment left right hl hr (fun v => v.2 i)
  have ht : Continuous (fun p : admissible (costDomain n) a b m × ℝ =>
      (progress (τ i.castSucc) (τ i.succ) p.2, p.1)) :=
    ((continuous_progress _ _).comp continuous_snd).prodMk continuous_fst
  exact (continuous_subtype_val.comp (hs.comp ht)).sub
    ((continuous_subtype_val.comp hl).comp continuous_fst)

theorem continuous_ambientPath (a b : Sphere n) (τ : Fin (m + 2) → ℝ) :
    Continuous (fun p : admissible (costDomain n) a b m × ℝ => ambientPath a b τ p.1.val p.2) :=
  continuous_const.add
    (continuous_partialSum (continuous_edgeDisplacement a b τ) (Fin.last (m + 1)))

theorem ambientPath_eq_segment (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    ambientPath a b τ v t =
      (rescaledSegment (vertices a b v i.castSucc) (vertices a b v i.succ)
        (τ i.castSucc) (τ i.succ) t).val := by
  have htime (j : Fin (m + 1)) : τ j.castSucc < τ j.succ :=
    hτ (show j.castSucc < j.succ by simp)
  let delta : Fin (m + 1) → Vector (n + 1) :=
    fun j => (vertices a b v j.succ).val - (vertices a b v j.castSucc).val
  have hbefore (j : Fin (m + 1)) (hj : j < i) : edgeDisplacement a b τ v t j = delta j := by
    have hji : j.succ ≤ i.castSucc := hj
    rw [edgeDisplacement, progress_after (htime j) ((hτ.monotone hji).trans ht.1),
      segment_one _ _ (hv j)]
  have hafter (j : Fin (m + 1)) (hj : i < j) : edgeDisplacement a b τ v t j = 0 := by
    have hij : i.succ ≤ j.castSucc := hj
    rw [edgeDisplacement, progress_before (htime j).le (ht.2.trans (hτ.monotone hij)),
      segment_zero, sub_self]
  have hprefix : a.val + Fin.partialSum delta i.castSucc = (vertices a b v i.castSucc).val :=
    partialSum_differences (fun j => (vertices a b v j).val) i.castSucc
  rw [ambientPath, partialSum_last_eq _ delta i hbefore hafter, ← add_assoc, hprefix,
    edgeDisplacement, progress_of_mem (htime i) ht]
  change (vertices a b v i.castSucc).val +
    ((rescaledSegment (vertices a b v i.castSucc) (vertices a b v i.succ)
      (τ i.castSucc) (τ i.succ) t).val - (vertices a b v i.castSucc).val) = _
  abel

theorem ambientPath_before (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m) {t : ℝ} (ht : t ≤ τ 0) :
    ambientPath a b τ v t = a.val := by
  have he : edgeDisplacement a b τ v t = fun _ => 0 := by
    funext i
    rw [edgeDisplacement, progress_before
      (hτ (show i.castSucc < i.succ by simp)).le
      (ht.trans (hτ.monotone (Fin.zero_le _))), segment_zero, sub_self]
  rw [ambientPath, he]
  simp [Fin.partialSum]

theorem ambientPath_after (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m)
    {t : ℝ} (ht : τ (Fin.last (m + 1)) ≤ t) : ambientPath a b τ v t = b.val := by
  have he : edgeDisplacement a b τ v t =
      fun i => (vertices a b v i.succ).val - (vertices a b v i.castSucc).val := by
    funext i
    rw [edgeDisplacement, progress_after
      (hτ (show i.castSucc < i.succ by simp))
      ((hτ.monotone (Fin.le_last _)).trans ht), segment_one _ _ (hv i)]
  rw [ambientPath, he]
  simpa only [vertices_zero, vertices_last] using
    partialSum_differences (fun j => (vertices a b v j).val) (Fin.last (m + 1))

theorem norm_ambientPath (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m) (t : ℝ) :
    ‖ambientPath a b τ v t‖ = 1 := by
  by_cases hlo : t ≤ τ 0
  · rw [ambientPath_before a b τ hτ v hlo, ClosedHemisphere.unit_norm]
  by_cases hhi : τ (Fin.last (m + 1)) ≤ t
  · rw [ambientPath_after a b τ hτ hv hhi, ClosedHemisphere.unit_norm]
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent τ
    ⟨(lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩
  rw [ambientPath_eq_segment a b τ hτ hv i hi, ClosedHemisphere.unit_norm]

def path (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : admissible (costDomain n) a b m) (t : ℝ) : Sphere n :=
  ⟨ambientPath a b τ v.val t, by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_ambientPath a b τ hτ v.2 t⟩

def family (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) :
    C(admissible (costDomain n) a b m × ℝ, Sphere n) :=
  ⟨fun p => path a b τ hτ p.1 p.2, (continuous_ambientPath a b τ).subtype_mk _⟩

theorem path_eq_segment (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) (i : Fin (m + 1))
    {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    path a b τ hτ v t = rescaledSegment (vertices a b v.val i.castSucc)
      (vertices a b v.val i.succ) (τ i.castSucc) (τ i.succ) t :=
  Subtype.ext (ambientPath_eq_segment a b τ hτ v.2 i ht)

theorem path_start (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) : path a b τ hτ v (τ 0) = a :=
  Subtype.ext (ambientPath_before a b τ hτ v.val le_rfl)

theorem path_end (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) :
    path a b τ hτ v (τ (Fin.last (m + 1))) = b :=
  Subtype.ext (ambientPath_after a b τ hτ v.2 le_rfl)

theorem path_vertex (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible (costDomain n) a b m) (j : Fin (m + 2)) :
    path a b τ hτ v (τ j) = vertices a b v.val j := by
  induction j using Fin.lastCases with
  | last => rw [path_end, vertices_last]
  | cast i =>
    have htime : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
    rw [path_eq_segment a b τ hτ v i ⟨le_rfl, htime.le⟩, rescaledSegment_start]

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
