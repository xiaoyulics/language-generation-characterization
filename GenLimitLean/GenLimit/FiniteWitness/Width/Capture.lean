import GenLimit.FiniteWitness.Width.Foundation

/-!
Bounded capture with avoidance of countably many infinite cores.
The formal proof inducts directly on the size bound. The sparse case uses
finite partial states; the frequent-point case deletes and reinserts a point.
No Delta-system theorem or regularity assumption is imported.
-/

namespace GenLimit.FiniteWitness

variable {α : Type*}

private structure CaptureState (U : ℕ → Finset α) where
  indices : Finset ℕ
  forbidden : Finset α
  safe : ∀ i ∈ indices, ∀ x ∈ forbidden, x ∉ U i

private theorem capture_step (U : ℕ → Finset α) (C : ℕ → Set α)
    (hf : ∀ x, {n | x ∈ U n}.Finite) (m : ℕ) (s : CaptureState U) :
    ∃ t : CaptureState U, s.indices ⊆ t.indices ∧ s.forbidden ⊆ t.forbidden ∧
      (∃ i ∈ t.indices, m < i) ∧
      ((C m).Infinite → ∃ x ∈ C m, x ∈ t.forbidden) := by
  classical
  let bad := Finset.range (m + 1) ∪ s.forbidden.biUnion (fun x => (hf x).toFinset)
  obtain ⟨i, _, hi⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finset bad
  have hmi : m < i := by
    have hn : i ∉ Finset.range (m + 1) := fun h => hi (Finset.mem_union_left _ h)
    simp only [Finset.mem_range, not_lt] at hn
    omega
  have hisafe : ∀ x ∈ s.forbidden, x ∉ U i := by
    intro x hx hxi
    apply hi
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨x, hx, (hf x).mem_toFinset.mpr hxi⟩
  let I := insert i s.indices
  have hsafe : ∀ j ∈ I, ∀ x ∈ s.forbidden, x ∉ U j := by
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hisafe x hx
    · exact s.safe j hj x hx
  by_cases hC : (C m).Infinite
  · obtain ⟨x, hx, hxnot⟩ := hC.exists_notMem_finset (I.biUnion U)
    let t : CaptureState U := ⟨I, insert x s.forbidden, by
      intro j hj y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · intro hxy
        exact hxnot (Finset.mem_biUnion.mpr ⟨j, hj, hxy⟩)
      · exact hsafe j hj y hy⟩
    exact ⟨t, Finset.subset_insert _ _, Finset.subset_insert _ _,
      ⟨i, Finset.mem_insert_self _ _, hmi⟩, fun _ => ⟨x, hx, Finset.mem_insert_self _ _⟩⟩
  · let t : CaptureState U := ⟨I, s.forbidden, hsafe⟩
    exact ⟨t, Finset.subset_insert _ _, (fun _ h => h),
      ⟨i, Finset.mem_insert_self _ _, hmi⟩, fun h => (hC h).elim⟩

private theorem sparse_capture (U : ℕ → Finset α) (C : ℕ → Set α)
    (hf : ∀ x, {n | x ∈ U n}.Finite) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ m, (C m).Infinite → ¬ C m ⊆ D := by
  classical
  choose next hi hf' hl hc using capture_step U C hf
  let start : CaptureState U := ⟨∅, ∅, by simp⟩
  let state : ℕ → CaptureState U := Nat.rec start (fun n s => next n s)
  have hstep (n) : state (n + 1) = next n (state n) := rfl
  have hI : Monotone (fun n => (state n).indices) :=
    monotone_nat_of_le_succ (fun n => hi n (state n))
  have hF : Monotone (fun n => (state n).forbidden) :=
    monotone_nat_of_le_succ (fun n => hf' n (state n))
  let D : Set α := {x | ∃ n, ∃ i ∈ (state n).indices, x ∈ U i}
  have hcap (n i) (hi : i ∈ (state n).indices) : (↑(U i) : Set α) ⊆ D :=
    fun x hx => ⟨n, i, hi, hx⟩
  refine ⟨D, ?_, ?_⟩
  · intro hfinite
    let N := hfinite.toFinset.sup id
    obtain ⟨i, himem, hNi⟩ := hl N (state N)
    have hmem : i ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr (hcap (N + 1) i himem)
    have hle : i ≤ N := Finset.le_sup (f := id) hmem
    omega
  · intro m hm hsub
    obtain ⟨x, hxC, hxF⟩ := hc m (state m) hm
    obtain ⟨n, i, hiI, hxi⟩ := hsub hxC
    exact (state (max n (m + 1))).safe i
      (hI (le_max_left _ _) hiI) x (hF (le_max_right _ _) hxF) hxi

/-- A uniformly bounded finite-set sequence is captured infinitely often by
one set containing none of the prescribed infinite cores. The universe is
arbitrary; no countability or measurability of its points is assumed. -/
theorem bounded_capture (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) (C : ℕ → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ m, (C m).Infinite → ¬ C m ⊆ D := by
  classical
  induction d generalizing U C with
  | zero =>
      have hzero (n) : U n = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hU n))
      refine ⟨∅, ?_, ?_⟩
      · simpa [hzero] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
      · intro m hm hs
        exact hm (Set.finite_empty.subset hs)
  | succ d ih =>
      by_cases hmany : ∃ x : α, {n | x ∈ U n}.Infinite
      · obtain ⟨x, hx⟩ := hmany
        let e := hx.natEmbedding {n | x ∈ U n}
        let f : ℕ → ℕ := fun n => (e n).val
        have hf : Function.Injective f := Subtype.val_injective.comp e.injective
        have hxf (n) : x ∈ U (f n) := (e n).property
        let V : ℕ → Finset α := fun n => (U (f n)).erase x
        have hV (n) : (V n).card ≤ d := by
          have he := Finset.card_erase_of_mem (hxf n)
          have hb := hU (f n)
          dsimp [V]
          omega
        obtain ⟨D, hD, havoid⟩ := ih V hV (fun m => C m \ {x})
        refine ⟨insert x D, ?_, ?_⟩
        · apply (hD.image hf.injOn).mono
          rintro _ ⟨n, hn, rfl⟩ y hy
          by_cases he : y = x
          · exact Set.mem_insert_iff.mpr (Or.inl he)
          · exact Set.mem_insert_iff.mpr (Or.inr (hn (Finset.mem_erase.mpr ⟨he, hy⟩)))
        · intro m hm hs
          apply havoid m (hm.diff (Set.finite_singleton x))
          intro y hy
          rcases hs hy.1 with he | hd
          · exact False.elim (hy.2 (by simpa using he))
          · exact hd
      · apply sparse_capture U C
        intro x
        by_contra hn
        exact hmany ⟨x, hn⟩

theorem bounded_capture_indexed {ι : Type*} [Countable ι]
    (d : ℕ) (U : ℕ → Finset α) (hU : ∀ n, (U n).card ≤ d) (C : ι → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ i, (C i).Infinite → ¬ C i ⊆ D := by
  classical
  letI : Encodable ι := Encodable.ofCountable ι
  let C' : ℕ → Set α := fun n => ((Encodable.decode (α := ι) n).map C).getD ∅
  obtain ⟨D, hD, hC⟩ := bounded_capture d U hU C'
  refine ⟨D, hD, ?_⟩
  intro i
  simpa [C'] using hC (Encodable.encode i)

end GenLimit.FiniteWitness
