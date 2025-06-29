import Mathlib.Analysis.RCLike.Basic
open Function Set
noncomputable section

/-!
# Dyadic Structures

We define dyadic intervals and dyadic rectangles, along with various lemmas about their properties (disjointness, covering the reals, etc.).
-/

namespace DyadicStructures

/-- Definition 1.1: Dyadic Interval and dyadic rectangle
  A dyadic interval is defined as `[2^k * n, 2^k * (n + 1))`. --/
def dyadicInterval (k n : ℤ) : Set ℝ :=
  { x | (2^k : ℝ) * n ≤ x ∧ x < (2^k : ℝ) * (n + 1) }


/-- Special case: the dyadic interval with `k,n = 0` is `[0, 1)`. -/
@[simp]
theorem zero_dyadicInterval : dyadicInterval 0 0 = Set.Ico 0 1 := by
  ext x
  simp [dyadicInterval]

/-- Special case: the dyadic interval with `k = 0` is `[n, n+1)`. --/
@[simp]
theorem dyadicInterval_of_k_zero (n : ℤ) :
    dyadicInterval 0 n = Set.Ico (n : ℝ) (n+1) := by
  ext x
  simp [Set.Ico, Set.mem_setOf_eq, dyadicInterval, zpow_zero]


/-- Special case: the dyadic interval with `k = 1` is `[2n, 2n+2)`. --/
@[simp]
theorem dyadicInterval_of_k_one (n : ℤ) :
    dyadicInterval 1 n = Set.Ico (2*n : ℝ) (2*n+2) := by
  ext x
  simp only [dyadicInterval, zpow_one, mem_setOf_eq, Ico, and_congr_right_iff]
  intro h
  ring_nf

/-- Special case: the dyadic interval with `k = -1` is `[n/2, (n+1)/2)`. --/
@[simp]
theorem dyadicInterval_of_k_negone (n : ℤ) :
    dyadicInterval (-1) n = Set.Ico (n/2 : ℝ ) ((n + 1)/2) := by
  ext x
  simp [Set.Ico, Set.mem_setOf_eq, dyadicInterval, zpow_neg_one]
  ring_nf

/-- Special case: the dyadic interval with `n = 0` is `[0, 2^k)`. --/
@[simp]
theorem dyadicInterval_of_n_zero (k : ℤ) :
    dyadicInterval k 0 = Set.Ico (0 : ℝ) (2^k : ℝ) := by
  ext x
  simp [dyadicInterval]

/-- Special case: the dyadic interval with `n = 1` is `[2^k, 2^(k+1))`. --/
@[simp]
theorem dyadicInterval_of_n_one (k : ℤ) :
    dyadicInterval k 1 = Set.Ico (2^k : ℝ) (2^(k+1) : ℝ) := by
  ext x
  simp only [dyadicInterval, Int.cast_one, mul_one, mem_setOf_eq, mem_Ico, and_congr_right_iff]
  intro h
  have h1 : 2 ^ k * (1 + 1) = (2 ^ (k + 1) : ℝ) := by
    have : 2 ≠ 0 := two_ne_zero
    calc (2 : ℝ)^k*(1+1)
        = (2 : ℝ  )^(k)*2 := by ring_nf
      _ = (2 : ℝ)^(k + 1) := by rw [← zpow_add_one₀ two_ne_zero k]
  rw [h1]


/-- General case: writting dyadic as Ico-/
theorem intervalform_dyadicInterval {k n : ℤ}: dyadicInterval k n = Set.Ico ((2^k: ℝ) *n) ((2^k : ℝ )* (n + 1)) := by
  ext x
  simp [dyadicInterval]

/--
Points inside the same dyadic interval at scale `k` are within `(2^k : ℝ)` of each other.
-/

theorem dyadicInterval_length (k n : ℤ) (x y : ℝ ) (h : x ∈ dyadicInterval k n ∧ y ∈ dyadicInterval k n) : |x - y| ≤ (2^k : ℝ) := by
  simp [dyadicInterval] at h
  rw[abs_sub_le_iff]
  constructor
  · linarith
  · linarith

/--
A dyadic interval at scale `k` can be expressed as a union of two smaller intervals of the scale `k - 1`.
-/

theorem scale_up {k n : ℤ} : dyadicInterval k n = { x | (2^(k-1) : ℝ)*(2*n) ≤ x ∧ x < (2^(k-1) : ℝ)*(2*n+2) } := by
  ext x
  simp only [dyadicInterval, mem_setOf_eq]
  rw[← mul_assoc,← zpow_add_one₀ two_ne_zero (k-1)]
  simp only [sub_add_cancel, and_congr_right_iff]
  intro h1
  constructor
  · intro h2
    rw[mul_add, ← mul_assoc, ← zpow_add_one₀ two_ne_zero (k-1)]
    simp only [sub_add_cancel]
    rw [← mul_one (2^k), mul_assoc, one_mul, ← mul_add]
    apply h2
  · intro h2
    rw[mul_add, ← mul_assoc, ← zpow_add_one₀ two_ne_zero (k-1)] at h2
    simp only [sub_add_cancel] at h2
    rw [← mul_one (2^k), mul_assoc, one_mul, ← mul_add] at h2
    apply h2



/--
A dyadic interval can be split into two smaller dyadic intervals.
-/
theorem dyadicInterval_split (k n : ℤ) :
  dyadicInterval k n = dyadicInterval (k - 1) (2 * n) ∪ dyadicInterval (k - 1) (2 * n + 1) := by
  rw[scale_up, intervalform_dyadicInterval, intervalform_dyadicInterval]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_one]
  rw[Set.Ico_union_Ico_eq_Ico]
  · unfold Set.Ico
    ring_nf
  · rw[mul_add]
    simp only [mul_one, le_add_iff_nonneg_right]
    apply le_of_lt
    apply zpow_pos
    simp
  · rw[mul_add, mul_add, mul_add]
    simp only [mul_one, le_add_iff_nonneg_right]
    apply le_of_lt
    apply zpow_pos
    simp




/--
The dyadic intervals at scale `k` cover the entire real line.
-/

theorem dyadicInterval_cover (k : ℤ) :
  ⋃ n : ℤ, dyadicInterval k n = Set.univ := by
  ext x
  simp only [dyadicInterval, mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
  let n := Int.floor (x / (2^k : ℝ))
  have h1 :  2^k* n ≤ x := by
    simp[n]
    ring_nf
    have : (⌊x / (2^k : ℝ)⌋ : ℝ) ≤ x / (2^k : ℝ) := Int.floor_le (x / (2^k : ℝ))
    rw[mul_comm,← le_div_iff₀]
    exact this
    apply zpow_pos ?ha k
    linarith
  have h2 : x < 2^k * (n+1) := by
    unfold n
    have : x / (2^k : ℝ) < (⌊x / (2^k : ℝ)⌋ + 1 : ℝ) := Int.lt_floor_add_one (x / (2^k : ℝ))
    rw[mul_comm, ← div_lt_iff₀]
    exact this
    apply zpow_pos ?ha k
  exact Filter.frequently_principal.mp fun a ↦ a h1 h2

/--
If `n < n'`, then the dyadic intervals at scale `k` indexed by `n` and `n'` are disjoint.
-/
theorem dyadicInterval_disjoint_help {k n n' : ℤ} (h : n < n') :
  (dyadicInterval k n ∩ dyadicInterval k n') = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h0 : n + 1 ≤ n' := by
    rw[Int.add_one_le_iff]
    apply h
  have h12 : (2 ^ k : ℝ) * (n + 1) ≤ (2 ^ k : ℝ) * n' := by
    apply mul_le_mul_of_nonneg_left
    exact_mod_cast h0
    linarith
  linarith

/--
Dyadic intervals at the same scale `k` and different indices `n ≠ n'` are disjoint.
-/
theorem dyadicInterval_disjoint {k n n' : ℤ} (h : n ≠ n') : (dyadicInterval k n ∩ dyadicInterval k n') = ∅ := by
  by_cases h1 : n<n'
  · apply dyadicInterval_disjoint_help
    apply h1
  push_neg at h1
  have h1' : n' < n := by
    exact lt_of_le_of_ne h1 (id (Ne.symm h))
  rw[Set.inter_comm]
  apply dyadicInterval_disjoint_help
  apply h1'

/--
Case when dyadic intervals with the scales `k<k'` - then they are disjoint or one is contained in the other.
-/

theorem dyadic_intervals_relation {k k' n n' : ℤ} (h : k < k') :
  dyadicInterval k n ∩ dyadicInterval k' n' = ∅ ∨
  dyadicInterval k n ⊆ dyadicInterval k' n' ∨
  dyadicInterval k' n' ⊆ dyadicInterval k n := by
  apply Int.le.dest at h
  obtain ⟨p, h_p⟩ := h
  set p':= 1+p with h_p'
  have hp' : (2^k' : ℝ) = 2^k * 2^↑p':= by
    rw[h_p', ← h_p]
    rw [add_assoc, zpow_add₀ two_ne_zero]
    norm_cast
  by_cases h_1 : (2^k *n : ℝ ) < (2^k' * n' : ℝ)
  · rw[hp'] at h_1
    have h_01 : n < (2 : ℕ) ^ p'  * ↑n' := by
      rw [mul_assoc, mul_lt_mul_left (zpow_pos zero_lt_two k)] at h_1
      norm_cast at h_1
      rw [Int.natCast_pow] at h_1
      exact h_1
    rw[← Int.add_one_le_iff] at h_01
    have h_02 : (2^k : ℝ ) * (n + 1) ≤ 2^ k * 2 ^ p' * n' := by
      rw[mul_assoc]
      refine mul_le_mul_of_nonneg_left (α := ℝ) ?_ (zpow_pos zero_lt_two k).le
      norm_cast
      rw [Int.natCast_pow]
      exact h_01
    rw[← hp'] at h_02
    left
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    linarith
  · push_neg at h_1
    by_cases h_2 : (2^k *(n+1) : ℝ ) ≤   (2^k' * (n'+1) : ℝ)
    · right
      left
      simp only [dyadicInterval, setOf_subset_setOf]
      intro a ha
      obtain ⟨ ha1,ha2⟩  := ha
      constructor
      · linarith
      · linarith
    · left
      push_neg at h_2
      have hn1: 2^p' * n' ≤  n := by
        rw[hp'] at h_1
        rw [mul_assoc, mul_le_mul_left (zpow_pos zero_lt_two k)] at h_1
        norm_cast at h_1
        rw [Int.natCast_pow] at h_1
        exact h_1
      have hn2 : 2^p' * (n' + 1) < n+1 := by
        rw[hp'] at h_2
        rw [mul_assoc, mul_lt_mul_left (zpow_pos zero_lt_two k)] at h_2
        norm_cast at h_2
        rw [Int.natCast_pow] at h_2
        exact h_2
      have hmain : (2^p' : ℕ ) *(n'+1) ≤  n := by
        rw[← Int.lt_add_one_iff]
        norm_cast
        rw [Int.natCast_pow]
        exact hn2
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have : (2^k' : ℝ  ) *(n'+1) ≤  2^k * n := by
        rw[hp']
        rw [mul_assoc, mul_le_mul_left (a := (2 ^ k : ℝ)) (zpow_pos zero_lt_two k)]
        norm_cast
      linarith



/--
Theorem: Two dyadic intervals are either disjoint or one is contained in the other.
-/
theorem dyadic_intervals_disjoint_or_contained (k k' n n' : ℤ) :
  (dyadicInterval k n ∩ dyadicInterval k' n' = ∅) ∨
  (dyadicInterval k n ⊆ dyadicInterval k' n') ∨
  (dyadicInterval k' n' ⊆ dyadicInterval k n) := by
  by_cases h : k=k'
  · rw[h]
    by_cases hn : n=n'
    · rw[hn]
      simp
    · push_neg at hn
      left
      apply dyadicInterval_disjoint hn
  push_neg at h
  by_cases h1 : k<k'
  · apply dyadic_intervals_relation
    apply h1
  push_neg at h1
  have h_lt : k' < k := lt_of_le_of_ne h1 h.symm
  rw[Set.inter_comm,← or_assoc, or_right_comm, or_assoc]
  apply dyadic_intervals_relation h_lt


/--
A dyadic rectangle is the Cartesian product of two dyadic intervals.
-/
def dyadicRectangle (k n k' n' : ℤ) : Set (ℝ × ℝ)  :=
  (dyadicInterval k n).prod (dyadicInterval k' n')

/--
Collection of dyadic intervals at a fixed scale.
-/
def SetDyadicIntervals (m : ℕ) : Set (Set ℝ) :=
  {dyadicInterval (-m) n | n ∈ Finset.range (2^m)}

/--
Tile.
-/
def Tile (I : Set ℝ) (ω : Set ℝ) : Prop :=
  ∃ k n : ℤ, I = dyadicInterval k n ∧ ω = {x | x = 2^(-k)}

end DyadicStructures
