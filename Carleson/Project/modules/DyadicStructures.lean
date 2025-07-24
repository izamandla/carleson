import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

theorem dyadicInterval_length (k n : ℤ) (x y : ℝ) (h : x ∈ dyadicInterval k n ∧ y ∈ dyadicInterval k n) : |x - y| ≤ (2^k : ℝ) := by
  simp [dyadicInterval] at h
  rw[abs_sub_le_iff]
  constructor
  · linarith
  · linarith

theorem dyadicInterval_measure (k n : ℤ): MeasureTheory.volume (dyadicInterval k n) = 2^k  := by
  rw[intervalform_dyadicInterval, Real.volume_Ico]
  have : ((2 ^ k : ℝ ) * (↑n + 1) - 2 ^ k * ↑n) = (2^k :ℝ ) := by
    linarith
  rw[this]

--proove this lemma for ENNReal.ofReal_pow but for ℤ


  sorry

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

theorem dyadicInterval_split' (k n : ℤ) :
  dyadicInterval (k+1) n = dyadicInterval k (2 * n) ∪ dyadicInterval k (2 * n + 1) := by
  rw[dyadicInterval_split (k+1) n]
  simp



theorem dyadicin (k n : ℤ) : dyadicInterval k n ⊆ dyadicInterval (k+1) (n/2) := by
  rw[ dyadicInterval_split (k+1)]
  simp only [add_sub_cancel_right]
  by_cases h : Odd n
  · rw [Int.two_mul_ediv_two_add_one_of_odd h]
    exact subset_union_right
  · simp only [Int.not_odd_iff_even] at h
    rw [Int.two_mul_ediv_two_of_even h]
    simp

theorem natdyadicin0 {M k : ℕ} (h : k < 2 ^ M): dyadicInterval (-M : ℤ) k ⊆ dyadicInterval 0 0 := by
  rw[zero_dyadicInterval]
  simp only [dyadicInterval, zpow_neg]
  rw [@Ico_def]
  refine Ico_subset_Ico ?_ ?_
  · simp
  · refine inv_mul_le_one_of_le₀ ?_ ?_
    · simp
      rw[Nat.lt_iff_add_one_le] at h
      norm_cast
    · simp

theorem natdyadicin0' {M k : ℕ} (h : k < 2 ^ M): dyadicInterval (-M : ℤ) k ⊆ Set.Ico 0 1 := by
  simp only [dyadicInterval, zpow_neg]
  rw [@Ico_def]
  refine Ico_subset_Ico ?_ ?_
  · simp
  · refine inv_mul_le_one_of_le₀ ?_ ?_
    · simp
      rw[Nat.lt_iff_add_one_le] at h
      norm_cast
    · simp


theorem infirsthalf {M k : ℕ} (hM : M ≠ 0): dyadicInterval (-M :ℤ) k ⊆ Ico 0 0.5 ↔ k < 2 ^ (M - 1 ) := by
  simp at hM
  rw[intervalform_dyadicInterval, Set.Ico_subset_Ico_iff]
  · simp only [zpow_neg, zpow_natCast, Int.cast_natCast, inv_pos, Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg, true_and]
    rw[inv_mul_le_iff₀]
    · ring_nf
      simp only [one_div]
      rw[ ← Nat.add_one_le_iff ]
      have : (2 ^ M :ℝ ) * 2⁻¹   = 2^(M-1) := by
        refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
        · simp
        · rw [pow_sub_one_mul hM 2]
      rw[this]
      norm_cast
      rw[add_comm]
    · simp
  · simp



theorem insecondhalf {M k : ℕ} (hk : k < 2 ^ M) (hM : M ≠ 0): dyadicInterval (-M :ℤ) k ⊆ Ico 0.5 1 ↔ 2 ^ (M - 1) ≤ k:= by
  simp at hM
  rw[intervalform_dyadicInterval, Set.Ico_subset_Ico_iff]
  · simp only [zpow_neg, zpow_natCast, Int.cast_natCast, inv_pos, Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg, true_and]
    rw[inv_mul_le_iff₀]
    · simp only [mul_one]
      rw[mul_comm, le_mul_inv_iff₀]
      · ring_nf
        simp only [one_div]
        have : (2 ^ M :ℝ ) * 2⁻¹   = 2^(M-1) := by
          refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
          · simp
          · rw [pow_sub_one_mul hM 2]
        rw[this]
        norm_cast
        simp only [and_iff_left_iff_imp]
        intro h
        rw[add_comm, Nat.add_one_le_iff ]
        exact hk
      · simp
    · simp
  · simp



theorem xinfirsthalf {M k : ℕ} {x : ℝ} (hx : x ∈ dyadicInterval (-M : ℤ) k) : 2*x ∈ dyadicInterval (-M :ℤ) (2*k) ∨ 2*x ∈ dyadicInterval (-M :ℤ) (2*k + 1) := by
  rw [← @mem_union, ← dyadicInterval_split']
  simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq] at hx
  simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
  have : (2 : ℝ ) ^ ((-M:ℤ) +1 ) = 2 * 2 ^ (-M : ℤ  ) := by
    rw [zpow_add₀, zpow_one, mul_comm]
    exact Ne.symm (NeZero.ne' 2)
  rw[this]
  obtain ⟨ hx1, hx2 ⟩ := hx
  constructor
  · rw[mul_assoc, mul_le_mul_left (two_pos), @zpow_neg]
    exact hx1
  · rw[mul_assoc, mul_lt_mul_left (two_pos), @zpow_neg]
    exact hx2


theorem xinfirsthalf' {M k : ℕ} {x : ℝ} (hx : x ∈ dyadicInterval (-M : ℤ) k) : 2*x ∈ dyadicInterval (-M + 1 :ℤ) k := by
  simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq] at hx
  simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
  have : (2 : ℝ ) ^ ((-M:ℤ) +1 ) = 2 * 2 ^ (-M : ℤ  ) := by
    rw [zpow_add₀, zpow_one, mul_comm]
    exact Ne.symm (NeZero.ne' 2)
  rw[this]
  obtain ⟨ hx1, hx2 ⟩ := hx
  constructor
  · rw[mul_assoc, mul_le_mul_left (two_pos), @zpow_neg]
    exact hx1
  · rw[mul_assoc, mul_lt_mul_left (two_pos), @zpow_neg]
    exact hx2


theorem xinsecondhalf {M k : ℕ} {x : ℝ} (hx : x ∈ dyadicInterval (-M : ℤ) k) (hM : M ≠ 0): (2*x-1) ∈ dyadicInterval (-M :ℤ) (2*k - 2^M) ∨ (2*x-1) ∈ dyadicInterval (-M :ℤ) (2*k -2 ^M + 1) := by
  have : 2*(k:ℤ) - 2^M = 2*(k - 2^(M-1)) := by
    rw [Int.mul_sub]
    rw [mul_pow_sub_one hM 2]
  simp_rw[this]
  rw [← @mem_union, ← dyadicInterval_split']
  simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq] at hx
  simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
  obtain ⟨ hx1, hx2 ⟩ := hx
  have : (2 ^ ((-M :ℤ) + 1) :ℝ ) * 2 ^ (M  - 1) = 1 := by
    have : (-M :ℤ) + 1 = - (M -1) := by
      simp only [neg_sub]
      rw [@neg_add_eq_sub]
    rw[this]
    rw [@zpow_neg]
    refine (inv_mul_eq_one₀ ?_).mpr ?_
    · apply zpow_ne_zero
      simp
    · rw[← zpow_natCast ]
      refine (zpow_right_inj₀ ?_ ?_).mpr ?_
      · simp
      · simp
      · have : M ≥ 1 := by
          exact Nat.one_le_iff_ne_zero.mpr hM
        exact Eq.symm (Int.natCast_pred_of_pos this)
  constructor
  · push_cast
    rw[mul_sub, tsub_le_iff_right]
    rw[this]
    simp only [sub_add_cancel, ge_iff_le]
    rw [zpow_add₀ (two_ne_zero) , zpow_one, mul_assoc, mul_comm, mul_assoc,  mul_le_mul_left (two_pos), mul_comm ]
    simp only [zpow_neg, zpow_natCast]
    exact hx1
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    rw[mul_add, mul_sub, this]
    simp only [mul_one]
    rw [@sub_lt_iff_lt_add]
    rw[zpow_add₀ (two_ne_zero) , zpow_one]
    ring_nf
    rw[← add_mul,  mul_lt_mul_right (two_pos), ← mul_one ( a := 2^(-M :ℤ )), mul_assoc, one_mul, ← mul_add, add_comm ]
    simp only [zpow_neg, zpow_natCast]
    exact hx2

theorem xinsecondhalf' {M k : ℕ} {x : ℝ} (hx : x ∈ dyadicInterval (-M : ℤ) k) (hM : M ≠ 0): (2*x-1) ∈ dyadicInterval (-M + 1 :ℤ) ((k - 2^(M-1)):ℤ) := by
  simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq] at hx
  simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
  obtain ⟨ hx1, hx2 ⟩ := hx
  have : (2 ^ ((-M :ℤ) + 1) :ℝ ) * 2 ^ (M  - 1) = 1 := by
    have : (-M :ℤ) + 1 = - (M -1) := by
      simp only [neg_sub]
      rw [@neg_add_eq_sub]
    rw[this]
    rw [@zpow_neg]
    refine (inv_mul_eq_one₀ ?_).mpr ?_
    · apply zpow_ne_zero
      simp
    · rw[← zpow_natCast ]
      refine (zpow_right_inj₀ ?_ ?_).mpr ?_
      · simp
      · simp
      · have : M ≥ 1 := by
          exact Nat.one_le_iff_ne_zero.mpr hM
        exact Eq.symm (Int.natCast_pred_of_pos this)
  constructor
  · push_cast
    rw[mul_sub, tsub_le_iff_right]
    rw[this]
    simp only [sub_add_cancel, ge_iff_le]
    rw [zpow_add₀ (two_ne_zero) , zpow_one, mul_assoc, mul_comm, mul_assoc,  mul_le_mul_left (two_pos), mul_comm ]
    simp only [zpow_neg, zpow_natCast]
    exact hx1
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    rw[mul_add, mul_sub, this]
    simp only [mul_one]
    rw [@sub_lt_iff_lt_add]
    rw[zpow_add₀ (two_ne_zero) , zpow_one]
    ring_nf
    rw[← add_mul,  mul_lt_mul_right (two_pos), ← mul_one ( a := 2^(-M :ℤ )), mul_assoc, one_mul, ← mul_add, add_comm ]
    simp only [zpow_neg, zpow_natCast]
    exact hx2


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


theorem dyadicInterval_cover01 (k : ℤ) :
  Ico 0 1 ⊆ ⋃ n : ℕ , dyadicInterval k n := by
  sorry


theorem extdi {M : ℤ} {x : ℝ} : ∃ k : ℤ, x ∈ dyadicInterval M k := by
  refine mem_iUnion.mp ?_
  rw[dyadicInterval_cover]
  simp

theorem extdiin01 {M : ℤ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1): ∃ k : ℕ , x ∈ dyadicInterval M k := by

  have hx : x ∈ Ico 0 1 := by sorry
  sorry

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



theorem dyadic_intervals_relation2 {k k' n n' : ℤ} (h1 : k ≤ k') :
  dyadicInterval k n ∩ dyadicInterval k' n' = ∅ ∨
  dyadicInterval k n ⊆ dyadicInterval k' n':= by
  by_cases hk : k = k'
  · by_cases hn : n= n'
    · rw[hn, hk]
      simp
    · left
      rw[hk]
      exact dyadicInterval_disjoint hn
  have h11: k < k' := by
    push_neg at hk
    rw [@Int.lt_iff_le_and_ne]
    constructor
    · exact h1
    · exact hk
  have h : dyadicInterval k n ∩ dyadicInterval k' n' = ∅ ∨
  dyadicInterval k n ⊆ dyadicInterval k' n' ∨
  dyadicInterval k' n' ⊆ dyadicInterval k n := by
    apply dyadic_intervals_relation h11
  rw[← or_assoc] at h
  rcases h with h|h
  · exact h
  · exfalso
    apply MeasureTheory.measure_mono (μ := MeasureTheory.volume ) at h
    simp_rw[dyadicInterval_measure] at h
    rw[← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast] at  h
    have : (k :ℝ ) < (k' : ℝ ) := by
      norm_cast
    apply ENNReal.rpow_lt_rpow_of_exponent_lt  (x := 2) at this
    · order
    · norm_num
    · simp



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
