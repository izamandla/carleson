import Mathlib
open Function Set Classical
noncomputable section

/- ## Binary representation set -/
namespace BinaryRepresentationSet

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (Nat.size n + 1))

/--
Condition for being in the binary representation set.
-/
theorem mem_binaryRepresentationSet_iff (n m : ℕ) :
  m ∈ binaryRepresentationSet n ↔ (Nat.testBit n m = true) := by
  simp only [binaryRepresentationSet, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  apply m.testBit_implies_ge at h
  rw [ge_iff_le, ← m.lt_size] at h
  linarith


/--
Binary representation set of `0` is empty.
-/
theorem binaryRepresentationSet_zero : binaryRepresentationSet 0 = ∅ := by
  simp [binaryRepresentationSet, Nat.testBit_zero]



/--
Binary representation set of `n>0` is nonempty.
-/

theorem binaryRepresentationSet_not_zero (n : ℕ ) (h : n >0 )  : binaryRepresentationSet n ≠  ∅ := by
  rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt] at h
  apply Nat.ne_zero_implies_bit_true at h
  obtain ⟨ i, h_i ⟩ := h
  rw[←  mem_binaryRepresentationSet_iff ] at h_i
  simp only [ne_eq]
  intro h
  rw [h] at h_i
  exact Finset.not_mem_empty i h_i

theorem binaryforpower (n M: ℕ ) ( h : n = 2^M ): binaryRepresentationSet n = { M } := by
  rw[h,binaryRepresentationSet]
  ext x
  constructor
  · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    intro h0
    obtain ⟨ h1, h2 ⟩ := h0
    by_contra hx
    rw[eq_comm] at hx
    push_neg at hx
    apply Nat.testBit_two_pow_of_ne at hx
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h2 hx
  · simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_range]
    intro h0
    rw[h0]
    constructor
    · rw[Nat.size_pow]
      linarith
    · apply Nat.testBit_two_pow_self

theorem remove_bithelp (N M a : ℕ ) (ha1 : a ∈ binaryRepresentationSet N)
(ha2 : a ≠  M) (h : M ∈ binaryRepresentationSet N) : a ∈ binaryRepresentationSet (N - 2 ^ M) := by
  refine (mem_binaryRepresentationSet_iff (N - 2 ^ M) a).mpr ?_
  simp only [mem_binaryRepresentationSet_iff] at h
  have h0 : 2^M ≤ N := by
    apply Nat.testBit_implies_ge h
  set N' := N - 2^M with hs
  have hs1: N' + 2^M = N := by
    rw[hs, Nat.sub_add_cancel]
    exact h0
  simp only [mem_binaryRepresentationSet_iff] at ha1
  rw[← hs1, add_comm] at ha1
  rw[← hs1, add_comm] at h
  rw[Nat.testBit_two_pow_add_eq] at h
  simp at h

  sorry

theorem remove_bit2 (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  refine Finset.ext_iff.mpr ?_
  intro a
  constructor
  · intro ha
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
    obtain ⟨ ha1, ha2 ⟩ := ha
    sorry
  · intro ha
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · sorry
    ·
      sorry

/--
Removing an element from the binary representation set.
-/

theorem remove_bit (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  rw [mem_binaryRepresentationSet_iff] at h
  have h0 : 2^M ≤ N := by
    apply Nat.testBit_implies_ge h
  set N' := N - 2^M with hs
  have hs1: N' + 2^M = N := by
    rw[hs, Nat.sub_add_cancel]
    exact h0
  have h1 : (N - 2^M).testBit M = false := by
    rw[← hs1, add_comm, Nat.testBit_two_pow_add_eq ]at h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact h
  rw[hs]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_binaryRepresentationSet_iff]
  constructor
  · intro hx
    obtain ⟨hx1,hx2⟩ := hx
    push_neg at hx2
    apply Nat.testBit_implies_ge at hx1
    sorry
  · intro hx
    constructor
    · sorry
    · sorry

  --Nat.testBit_two_pow_add_eq
  --Nat.testBit_two_pow_add_gt
 /- rw [mem_binaryRepresentationSet_iff ] at h
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro h1
    rcases h1 with ⟨hr, hl⟩
    · push_neg at hl
      rw [mem_binaryRepresentationSet_iff N x] at hr
      apply (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
      apply Nat.testBit_implies_ge at hr
      sorry
  · sorry-/




/--
Natural number can be written using the sum of two to the power of element of binary representation set.
-/

theorem binaryRepresentationSet_explicit (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^k = n := by
  induction' n using Nat.strong_induction_on with n ih
  sorry



theorem binaryRepresentationSet_explicit2 (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1) = 2*n := by
  conv_rhs => rw[← binaryRepresentationSet_explicit n, Finset.mul_sum]
  apply Finset.sum_congr
  · simp
  · intro k hk
    rw[pow_succ, mul_comm]

theorem binaryRepresentationSet_equiv2help (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1) =  ∑ k in binaryRepresentationSet (2*n), 2^k:= by
  rw[binaryRepresentationSet_explicit2, binaryRepresentationSet_explicit]


theorem binaryRepresentationSet_equiv2 (n k :ℕ ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n) := by
  sorry

/--
Binary representation set has maximal element.
-/

theorem max_binaryRepresentationSet (n : ℕ ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j > k, j ∉ binaryRepresentationSet n := by
  have h0 : (binaryRepresentationSet n).Nonempty := by
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  have h1 :  ∃ (a : ℕ), Finset.max (binaryRepresentationSet n )= a := by
    apply Finset.max_of_nonempty h0
  obtain ⟨ a , ha ⟩ := h1
  have h : a ∈ binaryRepresentationSet n := by
    exact Finset.mem_of_max ha
  use a, h
  simp only [gt_iff_lt]
  intro j hj
  exact Finset.not_mem_of_max_lt hj ha



/--
Binary representation set has minimal element.
-/
theorem min_binaryRepresentationSet (n : ℕ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j < k, j ∉ binaryRepresentationSet n := by
  have h0 : (binaryRepresentationSet n).Nonempty := by
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  have h1 :  ∃ (a : ℕ), Finset.min (binaryRepresentationSet n )= a := by
    apply Finset.min_of_nonempty h0
  obtain ⟨ a , ha ⟩ := h1
  have h : a ∈ binaryRepresentationSet n := by
    exact Finset.mem_of_min ha
  use a, h
  intro j hj
  exact Finset.not_mem_of_lt_min hj ha


  end BinaryRepresentationSet
