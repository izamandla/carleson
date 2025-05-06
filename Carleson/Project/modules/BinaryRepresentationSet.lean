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
/--
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
  rw [mem_binaryRepresentationSet_iff ] at h
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


theorem binaryRepresentationSet_equiv2 (n k :ℕ ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n) := by
  simp only [mem_binaryRepresentationSet_iff, Bool.coe_iff_coe]
  rw[← Nat.pow_one 2 , Nat.testBit_mul_pow_two]
  simp

theorem lackofzeroin2 (n : ℕ) : 0 ∉ binaryRepresentationSet (2*n) := by
  simp[mem_binaryRepresentationSet_iff]

theorem binaryRepresentationSet_equiv2result (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1) =  ∑ k in binaryRepresentationSet (2*n), 2^k:= by
  let i : ℕ → ℕ  := fun i ↦ i + 1
  apply Finset.sum_nbij i
  · intro a ha
    simp only [i]
    rw[← binaryRepresentationSet_equiv2]
    exact ha
  · unfold InjOn
    simp only [Finset.mem_coe]
    intro z hz
    intro y hy
    intro h
    simp only [add_left_inj, i] at h
    exact h
  · unfold SurjOn
    intro y hy
    simp only [mem_image, Finset.mem_coe, i]
    have hy0 : y ≥ 1 := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      by_contra a
      rw[a] at hy
      apply lackofzeroin2 at hy
      exact hy
    set s:= y -1 with hs
    use s
    constructor
    · rw[binaryRepresentationSet_equiv2, hs, Nat.sub_one_add_one_eq_of_pos hy0]
      exact hy
    · rw [Nat.sub_one_add_one_eq_of_pos hy0]
  · simp



theorem binaryRepresentationSet_equiv2plus1 (n k :ℕ ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n +1) := by
  simp only [mem_binaryRepresentationSet_iff, Bool.coe_iff_coe]
  rw[Nat.testBit_succ]
  have h : (2 * n + 1) / 2 = n := by
    set l:= 2 * n + 1 with hl
    rw[← Nat.mul_left_inj two_ne_zero, ← Nat.add_right_inj (n := 1), add_comm]
    have : Odd l := by
      exact odd_two_mul_add_one n
    rw[Nat.div_two_mul_two_add_one_of_odd this, hl]
    linarith
  rw[h]

theorem exofzeroin2plus1 (n : ℕ) : 0 ∈  binaryRepresentationSet (2*n +1) := by
  simp only [mem_binaryRepresentationSet_iff, Nat.testBit_zero, decide_eq_true_eq]
  refine Nat.succ_mod_two_eq_one_iff.mpr ?_
  simp

theorem binaryRepresentationSet_equiv2plus1resulthelp (n : ℕ ) : binaryRepresentationSet (2*n +1) = (binaryRepresentationSet (2*n +1) \ {0}) ∪ {0} := by
  simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Finset.singleton_subset_iff, exofzeroin2plus1 ]

theorem binaryRepresentationSet_equiv2plus1resulthelp2 (n : ℕ ) : ∑ k in binaryRepresentationSet (2*n +1), 2^k = ∑ k in binaryRepresentationSet (2*n +1) \ {0}, 2^k +1 := by
  conv_lhs => rw[binaryRepresentationSet_equiv2plus1resulthelp]
  apply Finset.sum_union
  simp

theorem binaryRepresentationSet_equiv2plus1other (n k :ℕ ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n +1)\ {0} := by
  simp only [Finset.mem_sdiff, Finset.mem_singleton, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
    and_false, not_false_eq_true, and_true]
  apply binaryRepresentationSet_equiv2plus1



theorem binaryRepresentationSet_equiv2plus1result (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1)  + 1=  ∑ k in binaryRepresentationSet (2*n +1), 2^k:= by
  rw[binaryRepresentationSet_equiv2plus1resulthelp2]
  simp only [add_left_inj]
  let i : ℕ → ℕ  := fun i ↦ i + 1
  apply Finset.sum_nbij i
  · intro a ha
    simp only [i]
    rw[← binaryRepresentationSet_equiv2plus1other]
    exact ha
  · unfold InjOn
    simp only [Finset.mem_coe]
    intro z hz
    intro y hy
    intro h
    simp only [add_left_inj, i] at h
    exact h
  · unfold SurjOn
    intro y hy
    simp only [mem_image, Finset.mem_coe, i]
    have hy0 : y ≥ 1 := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      by_contra a
      rw[a] at hy
      simp at hy
    set s:= y -1 with hs
    use s
    constructor
    · rw[binaryRepresentationSet_equiv2plus1other, hs, Nat.sub_one_add_one_eq_of_pos hy0]
      exact hy
    · rw [Nat.sub_one_add_one_eq_of_pos hy0]
  · simp


/--
Natural number can be written using the sum of two to the power of element of binary representation set.
-/

theorem binaryRepresentationSet_explicit (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^k = n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hzero :n = 0
  · rw[hzero]
    simp only [Finset.sum_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
      imp_false]
    rw[ binaryRepresentationSet_zero]
    simp
  · set l := n/2 with hl
    have hl1 : l< n := by
      push_neg at hzero
      rw[hl]
      apply Nat.div2Induction.proof_2
      apply Nat.pos_of_ne_zero hzero
    by_cases h : Odd n
    · have  hl0 : 2*l + 1=n  := by
        rw[hl]
        rw[mul_comm]
        apply Nat.div_two_mul_two_add_one_of_odd
        exact h
      rw[← hl0]
      conv_rhs => rw[← ih l hl1]
      rw[Finset.mul_sum]
      rw[← binaryRepresentationSet_equiv2plus1result]
      simp only [add_left_inj]
      rw[Finset.sum_congr]
      · simp
      · intro x hx
        rw[pow_succ, mul_comm]
    · rw[Nat.not_odd_iff_even] at h
      have hl0 : 2*l = n := by
        rw[hl]
        rw[mul_comm]
        apply Nat.div_two_mul_two_of_even
        exact h
      rw[← hl0]
      conv_rhs => rw[← ih l hl1]
      rw[Finset.mul_sum]
      rw[← binaryRepresentationSet_equiv2result]
      rw[Finset.sum_congr]
      · simp
      · intro x hx
        rw[pow_succ, mul_comm]


theorem removebit_help (N M : ℕ ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N = (binaryRepresentationSet N \ {M}) ∪ {M} := by
  simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Finset.singleton_subset_iff, exofzeroin2plus1 ]
  exact h

--jest szansa ze dowód tego trzeba za pomoca indukcji na maksymalnym/minimalnym elemencie
theorem remove_bit3 (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  conv_rhs => rw[← binaryRepresentationSet_explicit N, removebit_help N M h]
  rw[Finset.sum_union]
  · simp only [Finset.sum_singleton, add_tsub_cancel_right]
    sorry
  · simp



theorem binaryRepresentationSet_explicit2 (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1) = 2*n := by
  conv_rhs => rw[← binaryRepresentationSet_explicit n, Finset.mul_sum]
  apply Finset.sum_congr
  · simp
  · intro k hk
    rw[pow_succ, mul_comm]

theorem binaryRepresentationSet_equiv2help (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1) =  ∑ k in binaryRepresentationSet (2*n), 2^k:= by
  rw[binaryRepresentationSet_explicit2, binaryRepresentationSet_explicit]
--to mozna z tego kolejnego --moze tak by bylo lepiej??


theorem binaryRepresentationSet_equiv2plus1help (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^(k+1)  + 1=  ∑ k in binaryRepresentationSet (2*n +1), 2^k:= by
  rw[binaryRepresentationSet_explicit2, binaryRepresentationSet_explicit]




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
