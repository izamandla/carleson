import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Data.Nat.Size
open Function Set --Classical
noncomputable section

/- ## Binary representation set -/
namespace BinaryRepresentationSet

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (fun m => Nat.testBit n m) (Finset.range (Nat.size n + 1))

/--
Condition for being in the binary representation set.
-/
theorem mem_binaryRepresentationSet_iff (n m : ℕ) :
  m ∈ binaryRepresentationSet n ↔ (Nat.testBit n m = true) := by
  rw[binaryRepresentationSet, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  apply m.ge_two_pow_of_testBit at h
  rw [ge_iff_le, ← m.lt_size] at h
  linarith


/--
Binary representation set of `0` is empty.
-/
theorem binaryRepresentationSet_zero : binaryRepresentationSet 0 = ∅ := by
  simp[binaryRepresentationSet, Nat.testBit_zero]


/--
Binary representation set of `n>0` is nonempty.
-/

theorem binaryRepresentationSet_not_zero (n : ℕ) (h : n > 0) : binaryRepresentationSet n ≠  ∅ := by
  rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt] at h
  apply Nat.exists_testBit_of_ne_zero at h
  obtain ⟨ i, h_i ⟩ := h
  rw[←  mem_binaryRepresentationSet_iff ] at h_i
  simp only [ne_eq]
  intro h
  rw [h] at h_i
  exact Finset.notMem_empty i h_i


/--
Binary representation set of `2^M` equals `M`.
-/

theorem binaryforpower (M : ℕ): binaryRepresentationSet (2^M) = { M } := by
  rw[binaryRepresentationSet]
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hx
    rw[eq_comm] at hx
    apply Nat.testBit_two_pow_of_ne at hx
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h.2 hx
  · intro h
    simp_rw[h, Nat.size_pow, Nat.testBit_two_pow_self, and_true]
    linarith


/--
Binary representation set of odd number equals binary representation set of number one less of it with extra `0`.
-/

theorem bin2insert2plus1 (n : ℕ) : binaryRepresentationSet (2*n +1) = insert 0 (binaryRepresentationSet (2*n))  := by
  ext x
  simp only [mem_binaryRepresentationSet_iff, Finset.mem_insert]
  rcases x
  · simp only [Nat.testBit_zero, decide_eq_true_eq, Nat.mul_mod_right, zero_ne_one, decide_false,
      Bool.false_eq_true, or_false, iff_true]
    exact Nat.odd_iff.mp (odd_two_mul_add_one n)
  · simp only [Nat.testBit_add_one, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, false_or, Bool.coe_iff_coe]
    congr
    omega

/--
Binary representation set of `n` contains `k` iff bninary representation set of `2n` contains `k+1`.
-/

theorem binaryRepresentationSet_equiv2 (n k : ℕ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n) := by
  simp only [mem_binaryRepresentationSet_iff, Bool.coe_iff_coe]
  rw[← Nat.pow_one 2 , Nat.testBit_two_pow_mul]
  simp

/--
Binary representation set of even number doesn't contain `0`.
-/

theorem lackofzeroin2 (n : ℕ) : 0 ∉ binaryRepresentationSet (2*n) := by
  simp[mem_binaryRepresentationSet_iff]


/--
Relation between explicit forms of binary representation sets of `n` and `2n`.
-/

theorem binaryRepresentationSet_equiv2result (n : ℕ) : ∑ k ∈ binaryRepresentationSet n,
  2 ^ (k + 1) =  ∑ k ∈ binaryRepresentationSet (2 * n), 2 ^ k:= by
  let i : ℕ → ℕ  := fun i ↦ i + 1
  apply Finset.sum_nbij i
  · intro a ha
    rw[← binaryRepresentationSet_equiv2]
    exact ha
  · unfold InjOn
    simp only [Finset.mem_coe]
    intro z hz y hy h
    simp only [add_left_inj, i] at h
    exact h
  · unfold SurjOn
    intro y hy
    simp only [mem_image, Finset.mem_coe, i]
    have hy0 : y ≥ 1 := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      by_contra hy'
      rw[hy'] at hy
      apply lackofzeroin2 at hy
      exact hy
    use (y -1)
    constructor
    · rw[binaryRepresentationSet_equiv2, Nat.sub_one_add_one_eq_of_pos hy0]
      exact hy
    · rw [Nat.sub_one_add_one_eq_of_pos hy0]
  · simp[i]


/--
relation between product over binary rpresentation set of some funtions
-/

theorem binaryRepresentationSet_equiv2resultprod {n : ℕ} {α : Type*} [CommMonoid α] (f : ℕ → α) : ∏
  k ∈ binaryRepresentationSet n, f (k + 1) =  ∏ k ∈ binaryRepresentationSet (2 * n), f k:= by
  let i : ℕ → ℕ  := fun i ↦ i + 1
  apply Finset.prod_nbij i
  · intro a ha
    rw[← binaryRepresentationSet_equiv2]
    exact ha
  · unfold InjOn
    simp only [Finset.mem_coe]
    intro z hz y hy h
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
    use (y -1)
    constructor
    · rw[binaryRepresentationSet_equiv2, Nat.sub_one_add_one_eq_of_pos hy0]
      exact hy
    · rw [Nat.sub_one_add_one_eq_of_pos hy0]
  · simp[i]


/--
Partition of product taken over binary representation set
-/

theorem binaryRepresentationSet_fun_prod {n m : ℕ} {α : Type*} [CommMonoid α] (f : ℕ → α) : (∏
  k ∈ binaryRepresentationSet n, f k) * (∏ k ∈ binaryRepresentationSet m, f k)  =  (∏
    k ∈ (binaryRepresentationSet n) \ (binaryRepresentationSet m), f k) * (∏
      k ∈ (binaryRepresentationSet m) \ (binaryRepresentationSet n), f k) * (∏
        k ∈ (binaryRepresentationSet m) ∩ (binaryRepresentationSet n), f k)^2:= by
  conv_rhs => rw[pow_two,mul_assoc, mul_comm, ← mul_assoc]
  have h {i j :ℕ } : ((∏ k ∈ binaryRepresentationSet i\ binaryRepresentationSet j, f k) *
        ∏ k ∈ binaryRepresentationSet i ∩ binaryRepresentationSet j, f k) = (∏ k ∈ binaryRepresentationSet i, f k) := by
        rw[← Finset.prod_disjUnion (Finset.disjoint_sdiff_inter (binaryRepresentationSet i) (binaryRepresentationSet j)), Finset.disjUnion_eq_union, @Finset.sdiff_union_inter]
  simp_rw[h]
  simp_rw[mul_comm] at h
  conv_rhs => rw[mul_assoc, mul_comm]
  rw [@Finset.inter_comm]
  rw[h]


/--
Partition of product taken over binary representation set when square of function equals 1.
-/
theorem binaryRepresentationSet_fun_prod2 {n m : ℕ} {α : Type*} [CommMonoid α] (f : ℕ → α) (hf : ∀ k, (f k) ^ 2 = 1) : (∏
  k ∈ binaryRepresentationSet n, f k) * (∏ k ∈ binaryRepresentationSet m, f k)  =  (∏
    k ∈ (binaryRepresentationSet n) \ (binaryRepresentationSet m), f k) * (∏
      k ∈ (binaryRepresentationSet m) \ (binaryRepresentationSet n), f k):= by
  simp_rw[binaryRepresentationSet_fun_prod]
  conv_rhs =>rw[← mul_one ((∏ k ∈ binaryRepresentationSet n \ binaryRepresentationSet m, f k) *
    ∏ k ∈ binaryRepresentationSet m \ binaryRepresentationSet n, f k)]
  congr
  simp_rw[← Finset.prod_pow, hf, Finset.prod_const_one]



/--
Relation between elements of binary representation sets of odd and even numbers
-/

theorem binaryRepresentationSet_equiv2plus1 (n k : ℕ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n +1) := by
  simp only [mem_binaryRepresentationSet_iff, Bool.coe_iff_coe, Nat.testBit_succ]
  have h : (2 * n + 1) / 2 = n := by
    set l:= 2 * n + 1 with hl
    rw[← Nat.mul_left_inj two_ne_zero, ← Nat.add_right_inj (n := 1), add_comm]
    have : Odd l := by
      exact odd_two_mul_add_one n
    rw[Nat.div_two_mul_two_add_one_of_odd this, hl]
    linarith
  rw[h]


/--
`0` is a member of binary representation set of odd number.
-/
theorem exofzeroin2plus1 (n : ℕ) : 0 ∈  binaryRepresentationSet (2*n +1) := by
  simp only [mem_binaryRepresentationSet_iff, Nat.testBit_zero, decide_eq_true_eq]
  refine Nat.succ_mod_two_eq_one_iff.mpr ?_
  simp


/--
Stronger relation between odd and even numbers' binary representation sets. Includes `0`.
-/

theorem binaryRepresentationSet_equiv2plus1other (n k : ℕ) : k ∈ binaryRepresentationSet n ↔ (k+1) ∈ binaryRepresentationSet (2*n +1)\ {0} := by
  simp only [Finset.mem_sdiff, Finset.mem_singleton, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
    and_false, not_false_eq_true, and_true]
  apply binaryRepresentationSet_equiv2plus1



theorem binaryRepresentationSet_equiv2plus1resulthelp2 (n : ℕ) : ∑
  k ∈ binaryRepresentationSet (2 * n + 1), 2 ^ k = ∑
    k ∈ binaryRepresentationSet (2 * n + 1) \ {0}, 2 ^ k +1 := by
  have h : binaryRepresentationSet (2*n +1) = (binaryRepresentationSet (2*n +1) \ {0}) ∪ {0} := by
    simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Finset.singleton_subset_iff, exofzeroin2plus1 ]
  conv_lhs => rw[h]
  apply Finset.sum_union
  simp

/--
Relation between explicit forms of binary representation set of `n` and `2n+1`.
-/

theorem binaryRepresentationSet_equiv2plus1result (n : ℕ) : ∑ k ∈ binaryRepresentationSet n,
  2 ^ (k + 1)  + 1=  ∑ k ∈ binaryRepresentationSet (2 * n + 1), 2 ^ k:= by
  rw[binaryRepresentationSet_equiv2plus1resulthelp2, add_left_inj]
  let i : ℕ → ℕ  := fun i ↦ i + 1
  apply Finset.sum_nbij i
  · intro a ha
    rw[← binaryRepresentationSet_equiv2plus1other]
    exact ha
  · unfold InjOn
    intro z hz y hy h
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
    use (y -1 )
    constructor
    · rw[binaryRepresentationSet_equiv2plus1other, Nat.sub_one_add_one_eq_of_pos hy0]
      exact hy
    · rw [Nat.sub_one_add_one_eq_of_pos hy0]
  · simp[i]

/--
relation of prodacts between `n` and `2n+1`.
-/
theorem binaryRepresentationSet_equiv2plus1resultprod {n : ℕ} {α : Type*} [CommMonoid α] (f : ℕ → α): (f 0) * ∏
  k ∈ binaryRepresentationSet n, f (k + 1) =  ∏ k ∈ binaryRepresentationSet (2 * n + 1), f k:= by
  rw[bin2insert2plus1, Finset.prod_insert (lackofzeroin2 n), binaryRepresentationSet_equiv2resultprod]

/--
Natural number can be written using the sum of two to the power of element of binary representation set.
-/
theorem binaryRepresentationSet_explicit (n : ℕ) : ∑ k ∈ binaryRepresentationSet n, 2 ^ k = n := by
  induction' n using Nat.evenOddRec with n ih n ih
  · simp_rw[Finset.sum_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
      imp_false, binaryRepresentationSet_zero, Finset.notMem_empty, not_false_eq_true, implies_true]
  · conv_rhs => rw[← ih]
    rw[Finset.mul_sum, ← binaryRepresentationSet_equiv2result, Finset.sum_congr]
    · simp
    · simp_rw[pow_succ, mul_comm, implies_true]
  · conv_rhs => rw[← ih]
    rw[Finset.mul_sum, ← binaryRepresentationSet_equiv2plus1result, add_left_inj,Finset.sum_congr]
    · simp
    · simp_rw[pow_succ, mul_comm, implies_true]




/--
Relation between sum and bitwise or.
-/

theorem sumofbinaryrepsethelp {N M : ℕ} (h : Disjoint (binaryRepresentationSet M) (binaryRepresentationSet N)) : M + N = M ||| N := by
  conv_lhs => rw[← binaryRepresentationSet_explicit M, ← binaryRepresentationSet_explicit N]
  rw[← binaryRepresentationSet_explicit (M|||N), ← Finset.sum_union h]
  congr
  ext x
  simp[mem_binaryRepresentationSet_iff]


/--
Union of two disjoint binary representation sets.
-/

theorem sumofbinaryrepset {N M : ℕ} (h : Disjoint (binaryRepresentationSet M) (binaryRepresentationSet N)) : (binaryRepresentationSet M) ∪ (binaryRepresentationSet N) = binaryRepresentationSet (M + N) := by
  ext x
  conv_lhs => rw [@Finset.mem_union]
  simp_rw [mem_binaryRepresentationSet_iff, sumofbinaryrepsethelp h, Nat.testBit_or, Bool.or_eq_true]



/--
relation between xor and binary representation sets
-/

theorem differenceofbinaryrepset {N M k : ℕ} : k = M ^^^ N ↔ binaryRepresentationSet k = ((binaryRepresentationSet M)\(binaryRepresentationSet N)) ∪ ((binaryRepresentationSet N)\ (binaryRepresentationSet M)) := by
  constructor
  · intro h
    rw[h, @Finset.ext_iff]
    intro a
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_binaryRepresentationSet_iff, Nat.testBit_xor, bne_iff_ne, ne_eq, Bool.not_eq_true]
    by_cases h0: M.testBit a = true
    · rw[h0]
      simp
    · simp_rw[h0]
      simp
  · intro h
    rw[← binaryRepresentationSet_explicit k, ← binaryRepresentationSet_explicit (M^^^N), h ]
    congr
    rw [@Finset.ext_iff]
    intro a
    simp only [Finset.mem_union, Finset.mem_sdiff, mem_binaryRepresentationSet_iff, Bool.not_eq_true, Nat.testBit_xor, bne_iff_ne, ne_eq]
    by_cases h0: M.testBit a = true
    · rw[h0]
      simp
    · simp_rw[h0]
      simp

/-- If some `k < 2^M` then binary representation sets of `k` and `2^M` are disjoint. -/

theorem disjoftwopow {k M : ℕ} (h : k < 2 ^ M) : Disjoint (binaryRepresentationSet k) (binaryRepresentationSet (2 ^ M)) := by
  rw [binaryforpower, @Finset.disjoint_singleton_right]
  refine Finset.forall_mem_not_eq.mp ?_
  intro b hb
  refine Nat.ne_of_lt' ?_
  rw[← Nat.pow_lt_pow_iff_right (a:= 2) (Nat.one_lt_ofNat) ]
  have : 2^b ≤  k := by
    rw[← binaryRepresentationSet_explicit k]
    exact CanonicallyOrderedAddCommMonoid.single_le_sum hb
  exact Nat.lt_of_le_of_lt this h


/--
relation between xor of some `2^M` and sum.
-/

theorem about_altern_and_add' {k M : ℕ} (h : k < 2 ^ M) : k^^^(2^M) = k + 2^M := by
  rw[eq_comm, differenceofbinaryrepset]
  rw[← sumofbinaryrepset (disjoftwopow h), Finset.sdiff_eq_self_of_disjoint (disjoftwopow h), Finset.sdiff_eq_self_of_disjoint (id (Disjoint.symm (disjoftwopow h)))]


/--
Removing element of binary representation set.
-/
theorem remove_bit (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  rw [mem_binaryRepresentationSet_iff] at h
  set N' := N - 2^M with hs
  have hs': N' + 2^M = N := by
    rw[hs, Nat.sub_add_cancel]
    apply Nat.ge_two_pow_of_testBit h
  have h1 : Disjoint (binaryRepresentationSet N') {M} := by
    simp only [Finset.disjoint_singleton_right, mem_binaryRepresentationSet_iff, Bool.not_eq_true]
    rw[← hs', add_comm , Nat.testBit_two_pow_add_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact h
  rw[← hs', ← sumofbinaryrepset]
  · rw[binaryforpower]
    apply Finset.union_sdiff_cancel_right h1
  · rw[binaryforpower]
    exact h1


theorem binaryRepresentationSet_explicit2 (n : ℕ) : ∑ k ∈ binaryRepresentationSet n, 2 ^ (k + 1) = 2*n := by
  conv_rhs => rw[← binaryRepresentationSet_explicit n, Finset.mul_sum]
  apply Finset.sum_congr
  · simp
  · intro k hk
    rw[pow_succ, mul_comm]



/--
Binary representation set has maximal element.
-/

theorem max_binaryRepresentationSet (n : ℕ) (h : n > 0) : ∃ k ∈  binaryRepresentationSet n, ∀ j > k, j ∉ binaryRepresentationSet n := by
  have h1 :  ∃ (a : ℕ), Finset.max (binaryRepresentationSet n )= a := by
    apply Finset.max_of_nonempty
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨ a , ha ⟩ := h1
  use a, (Finset.mem_of_max ha)
  simp only [gt_iff_lt]
  intro j hj
  exact Finset.notMem_of_max_lt hj ha


/--
Binary representation set has minimal element.
-/
theorem min_binaryRepresentationSet (n : ℕ) (h : n > 0) : ∃ k ∈  binaryRepresentationSet n, ∀ j < k, j ∉ binaryRepresentationSet n := by
  have h1 :  ∃ (a : ℕ), Finset.min (binaryRepresentationSet n )= a := by
    apply Finset.min_of_nonempty
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨ a , ha ⟩ := h1
  use a, (Finset.mem_of_min ha)
  intro j hj
  exact Finset.notMem_of_lt_min hj ha

/-- Two to the power of element of binary representation set of `N` is smaller or equal to `N`. -/

theorem aboutM1 {N M : ℕ} (h1 : M ∈ binaryRepresentationSet N) : 2 ^ M ≤ N := by
  rw[← binaryRepresentationSet_explicit N]
  exact CanonicallyOrderedAddCommMonoid.single_le_sum h1

theorem aboutM2help {M : ℕ} : ∑ k ∈ Finset.range M, 2^k < 2^M :=by
  refine Nat.geomSum_lt ?_ ?_
  · simp
  · simp

/--
Two to the power of maximum element of binary representation set of `N` plus one is bigger than `N`.
-/

theorem aboutM2 {N M : ℕ} (h2 : ∀ j > M, j ∉ binaryRepresentationSet N) : N< 2^(M+1) := by
  rw[← binaryRepresentationSet_explicit N]
  have h0 : binaryRepresentationSet N ⊆ Finset.range (M+1) := by
    intro k hk
    simp only [Finset.mem_range]
    exact Nat.gt_of_not_le fun a ↦ h2 k a hk
  refine Nat.geomSum_lt ?_ ?_
  · simp
  · exact fun k a ↦ Nat.gt_of_not_le fun a_1 ↦ h2 k a_1 a

/--
If `M` fulfills `2^M ≤ N` and `N < 2^(M+1)` then it is a member of binary representation set of `N`.
-/


theorem aboutMfinal {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) : M ∈ binaryRepresentationSet N := by
  set k := N -2^M with hk
  have hk' : k +2^M = N := by
    exact Nat.sub_add_cancel h1
  rw[← hk', le_add_iff_nonneg_left] at h1
  rw[← hk', Nat.pow_add_one, mul_two, add_lt_add_iff_right] at h2
  rw[mem_binaryRepresentationSet_iff, ← hk', add_comm, Nat.testBit_two_pow_add_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  exact Nat.testBit_lt_two_pow h2




end BinaryRepresentationSet
