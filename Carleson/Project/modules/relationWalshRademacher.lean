import Carleson.Project.modules.BinaryRepresentationSet
import Carleson.Project.modules.Haar
import Carleson.Project.modules.Walsh
import Mathlib.Data.Nat.Bitwise

open InnerProductSpace MeasureTheory Set BigOperators
open Walsh Haar BinaryRepresentationSet

noncomputable section

namespace WalshRademacher



/--
Relation between Haar function and Walsh functions.
-/
theorem walsh_haar_one (x : ℝ) : walsh 1 x  = haarFunction x := by
  simp only [haarFunction, one_div]
  split_ifs with h1 h2
  · obtain ⟨ hl, hr⟩ := h1
    apply walsh_one_left
    · exact hl
    · norm_num at hr
      exact hr
  · obtain ⟨ hl, hr⟩ := h2
    apply walsh_one_right
    · norm_num at hl
      exact hl
    · exact hr
  · apply walsh_not_in
    simp_all only [not_and_or]
    push_neg at h1
    push_neg at h2
    obtain hl1|hr1 := h1
    · left
      linarith
    · obtain hl2|hr2 := h2
      · exfalso
        linarith
      · right
        linarith


/--
Walsh functions expressed using products of Rademacher functions.
-/
theorem walshRademacherRelation {n : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) : walsh n x = ∏
  m ∈ binaryRepresentationSet n, rademacherFunction m x := by
  induction' n using Nat.strong_induction_on with n ih generalizing x
  by_cases hzero :n = 0
  · rw[hzero, binaryRepresentationSet_zero, walsh_zero]
    · simp only [Finset.prod_empty]
    · exact hx1
    · exact hx2
  · set k := n/2 with h_k
    have hk0 : k < n := by
      rw[h_k]
      refine Nat.bitwise_rec_lemma hzero
    by_cases h0 : Odd n
    · have hk1 : 2*k+1 = n := by
        rw[h_k]
        rw[mul_comm]
        apply Nat.div_two_mul_two_add_one_of_odd
        exact h0
      rw[← hk1]
      by_cases h : x<1/2
      · rw[walsh_odd_left h]
        set y:= 2* x with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2, ← binaryRepresentationSet_equiv2plus1resultprod, rademacherFunctionzeroleft , one_mul]
        · apply Finset.prod_congr
          · simp
          · intro m hm
            rw[rademachernextfirsthalf]
            simp only [mem_Ico, hx1, true_and]
            ring_nf
            exact h
        · exact hx1
        · ring_nf
          exact h
      · push_neg at h
        rw[walsh_odd_right h ]
        set y:= 2* x -1 with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2, ← binaryRepresentationSet_equiv2plus1resultprod, rademacherFunctionzeroright, neg_mul, one_mul, neg_inj]
        · apply Finset.prod_congr
          · simp
          · intro m hm
            rw[rademachernextsecondhalf]
            simp only [mem_Ico]
            ring_nf
            constructor
            · exact h
            · exact hx2
        · ring_nf
          exact h
        · exact hx2
    · rw[Nat.not_odd_iff_even ] at h0
      have hk1 : 2*k = n := by
        rw[h_k, mul_comm]
        apply Nat.div_two_mul_two_of_even h0
      rw[← hk1]
      by_cases h : x<1/2
      · rw[walsh_even_left  h]
        set y:= 2* x with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2, ← binaryRepresentationSet_equiv2resultprod]
        apply Finset.prod_congr
        · simp
        · intro m hm
          rw[rademachernextfirsthalf]
          simp only [mem_Ico, hx1, true_and]
          ring_nf
          exact h
      · push_neg at h
        rw[walsh_even_right h ]
        set y:= 2* x -1 with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2, ← binaryRepresentationSet_equiv2resultprod]
        apply Finset.prod_congr
        · simp
        · intro m hm
          rw[rademachernextsecondhalf]
          simp only [mem_Ico]
          ring_nf
          constructor
          · exact h
          · exact hx2


theorem walshradrelbigger0 {n : ℕ} {x : ℝ} (hn : n > 0) :
  walsh n x = ∏ m ∈ binaryRepresentationSet n,
    rademacherFunction m x := by
  by_cases h : x≥ 0 ∧ x< 1
  · apply walshRademacherRelation h.1 h.2
  · simp only [not_and_or] at h
    push_neg at h
    rw[walsh_not_in x h]
    have h1 (m : ℕ ) : rademacherFunction m x = 0 := by
      rw[rademacherFunction_outside ]
      exact h
    rw[eq_comm, Finset.prod_eq_zero_iff]
    simp only [h1, and_true]
    refine Finset.Nonempty.exists_mem ?_
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    apply binaryRepresentationSet_not_zero
    exact hn


/--
Special case of Walsh-Rademacher relation for powers of two.
-/
theorem differentwalshRademacherRelation {n : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) : walsh (2^n) x = rademacherFunction n x := by
  rw[walshRademacherRelation, binaryforpower, Finset.prod_singleton]
  · exact hx1
  · exact hx2


/--
Walsh-Rademacher relation.
-/
theorem walshRademacherRelationresult {M N : ℕ} {x : ℝ} (h : M ∈ binaryRepresentationSet N) (hx1 : 0 ≤ x) (hx2 : x < 1) : walsh N x = walsh (2^M) x * ∏
  m ∈ binaryRepresentationSet (N - (2 ^ M)), rademacherFunction m x := by
  rw[walshRademacherRelation hx1 hx2, differentwalshRademacherRelation hx1 hx2, ← remove_bit N M h]
  exact Finset.prod_eq_mul_prod_diff_singleton h fun x_1 ↦ rademacherFunction x_1 x




/--
Product of two walsh functions
-/
theorem prodofwalshworse {M N k : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hk : k = M ^^^ N) : walsh k x = walsh M x * walsh N x:= by
  rw[differenceofbinaryrepset] at hk
  rw[walshRademacherRelation hx1 hx2,walshRademacherRelation hx1 hx2, walshRademacherRelation hx1 hx2, binaryRepresentationSet_fun_prod2 , ← Finset.prod_union (disjoint_sdiff_sdiff)]
  · rw[hk]
  · intro k
    apply rad_sqr hx1 hx2




theorem walsh_int {n : ℕ} (h : n > 0) : ∫ (x : ℝ) in Ico 0 1, walsh n x = 0 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h1: Odd n
  · rw[intofodd h1]
  · simp only [Nat.not_odd_iff_even] at h1
    set l :=n/2 with hl
    have hl' : 2* l = n := by
      exact Nat.two_mul_div_two_of_even h1
    have hl1 : l< n := by
      refine Nat.bitwise_rec_lemma (Nat.ne_zero_of_lt h)
    have hl2: 0< l := by
      refine Nat.zero_lt_of_ne_zero ?_
      by_contra hl3
      rw[hl3] at hl'
      linarith
    rw[intofeven hl']
    exact ih l hl1 hl2




theorem walsh_ort_dif {n m : ℕ} (h : m ≠ n) : walshInnerProduct (walsh n) m  = 0 := by
  set k := m^^^n with hk
  simp_rw[walshInnerProduct, ← Pi.mul_apply]
  have h1 : EqOn (walsh n * walsh m) (walsh k) (Set.Ico 0 1):= by
    unfold EqOn
    intro z hz
    simp only [mem_Ico] at hz
    rw[prodofwalshworse (M:=n) (N:= m) (x:= z) hz.1 hz.2 (Nat.xor_comm m n)]
    simp only [Pi.mul_apply]
  rw[MeasureTheory.setIntegral_congr_fun (measurableSet_Ico) h1, walsh_int]
  refine Nat.zero_lt_of_ne_zero (Nat.xor_ne_zero.mpr h)


theorem walsh_ort {n m : ℕ} (h : m ≠ n) : ∫ (x : ℝ) in Ico 0 1, walsh n x * walsh m x = 0 := by
  set k := m^^^n with hk
  simp_rw[← Pi.mul_apply]
  have h1 : EqOn (walsh n * walsh m) (walsh k) (Set.Ico 0 1):= by
    unfold EqOn
    intro z hz
    simp only [mem_Ico] at hz
    rw[prodofwalshworse (M:=n) (N:= m) (x:= z) hz.1 hz.2 (Nat.xor_comm m n)]
    simp only [Pi.mul_apply]
  rw[MeasureTheory.setIntegral_congr_fun (measurableSet_Ico) h1, walsh_int]
  refine Nat.zero_lt_of_ne_zero (Nat.xor_ne_zero.mpr h)



theorem fun_change_partial_sum (M N : ℕ) (f : ℝ → ℝ) (x : ℝ) : rademacherFunction M x *(walshFourierPartialSum (rademacherFunction M * f)  N ) x = ∑
  n ∈ Finset.range (N + 1),
  (∫ y in Set.Ico 0 1, (rademacherFunction M y) * f y * walsh n y) *
      rademacherFunction M x *
    walsh n x  := by
  unfold walshFourierPartialSum
  unfold walshInnerProduct
  rw[mul_comm, Finset.sum_mul, Finset.sum_congr]
  · simp
  · intro z hz
    simp only [Pi.mul_apply]
    linarith

end WalshRademacher
