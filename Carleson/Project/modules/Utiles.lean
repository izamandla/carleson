import Carleson.Project.modules.DyadicStructures
import Carleson.Project.modules.Haar
import Carleson.Project.modules.Walsh
import Carleson.Project.modules.BinaryRepresentationSet
open Function Set Classical
open unitInterval
noncomputable section


/- ## Kernel-/
namespace Kernel

/--
Kernel function defined using Haar functions and binary representation sets.
-/
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m in BinaryRepresentationSet.binaryRepresentationSet N, ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y)


/--
The kernel function at `N = 0` is constant 1.
-/
theorem kernel_zero (x y : ℝ) : kernel 0 x y = 1 := by
  simp only [kernel, add_right_eq_self]
  rw[BinaryRepresentationSet.binaryRepresentationSet_zero]
  exact rfl


/--
Kernel function for binary powers `N = 2^m`.
-/
theorem kernel_two_pow (N : ℕ) (x y : ℝ) : kernel (2^N) x y = 1 + ∑ n in Finset.range (2^N), (Haar.haarFunctionScaled N n x) * (Haar.haarFunctionScaled N n y) := by
  simp only [kernel, add_right_inj, BinaryRepresentationSet.binaryforpower,Finset.sum_singleton]



end Kernel

/- **ToDo** : Connect the facts about scaled Haar, Rademacher and Walsh functions with dyadic structures. -/

theorem wlashradhelp0 (n m : ℕ)(h: m ∈ BinaryRepresentationSet.binaryRepresentationSet n) : (m+1) ∈ BinaryRepresentationSet.binaryRepresentationSet (2*n) := by
  rw[BinaryRepresentationSet.mem_binaryRepresentationSet_iff] at h
  rw[BinaryRepresentationSet.mem_binaryRepresentationSet_iff]
  rw[← Nat.testBit_div_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  rw[h]

/--
Relation between Haar function and Walsh functions.
-/

theorem walsh_haar_one (x : ℝ ) : Walsh.walsh 1 x  = Haar.haarFunction x := by
  simp only [Haar.haarFunction, one_div]
  split_ifs with h1 h2
  · obtain ⟨ hl, hr⟩ := h1
    apply Walsh.walsh_one_left
    · exact hl
    · norm_num at hr
      exact hr
  · obtain ⟨ hl, hr⟩ := h2
    apply Walsh.walsh_one_right
    · norm_num at hl
      exact hl
    · exact hr
  · apply Walsh.walsh_not_in
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

theorem walshRademacherRelation {n : ℕ }{x : ℝ} (hx1 : 0 ≤ x) (hx2 :  x<1 ) :
  Walsh.walsh n x = ∏ m in BinaryRepresentationSet.binaryRepresentationSet n , Haar.rademacherFunction m x := by
  induction' n using Nat.strong_induction_on with n ih generalizing x
  by_cases hzero :n = 0
  · rw[hzero]
    rw[BinaryRepresentationSet.binaryRepresentationSet_zero, Walsh.walsh_zero]
    · simp only [Finset.prod_empty]
    · exact hx1
    · exact hx2
  · set k := n/2 with h_k
    have hk0 : k < n := by
      rw[h_k]
      refine Nat.bitwise_rec_lemma ?_
      push_neg at hzero
      exact hzero
    by_cases h0 : Odd n
    · have hk1 : 2*k+1 = n := by
        rw[h_k]
        rw[mul_comm]
        apply Nat.div_two_mul_two_add_one_of_odd
        exact h0
      rw[← hk1]
      by_cases h : x<1/2
      · rw[Walsh.walsh_odd_left h]
        set y:= 2* x with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2]
        rw[← BinaryRepresentationSet.binaryRepresentationSet_equiv2plus1resultprod, Haar.rademacherFunctionzeroleft , one_mul]
        · apply Finset.prod_congr
          · simp
          · intro m hm
            rw[Haar.rademachernextfirsthalf]
            simp only [mem_Ico, hx1, true_and]
            ring_nf
            exact h
        · exact hx1
        · ring_nf
          exact h
      · push_neg at h
        rw[Walsh.walsh_odd_right h ]
        set y:= 2* x -1 with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2]
        rw[← BinaryRepresentationSet.binaryRepresentationSet_equiv2plus1resultprod, Haar.rademacherFunctionzeroright, neg_mul, one_mul, neg_inj]
        · apply Finset.prod_congr
          · simp
          · intro m hm
            rw[Haar.rademachernextsecondhalf]
            simp only [mem_Ico, hx1, true_and]
            ring_nf
            constructor
            · exact h
            · exact hx2
        · ring_nf
          exact h
        · exact hx2
    · rw[Nat.not_odd_iff_even ] at h0
      have hk1 : 2*k = n := by
        rw[h_k]
        rw[mul_comm]
        apply Nat.div_two_mul_two_of_even
        exact h0
      rw[← hk1]
      by_cases h : x<1/2
      · rw[Walsh.walsh_even_left  h]
        set y:= 2* x with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2]
        rw[← BinaryRepresentationSet.binaryRepresentationSet_equiv2resultprod]
        apply Finset.prod_congr
        · simp
        · intro m hm
          rw[Haar.rademachernextfirsthalf]
          simp only [mem_Ico, hx1, true_and]
          ring_nf
          exact h
      · push_neg at h
        rw[Walsh.walsh_even_right h ]
        set y:= 2* x -1 with h_y
        have hy : 0≤ y ∧ y<1 := by
          rw[h_y]
          constructor
          · linarith
          · linarith
        rw[ih k hk0 hy.1 hy.2]
        rw[← BinaryRepresentationSet.binaryRepresentationSet_equiv2resultprod]
        apply Finset.prod_congr
        · simp
        · intro m hm
          rw[Haar.rademachernextsecondhalf]
          simp only [mem_Ico, hx1, true_and]
          ring_nf
          constructor
          · exact h
          · exact hx2


theorem walshradrelbigger0 {n : ℕ }{x : ℝ} (hn : n >0 ) :
  Walsh.walsh n x = ∏ m in BinaryRepresentationSet.binaryRepresentationSet n , Haar.rademacherFunction m x := by
  by_cases h : x≥ 0 ∧ x< 1
  · apply walshRademacherRelation h.1 h.2
  · simp only [not_and_or] at h
    push_neg at h
    rw[Walsh.walsh_not_in x h]
    have h1 (m : ℕ ) : Haar.rademacherFunction m x = 0 := by
      rw[Haar.rademacherFunction_outside ]
      exact h
    rw[eq_comm, Finset.prod_eq_zero_iff]
    simp only [h1, and_true]
    refine Finset.Nonempty.exists_mem ?_
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    apply BinaryRepresentationSet.binaryRepresentationSet_not_zero
    exact hn


/--
Special case of Walsh-Rademacher relation for powers of two.
-/
theorem differentwalshRademacherRelation {n : ℕ} {x : ℝ}  (hx1 : 0 ≤ x) (hx2 :  x<1 ):
  Walsh.walsh (2^n) x = Haar.rademacherFunction n x := by
  rw[walshRademacherRelation, BinaryRepresentationSet.binaryforpower, Finset.prod_singleton]
  · exact hx1
  · exact hx2

/--
Walsh-Rademacher relation.
-/
theorem walshRademacherRelationresult {M N : ℕ} {x : ℝ} (h : M ∈ BinaryRepresentationSet.binaryRepresentationSet N) (hx1 : 0 ≤ x) (hx2 :  x<1 ) :
  Walsh.walsh N x = Walsh.walsh (2^M) x * ∏ m in BinaryRepresentationSet.binaryRepresentationSet (N - (2^M)) , Haar.rademacherFunction m x := by
  rw[walshRademacherRelation hx1 hx2,differentwalshRademacherRelation hx1 hx2]
  rw[← BinaryRepresentationSet.remove_bit N M h]
  exact Finset.prod_eq_mul_prod_diff_singleton h fun x_1 ↦ Haar.rademacherFunction x_1 x

--co jak M nie jest w rozwinieciu binarnym N?


theorem walsh_ort_dif {n m : ℕ} (h: m ≠  n) : Walsh.walshInnerProduct (Walsh.walsh n) m  = 0 := by
  simp only [Walsh.walshInnerProduct]
  by_cases hn : n = 0 ∨ m = 0
  · by_cases hn1 : n =0
    · rw[hn1]
      have h1 : EqOn ((Walsh.walsh 0)*(Walsh.walsh m)) (Walsh.walsh m) (Set.Ico 0 (1:ℝ)):= by
        --simp_rw[Walsh.walsh_zero]
        sorry
      have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
        simp
      have h3 : ∫ (x : ℝ) in Ico 0 1, ((Walsh.walsh 0)*(Walsh.walsh m)) x = ∫ (x : ℝ) in Ico 0 1, (Walsh.walsh m) x := by
        change ∫ (x : ℝ) in Ico 0 1, ((Walsh.walsh 0)*(Walsh.walsh m)) x = ∫ (x : ℝ) in Ico 0 1, (Walsh.walsh m) x
        rw[MeasureTheory.setIntegral_congr_fun h2 h1]
      --simp[h3]
      sorry
    · sorry
  · simp only [not_or] at hn
    push_neg at hn
    sorry



theorem fun_change_partial_sum (M N : ℕ) (f : ℝ → ℝ) (x : ℝ ) : Haar.rademacherFunction M x *(Walsh.walshFourierPartialSum (Haar.rademacherFunction M * f)  N ) x = ∑ n in Finset.range N, (∫ y in Set.Icc 0 1, (Haar.rademacherFunction M y )* f y * Walsh.walsh n y) * Haar.rademacherFunction M x * Walsh.walsh n x  := by


  sorry

/- ## Additional lemmas needed for the main result -/

/--
Lemma 1
-/

theorem lemma1_1 (M N : ℕ) (h1 : 2^M ≤ N)(h2: N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.walshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Icc 0 1, f y * Walsh.walsh (2^M) y * (Haar.haarFunctionScaled M k y)  * Walsh.walsh (2^M) x  * (Haar.haarFunctionScaled M k x) ):= by
  simp only [Walsh.walshFourierPartialSum]



  --OrthonormalBasis.orthogonalProjection_eq_sum
  sorry

/--
Lemma 2
-/
theorem lemma1_2 (M N : ℕ) (h1 : 2^M ≤ N)(h2: N < 2^(M+1))(f : ℝ → ℝ) (x : ℝ) :
  Walsh.walshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M),(∫ y in Set.Icc 0 1, f y * Walsh.walsh N y * (Haar.haarFunctionScaled M k y) ) * Walsh.walsh N x * (Haar.haarFunctionScaled M k x) := by
  rw [lemma1_1]
  · sorry
  · sorry
  · sorry
  · sorry

/--
Lemma 3
-/
theorem lemma2 (M N N' : ℕ) (h1 : 2^M ≤ N ∧ N < 2^(M+1)) (h2 : N' = N - 2^M)
  (f : ℝ → ℝ) (x : ℝ) :
  ∑ i in Finset.range (N + 1) \ Finset.range (2^M), Walsh.walshInnerProduct f i  * Walsh.walsh i x =
  ∑ i in Finset.range (N' + 1), Walsh.walshInnerProduct (Haar.rademacherFunction M * f ) i * (Haar.rademacherFunction M x) *(Walsh.walsh i x) := by
  sorry
