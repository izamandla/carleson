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

namespace Extra
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

/--
Product of two walsh functions
-/


theorem prodofwalshworse {M N k : ℕ} {x : ℝ } (hx1 : 0 ≤ x) (hx2 :  x<1 ) (hk: k = M^^^N) :Walsh.walsh k x = Walsh.walsh M x * Walsh.walsh N x:= by
  rw[BinaryRepresentationSet.differenceofbinaryrepset] at hk
  rw[walshRademacherRelation hx1 hx2,walshRademacherRelation hx1 hx2, walshRademacherRelation hx1 hx2, BinaryRepresentationSet.binaryRepresentationSet_fun_prod2 , ← Finset.prod_union (disjoint_sdiff_sdiff)]
  · rw[hk]
  · intro k
    apply Haar.rad_sqr hx1 hx2




theorem prodofwalsh{M N k : ℕ} {x : ℝ } (hx1 : 0 ≤ x) (hx2 :  x<1 ) : k = M^^^N ↔ Walsh.walsh k x = Walsh.walsh M x * Walsh.walsh N x:= by
  rw[walshRademacherRelation hx1 hx2,walshRademacherRelation hx1 hx2, walshRademacherRelation hx1 hx2, BinaryRepresentationSet.differenceofbinaryrepset, BinaryRepresentationSet.binaryRepresentationSet_fun_prod2 , ← Finset.prod_union (disjoint_sdiff_sdiff)]
  · --nie jestem pewna jak to zrobic - z załozen o funkcji redamachera powiino to jakosc isc ale jak?
    sorry
  · intro k
    apply Haar.rad_sqr hx1 hx2



theorem walsh_int {n : ℕ } (h : n>0) : ∫ (x : ℝ) in Ico 0 1, Walsh.walsh n x = 0 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h1: Odd n
  · rw[Walsh.intofodd h1]
  · simp only [Nat.not_odd_iff_even] at h1
    set l :=n/2 with hl
    have hl' : 2* l = n := by
      exact Nat.two_mul_div_two_of_even h1
    have hl1 : l< n := by
      refine Nat.bitwise_rec_lemma (Nat.not_eq_zero_of_lt h)
    have hl2: 0< l := by
      refine Nat.zero_lt_of_ne_zero ?_
      by_contra hl3
      rw[hl3] at hl'
      linarith
    rw[Walsh.intofeven hl']
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact ih l hl1 hl2




theorem walsh_ort_dif {n m : ℕ} (h: m ≠  n) : Walsh.walshInnerProduct (Walsh.walsh n) m  = 0 := by
  simp only [Walsh.walshInnerProduct]
  set k := m^^^n with hk
  simp_rw[← Pi.mul_apply]
  have h1 : EqOn (Walsh.walsh n * Walsh.walsh m) (Walsh.walsh k) (Set.Ico 0 1):= by
    unfold EqOn
    intro z hz
    simp only [mem_Ico] at hz
    rw[prodofwalshworse (M:=n) (N:= m) ]
    · simp only [Pi.mul_apply]
    · exact hz.1
    · exact hz.2
    · exact Nat.xor_comm m n
  have h2: MeasurableSet (Set.Ico 0 (1 : ℝ )) := by
    simp
  rw[MeasureTheory.setIntegral_congr_fun h2 h1, walsh_int]
  refine Nat.zero_lt_of_ne_zero ?_
  exact Nat.xor_ne_zero.mpr h



theorem fun_change_partial_sum (M N : ℕ) (f : ℝ → ℝ) (x : ℝ ) : Haar.rademacherFunction M x *(Walsh.walshFourierPartialSum (Haar.rademacherFunction M * f)  N ) x = ∑ n in Finset.range N, (∫ y in Set.Ico 0 1, (Haar.rademacherFunction M y )* f y * Walsh.walsh n y) * Haar.rademacherFunction M x * Walsh.walsh n x  := by
  unfold Walsh.walshFourierPartialSum
  unfold Walsh.walshInnerProduct
  rw[mul_comm, Finset.sum_mul ]
  set b:= Haar.rademacherFunction M x with hb
  simp only [Pi.mul_apply]
  rw[Finset.sum_congr]
  · simp
  · intro z hz
    linarith



/- ## Additional lemmas needed for the main result -/

/--
Lemma 1
-/
def walshhaar (M k: ℕ ) : ℝ → ℝ
| x =>
  Walsh.walsh (2^M) x * (Haar.haarFunctionScaled M k x)


theorem walshHaar_ort_help {M k k': ℕ } {x :ℝ } (h : k ≠ k'):  walshhaar M k x * walshhaar M k' x = 0 := by
  unfold walshhaar
  rw[mul_comm]
  rw [@mul_mul_mul_comm]
  rw[Haar.haarFunctionScaled_mul ]
  · simp only [mul_zero]
  · simp only [ne_eq, Nat.cast_inj]
    rw[ne_comm, ne_eq] at h
    exact h


theorem walshHaar_ort {M k k': ℕ } (h : k ≠ k'):  ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k' y = 0 := by
  have h1 : EqOn (walshhaar M k * walshhaar M k') 0 (Set.Ico 0 1) := by
    unfold EqOn
    intro z hz
    apply walshHaar_ort_help h
  have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
    simp
  simp_rw[← Pi.mul_apply]
  rw[MeasureTheory.setIntegral_congr_fun h2 h1]
  simp




--sumowanie jest do 2^M - 1 wiec tu przedzialy sa ok
theorem lemma1_1 {M N : ℕ} (h1 : 2^M ≤ N)(h2: N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Ico 0 1, f y * Walsh.walsh (2^M) y * (Haar.haarFunctionScaled M k y)  * Walsh.walsh (2^M) x  * (Haar.haarFunctionScaled M k x) ):= by


  --OrthonormalBasis.orthogonalProjection_eq_sum
  sorry

/--
Lemma 2
-/



theorem aboutprodrad {k N M : ℕ } {x y : ℝ} (h: N < 2^M) (hy1 : 0≤ y) (hy2 : y< 1) (hx1 : 0≤ x) (hx2 : x<1)(hk: k ∈ BinaryRepresentationSet.binaryRepresentationSet N ) : Haar.rademacherFunction k x * Haar.rademacherFunction k y = 1 := by
  by_cases h : ∃ n, x ∈ Ico (2^((-k) : ℤ )*n) (2^((-k) : ℤ )*(n+1)) ∧ y ∈ Ico (2^((-k) : ℤ )*n ) ( 2^((-k) : ℤ )*(n+1))
  · sorry
  · sorry

---tu trzeba sie lepiej zastanowic jak zrobic to najkrocej




theorem lemma1_2help  {M N : ℕ} (h1 : 2^M ≤ N)(h2: N < 2^(M+1))(f : ℝ → ℝ) (x y : ℝ) (hy1 : 0≤ y) (hy2 : y< 1) (hx1 : 0≤ x) (hx2 : x<1):
  ∑ k ∈ Finset.range (2 ^ M),
      f y * Walsh.walsh (2 ^ M) y * Haar.haarFunctionScaled M k y * Walsh.walsh (2 ^ M) x *
        Haar.haarFunctionScaled M k x =
  ∑ k ∈ Finset.range (2 ^ M),
     f y * Walsh.walsh N y * Haar.haarFunctionScaled M k y * Walsh.walsh N x *
      Haar.haarFunctionScaled M k x := by
  simp_rw[mul_assoc, mul_comm (a:= f y), ← Finset.sum_mul ]
  simp only [mul_eq_mul_right_iff]
  left
  conv_rhs => rw[walshRademacherRelationresult (BinaryRepresentationSet.aboutMfinal h1 h2) hy1 hy2,walshRademacherRelationresult (BinaryRepresentationSet.aboutMfinal h1 h2) hx1 hx2 , mul_comm]
  simp_rw[mul_comm, ← mul_assoc, ← Finset.sum_mul ]
  conv_rhs => rw[ mul_comm, ← mul_assoc, ]
  simp only [mul_eq_mul_right_iff]
  left
  conv_rhs => rw[← mul_assoc, mul_comm, ← mul_assoc, ← mul_assoc ]
  simp only [mul_eq_mul_right_iff]
  left
  conv_lhs => rw[← one_mul (a:=   ∑ i ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (↑M) (↑i) y * Haar.haarFunctionScaled (↑M) (↑i) x)]
  congr
  rw[← Finset.prod_mul_distrib, Finset.prod_eq_one]
  intro k hk
  set N' := N - 2 ^ M with hN
  have hN1 : N' < 2^M := by
    rw[hN, propext (Nat.sub_lt_iff_lt_add' h1), ← mul_two, ← Nat.pow_add_one]
    exact h2
  apply aboutprodrad hN1 hy1 hy2 hx1 hx2 hk

theorem lemma1_2 {M N : ℕ} (h1 : 2^M ≤ N)(h2: N < 2^(M+1))(f : ℝ → ℝ) (x : ℝ) (hx1 : 0≤ x) (hx2 : x<1) :
  ∑ i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x=
  ∑ k in Finset.range (2^M),(∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * (Haar.haarFunctionScaled M k y) ) * Walsh.walsh N x * (Haar.haarFunctionScaled M k x) := by
  rw [lemma1_1 h1 h2 ]
  simp_rw[← MeasureTheory.integral_mul_right]
  rw[← MeasureTheory.integral_finset_sum, ← MeasureTheory.integral_finset_sum]
  · apply MeasureTheory.setIntegral_congr_fun
    · simp
    · unfold EqOn
      intro z hz
      simp only [mem_Ico] at hz
      simp only
      apply lemma1_2help h1 h2
      · exact hz.1
      · exact hz.2
      · exact hx1
      · exact hx2
  · intro i hi
    simp_all only [Finset.mem_range]
    --rw[MeasureTheory.MemLp.integrable_mul]
    --MeasureTheory.Integrable.mul_of_top_right
    sorry
  · simp only [Finset.mem_range]

    sorry

/--
Lemma 3
-/
theorem lemma2helphelp {M: ℕ} {y : ℝ } {i : ℕ } (h3 : y ∈ (Set.Ico 0 1)) : Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  simp only [Finset.mem_range, mem_Ico] at h3
  rw[← differentwalshRademacherRelation h3.1 h3.2 , ← prodofwalshworse h3.1 h3.2 ]
  exact Nat.xor_comm (2 ^ M) i

theorem lemma2helphelpextra {M: ℕ} {y : ℝ } {i : ℕ } (h : y ∈ univ \ (Set.Ico 0 1)) : Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  simp only [mem_diff, mem_univ, mem_Ico, not_and, not_lt, true_and] at h
  rw[Walsh.walsh_not_in, Walsh.walsh_not_in]
  · simp only [zero_mul]
  · rw[lt_iff_not_ge]
    exact Decidable.not_or_of_imp h
  · rw[lt_iff_not_ge]
    exact Decidable.not_or_of_imp h

theorem lemma2helphelp' {M: ℕ} {y : ℝ } {i : ℕ }: Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  by_cases h : y ∈ (Set.Ico 0 1)
  · exact lemma2helphelp h
  · push_neg at h
    refine lemma2helphelpextra ?_
    exact mem_diff_of_mem trivial h




theorem lemma2help {M N N' : ℕ}(h10 : 2^M ≤ N )( h11: N < 2^(M+1)) (h2 : N' = N - 2^M)
  (f : ℝ → ℝ) (x : ℝ):
  ∑ i in Finset.range (N+1)  \ Finset.range (2^M), ∫ (y : ℝ) in Ico 0 1,
      f y * Walsh.walsh i y * Walsh.walsh i x  =
  ∑ i in Finset.range (N'+1),  ∫ (y : ℝ) in Ico 0 1,
      f y * Walsh.walsh i y * Haar.rademacherFunction M y * Walsh.walsh i x  * Haar.rademacherFunction M x:= by
  rw[← MeasureTheory.integral_finset_sum, ← MeasureTheory.integral_finset_sum]
  · congr
    ext y
    rw[eq_comm]
    let i : ℕ → ℕ  := fun i ↦ i + 2^M
    apply Finset.sum_nbij i
    · simp only [Finset.mem_range, Finset.mem_sdiff, not_lt]
      unfold i
      simp only [le_add_iff_nonneg_left, zero_le, and_true, h2]
      intro a ha
      refine Nat.lt_sub_iff_add_lt.mp ?_
      exact Nat.lt_of_lt_of_eq ha (Eq.symm (Nat.sub_add_comm h10))
    · unfold InjOn
      unfold i
      simp
    · unfold SurjOn
      intro k hk
      simp only [Finset.coe_range, mem_image, mem_Iio]
      unfold i
      set s := k - 2^M with hs
      use s
      simp only [Finset.coe_sdiff, Finset.coe_range, Iio_diff_Iio, mem_Ico] at hk
      constructor
      · rw[h2]
        refine Nat.sub_lt_left_of_lt_add ?_ ?_
        · exact hk.1
        · have : 2 ^ M + (N - 2 ^ M + 1) = N + 1 := by
            rw [Nat.add_comm, add_assoc, add_comm]
            conv_rhs => rw[add_comm]
            rw[add_assoc, add_left_cancel_iff, Nat.add_sub_cancel' h10]
          rw[this]
          exact hk.2
      · rw[hs]
        refine Nat.sub_add_cancel ?_
        exact hk.1
    · intro k hk
      rw[h2] at hk
      simp only [Finset.mem_range] at hk
      have hk' : k < 2^ M := by
        rw[← Nat.add_one_le_iff ,pow_add, pow_one, mul_two] at h11
        apply Nat.sub_le_sub_right (k:= 2^M) at h11
        rw[Nat.add_sub_cancel, Nat.sub_add_comm h10] at h11
        exact Nat.lt_of_lt_of_le hk h11
      unfold i
      conv_lhs => rw[mul_assoc, lemma2helphelp', mul_comm, mul_assoc, lemma2helphelp', ← mul_assoc, mul_comm, ← mul_assoc, mul_comm, ← mul_assoc ]
      congr
      · rw[Nat.xor_comm ]
        apply BinaryRepresentationSet.about_altern_and_add' hk'
      · rw[Nat.xor_comm ]
        apply BinaryRepresentationSet.about_altern_and_add' hk'
  · intro i hi

    sorry
  · intro i hi
    sorry

theorem lemma2 {M N N' : ℕ}(h10 : 2^M ≤ N )( h11: N < 2^(M+1)) (h2 : N' = N - 2^M)
  (f : ℝ → ℝ) (x : ℝ) :
  ∑ i in Finset.range (N+1)  \ Finset.range (2^M), Walsh.walshInnerProduct f i  * Walsh.walsh i x =
  ∑ i in Finset.range (N' +1), Walsh.walshInnerProduct (Haar.rademacherFunction M * f ) i * (Haar.rademacherFunction M x) *(Walsh.walsh i x) := by
  unfold Walsh.walshInnerProduct
  simp only [Pi.mul_apply]
  simp_rw[← MeasureTheory.integral_mul_right]
  rw[lemma2help h10 h11 h2]
  apply Finset.sum_congr
  · simp
  · intro k hk
    congr
    rw [funext_iff]
    intro y
    conv_lhs => rw[mul_comm, ← mul_assoc]
    simp only [mul_eq_mul_right_iff]
    left
    rw[mul_comm]
    simp only [mul_eq_mul_right_iff]
    left
    rw[mul_comm, ← mul_assoc]



theorem partition {M N : ℕ } (h1 : 2^M ≤ N) (f : ℝ → ℝ) (x : ℝ) : ∑ i in Finset.range (N ), Walsh.walshInnerProduct f i  * Walsh.walsh i x =∑ i in  Finset.range (2^M), Walsh.walshInnerProduct f i  * Walsh.walsh i x + ∑ i in Finset.range (N) \ Finset.range (2^M), Walsh.walshInnerProduct f i  * Walsh.walsh i x := by
  conv_rhs => rw[add_comm]
  rw[Finset.sum_sdiff]
  rw[Finset.range_subset]
  exact h1


end Extra
