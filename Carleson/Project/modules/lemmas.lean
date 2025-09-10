import Carleson.Project.modules.coef

open InnerProductSpace MeasureTheory Set BigOperators
open Walsh Haar BinaryRepresentationSet WalshHaar WalshRademacher Coef
open Function Set
open unitInterval DyadicStructures

noncomputable section

namespace Lemmas




theorem lemma1_1' {M : ℕ} (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x =
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1,
      f y * walshhaar M k y) * walshhaar M k x:= by
  simp only [walshInnerProduct, ← MeasureTheory.integral_mul_const]
  rw[eq_comm, ← MeasureTheory.integral_finset_sum ]
  · simp_rw[← basiccoef, Finset.mul_sum, ← mul_assoc , Finset.sum_mul]
    --here
    have (a :ℝ): ∑ x_1 ∈ Finset.range (2 ^ M),
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * walsh i a * coef M x_1 i * walsh x_2 x * coef M x_1 x_2  =
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * walsh i a  * walsh x_2 x *(∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i) := by
          simp_rw[Finset.mul_sum]
          rw[Finset.sum_comm]
          congr
          ext y
          rw[Finset.sum_comm]
          congr
          ext k
          congr
          ext i
          rw[← mul_assoc]
          linarith
    simp_rw[this]
    --here
    have :
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        (∫ (a : ℝ) in Ico 0 1,f a * walsh i a * walsh x_2 x )* ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i = ∫ (a : ℝ) in Ico 0 1,
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        f a * walsh i a * walsh x_2 x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i := by
          rw[MeasureTheory.integral_finset_sum]
          · congr
            ext i
            rw[MeasureTheory.integral_finset_sum]
            · congr
              ext m
              rw[← MeasureTheory.integral_mul_const]
            · intro m hm
              have : (fun a ↦ f a * walsh m a * walsh i x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 i * coef M x_1 m)= (fun a ↦  ∑ x_1 ∈ Finset.range (2 ^ M), ( walsh m a  * f a ) *(walsh i x* coef M x_1 i * coef M x_1 m) ):= by
                ext a
                rw[mul_comm, Finset.sum_mul]
                congr
                ext y
                linarith
              simp_rw[this]
              apply MeasureTheory.integrable_finset_sum
              intro j hj
              apply MeasureTheory.Integrable.mul_const
              apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_walsh01 hf'
          · intro i hi
            apply MeasureTheory.integrable_finset_sum
            intro j hj
            have : (fun a ↦ f a * walsh j a * walsh i x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 i * coef M x_1 j) = (fun a ↦ ∑ x_1 ∈ Finset.range (2 ^ M),  ( walsh j a * f a  )* (walsh i x * coef M x_1 i * coef M x_1 j) ):= by
              ext a
              rw[mul_comm, Finset.sum_mul]
              congr
              ext y
              linarith
            simp_rw[this]
            apply MeasureTheory.integrable_finset_sum
            intro j hj
            apply MeasureTheory.Integrable.mul_const
            apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_walsh01 hf'
    simp_rw[← this]
    apply Finset.sum_congr (by simp)
    intro n hn
    rw[Finset.sum_eq_sum_diff_singleton_add hn fun x_1 ↦
            (∫ (a : ℝ) in Ico 0 1, f a * walsh x_1 a * walsh n x) *
              ∑ x_1_1 ∈ Finset.range (2 ^ M), coef M x_1_1 n * coef M x_1_1 x_1, bighelpextra1wrr (M:= M) hn]
    simp only [mul_one, add_eq_right]
    apply Finset.sum_eq_zero
    intro h hj
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hj
    rw[bighelpextra0wrr]
    · rw[mul_zero]
    · simp only [ne_eq]
      rw[eq_comm]
      exact hj.2
    · exact hn
    · simp only [Finset.mem_range]
      exact hj.1
  · intro i hi
    apply MeasureTheory.Integrable.mul_const
    simp_rw[mul_comm (a:= f ?_)]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_WalshHaar01 hf'




theorem lemma1_1'' {M : ℕ} (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x =
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1,
      f y * walshhaar M k y) * walshhaar M k x:= by
  simp only [walshInnerProduct, ← MeasureTheory.integral_mul_const]
  rw[eq_comm, ← MeasureTheory.integral_finset_sum ]
  · simp_rw[← basiccoef, Finset.mul_sum, ← mul_assoc , Finset.sum_mul]
    --simp_rw[mul_assoc (a:= f ?_ * walsh ?_ ?_ ), mul_comm (a:= coef ?_ ?_ ?_ ), ← mul_assoc, mul_assoc (a:= f ?_ * walsh ?_ ?_ * walsh ?_ ?_ )]

    --here
    have (a :ℝ): ∑ x_1 ∈ Finset.range (2 ^ M),
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * walsh i a * coef M x_1 i * walsh x_2 x * coef M x_1 x_2  =
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * walsh i a  * walsh x_2 x *(∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i) := by
          simp_rw[Finset.mul_sum]
          rw[Finset.sum_comm]
          congr
          ext y
          rw[Finset.sum_comm]
          congr
          ext k
          congr
          ext i
          rw[← mul_assoc]
          linarith
    simp_rw[this]
    --here
    have :
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        (∫ (a : ℝ) in Ico 0 1,f a * walsh i a * walsh x_2 x )* ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i = ∫ (a : ℝ) in Ico 0 1,
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        f a * walsh i a * walsh x_2 x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i := by
          rw[MeasureTheory.integral_finset_sum]
          · congr
            ext i
            rw[MeasureTheory.integral_finset_sum]
            · congr
              ext m
              rw[← MeasureTheory.integral_mul_const]
            · intro m hm
              have : (fun a ↦ f a * walsh m a * walsh i x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 i * coef M x_1 m)= (fun a ↦  ∑ x_1 ∈ Finset.range (2 ^ M), ( walsh m a  * f a ) *(walsh i x* coef M x_1 i * coef M x_1 m) ):= by
                ext a
                rw[mul_comm, Finset.sum_mul]
                congr
                ext y
                linarith
              simp_rw[this]
              apply MeasureTheory.integrable_finset_sum
              intro j hj
              apply MeasureTheory.Integrable.mul_const
              apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_walsh01 hf'
          · intro i hi
            apply MeasureTheory.integrable_finset_sum
            intro j hj
            have : (fun a ↦ f a * walsh j a * walsh i x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 i * coef M x_1 j) = (fun a ↦ ∑ x_1 ∈ Finset.range (2 ^ M),  ( walsh j a * f a  )* (walsh i x * coef M x_1 i * coef M x_1 j) ):= by
              ext a
              rw[mul_comm, Finset.sum_mul]
              congr
              ext y
              linarith
            simp_rw[this]
            apply MeasureTheory.integrable_finset_sum
            intro j hj
            apply MeasureTheory.Integrable.mul_const
            apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_walsh01 hf'
    simp_rw[← this]
    apply Finset.sum_congr (by simp)
    intro n hn
    rw[Finset.sum_eq_sum_diff_singleton_add hn fun x_1 ↦
            (∫ (a : ℝ) in Ico 0 1, f a * walsh x_1 a * walsh n x) *
              ∑ x_1_1 ∈ Finset.range (2 ^ M), coef M x_1_1 n * coef M x_1_1 x_1, bighelpextra1wrr (M:= M) hn]
    simp only [mul_one, add_eq_right]
    apply Finset.sum_eq_zero
    intro h hj
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hj
    rw[bighelpextra0wrr]
    · rw[mul_zero]
    · simp only [ne_eq]
      rw[eq_comm]
      exact hj.2
    · exact hn
    · simp only [Finset.mem_range]
      exact hj.1
  · intro i hi
    apply MeasureTheory.Integrable.mul_const
    simp_rw[mul_comm (a:= f ?_)]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul bcs_WalshHaar01 hf'




theorem lemma1_1 {M : ℕ} (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x =
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1,
      f y * walsh (2 ^ M) y * (haarFunctionScaled (-M) k y) * walsh (2 ^ M) x *
        (haarFunctionScaled (-M) k x)):= by
  rw[lemma1_1' f hf']
  congr
  ext k
  rw[← MeasureTheory.integral_mul_const]
  congr
  ext y
  simp_rw[walshhaar, ← mul_assoc]






/--
Lemma 2
-/

theorem lemma1_helphelphelp {n m : ℤ} {x : ENNReal} (hx : 1 < x) (hx2 : x ≠ ⊤) : x^n ≤ x^m ↔ n ≤ m := by
  constructor
  · rw[← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast, le_imp_le_iff_lt_imp_lt]
    intro h
    apply ENNReal.rpow_lt_rpow_of_exponent_lt hx hx2
    norm_cast
  · apply ENNReal.zpow_le_of_le hx.le


theorem lemma1_2helphelp {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (x y : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) : ∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m y) *
      haarFunctionScaled (-↑M) (↑i) y *
           ( ∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m x) *
          haarFunctionScaled (-↑M) (↑i) x = ∑ i ∈ Finset.range (2 ^ M),
      (haarFunctionScaled (-↑M) (↑i) y *  haarFunctionScaled (-↑M) (↑i) x) := by
      apply Finset.sum_congr
      · simp
      · intro k hk
        rw[ mul_assoc (b:= haarFunctionScaled (-↑M) (↑k) y), mul_comm (a:= haarFunctionScaled (-↑M) (↑k) y), ← mul_assoc, mul_assoc (b:= haarFunctionScaled (-↑M) (↑k) y)]
        conv_rhs => rw[← one_mul (a:= haarFunctionScaled (-↑M) (↑k) y), mul_assoc]
        simp only [mul_eq_mul_right_iff]
        by_cases h : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1) ∨ ( 2 ^ (M : ℤ ) * y - k < 0 ∨ 2 ^ (M : ℤ ) * y - k ≥ 1)
        · right
          simp only [mul_eq_zero]
          by_cases h_1 : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1)
          · rw[haarFunctionScaled_outside (-M) k x ]
            · simp
            · simp only [neg_neg]
              exact h_1
          · rw[or_iff_right h_1] at h
            left
            rw[haarFunctionScaled_outside (-M) k y ?_]
            rw[neg_neg]
            exact h
        by_cases h : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1) ∨ ( 2 ^ (M : ℤ ) * y - k < 0 ∨ 2 ^ (M : ℤ ) * y - k ≥ 1)
        · right
          simp only [mul_eq_zero]
          by_cases h_1 : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1)
          · rw[haarFunctionScaled_outside (-M) k x ?_]
            · right
              simp
            · rw[neg_neg]
              exact h_1
          · rw[or_iff_right h_1] at h
            left
            rw[haarFunctionScaled_outside (-M) k y ?_]
            rw[neg_neg]
            exact h
        · push_neg at h
          have hi1 : x ∈ dyadicInterval (-M) k := by
            simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
            constructor
            · simp only [zpow_neg, zpow_natCast]
              rw[mul_comm , mul_inv_le_iff₀ (pow_pos (zero_lt_two) M), ← sub_nonneg, mul_comm]
              exact h.1.1
            · simp only [zpow_neg, zpow_natCast]
              rw[lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M) , ← sub_lt_iff_lt_add']
              exact h.1.2
          have hi2 : y ∈ dyadicInterval (-M) k := by
            simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
            constructor
            · simp only [zpow_neg, zpow_natCast]
              rw[mul_comm , mul_inv_le_iff₀ (pow_pos (zero_lt_two) M), ← sub_nonneg, mul_comm]
              exact h.2.1
            · simp only [zpow_neg, zpow_natCast]
              rw[lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M) , ← sub_lt_iff_lt_add']
              exact h.2.2
          left
          rw[← Finset.prod_mul_distrib]
          apply Finset.prod_eq_one
          intro i hi
          have hiM: i < M := by
                    apply aboutM1 at hi
                    rw[le_tsub_iff_right h1 ] at hi
                    apply lt_of_le_of_lt  hi at h2
                    rw[pow_add,pow_one, mul_two, add_lt_add_iff_right] at h2
                    rw[← pow_lt_pow_iff_right₀ (Nat.one_lt_two) ]
                    exact h2
          have hr: rademacherFunction i y = rademacherFunction i x := by
            simp only [rademacherFunction, mul_eq_mul_left_iff]
            left
            apply Finset.sum_congr
            · simp
            · intro l hl
              simp only [Finset.mem_range] at hl
              rw[haarscl_di, haarscl_di]
              have hdih0 : dyadicInterval (-↑i - 1) (2 * ↑l ) ∪ dyadicInterval (-↑i - 1) (2 * ↑l  +1) = dyadicInterval (-↑i) ( ↑l ) := by
                exact Eq.symm (dyadicInterval_split (-↑i) ↑l)
              have hdih : (dyadicInterval (-↑M) ↑k ⊆ dyadicInterval (-↑i - 1) (2 * ↑l ) ∪ dyadicInterval (-↑i - 1) (2 * ↑l  +1)) ∨ ((dyadicInterval (-↑M) ↑k ) ∩  (dyadicInterval (-↑i - 1) (2 * ↑l) ∪ dyadicInterval (-↑i - 1) (2 * ↑l+1)))= ∅  := by
                simp_rw[hdih0]
                have hh1: ((dyadicInterval (-↑M) ↑k ) ∩  dyadicInterval (-↑i) ( ↑l ))= ∅ ∨ (dyadicInterval (-↑M) ↑k ⊆ dyadicInterval (-↑i) ( ↑l )) ∨ (dyadicInterval (-↑i) ( ↑l )⊆ dyadicInterval (-↑M) ↑k ):= by
                  exact dyadic_intervals_disjoint_or_contained (-↑M) (-↑i) ↑k ↑l
                have hh2 :  (dyadicInterval (-↑i) ( ↑l )⊆ dyadicInterval (-↑M) ↑k ) = False := by
                  refine eq_false ?_
                  by_contra hh22
                  apply MeasureTheory.measure_mono (μ := MeasureTheory.volume ) at hh22
                  simp_rw[dyadicInterval_measure] at hh22
                  have hh222: M ≤ i := by
                    rw[← Int.ofNat_le ]
                    rw[← neg_le_neg_iff]
                    rw[← lemma1_helphelphelp (x := 2)]
                    · exact hh22
                    · simp
                    · simp
                  linarith
                rcases hh1 with hh1|hh1|hh1
                · right
                  exact hh1
                · left
                  exact hh1
                · exfalso
                  simp only [eq_iff_iff, iff_false] at hh2
                  exact hh2 hh1
              have hdi : (dyadicInterval (-↑M) ↑k ⊆ dyadicInterval (-↑i - 1) (2 * ↑l )) ∨ (dyadicInterval (-↑M) ↑k ⊆ dyadicInterval (-↑i - 1) (2 * ↑l  +1)) ∨ ((dyadicInterval (-↑M) ↑k ∩  dyadicInterval (-↑i - 1) (2 * ↑l)) ∪ (dyadicInterval (-↑M) ↑k ∩  dyadicInterval (-↑i - 1) (2 * ↑l+1))) =∅ := by
                rw[← or_assoc]
                rcases hdih with hdih|hdih
                · left
                  by_cases hhhh : dyadicInterval (-↑M) ↑k ⊆ dyadicInterval (-↑i - 1) (2 * ↑l)
                  · left
                    exact hhhh
                  · right
                    apply Disjoint.subset_right_of_subset_union hdih
                    rw [@disjoint_iff_inter_eq_empty]
                    rw[← Int.ofNat_lt , Int.lt_iff_add_one_le, ← Int.neg_le_neg_iff , neg_add] at hiM
                    apply dyadic_intervals_relation2 (k := ((-M) : ℤ) ) (k':= -i -1) (n':= 2* (l:ℤ )) (n:= (k:ℤ) ) at hiM
                    rcases hiM with hiM|hiM
                    · exact hiM
                    · exfalso
                      exact hhhh hiM
                · right
                  rw[← Set.inter_union_distrib_left ]
                  exact hdih
              have obv : Disjoint (dyadicInterval (-↑i - 1) (2 * ↑l )) (dyadicInterval (-↑i - 1) (2 * ↑l+1)) := by
                rw [@disjoint_iff_inter_eq_empty]
                apply dyadicInterval_disjoint
                simp
              have obv2: Disjoint (dyadicInterval (-↑i - 1) (2 * ↑l+1)) (dyadicInterval (-↑i - 1) (2 * ↑l ))  := by
                exact id (Disjoint.symm obv)
              rcases hdi with hdi|hdi|hdi
              · have hxxc:  x ∈ dyadicInterval (-↑i - 1) (2 * ↑l ) := Set.mem_of_mem_of_subset hi1 hdi
                have hyyc:  y ∈  dyadicInterval (-↑i - 1) (2 * ↑l ) := Set.mem_of_mem_of_subset hi2 hdi
                have hxx: x ∉ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := by
                  rw [Set.disjoint_left ] at obv
                  exact obv hxxc
                have hyy: y∉ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := by
                  rw [Set.disjoint_left ] at obv
                  exact obv hyyc
                simp[ hxx, hyy, indicator, hxxc , hyyc]
              · have hxx: x ∈ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := Set.mem_of_mem_of_subset hi1 hdi
                have hyy: y∈ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := Set.mem_of_mem_of_subset hi2 hdi
                have hxxc:  x ∉ dyadicInterval (-↑i - 1) (2 * ↑l ) := by
                  rw [Set.disjoint_left ] at obv2
                  exact obv2 hxx
                have hyyc:  y ∉ dyadicInterval (-↑i - 1) (2 * ↑l ) := by
                  rw [Set.disjoint_left ] at obv2
                  exact obv2 hyy
                simp[ hxx, hyy, indicator, hxxc , hyyc]
              · simp only [union_empty_iff] at hdi
                simp_rw[← Set.disjoint_iff_inter_eq_empty] at hdi
                obtain ⟨hdi1, hdi2⟩ := hdi
                rw [Set.disjoint_left ] at hdi1
                rw [Set.disjoint_left ] at hdi2
                have hxxc:  x ∉ dyadicInterval (-↑i - 1) (2 * ↑l ) := by
                  exact hdi1 hi1
                have hyyc:  y ∉ dyadicInterval (-↑i - 1) (2 * ↑l ) := by
                  exact hdi1 hi2
                have hxx: x ∉ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := by
                  exact hdi2 hi1
                have hyy: y∉ dyadicInterval (-↑i - 1) (2 * ↑l + 1) := by
                  exact hdi2 hi2
                simp[ hxx, hyy, indicator, hxxc , hyyc]
          rw[hr, ← pow_two, rad_sqr hx1 hx2]






theorem lemma1_2help {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (x y : ℝ) (hy1 : 0 ≤ y) (hy2 : y < 1) (hx1 : 0 ≤ x) (hx2 : x < 1) :
  ∑ k ∈ Finset.range (2 ^ M),
      f y * walsh (2 ^ M) y * haarFunctionScaled (-M) k y * walsh (2 ^ M) x *
        haarFunctionScaled (-M : ℤ ) k x =
  ∑ k ∈ Finset.range (2 ^ M),
     f y * walsh N y * haarFunctionScaled (-M) k y * walsh N x *
      haarFunctionScaled (-M) k x := by
      simp_rw[mul_assoc, mul_comm (a:= f y), ← Finset.sum_mul ,mul_eq_mul_right_iff]
      left
      conv_rhs => rw[walshRademacherRelationresult (aboutMfinal h1 h2) hy1 hy2,walshRademacherRelationresult (aboutMfinal h1 h2) hx1 hx2 , mul_comm]
      have : (∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m y) *
        walsh (2 ^ M) y *
      (haarFunctionScaled (-↑M) (↑i) y *
        ((walsh (2 ^ M) x *
            ∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m x) *
          haarFunctionScaled (-↑M) (↑i) x))) = ( ∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m y) *
      haarFunctionScaled (-↑M) (↑i) y *
           ( ∏ m ∈ binaryRepresentationSet (N - 2 ^ M), rademacherFunction m x) *
          haarFunctionScaled (-↑M) (↑i) x) * walsh (2 ^ M) y * walsh (2 ^ M) x := by
          rw[Finset.sum_mul, Finset.sum_mul]
          congr
          ext i
          linarith
      rw[this,lemma1_2helphelp h1 h2  x y  hx1 hx2 , Finset.sum_mul, Finset.sum_mul]
      congr
      ext i
      linarith


theorem lemma1_2 {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) :
  ∑ i ∈ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x=
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1, f y * walsh N y * (haarFunctionScaled (-M) k y)) *
        walsh N x *
      (haarFunctionScaled (-M) k x) := by
  rw [lemma1_1 f hf']
  simp_rw[← MeasureTheory.integral_mul_const]
  rw[← MeasureTheory.integral_finset_sum, ← MeasureTheory.integral_finset_sum]
  · apply MeasureTheory.setIntegral_congr_fun
    · simp
    · unfold EqOn
      intro z hz
      simp only [mem_Ico] at hz
      apply lemma1_2help h1 h2 f x z hz.1 hz.2 hx1 hx2
  · intro i hi
    have : (fun a ↦
    f a * walsh N a * haarFunctionScaled (-↑M) (↑i) a * walsh N x * haarFunctionScaled (-↑M) (↑i) x )= (fun a ↦
    walsh N x * haarFunctionScaled (-↑M) (↑i) x * walsh N a * haarFunctionScaled (-↑M) (↑i) a * f a ) := by
      ext a
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf'
    simp_rw[mul_assoc]
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.mul bcs_walsh01 bcs_haarscaled01
  · simp only [Finset.mem_range]
    intro i hi
    have : (fun y ↦
    f y * walsh (2 ^ M) y * haarFunctionScaled (-↑M) (↑i) y * walsh (2 ^ M) x *
      haarFunctionScaled (-↑M) (↑i) x) = (fun y ↦
    walsh (2 ^ M) x *
      haarFunctionScaled (-↑M) (↑i) x * walsh (2 ^ M) y * haarFunctionScaled (-↑M) (↑i) y * f y ) := by
      ext a
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf'
    simp_rw[mul_assoc]
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.mul bcs_walsh01 bcs_haarscaled01




/--
Lemma 3
-/
theorem lemma2helphelp {M : ℕ} {y : ℝ} {i : ℕ} (h3 : y ∈ (Set.Ico 0 1)) : walsh i y * rademacherFunction M y = walsh (2^M^^^i) y := by
  simp only [mem_Ico] at h3
  rw[← differentwalshRademacherRelation h3.1 h3.2 , ← prodofwalshworse h3.1 h3.2 ]
  exact Nat.xor_comm (2 ^ M) i

theorem lemma2helphelpextra {M : ℕ} {y : ℝ} {i : ℕ} (h : y ∈ univ \ (Set.Ico 0 1)) : walsh i y * rademacherFunction M y = walsh (2^M^^^i) y := by
  simp only [mem_diff, mem_univ, mem_Ico, not_and, not_lt, true_and] at h
  apply Decidable.not_or_of_imp at h
  simp only [not_le] at h
  rw[walsh_not_in y h , walsh_not_in y h]
  simp only [zero_mul]


theorem lemma2helphelp' {M : ℕ} {y : ℝ} {i : ℕ} : walsh i y * rademacherFunction M y = walsh (2^M^^^i) y := by
  by_cases h : y ∈ (Set.Ico 0 1)
  · exact lemma2helphelp h
  · push_neg at h
    refine lemma2helphelpextra (mem_diff_of_mem trivial h)

theorem lemma2help {M N N' : ℕ} (h10 : 2 ^ M ≤ N) (h11 : N < 2 ^ (M + 1)) (h2 : N' = N - 2 ^ M)
  (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M),
    ∫ (y : ℝ) in Ico 0 1, f y * walsh i y * walsh i x  =
  ∑ i ∈ Finset.range (N' + 1),
    ∫ (y : ℝ) in Ico 0 1,
      f y * walsh i y * rademacherFunction M y * walsh i x *
        rademacherFunction M x:= by
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
        apply about_altern_and_add' hk'
      · rw[Nat.xor_comm ]
        apply about_altern_and_add' hk'
  · intro i hi
    have : (fun y ↦ f y * walsh i y * rademacherFunction M y * walsh i x * rademacherFunction M x )= (fun y ↦ walsh i x * rademacherFunction M x *walsh i y * rademacherFunction M y *   f y ) := by
      ext y
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf'
    apply MeasureTheory.BoundedCompactSupport.mul ?_ bcs_rademacher01
    apply MeasureTheory.BoundedCompactSupport.const_mul bcs_walsh01
  · intro i hi
    have : (fun y ↦ f y * walsh i y * walsh i x)= (fun y ↦ walsh i x * walsh i y *  f y ) := by
      ext y
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf'
    apply MeasureTheory.BoundedCompactSupport.const_mul bcs_walsh01



theorem lemma2 {M N N' : ℕ} (h10 : 2 ^ M ≤ N) (h11 : N < 2 ^ (M + 1)) (h2 : N' = N - 2 ^ M)
  (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x =
  ∑ i ∈ Finset.range (N' + 1),
    walshInnerProduct (rademacherFunction M * f) i * (rademacherFunction M x) *
      (walsh i x) := by
  unfold walshInnerProduct
  simp only [Pi.mul_apply]
  simp_rw[← MeasureTheory.integral_mul_const]
  rw[lemma2help h10 h11 h2 f hf]
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



theorem partition {M N : ℕ} (h1 : 2 ^ M ≤ N) (f : ℝ → ℝ) (x : ℝ) : ∑
  i ∈ Finset.range (N + 1), walshInnerProduct f i * walsh i x =∑
    i ∈ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x + ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M), walshInnerProduct f i * walsh i x := by
  conv_rhs => rw[add_comm]
  rw[Finset.sum_sdiff ]
  rw[Finset.range_subset]
  exact Nat.le_add_right_of_le h1

end Lemmas
