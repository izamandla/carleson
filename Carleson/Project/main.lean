import Carleson.Project.modules.lemmas
import Carleson.Project.modules.kernel
open BinaryRepresentationSet Walsh Haar Kernel Coef WalshHaar WalshRademacher Lemmas
open Walsh Function Set MeasureTheory

/- ## Main result -/


/--
Locally integrable function is integrable on `Ico 0 1`.
-/
theorem inthelp (f : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) :
  MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1)) := by
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Icc 0 1) ?_ Ico_subset_Icc_self
  rw[MeasureTheory.locallyIntegrable_iff] at hf
  apply hf
  exact isCompact_Icc


/--
Integral form of Walsh Fourier Series.
-/
theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) (hf : MeasureTheory.LocallyIntegrable f) :
  walshFourierPartialSum f N x = (∫ y in Set.Ico 0 1, f y * walsh N y * walsh N x * kernel N x y) := by
  apply inthelp at hf
  simp only [walshFourierPartialSum]
  induction' N using Nat.strong_induction_on with N ih generalizing f
  by_cases hN : N = 0
  · rw[hN]
    simp only [walshInnerProduct, zero_add, Finset.range_one, Finset.sum_singleton]
    conv_lhs => rw[walsh_zero hx1 hx2, mul_one]
    apply MeasureTheory.integral_congr_ae
    simp only [measurableSet_Ico, MeasureTheory.ae_restrict_eq]
    refine Filter.eventuallyEq_inf_principal_iff.mpr ?_
    apply Filter.Eventually.of_forall
    intro y hy
    simp only [Set.mem_Ico] at hy
    rw[walsh_zero hy.1 hy.2, walsh_zero hx1 hx2, kernel_zero]
    simp only [mul_one]
  push_neg at hN
  obtain ⟨M, hM⟩ := max_binaryRepresentationSet N (Nat.zero_lt_of_ne_zero hN)
  obtain hM1 := aboutM1 hM.1
  obtain hM2 := aboutM2 hM.2
  set N' := N - 2^M with hN'
  have hN'' : N' < N := by
    rw[hN']
    omega
  rw[partition hM1, lemma1_2 hM1 hM2 f hf x hx1 hx2 , lemma2 hM1 hM2 hN' f hf]
  · set g:= rademacherFunction M * f with hg
    have hg2 :  Integrable g (volume.restrict (Ico 0 1)) := by
      rw[hg]
      apply BoundedCompactSupport.integrable_mul bcs_rademacher01 hf
    have :( ∑ i ∈ Finset.range (N' + 1), walshInnerProduct g i * rademacherFunction M x * walsh i x) = rademacherFunction M x * (∑ x_1 ∈ Finset.range (N' + 1),  walshInnerProduct g x_1 * walsh x_1 x):= by
      conv_rhs => rw[mul_comm, Finset.sum_mul ]
      congr
      ext i
      linarith
    rw[this, ih N' hN'' g hg2 ]
    simp_rw[← MeasureTheory.integral_mul_const]
    rw[← MeasureTheory.integral_finset_sum]
    · rw[mul_comm, ← MeasureTheory.integral_mul_const]
      rw[← MeasureTheory.integral_add']
      · rw[← MeasureTheory.integral_indicator (measurableSet_Ico), ← MeasureTheory.integral_indicator (measurableSet_Ico)]
        apply MeasureTheory.integral_congr_ae
        rw[Filter.EventuallyEq ]
        apply Filter.Eventually.of_forall
        simp only [indicator, mem_Ico, Pi.add_apply]
        intro y
        split_ifs with h1
        · rw[mul_comm] at hg
          rw[hg]
          simp only [Pi.mul_apply]
          --here
          --simp_rw[mul_assoc, ← Finset.mul_sum ]
          --simp_rw[mul_left_comm (a:= haarFunctionScaled _ _ y ), ← Finset.mul_sum ]
          have : (∑ i ∈ Finset.range (2 ^ M),
        f y * walsh N y * haarFunctionScaled (-↑M) (↑i) y * walsh N x * haarFunctionScaled (-↑M) (↑i) x) = (f y * walsh N y * walsh N x * ∑ i ∈ Finset.range (2 ^ M),
        haarFunctionScaled (-↑M) (↑i) y * haarFunctionScaled (-↑M) (↑i) x) := by
            conv_rhs => rw[mul_comm, Finset.sum_mul ]
            congr
            ext i
            linarith
          rw[this ]
          have h1_1 : (rademacherFunction M * walsh N') x = walsh N x:= by
            simp only [Pi.mul_apply]
            rw[hN', walshRademacherRelationresult hM.1 hx1 hx2, differentwalshRademacherRelation hx1 hx2]
            simp only [mul_eq_mul_left_iff]
            left
            exact walshRademacherRelation hx1 hx2
          have h1_2 : rademacherFunction M y * walsh N' y = walsh N y:= by
            rw[hN', walshRademacherRelationresult hM.1 h1.1 h1.2, differentwalshRademacherRelation h1.1 h1.2]
            simp only [mul_eq_mul_left_iff]
            left
            exact walshRademacherRelation h1.1 h1.2
          have: (f y * rademacherFunction M y * walsh N' y * walsh N' x * kernel N' x y * rademacherFunction M x) = f y * walsh N y * walsh N x * kernel N' x y := by
            rw[← h1_2, ← h1_1]
            simp only [Pi.mul_apply]
            linarith
          rw[this]
          rw[Eq.symm
                (LeftDistribClass.left_distrib (f y * walsh N y * walsh N x)
                  (∑ i ∈ Finset.range (2 ^ M),
                    haarFunctionScaled (-↑M) (↑i) y * haarFunctionScaled (-↑M) (↑i) x)
                  (kernel N' x y))]
          simp only [mul_eq_mul_left_iff, mul_eq_zero]
          left
          simp only [kernel]
          rw[← add_assoc, add_comm, ← add_assoc, add_comm, add_right_inj]
          rw[← remove_bit N M hM.1]
          have : ∑ i ∈ Finset.range (2 ^ M), haarFunctionScaled (-↑M) (↑i) y * haarFunctionScaled (-↑M) (↑i) x = ∑ m ∈ {M},
      ∑ n ∈ Finset.range (2 ^ m), haarFunctionScaled (-↑m) (↑n) x * haarFunctionScaled (-↑m) (↑n) y:= by
            simp only [Finset.sum_singleton]
            congr
            ext i
            linarith
          rw[this, ← Finset.sum_union (by simp) ]
          congr
          simp only [Finset.sdiff_union_self_eq_union, Finset.union_eq_left,
            Finset.singleton_subset_iff]
          exact aboutMfinal hM1 hM2
        · linarith
      · apply MeasureTheory.integrable_finset_sum
        intro i hi
        have : (fun a ↦ f a * walsh N a * haarFunctionScaled (-↑M) (↑i) a * walsh N x * haarFunctionScaled (-↑M) (↑i) x) = (fun a ↦ walsh N x * haarFunctionScaled (-↑M) (↑i) x * walsh N a * haarFunctionScaled (-↑M) (↑i) a * f a ) := by
          ext a
          linarith
        rw[this]
        apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf
        simp_rw[mul_assoc]
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.mul bcs_walsh01 bcs_haarscaled01
      · simp_rw[hg]
        simp only [Pi.mul_apply]
        have : (fun a ↦
    rademacherFunction M a * f a * walsh N' a * walsh N' x * kernel N' x a * rademacherFunction M x) = (fun a ↦  walsh N' x * rademacherFunction M x *
    rademacherFunction M a  * walsh N' a * (kernel N' x a *  f a)):= by
          ext a
          linarith
        rw[this]
        apply MeasureTheory.BoundedCompactSupport.integrable_mul
        · simp_rw[mul_assoc]
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.mul bcs_rademacher01 bcs_walsh01
        · unfold kernel
          simp_rw[add_mul]
          simp only [one_mul]
          apply MeasureTheory.Integrable.add''
          · exact hf
          · apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf
            apply BoundedCompactSupport.finset_sum
            intro i hi
            apply BoundedCompactSupport.finset_sum
            intro j hj
            apply MeasureTheory.BoundedCompactSupport.const_mul bcs_haarscaled01
    intro i hi
    have : (fun a ↦ f a * walsh N a * haarFunctionScaled (-↑M) (↑i) a * walsh N x * haarFunctionScaled (-↑M) (↑i) x) = (fun a ↦ walsh N x * haarFunctionScaled (-↑M) (↑i) x  * walsh N a * haarFunctionScaled (-↑M) (↑i) a * f a ) := by
      ext a
      ring
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul ?_ hf
    simp_rw[mul_assoc]
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.const_mul
    apply MeasureTheory.BoundedCompactSupport.mul bcs_walsh01 bcs_haarscaled01
