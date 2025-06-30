import Carleson.Project.modules.Utiles
open Extra
open BinaryRepresentationSet
open Walsh Function Set MeasureTheory
/- ## Main result -/




/-theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) (hf : MeasureTheory.LocallyIntegrable f):
  Walsh.walshFourierPartialSum f N x = (∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  have hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1)) := by
      refine MeasureTheory.IntegrableOn.integrable ?_
      apply MeasureTheory.IntegrableOn.mono_set ( t := Icc 0 1)
      · rw[MeasureTheory.locallyIntegrable_iff] at hf
        apply hf
        exact isCompact_Icc
      · exact Ico_subset_Icc_self

  unfold Walsh.walshFourierPartialSum
  induction' N using Nat.strong_induction_on with N ih generalizing f
  by_cases hN : N = 0
  · rw[hN]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    unfold walshInnerProduct
    conv_lhs => rw[walsh_zero hx1 hx2, mul_one]
    apply MeasureTheory.integral_congr_ae
    simp only [measurableSet_Ico, MeasureTheory.ae_restrict_eq]
    refine Filter.eventuallyEq_inf_principal_iff.mpr ?_
    apply Filter.Eventually.of_forall
    intro y hy
    simp only [Set.mem_Ico] at hy
    rw[walsh_zero hy.1 hy.2, walsh_zero hx1 hx2, Kernel.kernel_zero]
    simp only [mul_one]
  push_neg at hN
  obtain ⟨M, hM⟩ := max_binaryRepresentationSet N (Nat.zero_lt_of_ne_zero hN)
  have hM1 : 2^M ≤ N := aboutM1 hM.1
  have hM2 : N < 2^(M+1) := aboutM2 hM.2
  set N' := N - 2^M with hN'
  have hN'' : N' < N := by sorry
  have h0 :∫ (y : ℝ) in Ico 0 1, ∑ x_1 ∈ Finset.range (N' + 1),
      Haar.rademacherFunction M y * f y * walsh x_1 y  * walsh x_1 x = ∫ (y : ℝ) in Ico 0 1,
      Haar.rademacherFunction M y * f y * walsh N' y * Kernel.kernel N' x y  * walsh N' x := by
      simp only [walshInnerProduct] at ih
      set g := Haar.rademacherFunction M  * f with hg
      have hg' : LocallyIntegrable g volume := by sorry
      have hg2 :  Integrable g (volume.restrict (Ico 0 1)) := by sorry
      simp_rw[← MeasureTheory.integral_mul_const] at ih
      simp_rw[← Pi.mul_apply (f:= Haar.rademacherFunction M ), ← hg]
      rw[MeasureTheory.integral_finset_sum]
      · rw[ih N' hN'' g hg' hg2]
        congr
        ext y
        linarith
      sorry

  rw[partition hM1, lemma1_2 hM1 hM2 f hf , lemma2 hM1 hM2 hN' f hf]
  · unfold walshInnerProduct
    simp_rw[← MeasureTheory.integral_mul_const]
    rw[← MeasureTheory.integral_finset_sum, ← MeasureTheory.integral_finset_sum]
    · rw[← MeasureTheory.integral_add']
      · simp only [Pi.mul_apply, Pi.add_apply]
        apply MeasureTheory.integral_congr_ae
        rw[Filter.EventuallyEq ]
        apply Filter.Eventually.of_forall
        intro y

        /- chyba bez sensu have : (∑ i ∈ Finset.range (2 ^ M),
      f y * walsh N y * Haar.haarFunctionScaled (↑M) (↑i) y * walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x +
    ∑ x_1 ∈ Finset.range (N' + 1),
      Haar.rademacherFunction M y * f y * walsh x_1 y * Haar.rademacherFunction M x * walsh x_1 x )= (
      f y * walsh N y * walsh N x * (∑ i ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (↑M) (↑i) y *  Haar.haarFunctionScaled (↑M) (↑i) x)+

      Haar.rademacherFunction M x * Haar.rademacherFunction M y * f y * (∑ x_1 ∈ Finset.range (N' + 1), walsh x_1 y *  walsh x_1 x )):= by sorry--/
        --teraz jest jakies zamieszanie z tym kiedy jest calka a kiedy nie

        sorry


        /-simp only [Pi.mul_apply, Pi.add_apply]
        apply MeasureTheory.integral_congr_ae
        rw[Filter.EventuallyEq ]
        apply Filter.Eventually.of_forall
        intro y-/


        -- to musi zostac zrobione przez indukcje
      · apply MeasureTheory.integrable_finset_sum
        intro i hi
        have : (fun a ↦ f a * walsh N a * Haar.haarFunctionScaled (↑M) (↑i) a * walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x) = (fun a ↦ walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x * walsh N a * Haar.haarFunctionScaled (↑M) (↑i) a * f a ) := by
          ext a
          linarith
        rw[this]
        apply MeasureTheory.BoundedCompactSupport.integrable_mul
        · simp_rw[mul_assoc]
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.restrict
          apply MeasureTheory.BoundedCompactSupport.mul
          · exact bcs_walsh
          · exact Haar.bcs_haarscaled
        · exact hf'
      · apply MeasureTheory.integrable_finset_sum
        intro i hi
        have : (fun a ↦ (Haar.rademacherFunction M * f) a * walsh i a * Haar.rademacherFunction M x * walsh i x) = (fun a ↦ Haar.rademacherFunction M x * walsh i x * Haar.rademacherFunction M  a * walsh i a * f a  ) := by
          ext a
          simp only [Pi.mul_apply]
          linarith
        rw[this]
        apply MeasureTheory.BoundedCompactSupport.integrable_mul
        · simp_rw[mul_assoc]
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.const_mul
          apply MeasureTheory.BoundedCompactSupport.restrict
          apply MeasureTheory.BoundedCompactSupport.mul
          · exact Haar.bcs_rademacher
          · exact bcs_walsh
        · exact hf'
    · intro i hi
      have : (fun a ↦ (Haar.rademacherFunction M * f) a * walsh i a * Haar.rademacherFunction M x * walsh i x) = (fun a ↦ Haar.rademacherFunction M x * walsh i x * Haar.rademacherFunction M a * walsh i a *  f a) := by
        ext a
        simp only [Pi.mul_apply]
        linarith
      simp_rw[this]
      apply MeasureTheory.BoundedCompactSupport.integrable_mul
      · simp_rw[mul_assoc]
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.restrict
        apply MeasureTheory.BoundedCompactSupport.mul
        · exact Haar.bcs_rademacher
        · exact bcs_walsh
      · exact hf'
    · intro i hi
      have : (fun a ↦ f a * walsh N a * Haar.haarFunctionScaled (↑M) (↑i) a * walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x) = (fun a ↦ walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x  * walsh N a * Haar.haarFunctionScaled (↑M) (↑i) a * f a ) := by
        ext a
        linarith
      simp_rw[this]
      apply MeasureTheory.BoundedCompactSupport.integrable_mul
      · simp_rw[mul_assoc]
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.restrict
        apply MeasureTheory.BoundedCompactSupport.mul
        · exact bcs_walsh
        · exact Haar.bcs_haarscaled
      · exact hf'
  · exact hx1
  · exact hx2-/



theorem inthelp (f : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f):
  MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1)) := by
  refine MeasureTheory.IntegrableOn.integrable ?_
  apply MeasureTheory.IntegrableOn.mono_set ( t := Icc 0 1)
  · rw[MeasureTheory.locallyIntegrable_iff] at hf
    apply hf
    exact isCompact_Icc
  · exact Ico_subset_Icc_self


theorem mainresult' (N : ℕ) (f : ℝ → ℝ) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) (hf : MeasureTheory.LocallyIntegrable f):
  Walsh.walshFourierPartialSum f N x = (∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
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
    rw[walsh_zero hy.1 hy.2, walsh_zero hx1 hx2, Kernel.kernel_zero]
    simp only [mul_one]
  push_neg at hN
  obtain ⟨M, hM⟩ := max_binaryRepresentationSet N (Nat.zero_lt_of_ne_zero hN)
  have hM1 : 2^M ≤ N := aboutM1 hM.1
  have hM2 : N < 2^(M+1) := aboutM2 hM.2
  set N' := N - 2^M with hN'
  have hN'' : N' < N := by
    rw[hN']
    omega
  rw[partition hM1, lemma1_2 hM1 hM2 f hf , lemma2 hM1 hM2 hN' f hf]
  · set g:= Haar.rademacherFunction M * f with hg
    have hg2 :  Integrable g (volume.restrict (Ico 0 1)) := by
      rw[hg]
      apply BoundedCompactSupport.integrable_mul
      · refine BoundedCompactSupport.restrict ?_
        exact Haar.bcs_rademacher
      · exact hf
    have :( ∑ i ∈ Finset.range (N' + 1), walshInnerProduct g i * Haar.rademacherFunction M x * walsh i x) = Haar.rademacherFunction M x * (∑ x_1 ∈ Finset.range (N' + 1),  walshInnerProduct g x_1 * walsh x_1 x):= by
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
        intro y

        sorry

        /- ext y
          rw[mul_comm] at hg
          rw[hg]
          simp only [Pi.mul_apply]
          have : (∑ i ∈ Finset.range (2 ^ M),
        f y * walsh N y * Haar.haarFunctionScaled (↑M) (↑i) y * walsh N x * Haar.haarFunctionScaled (↑M) (↑i) x) = (f y * walsh N y * walsh N x * ∑ i ∈ Finset.range (2 ^ M),
        Haar.haarFunctionScaled (↑M) (↑i) y * Haar.haarFunctionScaled (↑M) (↑i) x) := by
            conv_rhs => rw[mul_comm, Finset.sum_mul ]
            congr
            ext i
            linarith
          rw[this ]
          have h1 : (Haar.rademacherFunction M * walsh N') x = walsh N x:= by
            simp only [Pi.mul_apply]
            rw[hN', walshRademacherRelationresult hM.1 hx1 hx2]
            rw[differentwalshRademacherRelation hx1 hx2]
            simp only [mul_eq_mul_left_iff]
            left
            exact walshRademacherRelation hx1 hx2
            sorry-/

      · sorry
      · sorry
    sorry
  · sorry
  · sorry
