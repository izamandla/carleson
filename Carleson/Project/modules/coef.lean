import Carleson.Project.modules.WalshHaarproduct


open InnerProductSpace MeasureTheory Set BigOperators
open Walsh Haar BinaryRepresentationSet WalshHaar WalshRademacher
open Function Set
open unitInterval DyadicStructures

noncomputable section

namespace Coef

def coef (M k : ℕ) : ℕ → ℝ :=
  (walshindicatorrightform (M := M) (k := k)).choose


theorem basiccoef (M k : ℕ) {x : ℝ} : ∑ j ∈ Finset.range (2 ^ M),  walsh j x * coef M k j = walshhaar M k x := by
  apply congrFun ((walshindicatorrightform (M := M) (k := k)).choose_spec) x


theorem notsobasiccoef (M k j : ℕ) (hj : j ∈ Finset.range (2 ^ M)) : coef M k j = ∫ y in Set.Ico 0 1, walshhaar M k y * walsh j y := by
  simp_rw[← basiccoef, Finset.sum_mul, mul_assoc, mul_comm, mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · simp_rw[MeasureTheory.integral_const_mul]
    rw[Finset.sum_eq_sum_diff_singleton_add hj fun x ↦
          coef M k x * ∫ (a : ℝ) in Ico 0 1, walsh j a * walsh x a]
    rw[walsh_norm']
    simp only [mul_one, right_eq_add]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
    rw[walsh_ort]
    · simp
    · simp only [ne_eq]
      exact hi.2
  · intro i hi
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul bcs_walsh bcs_walsh





theorem bighelpextra0 {M k k' : ℕ} (h0 : k ≠ k') : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k' j = 0 := by
  have h: ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k' y = 0 := by
    refine walshHaar_ort h0
  rw[← h]
  have hf (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), walsh j x * coef M k j = walshhaar M k x :=by
    apply congrFun ((walshindicatorrightform (M := M) (k := k)).choose_spec) x
  have hg (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), walsh j x * coef M k' j = walshhaar M k' x := by
    apply congrFun ((walshindicatorrightform (M := M) (k := k')).choose_spec) x
  have hr : ∫ (y : ℝ) in Ico 0 1, walshhaar M k y * walshhaar M k' y = ∫ (y : ℝ) in Ico 0 1,  (∑ j ∈ Finset.range (2 ^ M), (walsh j y * coef M k j)) * (∑ j ∈ Finset.range (2 ^ M), (walsh j y * coef M k' j)) := by
    congr
    ext y
    rw[hf y, hg]
  rw[hr]
  simp_rw [@Finset.sum_mul_sum, ← mul_assoc, mul_comm, ← mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr
    · simp
    · intro n hn
      rw[MeasureTheory.integral_finset_sum]
      · have (i : ℕ): ∫ (a : ℝ) in Ico 0 1, coef M k' i * coef M k n * walsh n a * walsh i a= coef M k' i * coef M k n * ∫ (a : ℝ) in Ico 0 1, walsh n a * walsh i a := by
          rw[← MeasureTheory.integral_const_mul]
          congr
          ext a
          rw[← mul_assoc]
        simp_rw[this]
        rw[Finset.sum_eq_add_sum_diff_singleton hn fun x ↦
              coef M k' x * coef M k n * ∫ (a : ℝ) in Ico 0 1, walsh n a * walsh x a]
        rw[walsh_norm' n, mul_comm]
        simp only [mul_one, left_eq_add]
        apply Finset.sum_eq_zero
        intro p hp
        rw [@mul_eq_zero]
        right
        rw[walsh_ort]
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hp
        push_neg at hp
        exact hp.2
      · intro i hi
        simp_rw[mul_assoc]
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.Integrable.const_mul
        apply BoundedCompactSupport.integrable
        apply BoundedCompactSupport.restrict
        apply BoundedCompactSupport.mul bcs_walsh bcs_walsh
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    simp_rw[mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul bcs_walsh bcs_walsh







theorem bighelpextra1 {M k k' : ℕ} (hk : k ≤ 2 ^ M - 1) (h0 : k = k') : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k' j = 1 := by
  rw[h0, ← wlashhaar_norm hk]
  have hf (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), walsh j x * coef M k j = walshhaar M k x :=by
    apply congrFun ((walshindicatorrightform (M := M) (k := k)).choose_spec) x
  have hr : ∫ (y : ℝ) in Ico 0 1, walshhaar M k y * walshhaar M k y = ∫ (y : ℝ) in Ico 0 1,  (∑ j ∈ Finset.range (2 ^ M), (walsh j y * coef M k j)) * (∑ j ∈ Finset.range (2 ^ M), (walsh j y * coef M k j)) := by
    congr
    ext y
    rw[hf y]
  rw[hr]
  simp_rw [@Finset.sum_mul_sum, ← mul_assoc, mul_comm, ← mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr
    · simp
    · intro j hj
      rw[MeasureTheory.integral_finset_sum]
      · conv_lhs => rw[← mul_one (a:= coef M k' j * coef M k' j), ← walsh_norm' j, ← h0, ← MeasureTheory.integral_const_mul, ← zero_add (a:= ∫ (a : ℝ) in Ico 0 1, coef M k j * coef M k j * (walsh j a * walsh j a))]
        rw[Finset.sum_eq_sum_diff_singleton_add hj fun x ↦
              ∫ (a : ℝ) in Ico 0 1, coef M k x * coef M k j * walsh j a * walsh x a]
        congr
        · rw[eq_comm ]
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hm
          have (i : ℕ): ∫ (a : ℝ) in Ico 0 1, coef M k i * coef M k j * walsh j a * walsh i a = coef M k i * coef M k j * ∫ (a : ℝ) in Ico 0 1, walsh j a * walsh i a := by
            rw[← MeasureTheory.integral_const_mul]
            congr
            ext a
            rw[← mul_assoc]
          rw[this]
          rw[walsh_ort]
          · simp
          · simp only [ne_eq]
            exact  hm.2
        · ext y
          rw[← mul_assoc]
      · intro i hi
        simp_rw[mul_assoc]
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.Integrable.const_mul
        apply BoundedCompactSupport.integrable
        apply BoundedCompactSupport.restrict
        apply BoundedCompactSupport.mul bcs_walsh bcs_walsh
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    simp_rw[mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul bcs_walsh bcs_walsh


theorem bighelpextra1' {M k : ℕ} (hk : k ≤ 2 ^ M - 1) : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k j = 1 := by
  exact bighelpextra1 hk rfl






theorem aboutwalshhelp {M n k : ℕ} {x : ℝ} (hn : n < 2 ^ M) (hk : k < 2 ^ M) (hx : x ∈ dyadicInterval (-M : ℤ) k) : (2^(-M :ℤ )) * walsh n x = ∫ (y : ℝ) in Ico (2^(-M :ℤ ) * k :ℝ ) (2^(-M :ℤ ) * (k+1) :ℝ ) , walsh n y := by
  obtain  hp :=  (walshonint ( M := M ) ( n := n ) ( k := k) hn hk).choose_spec
  set p := (walshonint ( M := M ) ( n := n ) ( k := k) hn hk).choose with hp1
  apply hp at hx
  rw[hx]
  have h : ∫ (y : ℝ) in Ico (2 ^ (-M :ℤ ) * k :ℝ ) (2 ^ (-M :ℤ ) * (↑k + 1)), walsh n y = ∫ (y : ℝ) in Ico (2 ^ (-M :ℤ ) * k :ℝ ) (2 ^ (-M :ℤ ) * (k + 1)), p := by
    refine setIntegral_congr_fun measurableSet_Ico hp
  rw[h]
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
    Real.volume_real_Ico, smul_eq_mul, mul_eq_mul_right_iff]
  ring_nf
  simp







theorem aboutwalsh {M n k : ℕ} {x : ℝ} (hn : n < 2 ^ M) (hk : k < 2 ^ M) (hx : x ∈ dyadicInterval (-M : ℤ) k) : walsh n x = coef M k n  * (2 ^ ((M:ℝ )/2)) := by
  rw[← mul_right_inj' (a := (2^(-M :ℤ )) ) ]
  · rw[aboutwalshhelp hn hk hx]
    rw[notsobasiccoef]
    · rw[← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
      simp_rw[mul_comm, ← mul_assoc]
      rw[← MeasureTheory.integral_indicator (measurableSet_Ico), ← MeasureTheory.integral_indicator (measurableSet_Ico)]
      congr
      ext x
      simp only [indicator, zpow_neg, zpow_natCast, mem_Ico]
      split_ifs with h1 h2 h3
      · rw[walshhaarprop ?_ h2.1 h2.2]
        · simp only [indicator, zpow_neg, zpow_natCast, mem_Ico, Pi.pow_apply, Pi.ofNat_apply,
          mul_ite, mul_zero]
          split_ifs with h4
          · rw[← mul_comm]
            conv_lhs => rw[← one_mul (a:= walsh n x)]
            rw [← mul_assoc, @mul_eq_mul_right_iff]
            left
            rw[mul_comm, mul_assoc, ←  Real.rpow_add (zero_lt_two)]
            simp
          · simp_rw[mul_comm] at h4
            exact False.elim (h4 h1)
        · simp only [Finset.mem_range]
          exact hk
      · rw[Decidable.not_and_iff_or_not, not_le, not_lt, ← ge_iff_le] at h2
        rw[walsh_zero_outside_domain n x h2]
      · rw[walshhaarprop ?_ h3.1 h3.2]
        · simp only [indicator]
          rw[mul_assoc]
          simp only [zpow_neg, zpow_natCast, mem_Ico, Pi.pow_apply, Pi.ofNat_apply, mul_ite,
            mul_zero, right_eq_ite_iff, zero_eq_mul, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff',
            OfNat.ofNat_ne_zero, ne_eq, false_and, false_or, and_imp]
          intro hh1 hh2
          rw[mul_comm] at hh1
          rw[mul_comm] at hh2
          exfalso
          exact  h1 ⟨hh1, hh2⟩
        · simp only [Finset.mem_range]
          exact hk
      · simp
    · simp only [Finset.mem_range]
      exact hn
  · simp



theorem ayayayhelp {M n k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) (hx : x ∈ dyadicInterval (-M : ℤ) k) :  ∑ l ∈ Finset.range (2^M), coef M l n  * walshhaar M l x = coef M k n  * walshhaar M k x := by
  rw[Finset.sum_eq_sum_diff_singleton_add hk fun x_1 ↦ coef M x_1 n * walshhaar M x_1 x]
  simp only [add_eq_right]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [Finset.mem_range] at hk
  rw[walshhaarprop (Finset.sdiff_subset hl) (ago hk hx).1 (ago hk hx).2]
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, indicator_apply_eq_zero, mem_Ico, Pi.pow_apply,
    Pi.ofNat_apply]
  right
  intro h
  have h1 : x ∈ dyadicInterval (-↑M) l := by
      simp only [dyadicInterval, zpow_neg, zpow_natCast, Int.cast_natCast, mem_setOf_eq]
      exact h
  have h2 : dyadicInterval  (-↑M) ↑l ∩ dyadicInterval  (-↑M) k = ∅ := by
      apply dyadicInterval_disjoint
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hl
      rw [@Ne.eq_def]
      norm_cast
      exact hl.2
  exfalso
  rw[← Set.disjoint_iff_inter_eq_empty ] at h2
  apply Disjoint.notMem_of_mem_left h2 h1 hx



theorem ayayay {M n : ℕ} (hn : n < 2 ^ M) : (fun x ↦ walsh n x) = (fun x↦ ∑ k ∈ Finset.range (2^M), coef M k n  * walshhaar M k x) := by
  ext x
  by_cases hx : x<0 ∨  x ≥ 1
  · rw[walsh_zero_outside_domain n x hx]
    rw[Finset.sum_eq_zero]
    intro k hk
    rw[notsobasiccoef]
    · simp only [mul_eq_zero]
      right
      unfold walshhaar
      simp only [mul_eq_zero]
      left
      rw[walsh_zero_outside_domain (2 ^ M) x hx]
    · simp only [Finset.mem_range]
      exact hn
  simp only [ge_iff_le, not_or, not_lt, not_le] at hx
  obtain ⟨  p, hp1, hp2 ⟩  := (extdiin01 hx.1 hx.2  (M := M ) (x := x))
  rw[ayayayhelp (k:= p) hp1 hp2 ]
  simp only [Finset.mem_range] at hp1
  rw[aboutwalsh hn hp1 hp2]
  simp only [mul_eq_mul_left_iff]
  rw[← Finset.mem_range] at hp1
  rw[walshhaarprop hp1 hx.1 hx.2 , indicator]
  rw[intervalform_dyadicInterval ] at hp2
  split_ifs with h1
  · simp
  · exfalso
    exact h1 hp2




theorem bighelpextra0wrr {M k k' : ℕ} (h0 : k ≠ k') (hk : k ∈ Finset.range (2 ^ M)) (hk' : k' ∈ Finset.range (2 ^ M)) : ∑ j ∈ Finset.range (2^M), coef M j k  * coef M j k'  =  0 := by
  rw[← walsh_ort (id (Ne.symm h0))]
  have hf (x : ℝ ) : walsh k x =  ∑ j ∈ Finset.range (2^M), coef M j k  * walshhaar M j x:=by
    simp only [Finset.mem_range] at hk
    apply congrFun (ayayay hk)
  have hg (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M),walshhaar M j x * coef M j k' =  walsh k' x:= by
    simp only [Finset.mem_range] at hk'
    rw[eq_comm]
    simp_rw[mul_comm]
    apply congrFun (ayayay hk')
  have hr : ∫ (y : ℝ) in Ico 0 1, walsh k y * walsh k' y= ∫ (y : ℝ) in Ico 0 1,  ( ∑ j ∈ Finset.range (2^M), coef M j k  * walshhaar M j y) * (∑ j ∈ Finset.range (2 ^ M),walshhaar M j y * coef M j k') := by
    congr
    ext y
    rw[hf y, hg]
  rw[hr]
  simp_rw [@Finset.sum_mul_sum, ← mul_assoc, mul_comm, ← mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr (by simp)
    intro n hn
    rw[MeasureTheory.integral_finset_sum]
    · simp_rw[mul_assoc, MeasureTheory.integral_const_mul, ← mul_assoc]
      rw[Finset.sum_eq_add_sum_diff_singleton hn fun x ↦
              coef M x k' * coef M n k * ∫ (a : ℝ) in Ico 0 1, walshhaar M n a * walshhaar M x a, wlashhaar_norm, mul_comm]
      · simp only [mul_one, left_eq_add]
        apply Finset.sum_eq_zero
        intro p hp
        rw [@mul_eq_zero]
        right
        rw[walshHaar_ort]
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hp
        push_neg at hp
        rw[ne_comm] at hp
        exact hp.2
      · rw[← Nat.lt_iff_le_pred]
        · exact List.mem_range.mp hn
        · exact Nat.two_pow_pos M
    · intro i hi
      simp_rw[mul_assoc (a:= coef M i k' * coef M n k )]
      unfold walshhaar
      apply MeasureTheory.Integrable.const_mul
      apply BoundedCompactSupport.integrable
      apply BoundedCompactSupport.restrict
      apply BoundedCompactSupport.mul
      · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
      · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    have : (fun a ↦ coef M j k' * walshhaar M j a * coef M i k * walshhaar M i a) = (fun a ↦ (coef M j k' * coef M i k) * (walshhaar M j a *walshhaar M i a) ):= by
      ext a
      linarith
    simp_rw[mul_assoc (a:= coef M j k' * coef M i k )]
    unfold walshhaar
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul
    · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
    · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled


theorem bighelpextra1wrr {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)) : ∑ j ∈ Finset.range (2^M), coef M j k  * coef M j k  =  1 := by
  rw[← walsh_norm' k]
  have hf (x : ℝ ) : walsh k x =  ∑ j ∈ Finset.range (2^M), coef M j k  * walshhaar M j x:=by
    simp only [Finset.mem_range] at hk
    apply congrFun (ayayay hk)
  have hr : ∫ (y : ℝ) in Ico 0 1, walsh k y * walsh k y= ∫ (y : ℝ) in Ico 0 1,  ( ∑ j ∈ Finset.range (2^M), coef M j k  * walshhaar M j y) * (∑ j ∈ Finset.range (2 ^ M),walshhaar M j y * coef M j k) := by
    congr
    ext y
    rw[hf y]
    simp only [mul_eq_mul_left_iff]
    left
    congr
    ext y
    rw[mul_comm]
  rw[hr]
  simp_rw [@Finset.sum_mul_sum, ← mul_assoc, mul_comm, ← mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr
    · simp
    · intro n hn
      rw[MeasureTheory.integral_finset_sum]
      · simp_rw[mul_assoc (a:= coef M ?_ k * coef M n k ), MeasureTheory.integral_const_mul]
        rw[Finset.sum_eq_add_sum_diff_singleton hn fun x ↦
              coef M x k * coef M n k * ∫ (a : ℝ) in Ico 0 1, walshhaar M n a * walshhaar M x a]
        rw[wlashhaar_norm, mul_comm]
        · simp only [mul_one, left_eq_add]
          apply Finset.sum_eq_zero
          intro p hp
          rw [@mul_eq_zero]
          right
          rw[walshHaar_ort]
          simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hp
          push_neg at hp
          rw[ne_comm] at hp
          exact hp.2
        · rw[← Nat.lt_iff_le_pred]
          · exact List.mem_range.mp hn
          · exact Nat.two_pow_pos M
      · intro i hi
        simp_rw[ mul_assoc (a:= coef M i k * coef M n k) ]
        unfold walshhaar
        apply MeasureTheory.Integrable.const_mul
        apply BoundedCompactSupport.integrable
        apply BoundedCompactSupport.restrict
        apply BoundedCompactSupport.mul
        · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
        · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    simp_rw[mul_assoc (a:= coef M j k * coef M i k)]
    unfold walshhaar
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul
    · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled
    · apply BoundedCompactSupport.mul bcs_walsh bcs_haarscaled


end Coef
