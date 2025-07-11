import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Carleson.Project.modules.Haar
import Carleson.Project.modules.Walsh
import Carleson.Project.modules.BinaryRepresentationSet
import Carleson.Project.modules.DyadicStructures
import Mathlib.Analysis.InnerProductSpace.Projection


open InnerProductSpace MeasureTheory Set BigOperators
open Function Set
open unitInterval DyadicStructures

noncomputable section


/- ## Kernel-/
namespace Kernel

/--
Kernel function defined using Haar functions and binary representation sets.
-/
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m ∈ BinaryRepresentationSet.binaryRepresentationSet N,
      ∑ n ∈ Finset.range (2 ^ m), (Haar.haarFunctionScaled (-m) n x) * (Haar.haarFunctionScaled (-m) n y)


/--
The kernel function at `N = 0` is constant 1.
-/
theorem kernel_zero (x y : ℝ) : kernel 0 x y = 1 := by
  simp only [kernel, add_eq_left]
  rw[BinaryRepresentationSet.binaryRepresentationSet_zero]
  exact rfl


/--
Kernel function for binary powers `N = 2^m`.
-/
theorem kernel_two_pow (N : ℕ) (x y : ℝ) : kernel (2^N) x y = 1 + ∑ n ∈ Finset.range (2 ^ N),
  (Haar.haarFunctionScaled (-N) n x) * (Haar.haarFunctionScaled (-N) n y) := by
  simp only [kernel, add_right_inj, BinaryRepresentationSet.binaryforpower,Finset.sum_singleton]



end Kernel

namespace Extra
/- **ToDo** : Connect the facts about scaled Haar, Rademacher and Walsh functions with dyadic structures. -/

theorem wlashradhelp0 (n m : ℕ) (h : m ∈ BinaryRepresentationSet.binaryRepresentationSet n) : (m+1) ∈ BinaryRepresentationSet.binaryRepresentationSet (2*n) := by
  rw[BinaryRepresentationSet.mem_binaryRepresentationSet_iff] at h
  rw[BinaryRepresentationSet.mem_binaryRepresentationSet_iff]
  rw[← Nat.testBit_div_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  rw[h]

/--
Relation between Haar function and Walsh functions.
-/

theorem walsh_haar_one (x : ℝ) : Walsh.walsh 1 x  = Haar.haarFunction x := by
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

theorem walshRademacherRelation {n : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) : Walsh.walsh n x = ∏
  m ∈ BinaryRepresentationSet.binaryRepresentationSet n, Haar.rademacherFunction m x := by
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


theorem walshradrelbigger0 {n : ℕ} {x : ℝ} (hn : n > 0) :
  Walsh.walsh n x = ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet n,
    Haar.rademacherFunction m x := by
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
theorem differentwalshRademacherRelation {n : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1): Walsh.walsh (2^n) x = Haar.rademacherFunction n x := by
  rw[walshRademacherRelation, BinaryRepresentationSet.binaryforpower, Finset.prod_singleton]
  · exact hx1
  · exact hx2

/--
Walsh-Rademacher relation.
-/
theorem walshRademacherRelationresult {M N : ℕ} {x : ℝ} (h : M ∈ BinaryRepresentationSet.binaryRepresentationSet N) (hx1 : 0 ≤ x) (hx2 : x < 1) : Walsh.walsh N x = Walsh.walsh (2^M) x * ∏
  m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - (2 ^ M)), Haar.rademacherFunction m x := by
  rw[walshRademacherRelation hx1 hx2,differentwalshRademacherRelation hx1 hx2]
  rw[← BinaryRepresentationSet.remove_bit N M h]
  exact Finset.prod_eq_mul_prod_diff_singleton h fun x_1 ↦ Haar.rademacherFunction x_1 x


--co jak M nie jest w rozwinieciu binarnym N?

/--
Product of two walsh functions
-/


theorem prodofwalshworse {M N k : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hk : k = M ^^^ N) :Walsh.walsh k x = Walsh.walsh M x * Walsh.walsh N x:= by
  rw[BinaryRepresentationSet.differenceofbinaryrepset] at hk
  rw[walshRademacherRelation hx1 hx2,walshRademacherRelation hx1 hx2, walshRademacherRelation hx1 hx2, BinaryRepresentationSet.binaryRepresentationSet_fun_prod2 , ← Finset.prod_union (disjoint_sdiff_sdiff)]
  · rw[hk]
  · intro k
    apply Haar.rad_sqr hx1 hx2




/-theorem prodofwalsh {M N k : ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) : k = M^^^N ↔ Walsh.walsh k x = Walsh.walsh M x * Walsh.walsh N x:= by
  rw[walshRademacherRelation hx1 hx2,walshRademacherRelation hx1 hx2, walshRademacherRelation hx1 hx2, BinaryRepresentationSet.differenceofbinaryrepset, BinaryRepresentationSet.binaryRepresentationSet_fun_prod2 , ← Finset.prod_union (disjoint_sdiff_sdiff)]
  · --nie jestem pewna jak to zrobic - z załozen o funkcji redamachera powiino to jakosc isc ale jak?
    sorry
  · intro k
    apply Haar.rad_sqr hx1 hx2
-/


theorem walsh_int {n : ℕ} (h : n > 0) : ∫ (x : ℝ) in Ico 0 1, Walsh.walsh n x = 0 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h1: Odd n
  · rw[Walsh.intofodd h1]
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
    rw[Walsh.intofeven hl']
    exact ih l hl1 hl2




theorem walsh_ort_dif {n m : ℕ} (h : m ≠ n) : Walsh.walshInnerProduct (Walsh.walsh n) m  = 0 := by
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

theorem walsh_ort {n m : ℕ} (h : m ≠ n) : ∫ (x : ℝ) in Ico 0 1, Walsh.walsh n x * Walsh.walsh m x = 0 := by
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



theorem fun_change_partial_sum (M N : ℕ) (f : ℝ → ℝ) (x : ℝ) : Haar.rademacherFunction M x *(Walsh.walshFourierPartialSum (Haar.rademacherFunction M * f)  N ) x = ∑
  n ∈ Finset.range (N + 1),
  (∫ y in Set.Ico 0 1, (Haar.rademacherFunction M y) * f y * Walsh.walsh n y) *
      Haar.rademacherFunction M x *
    Walsh.walsh n x  := by
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
def walshhaar (M k : ℕ) : ℝ → ℝ
| x =>
  Walsh.walsh (2^M) x * (Haar.haarFunctionScaled (-M) k x)


theorem walshhaarprop {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) (hx1 : 0 ≤ x) (hx2 : x < 1) :  walshhaar M k x = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x:= by
  unfold walshhaar
  simp only
  rw[differentwalshRademacherRelation hx1 hx2]
  simp only [Haar.rademacherFunction]
  have h : (∑ n ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑n) x) *
    Haar.haarFunctionScaled (-↑M) (↑k) x = Haar.haarFunctionScaled (-↑M) (↑k) x *
    Haar.haarFunctionScaled (-↑M) (↑k) x := by
      rw[Finset.sum_mul]
      have : ∑ i ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x = ∑ i ∈ Finset.range (2 ^ M)\ {k}, Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x  +  Haar.haarFunctionScaled (-↑M) (↑k) x * Haar.haarFunctionScaled (-↑M) (↑k) x := by
        exact
          Finset.sum_eq_sum_diff_singleton_add hk fun x_1 ↦
            Haar.haarFunctionScaled (-↑M) (↑x_1) x * Haar.haarFunctionScaled (-↑M) (↑k) x
      rw[this]
      simp only [add_eq_right]
      apply Finset.sum_eq_zero
      intro l hl
      rw[← Haar.haarFunctionScaled_mul (k := -M) (n:= l) (n':= k) (x:= x)]
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hl
      push_neg at hl
      norm_cast
      exact hl.2
  rw[mul_assoc, h, indicator]
  split_ifs with h1
  · rw[← pow_two, Haar.haarFunctionScaled_sqr]
    · simp only [neg_neg, Pi.one_apply]
      simp only [Pi.pow_apply, Pi.ofNat_apply]
      rw[←Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
      congr
      push_cast
      ring
    · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
      simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_nonneg]
      rw[ ← inv_mul_le_iff₀]
      · exact h1.1
      · simp
    · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
      simp only [neg_neg, zpow_natCast, Int.cast_natCast]
      rw[sub_lt_iff_lt_add, add_comm]
      rw[ ← lt_inv_mul_iff₀]
      · exact h1.2
      · simp
  · rw[Haar.haarFunctionScaled_outside]
    · simp
    · simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
      simp only [zpow_neg, zpow_natCast, mem_Ico, Decidable.not_and_iff_or_not] at h1
      simp only [not_le, not_lt] at h1
      rw[ ← lt_inv_mul_iff₀]
      · rw[inv_mul_le_iff₀] at h1
        · rw[le_sub_iff_add_le, add_comm]
          exact h1
        · simp
      · simp


theorem walshhaarprop' {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) :  walshhaar M k x = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x:= by
  unfold walshhaar
  simp only
  by_cases hx : x< 0 ∨  1≤ x
  · rw[Walsh.walsh_not_in x hx ]
    simp only [zero_mul, zpow_neg, zpow_natCast]
    unfold indicator
    split_ifs with h1
    · exfalso
      simp only [mem_Ico] at h1
      obtain ⟨ h11, h12⟩ := h1
      rcases hx with hx|hx
      · have : 0 ≤ ((2 ^ M)⁻¹:ℝ ) * ↑k := by
          simp
        apply le_trans this at h11
        linarith
      · have : ((2 ^ M)⁻¹:ℝ ) * (↑k + 1) ≤  1 := by
          simp only [Finset.mem_range] at hk
          apply Nat.add_one_le_of_lt at hk
          have : ((2 ^ M)⁻¹ :ℝ ) * (↑k + 1) ≤  (2 ^ M)⁻¹*  (2 ^ M) := by
            refine (mul_le_mul_left ?_).mpr ?_
            · simp
            · norm_cast
          refine inv_mul_le_one_of_le₀ ?_ ?_
          · norm_cast
          · simp
        apply le_trans this at hx
        linarith
    · simp
  · push_neg at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    rw[differentwalshRademacherRelation hx1 hx2, Haar.rademacherFunction]
    have h : (∑ n ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑n) x) *
      Haar.haarFunctionScaled (-↑M) (↑k) x = Haar.haarFunctionScaled (-↑M) (↑k) x *
      Haar.haarFunctionScaled (-↑M) (↑k) x := by
        rw[Finset.sum_mul]
        have : ∑ i ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x = ∑ i ∈ Finset.range (2 ^ M)\ {k}, Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x  +  Haar.haarFunctionScaled (-↑M) (↑k) x * Haar.haarFunctionScaled (-↑M) (↑k) x := by
          exact
            Finset.sum_eq_sum_diff_singleton_add hk fun x_1 ↦
              Haar.haarFunctionScaled (-↑M) (↑x_1) x * Haar.haarFunctionScaled (-↑M) (↑k) x
        rw[this]
        simp only [add_eq_right]
        apply Finset.sum_eq_zero
        intro l hl
        rw[← Haar.haarFunctionScaled_mul (k := -M) (n:= l) (n':= k) (x:= x)]
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hl
        push_neg at hl
        norm_cast
        exact hl.2
    rw[mul_assoc, h, indicator]
    split_ifs with h1
    · rw[← pow_two, Haar.haarFunctionScaled_sqr]
      · simp only [neg_neg, Pi.one_apply]
        simp only [Pi.pow_apply, Pi.ofNat_apply]
        rw[←Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
        congr
        push_cast
        ring
      · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
        simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_nonneg]
        rw[ ← inv_mul_le_iff₀]
        · exact h1.1
        · simp
      · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
        simp only [neg_neg, zpow_natCast, Int.cast_natCast]
        rw[sub_lt_iff_lt_add, add_comm, ← lt_inv_mul_iff₀]
        · exact h1.2
        · simp
    · rw[Haar.haarFunctionScaled_outside]
      · simp
      · simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
        simp only [zpow_neg, zpow_natCast, mem_Ico, Decidable.not_and_iff_or_not, not_le, not_lt] at h1
        rw[ ← lt_inv_mul_iff₀]
        · rw[inv_mul_le_iff₀] at h1
          · rw[le_sub_iff_add_le, add_comm]
            exact h1
          · simp
        · simp

theorem walshhaarprop'' {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)) : (fun x ↦   walshhaar M k x) =(fun x ↦  (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x):= by
  unfold walshhaar
  simp only
  ext x
  by_cases hx : x< 0 ∨  1≤ x
  · rw[Walsh.walsh_not_in x hx ]
    simp only [zero_mul, zpow_neg, zpow_natCast]
    unfold indicator
    split_ifs with h1
    · exfalso
      simp only [mem_Ico] at h1
      obtain ⟨ h11, h12⟩ := h1
      rcases hx with hx|hx
      · have : 0 ≤ ((2 ^ M)⁻¹:ℝ ) * ↑k := by
          simp
        apply le_trans this at h11
        linarith
      · have : ((2 ^ M)⁻¹:ℝ ) * (↑k + 1) ≤  1 := by
          simp only [Finset.mem_range] at hk
          apply Nat.add_one_le_of_lt at hk
          have : ((2 ^ M)⁻¹ :ℝ ) * (↑k + 1) ≤  (2 ^ M)⁻¹*  (2 ^ M) := by
            refine (mul_le_mul_left ?_).mpr ?_
            · simp
            · norm_cast
          refine inv_mul_le_one_of_le₀ ?_ ?_
          · norm_cast
          · simp
        apply le_trans this at hx
        linarith
    · simp
  · push_neg at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    rw[differentwalshRademacherRelation hx1 hx2, Haar.rademacherFunction]
    have h : (∑ n ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑n) x) *
      Haar.haarFunctionScaled (-↑M) (↑k) x = Haar.haarFunctionScaled (-↑M) (↑k) x *
      Haar.haarFunctionScaled (-↑M) (↑k) x := by
        rw[Finset.sum_mul]
        have : ∑ i ∈ Finset.range (2 ^ M), Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x = ∑ i ∈ Finset.range (2 ^ M)\ {k}, Haar.haarFunctionScaled (-↑M) (↑i) x * Haar.haarFunctionScaled (-↑M) (↑k) x  +  Haar.haarFunctionScaled (-↑M) (↑k) x * Haar.haarFunctionScaled (-↑M) (↑k) x := by
          exact
            Finset.sum_eq_sum_diff_singleton_add hk fun x_1 ↦
              Haar.haarFunctionScaled (-↑M) (↑x_1) x * Haar.haarFunctionScaled (-↑M) (↑k) x
        rw[this]
        simp only [add_eq_right]
        apply Finset.sum_eq_zero
        intro l hl
        rw[← Haar.haarFunctionScaled_mul (k := -M) (n:= l) (n':= k) (x:= x)]
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hl
        push_neg at hl
        norm_cast
        exact hl.2
    rw[mul_assoc, h, indicator]
    split_ifs with h1
    · rw[← pow_two, Haar.haarFunctionScaled_sqr]
      · simp only [neg_neg, Pi.one_apply]
        simp only [Pi.pow_apply, Pi.ofNat_apply]
        rw[←Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
        congr
        push_cast
        ring
      · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
        simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_nonneg]
        rw[ ← inv_mul_le_iff₀]
        · exact h1.1
        · simp
      · simp only [zpow_neg, zpow_natCast, mem_Ico] at h1
        simp only [neg_neg, zpow_natCast, Int.cast_natCast]
        rw[sub_lt_iff_lt_add, add_comm, ← lt_inv_mul_iff₀]
        · exact h1.2
        · simp
    · rw[Haar.haarFunctionScaled_outside]
      · simp
      · simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
        simp only [zpow_neg, zpow_natCast, mem_Ico, Decidable.not_and_iff_or_not, not_le, not_lt] at h1
        rw[ ← lt_inv_mul_iff₀]
        · rw[inv_mul_le_iff₀] at h1
          · rw[le_sub_iff_add_le, add_comm]
            exact h1
          · simp
        · simp

theorem walshhaarpropsqr {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) (hx1 : 0 ≤ x) (hx2 : x < 1) :  (walshhaar M k x)*(walshhaar M k x) = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M :ℝ  )) x:= by
  rw[walshhaarprop hk hx1 hx2]
  rw[indicator, indicator]
  simp only [zpow_neg, zpow_natCast, mem_Ico, Pi.pow_apply, Pi.ofNat_apply, mul_ite, ite_mul,
    zero_mul, mul_zero]
  by_cases h : (2 ^ M)⁻¹ * ↑k ≤ x ∧ x < (2 ^ M)⁻¹ * (↑k + 1)
  · simp only [h, and_self, ↓reduceIte]
    rw[ ← Real.rpow_add (by norm_num)]
    simp
  · simp[h]

theorem walshhaarsqr' {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)) :  (walshhaar M k)*(walshhaar M k ) = (2 ^ (M / 2 : ℝ))* walshhaar M k := by


  sorry



--był bład w definicji walshhaar - UWAZAJ!

theorem walshHaar_ort_help {M k k' : ℕ} {x : ℝ} (h : k ≠ k'):  walshhaar M k x * walshhaar M k' x = 0 := by
  unfold walshhaar
  rw[mul_comm]
  rw [@mul_mul_mul_comm]
  rw[Haar.haarFunctionScaled_mul ]
  · simp only [mul_zero]
  · simp only [ne_eq, Nat.cast_inj]
    rw[ne_comm, ne_eq] at h
    exact h



theorem walshHaar_ort {M k k' : ℕ} (h : k ≠ k'):  ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k' y = 0 := by
  have h1 : EqOn (walshhaar M k * walshhaar M k') 0 (Set.Ico 0 1) := by
    unfold EqOn
    intro z hz
    apply walshHaar_ort_help h
  have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
    simp
  simp_rw[← Pi.mul_apply]
  rw[MeasureTheory.setIntegral_congr_fun h2 h1]
  simp

--w def walshhaar musi być dodatkowy warunek na k

theorem walshhaar_s {M k : ℕ} :  (∫ x in Set.Ico  0 0.5,  walshhaar M k x) + ∫ x in Set.Ico 0.5 1,  walshhaar M k x = ∫ x in Set.Ico 0 1, walshhaar M k x  := by
  have : (Set.Ico 0 (1 :ℝ )) = (Set.Ico 0 0.5) ∪ (Set.Ico 0.5 1) := by
    refine Eq.symm (Ico_union_Ico_eq_Ico ?_ ?_)
    · linarith
    · linarith
  simp_rw[this]
  rw[MeasureTheory.integral_union_ae]
  · refine Disjoint.aedisjoint ?_
    simp
  · simp
  · unfold walshhaar
    simp only
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · refine MeasureTheory.BoundedCompactSupport.restrict ?_
      exact Walsh.bcs_walsh
    · apply MeasureTheory.BoundedCompactSupport.integrable
      refine MeasureTheory.BoundedCompactSupport.restrict ?_
      exact Haar.bcs_haarscaled
  · unfold walshhaar
    simp only
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · refine MeasureTheory.BoundedCompactSupport.restrict ?_
      exact Walsh.bcs_walsh
    · apply MeasureTheory.BoundedCompactSupport.integrable
      refine MeasureTheory.BoundedCompactSupport.restrict ?_
      exact Haar.bcs_haarscaled



theorem wlashhaar_norm {M k : ℕ} (hk : k ≤ 2 ^ M - 1): ∫ y in Set.Ico 0 1, (walshhaar M k y)*(walshhaar M k y)  = 1 := by
  rw[← MeasureTheory.integral_indicator (measurableSet_Ico)]
  have h1: ∫ (x : ℝ), (Ico 0 1).indicator (fun y ↦ walshhaar M k y * walshhaar M k y) x = ∫ (x : ℝ), (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M :ℝ  )) x := by
    congr
    ext x
    conv_lhs => simp[indicator]
    split_ifs with h
    · rw[walshhaarpropsqr ?_ h.1 h.2]
      simp only [Finset.mem_range]
      rw[Nat.lt_iff_le_pred ]
      · exact hk
      · simp
    · simp only [indicator]
      split_ifs with h0
      · exfalso
        simp only [zpow_neg, zpow_natCast, mem_Ico] at h0
        have h01 : 0 ≤ ((2 ^ M)⁻¹: ℝ ) * ↑k := by
          rw [@mul_nonneg_iff]
          left
          constructor
          · linarith
          · linarith
        have h02 : ((2 ^ M)⁻¹: ℝ ) * (↑k + 1) ≤ 1 := by
          refine inv_mul_le_one_of_le₀ ?_ ?_
          · norm_cast
            refine Nat.add_le_of_le_sub ?_ hk
            exact Nat.one_le_two_pow
          · simp
        obtain ⟨ h0_01, h0_02⟩ := h0
        apply lt_of_lt_of_le h0_02 at h02
        apply le_trans h01 at h0_01
        push_neg at h
        simp[h0_01] at h
        linarith
      · simp
  rw[h1]
  rw[ MeasureTheory.integral_indicator (measurableSet_Ico)]
  simp only [zpow_neg, zpow_natCast, Pi.pow_apply, Pi.ofNat_apply, Real.rpow_natCast,
    MeasureTheory.integral_const, MeasurableSet.univ, MeasureTheory.measureReal_restrict_apply,
    univ_inter, Real.volume_real_Ico, smul_eq_mul]
  have : ((2 ^ M)⁻¹ : ℝ )* (↑k + 1) - (2 ^ M)⁻¹ * ↑k = (2 ^ M)⁻¹ := by
    linarith
  simp_rw[this]
  simp

--chyba powinno byc inaczej - powinno być dla wszystkich x zamiast na początku podany x
theorem walshindicatorrightform {M k : ℕ} {x : ℝ} (hk : k < 2 ^ M): ∃ (f:ℕ  → ℝ), ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j )= walshhaar M k x:= by
  rw[walshhaarprop']
  · have : (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator ((2 : ℝ → ℝ) ^ ((M : ℝ) / 2)) x = ((2 : ℝ) ^ ((M : ℝ) / 2)) * (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator 1 x := by
      simp[indicator]
    rw[this]
    have hp : ∃ (f:ℕ  → ℝ), ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j )= (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x := by
      exact Walsh.walshindicator hk
    obtain ⟨ g, hg⟩ := hp
    simp_rw[mul_comm]
    rw[← hg]
    rw[mul_comm, Finset.sum_mul]
    use g * 2 ^ (M / 2 :ℝ )
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply]
    congr
    ext i
    linarith
  · simp only [Finset.mem_range]
    exact hk

theorem walshindicatorrightform' {M k : ℕ} {x : ℝ}: ∃ (f:ℕ  → ℝ), ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j )= walshhaar M k x:= by
  by_cases hk : k < 2 ^ M
  · rw[walshhaarprop']
    · have : (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator ((2 : ℝ → ℝ) ^ ((M : ℝ) / 2)) x = ((2 : ℝ) ^ ((M : ℝ) / 2)) * (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator 1 x := by
        simp[indicator]
      rw[this]
      have hp : ∃ (f:ℕ  → ℝ), ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j )= (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x := by
        exact Walsh.walshindicator hk
      obtain ⟨ g, hg⟩ := hp
      simp_rw[mul_comm]
      rw[← hg]
      rw[mul_comm, Finset.sum_mul]
      use g * 2 ^ (M / 2 :ℝ )
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply]
      congr
      ext i
      linarith
    · simp only [Finset.mem_range]
      exact hk
  · use 0
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    simp only [walshhaar, zero_eq_mul]
    by_cases h : Walsh.walsh (2 ^ M) x = 0
    · left
      exact h
    · right
      apply Walsh.domain at h
      rw[Haar.haarFunctionScaled_outside]
      simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
      left
      simp only [not_lt] at hk
      have : 2 ^ M * x < 2^M := by
        norm_num
        exact h.2
      apply lt_of_lt_of_le this
      norm_cast


theorem walshindicatorrightform1 {M k : ℕ}: ∃ (f:ℕ  → ℝ), (fun x ↦ ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j ))= (fun x ↦walshhaar M k x):= by
  by_cases hk : k < 2 ^ M
  · rw[walshhaarprop'']
    · have : (fun x↦ (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator ((2 : ℝ → ℝ) ^ ((M : ℝ) / 2)) x) = (fun x ↦ ((2 : ℝ) ^ ((M : ℝ) / 2)) * (Ico (2 ^ (-↑M :ℤ ) * ↑k :ℝ ) (2 ^ (-↑M :ℤ ) * (↑k + 1))).indicator 1 x ):= by
        simp[indicator]
      rw[this]
      have hp : ∃ (f:ℕ  → ℝ),(fun x ↦ ∑ j ∈ Finset.range (2^M), (Walsh.walsh j x  * f j ))= (fun x ↦ (Ico (k * 2 ^ (-M :ℤ )  : ℝ ) ((k+1)* 2 ^ (-M : ℤ )  : ℝ ) ).indicator 1 x ):= by
        exact Walsh.walshindicator' hk
      obtain ⟨ g, hg⟩ := hp
      use g * 2 ^ (M / 2 :ℝ )
      ext x
      have h_p := congrFun hg x
      simp_rw[mul_comm]
      rw[← h_p]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply]
      rw[mul_comm, Finset.sum_mul]
      congr
      ext i
      linarith
    · simp only [Finset.mem_range]
      exact hk
  · use 0
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    simp only [walshhaar, zero_eq_mul]
    ext x
    simp only [zero_eq_mul]
    by_cases h : Walsh.walsh (2 ^ M) x = 0
    · left
      exact h
    · right
      apply Walsh.domain at h
      rw[Haar.haarFunctionScaled_outside]
      simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
      left
      simp only [not_lt] at hk
      have : 2 ^ M * x < 2^M := by
        norm_num
        exact h.2
      apply lt_of_lt_of_le this
      norm_cast

def coef (M k : ℕ) : ℕ → ℝ :=
  (walshindicatorrightform1 (M := M) (k := k)).choose


theorem basiccoef (M k : ℕ) {x : ℝ} : ∑ j ∈ Finset.range (2 ^ M),  Walsh.walsh j x * coef M k j = walshhaar M k x := by
  apply congrFun ((walshindicatorrightform1 (M := M) (k := k)).choose_spec) x


theorem notsobasiccoef (M k j : ℕ) (hj : j ∈ Finset.range (2 ^ M)): coef M k j = ∫ y in Set.Ico 0 1, walshhaar M k y * Walsh.walsh j y := by
  simp_rw[← basiccoef, Finset.sum_mul, mul_assoc, mul_comm, mul_assoc]
  rw[MeasureTheory.integral_finset_sum]
  · simp_rw[MeasureTheory.integral_const_mul]
    have : ∑ x ∈ Finset.range (2 ^ M), coef M k x * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh x a = (∑ x ∈ Finset.range (2 ^ M) \{j}, coef M k x * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh x a ) + coef M k j * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh j a := by
      exact
        Finset.sum_eq_sum_diff_singleton_add hj fun x ↦
          coef M k x * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh x a
    rw[this, Walsh.walsh_norm']
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
    apply BoundedCompactSupport.mul
    · exact Walsh.bcs_walsh
    · exact Walsh.bcs_walsh





theorem bighelpextra0 {M k k' : ℕ} (h0 : k ≠ k') : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k' j = 0 := by
  have h: ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k' y = 0 := by
    refine walshHaar_ort h0
  rw[← h]
  have hf (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh j x * coef M k j = walshhaar M k x :=by
    apply congrFun ((walshindicatorrightform1 (M := M) (k := k)).choose_spec) x
  have hg (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh j x * coef M k' j = walshhaar M k' x := by
    apply congrFun ((walshindicatorrightform1 (M := M) (k := k')).choose_spec) x
  have hr : ∫ (y : ℝ) in Ico 0 1, walshhaar M k y * walshhaar M k' y = ∫ (y : ℝ) in Ico 0 1,  (∑ j ∈ Finset.range (2 ^ M), (Walsh.walsh j y * coef M k j)) * (∑ j ∈ Finset.range (2 ^ M), (Walsh.walsh j y * coef M k' j)) := by
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
      · have (i : ℕ): ∫ (a : ℝ) in Ico 0 1, coef M k' i * coef M k n * Walsh.walsh n a * Walsh.walsh i a= coef M k' i * coef M k n * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh n a * Walsh.walsh i a := by
          rw[← MeasureTheory.integral_const_mul]
          congr
          ext a
          rw[← mul_assoc]
        simp_rw[this]
        have : ∑ x ∈ Finset.range (2 ^ M), coef M k' x * coef M k n * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh n a * Walsh.walsh x a =(coef M k' n * coef M k n * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh n a * Walsh.walsh n a) +  ∑ x ∈ Finset.range (2 ^ M) \ {n}, coef M k' x * coef M k n * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh n a * Walsh.walsh x a   := by
          exact
            Finset.sum_eq_add_sum_diff_singleton hn fun x ↦
              coef M k' x * coef M k n * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh n a * Walsh.walsh x a
        rw[this]
        rw[Walsh.walsh_norm' n, mul_comm]
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
        simp at hi
        simp_rw[mul_assoc]
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.Integrable.const_mul
        apply BoundedCompactSupport.integrable
        apply BoundedCompactSupport.restrict
        apply BoundedCompactSupport.mul
        · exact Walsh.bcs_walsh
        · exact Walsh.bcs_walsh
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    simp_rw[mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul
    · exact Walsh.bcs_walsh
    · exact Walsh.bcs_walsh


-- ajaj potrzeba nowego twierdzenia!!

/-  have h (x :ℝ ): (∑ j ∈ Finset.range (2^M), walshhaar M j x)*  (∑ j ∈ Finset.range (2^M), walshhaar M j x) = 2 ^ ((M :ℝ) / 2) * (∑ j ∈ Finset.range (2^M), walshhaar M j x) := by
    rw[Finset.sum_mul_sum ]
    conv_rhs => rw[mul_comm, Finset.sum_mul]
    apply Finset.sum_congr
    · simp
    · intro i hi
      have : ∑ x_1 ∈ Finset.range (2 ^ M), walshhaar M i x * walshhaar M x_1 x = (∑ x_1 ∈ Finset.range (2 ^ M) \{i}, walshhaar M i x * walshhaar M x_1 x) +  (walshhaar M i  * walshhaar M i) x:= by
        exact Finset.sum_eq_sum_diff_singleton_add hi fun x_1 ↦ walshhaar M i x * walshhaar M x_1 x
      rw[this, walshhaarsqr' hi, mul_comm]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, add_eq_right]
      apply Finset.sum_eq_zero
      intro j hj
      apply walshHaar_ort_help (M:= M)
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hj
      rw[ne_eq, eq_comm]
      exact hj.2-/






 /-have h : ∫ (x : ℝ) in Ico 0 1, (∑ j ∈ Finset.range (2 ^ M),  Walsh.walsh j x * coef M k j)*(∑ j ∈ Finset.range (2 ^ M),  Walsh.walsh j x * coef M k' j) = 0 := by
    conv_rhs => rw[← walshHaar_ort h0 (M := M)]
    simp_rw[basiccoef]
  simp_rw[@Finset.sum_mul_sum] at h
  have h1 : ∫ (x : ℝ) in Ico 0 1,
    ∑ i ∈ Finset.range (2 ^ M),
      ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh i x * coef M k i * (Walsh.walsh j x * coef M k' j) =
    ∑ i ∈ Finset.range (2 ^ M),
      ∑ j ∈ Finset.range (2 ^ M),( ∫ (x : ℝ) in Ico 0 1, Walsh.walsh i x * Walsh.walsh j x) * coef M k i * coef M k' j:= by
      rw[MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr
        · simp
        · intro i hi
          rw[MeasureTheory.integral_finset_sum]
          · simp_rw[← MeasureTheory.integral_mul_const, ← mul_assoc]
            congr
            ext x
            congr
            ext a
            linarith
          · sorry
      · sorry
  rw[h1] at h
  rw[← h]
  rw[Finset.sum_congr]
  · simp
  · intro i hi

--kurdebele-/




theorem bighelpextra1 {M k k' : ℕ} (hk : k ≤ 2 ^ M - 1) (h0 : k = k') : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k' j = 1 := by
  rw[h0]
  have h: ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k y = 1:= by
    apply wlashhaar_norm hk
  rw[← h]
  have hf (x : ℝ ) : ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh j x * coef M k j = walshhaar M k x :=by
    apply congrFun ((walshindicatorrightform1 (M := M) (k := k)).choose_spec) x
  have hr : ∫ (y : ℝ) in Ico 0 1, walshhaar M k y * walshhaar M k y = ∫ (y : ℝ) in Ico 0 1,  (∑ j ∈ Finset.range (2 ^ M), (Walsh.walsh j y * coef M k j)) * (∑ j ∈ Finset.range (2 ^ M), (Walsh.walsh j y * coef M k j)) := by
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
      · have : ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh j a = 1 := by
          exact Walsh.walsh_norm' j
        conv_lhs => rw[← mul_one (a:= coef M k' j * coef M k' j), ← this, ← h0, ← MeasureTheory.integral_const_mul, ← zero_add (a:= ∫ (a : ℝ) in Ico 0 1, coef M k j * coef M k j * (Walsh.walsh j a * Walsh.walsh j a))]
        have : ∑ i ∈ Finset.range (2 ^ M), ∫ (a : ℝ) in Ico 0 1, coef M k i * coef M k j * Walsh.walsh j a * Walsh.walsh i a = (∑ i ∈ Finset.range (2 ^ M) \ {j}, ∫ (a : ℝ) in Ico 0 1, coef M k i * coef M k j * Walsh.walsh j a * Walsh.walsh i a ) + ∫ (a : ℝ) in Ico 0 1, coef M k j * coef M k j * Walsh.walsh j a * Walsh.walsh j a:= by
          exact
            Finset.sum_eq_sum_diff_singleton_add hj fun x ↦
              ∫ (a : ℝ) in Ico 0 1, coef M k x * coef M k j * Walsh.walsh j a * Walsh.walsh x a
        rw[this]
        congr
        · rw[eq_comm ]
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hm
          have (i : ℕ): ∫ (a : ℝ) in Ico 0 1, coef M k i * coef M k j * Walsh.walsh j a * Walsh.walsh i a = coef M k i * coef M k j * ∫ (a : ℝ) in Ico 0 1, Walsh.walsh j a * Walsh.walsh i a := by
            rw[← MeasureTheory.integral_const_mul]
            congr
            ext a
            rw[← mul_assoc]
          rw[this]
          rw[walsh_ort]
          · simp
          · simp only [ne_eq]
            exact hm.2
        · ext y
          rw[← mul_assoc]
      · intro i hi
        simp at hi
        simp_rw[mul_assoc]
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.Integrable.const_mul
        apply BoundedCompactSupport.integrable
        apply BoundedCompactSupport.restrict
        apply BoundedCompactSupport.mul
        · exact Walsh.bcs_walsh
        · exact Walsh.bcs_walsh
  · intro i hi
    apply MeasureTheory.integrable_finset_sum
    intro j hj
    simp_rw[mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.const_mul
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.mul
    · exact Walsh.bcs_walsh
    · exact Walsh.bcs_walsh

theorem bighelpextra1' {M k : ℕ} (hk : k ≤ 2 ^ M - 1) : ∑ j ∈ Finset.range (2^M), coef M k j * coef M k j = 1 := by
  exact bighelpextra1 hk rfl


--to podobno powinno działać
theorem ayayay {M n : ℕ} (hj : n < 2 ^ M) : (fun x ↦ Walsh.walsh n x) = (fun x↦ ∑ k ∈ Finset.range (2^M), coef M k n  * walshhaar M k x) := by
  ext x
  simp_rw[← basiccoef]
  have : ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh j x * coef M x_1 j =  ∑ j ∈ Finset.range (2 ^ M), Walsh.walsh j x * (∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 j ):= by
    have (j :ℕ ) : Walsh.walsh j x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 j =  ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 j * Walsh.walsh j x := by
      rw[mul_comm, ← Finset.sum_mul]
    simp_rw[this]

    sorry
  rw[this]
  --tak z tego wgl powinno wyjść ze ta suma coef wyjdzie 1 bo te walshe sa ortonormalne wiec no



  sorry

theorem bighelpextra0wrr {M k k' : ℕ} (h0 : k ≠ k') (hk : k ∈ Finset.range (2 ^ M)) (hk' : k' ∈ Finset.range (2 ^ M)) : ∑ j ∈ Finset.range (2^M), coef M j k  * coef M j k'  =  0 := by



  sorry


theorem bighelpextra1wrr {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)): ∑ j ∈ Finset.range (2^M), coef M j k  * coef M j k  =  1 := by sorry


theorem lemma1_1' {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x =
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1,
      f y * walshhaar M k y) * walshhaar M k x:= by
  simp only [Walsh.walshInnerProduct, ← MeasureTheory.integral_mul_const]
  rw[eq_comm]
  rw[ ← MeasureTheory.integral_finset_sum]
  · simp_rw[← basiccoef, Finset.mul_sum, ← mul_assoc , Finset.sum_mul]
    have (a :ℝ): ∑ x_1 ∈ Finset.range (2 ^ M),
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * Walsh.walsh i a * coef M x_1 i * Walsh.walsh x_2 x * coef M x_1 x_2  =
      ∑ x_2 ∈ Finset.range (2 ^ M),
        ∑ i ∈ Finset.range (2 ^ M), f a * Walsh.walsh i a  * Walsh.walsh x_2 x *(∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i) := by
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
    have :
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        (∫ (a : ℝ) in Ico 0 1,f a * Walsh.walsh i a * Walsh.walsh x_2 x )* ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i = ∫ (a : ℝ) in Ico 0 1,
    ∑ x_2 ∈ Finset.range (2 ^ M),
      ∑ i ∈ Finset.range (2 ^ M),
        f a * Walsh.walsh i a * Walsh.walsh x_2 x * ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 x_2 * coef M x_1 i := by sorry
    simp_rw[← this]
    apply Finset.sum_congr
    · simp
    · intro n hn
      have : ∑ i ∈ Finset.range (2 ^ M),
    (∫ (a : ℝ) in Ico 0 1, f a * Walsh.walsh i a * Walsh.walsh n x) *
      ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 i = (∑ i ∈ Finset.range (2 ^ M) \ {n},
    (∫ (a : ℝ) in Ico 0 1, f a * Walsh.walsh i a * Walsh.walsh n x) *
      ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 i) + (∫ (a : ℝ) in Ico 0 1, f a * Walsh.walsh n a * Walsh.walsh n x) *
      ∑ x_1 ∈ Finset.range (2 ^ M), coef M x_1 n * coef M x_1 n := by
        exact
          Finset.sum_eq_sum_diff_singleton_add hn fun x_1 ↦
            (∫ (a : ℝ) in Ico 0 1, f a * Walsh.walsh x_1 a * Walsh.walsh n x) *
              ∑ x_1_1 ∈ Finset.range (2 ^ M), coef M x_1_1 n * coef M x_1_1 x_1
      rw[this, bighelpextra1wrr (M:= M) hn]
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


    sorry





theorem lemma1_1 {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1)))(x : ℝ) :
  ∑ i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x =
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1,
      f y * Walsh.walsh (2 ^ M) y * (Haar.haarFunctionScaled (-M) k y) * Walsh.walsh (2 ^ M) x *
        (Haar.haarFunctionScaled (-M) k x)):= by
  rw[lemma1_1' h1 h2 f hf']
  congr
  ext k
  rw[← MeasureTheory.integral_mul_const]
  congr
  ext y
  simp_rw[walshhaar, ← mul_assoc]






/--
Lemma 2
-/


theorem lemma1_2helphelp {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (x y : ℝ) (hy1 : 0 ≤ y) (hy2 : y < 1) (hx1 : 0 ≤ x) (hx2 : x < 1) : ∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m y) *
      Haar.haarFunctionScaled (-↑M) (↑i) y *
           ( ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m x) *
          Haar.haarFunctionScaled (-↑M) (↑i) x = ∑ i ∈ Finset.range (2 ^ M),
      (Haar.haarFunctionScaled (-↑M) (↑i) y *  Haar.haarFunctionScaled (-↑M) (↑i) x) := by
      apply Finset.sum_congr
      · simp
      · intro k hk
        have : ((∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m y) *
        Haar.haarFunctionScaled (-↑M) (↑k) y *
      ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m x) *
    Haar.haarFunctionScaled (-↑M) (↑k) x= ((∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m y) *
      ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m x) *
    (Haar.haarFunctionScaled (-↑M) (↑k) y * Haar.haarFunctionScaled (-↑M) (↑k) x ):= by
          linarith

        rw[this]
        conv_rhs => rw[← one_mul (a:= Haar.haarFunctionScaled (-↑M) (↑k) y), mul_assoc]
        simp only [mul_eq_mul_right_iff]
        by_cases h : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1) ∨ ( 2 ^ (M : ℤ ) * y - k < 0 ∨ 2 ^ (M : ℤ ) * y - k ≥ 1)
        · right
          simp only [mul_eq_zero]
          by_cases h_1 : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1)
          · rw[Haar.haarFunctionScaled_outside (-M) k x ?_]
            · right
              simp
            · simp only [neg_neg]
              exact h_1
          · rw[or_iff_right h_1] at h
            left
            rw[Haar.haarFunctionScaled_outside (-M) k y ?_]
            rw[neg_neg]
            exact h
        by_cases h : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1) ∨ ( 2 ^ (M : ℤ ) * y - k < 0 ∨ 2 ^ (M : ℤ ) * y - k ≥ 1)
        · right
          simp only [mul_eq_zero]
          by_cases h_1 : ( 2 ^ (M : ℤ ) * x - k < 0 ∨ 2 ^ (M : ℤ ) * x - k ≥ 1)
          · rw[Haar.haarFunctionScaled_outside (-M) k x ?_]
            · right
              simp
            · rw[neg_neg]
              exact h_1
          · rw[or_iff_right h_1] at h
            left
            rw[Haar.haarFunctionScaled_outside (-M) k y ?_]
            rw[neg_neg]
            exact h
        · push_neg at h
          have hi1 : x ∈ dyadicInterval (-M) k := by
            simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
            constructor
            · simp only [zpow_neg, zpow_natCast]
              rw[mul_comm , mul_inv_le_iff₀ (pow_pos (zero_lt_two) M) ]
              rw[← sub_nonneg, mul_comm]
              exact h.1.1
            · simp only [zpow_neg, zpow_natCast]
              rw[lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M) ]
              rw [← sub_lt_iff_lt_add']
              exact h.1.2
          have hi2 : y ∈ dyadicInterval (-M) k := by
            simp only [dyadicInterval, Int.cast_natCast, mem_setOf_eq]
            constructor
            · simp only [zpow_neg, zpow_natCast]
              rw[mul_comm , mul_inv_le_iff₀ (pow_pos (zero_lt_two) M) ]
              rw[← sub_nonneg, mul_comm]
              exact h.2.1
            · simp only [zpow_neg, zpow_natCast]
              rw[lt_inv_mul_iff₀ (pow_pos (zero_lt_two) M) ]
              rw [← sub_lt_iff_lt_add']
              exact h.2.2
          left
          rw[← Finset.prod_mul_distrib]
          apply Finset.prod_eq_one
          intro i hi
          have hiM: i < M := by
                    apply BinaryRepresentationSet.aboutM1 at hi
                    rw[le_tsub_iff_right h1 ] at hi
                    apply lt_of_le_of_lt  hi at h2
                    rw[pow_add,pow_one, mul_two, add_lt_add_iff_right] at h2
                    rw[← pow_lt_pow_iff_right₀ (Nat.one_lt_two) ]
                    exact h2
          have hr: Haar.rademacherFunction i y = Haar.rademacherFunction i x := by
            simp only [Haar.rademacherFunction, mul_eq_mul_left_iff, Nat.ofNat_nonneg]
            left
            apply Finset.sum_congr
            · simp
            · intro l hl
              simp only [Finset.mem_range] at hl
              rw[Haar.haarscl_di, Haar.haarscl_di]
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
                    rw[← zpow_le_zpow_iff_right₀ (a:= (2:ℝ )) ]
                    · sorry
                    · exact one_lt_two
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
          rw[hr, ← pow_two, Haar.rad_sqr hx1 hx2]






theorem lemma1_2help {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (x y : ℝ) (hy1 : 0 ≤ y) (hy2 : y < 1) (hx1 : 0 ≤ x) (hx2 : x < 1):
  ∑ k ∈ Finset.range (2 ^ M),
      f y * Walsh.walsh (2 ^ M) y * Haar.haarFunctionScaled (-M) k y * Walsh.walsh (2 ^ M) x *
        Haar.haarFunctionScaled (-M : ℤ ) k x =
  ∑ k ∈ Finset.range (2 ^ M),
     f y * Walsh.walsh N y * Haar.haarFunctionScaled (-M) k y * Walsh.walsh N x *
      Haar.haarFunctionScaled (-M) k x := by
      simp_rw[mul_assoc, mul_comm (a:= f y), ← Finset.sum_mul ,mul_eq_mul_right_iff]
      left
      conv_rhs => rw[walshRademacherRelationresult (BinaryRepresentationSet.aboutMfinal h1 h2) hy1 hy2,walshRademacherRelationresult (BinaryRepresentationSet.aboutMfinal h1 h2) hx1 hx2 , mul_comm]
      have : (∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m y) *
        Walsh.walsh (2 ^ M) y *
      (Haar.haarFunctionScaled (-↑M) (↑i) y *
        ((Walsh.walsh (2 ^ M) x *
            ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m x) *
          Haar.haarFunctionScaled (-↑M) (↑i) x))) = ( ∑ i ∈ Finset.range (2 ^ M),
    (∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m y) *
      Haar.haarFunctionScaled (-↑M) (↑i) y *
           ( ∏ m ∈ BinaryRepresentationSet.binaryRepresentationSet (N - 2 ^ M), Haar.rademacherFunction m x) *
          Haar.haarFunctionScaled (-↑M) (↑i) x) * Walsh.walsh (2 ^ M) y * Walsh.walsh (2 ^ M) x := by
          rw[Finset.sum_mul, Finset.sum_mul]
          congr
          ext i
          linarith
      rw[this,lemma1_2helphelp h1 h2 f x y hy1 hy2 hx1 hx2 ]
      rw[Finset.sum_mul, Finset.sum_mul]
      congr
      ext i
      linarith


theorem lemma1_2 {M N : ℕ} (h1 : 2 ^ M ≤ N) (h2 : N < 2 ^ (M + 1)) (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) :
  ∑ i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x=
  ∑ k ∈ Finset.range (2 ^ M),
    (∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * (Haar.haarFunctionScaled (-M) k y)) *
        Walsh.walsh N x *
      (Haar.haarFunctionScaled (-M) k x) := by
  rw [lemma1_1 h1 h2 f hf']
  simp_rw[← MeasureTheory.integral_mul_const]
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
    have : (fun a ↦
    f a * Walsh.walsh N a * Haar.haarFunctionScaled (-↑M) (↑i) a * Walsh.walsh N x * Haar.haarFunctionScaled (-↑M) (↑i) x )= (fun a ↦
    Walsh.walsh N x * Haar.haarFunctionScaled (-↑M) (↑i) x * Walsh.walsh N a * Haar.haarFunctionScaled (-↑M) (↑i) a * f a ) := by
      ext a
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · apply MeasureTheory.BoundedCompactSupport.restrict
      simp_rw[mul_assoc]
      apply MeasureTheory.BoundedCompactSupport.const_mul
      apply MeasureTheory.BoundedCompactSupport.const_mul
      apply MeasureTheory.BoundedCompactSupport.mul
      · exact Walsh.bcs_walsh
      · exact Haar.bcs_haarscaled
    · exact hf'
  · simp only [Finset.mem_range]
    intro i hi
    have : (fun y ↦
    f y * Walsh.walsh (2 ^ M) y * Haar.haarFunctionScaled (-↑M) (↑i) y * Walsh.walsh (2 ^ M) x *
      Haar.haarFunctionScaled (-↑M) (↑i) x) = (fun y ↦
    Walsh.walsh (2 ^ M) x *
      Haar.haarFunctionScaled (-↑M) (↑i) x * Walsh.walsh (2 ^ M) y * Haar.haarFunctionScaled (-↑M) (↑i) y * f y ) := by
      ext a
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · simp_rw[mul_assoc]
      apply MeasureTheory.BoundedCompactSupport.restrict
      apply MeasureTheory.BoundedCompactSupport.const_mul
      apply MeasureTheory.BoundedCompactSupport.const_mul
      apply MeasureTheory.BoundedCompactSupport.mul
      · exact Walsh.bcs_walsh
      · exact Haar.bcs_haarscaled
    · exact hf'



/--
Lemma 3
-/
theorem lemma2helphelp {M : ℕ} {y : ℝ} {i : ℕ} (h3 : y ∈ (Set.Ico 0 1)) : Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  simp only [Finset.mem_range, mem_Ico] at h3
  rw[← differentwalshRademacherRelation h3.1 h3.2 , ← prodofwalshworse h3.1 h3.2 ]
  exact Nat.xor_comm (2 ^ M) i

theorem lemma2helphelpextra {M : ℕ} {y : ℝ} {i : ℕ} (h : y ∈ univ \ (Set.Ico 0 1)) : Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  simp only [mem_diff, mem_univ, mem_Ico, not_and, not_lt, true_and] at h
  rw[Walsh.walsh_not_in, Walsh.walsh_not_in]
  · simp only [zero_mul]
  · rw[lt_iff_not_ge]
    exact Decidable.not_or_of_imp h
  · rw[lt_iff_not_ge]
    exact Decidable.not_or_of_imp h

theorem lemma2helphelp' {M : ℕ} {y : ℝ} {i : ℕ}: Walsh.walsh i y * Haar.rademacherFunction M y = Walsh.walsh (2^M^^^i) y := by
  by_cases h : y ∈ (Set.Ico 0 1)
  · exact lemma2helphelp h
  · push_neg at h
    refine lemma2helphelpextra ?_
    exact mem_diff_of_mem trivial h




theorem lemma2help {M N N' : ℕ} (h10 : 2 ^ M ≤ N) (h11 : N < 2 ^ (M + 1)) (h2 : N' = N - 2 ^ M)
  (f : ℝ → ℝ) (hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ):
  ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M),
    ∫ (y : ℝ) in Ico 0 1, f y * Walsh.walsh i y * Walsh.walsh i x  =
  ∑ i ∈ Finset.range (N' + 1),
    ∫ (y : ℝ) in Ico 0 1,
      f y * Walsh.walsh i y * Haar.rademacherFunction M y * Walsh.walsh i x *
        Haar.rademacherFunction M x:= by
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
    have : (fun y ↦ f y * Walsh.walsh i y * Haar.rademacherFunction M y * Walsh.walsh i x * Haar.rademacherFunction M x )= (fun y ↦ Walsh.walsh i x * Haar.rademacherFunction M x *Walsh.walsh i y * Haar.rademacherFunction M y *   f y ) := by
      ext y
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · apply MeasureTheory.BoundedCompactSupport.restrict
      apply MeasureTheory.BoundedCompactSupport.mul
      · apply MeasureTheory.BoundedCompactSupport.const_mul
        exact Walsh.bcs_walsh
      · exact Haar.bcs_rademacher
    · exact hf'
  · intro i hi
    have : (fun y ↦ f y * Walsh.walsh i y * Walsh.walsh i x)= (fun y ↦ Walsh.walsh i x * Walsh.walsh i y *  f y ) := by
      ext y
      linarith
    simp_rw[this]
    apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · apply MeasureTheory.BoundedCompactSupport.restrict
      apply MeasureTheory.BoundedCompactSupport.const_mul
      exact Walsh.bcs_walsh
    · exact hf'


theorem lemma2 {M N N' : ℕ} (h10 : 2 ^ M ≤ N) (h11 : N < 2 ^ (M + 1)) (h2 : N' = N - 2 ^ M)
  (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1))) (x : ℝ) :
  ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x =
  ∑ i ∈ Finset.range (N' + 1),
    Walsh.walshInnerProduct (Haar.rademacherFunction M * f) i * (Haar.rademacherFunction M x) *
      (Walsh.walsh i x) := by
  unfold Walsh.walshInnerProduct
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


--zmienilam granice sumowania - czy slusznie?
theorem partition {M N : ℕ} (h1 : 2 ^ M ≤ N) (f : ℝ → ℝ) (x : ℝ) : ∑
  i ∈ Finset.range (N + 1), Walsh.walshInnerProduct f i * Walsh.walsh i x =∑
    i ∈ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x + ∑ i ∈ Finset.range (N + 1) \ Finset.range (2 ^ M), Walsh.walshInnerProduct f i * Walsh.walsh i x := by
  conv_rhs => rw[add_comm]
  rw[Finset.sum_sdiff]
  rw[Finset.range_subset]
  exact Nat.le_add_right_of_le h1


end Extra
