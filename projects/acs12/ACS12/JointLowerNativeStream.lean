import ACS12.JointLowerNativeDecay

/-! Uniform absolute convergence for all three derivatives of the original native stream. -/
namespace ACS12.GammaMeasure

open Set

private theorem weightedAffineResponse_compact {k : ℕ} (hk : k ≤ 3) (A B C D q : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ r ∈ Icc (0 : ℝ) 4,
      ‖weightedAffineResponse k A B C D (1 + r * d) r q d‖ ≤ M := by
  let S := Icc (-(1 / 4) : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) 4
  let F (x : ℝ × ℝ) := ‖weightedAffineResponse k A B C D (1 + x.2 * x.1) x.2 q x.1‖
  let P₀ (d : ℝ) := A + B * d + C * d ^ 2 + D * d ^ 3
  let P₁ (d : ℝ) := B + 2 * C * d + 3 * D * d ^ 2
  let P₂ (d : ℝ) := 2 * C + 6 * D * d
  let P₃ := 6 * D
  have hX (d r : ℝ) : 1 + r * d - r * d = 1 := by ring
  have hC : Continuous F := by
    unfold F
    apply Continuous.norm
    interval_cases k
    · have hE : (fun x : ℝ × ℝ => weightedAffineResponse 0 A B C D (1 + x.2 * x.1) x.2 q x.1) =
          fun x => P₀ x.1 := by
        funext x
        rw [weightedAffineResponse_zero,hX,Real.one_rpow,mul_one]
      rw [hE]
      unfold P₀
      fun_prop
    · have hE : (fun x : ℝ × ℝ => weightedAffineResponse 1 A B C D (1 + x.2 * x.1) x.2 q x.1) =
          fun x => P₁ x.1 + P₀ x.1 * (x.2 * q) := by
        funext x
        unfold weightedAffineResponse
        dsimp only
        rw [hX,Real.one_rpow,Real.one_rpow,mul_one,mul_one]
        rfl
      rw [hE]
      unfold P₀ P₁
      fun_prop
    · have hE : (fun x : ℝ × ℝ => weightedAffineResponse 2 A B C D (1 + x.2 * x.1) x.2 q x.1) =
          fun x => P₂ x.1 + 2 * P₁ x.1 * (x.2 * q) + P₀ x.1 * (x.2 ^ 2 * q * (q + 1)) := by
        funext x
        unfold weightedAffineResponse
        dsimp only
        rw [hX,Real.one_rpow,Real.one_rpow,Real.one_rpow,mul_one,mul_one,mul_one]
        rfl
      rw [hE]
      unfold P₀ P₁ P₂
      fun_prop
    · have hE : (fun x : ℝ × ℝ => weightedAffineResponse 3 A B C D (1 + x.2 * x.1) x.2 q x.1) =
          fun x => P₃ + 3 * P₂ x.1 * (x.2 * q) + 3 * P₁ x.1 * (x.2 ^ 2 * q * (q + 1)) +
            P₀ x.1 * (x.2 ^ 3 * q * (q + 1) * (q + 2)) := by
        funext x
        rw [weightedAffineResponse_third,hX,Real.one_rpow,Real.one_rpow,Real.one_rpow,Real.one_rpow]
        simp only [mul_one]
        rfl
      rw [hE]
      unfold P₀ P₁ P₂
      fun_prop
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M,hM⟩ := hS.bddAbove_image hC.continuousOn
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro d hd r hr
  exact (hM (mem_image_of_mem F (show (d,r) ∈ S from ⟨hd,hr⟩))).trans (le_max_right _ _)

private theorem weightedAffineResponse_tail_bound {k : ℕ} (hk : k ≤ 3) (A B C D q : ℝ) (hq : 2 ≤ q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j ≥ (0 : ℝ), ∀ d ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ∀ a ≥ 1 + j,
      ‖weightedAffineResponse k A B C D a (1 + 2 * j) q d‖ ≤ M * (1 + j) ^ (-2 : ℝ) := by
  obtain ⟨M,hM,hB⟩ := weightedAffineResponse_compact hk A B C D q
  refine ⟨M * (2 : ℝ) ^ q,by positivity,?_⟩
  intro j hj d hd a ha
  let b := 1 + 2 * j
  let x := a - b * d
  have hb : 0 < b := by unfold b; positivity
  have hX : (1 + j) / 2 ≤ x := by
    have h := mul_le_mul_of_nonneg_left hd.2 hb.le
    unfold b x at *
    linarith only [h,ha]
  have hx : 0 < x := (by positivity : 0 < (1 + j) / 2).trans_le hX
  have hR : b / x ∈ Icc (0 : ℝ) 4 := by
    refine ⟨div_nonneg hb.le hx.le,(div_le_iff₀ hx).mpr ?_⟩
    unfold b
    linarith only [hX]
  have hPow : x ^ (-q) ≤ (2 : ℝ) ^ q * (1 + j) ^ (-2 : ℝ) := by
    have hJ : 0 < 1 + j := by positivity
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + j) / 2) hX (by linarith only [hq] : -q ≤ 0)
    have hE : ((1 + j) / 2) ^ (-q) = (2 : ℝ) ^ q * (1 + j) ^ (-q) := by
      rw [Real.div_rpow hJ.le (by norm_num),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),div_inv_eq_mul,mul_comm]
    rw [hE] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right hj) (neg_le_neg hq)) (Real.rpow_nonneg (by norm_num) _))
  change ‖weightedAffineResponse k A B C D a b q d‖ ≤ _
  rw [weightedAffineResponse_scaled hk A B C D a b q d hx,norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  exact (mul_le_mul (hB d hd (b / x) hR) hPow (Real.rpow_nonneg hx.le _) hM).trans_eq (by ring)

private theorem nativeAffine_difference_bound {k : ℕ} (hk : k ≤ 3) {p : ℝ} (hp : 1 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j ≥ (0 : ℝ), ∀ d ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      ‖weightedAffineResponse k 1 (-2) 0 0 (1 + j + 1) (1 + 2 * j) p d -
        weightedAffineResponse k 1 (-2) 0 0 (1 + j) (1 + 2 * j) p d‖ ≤ M * (1 + j) ^ (-2 : ℝ) := by
  obtain ⟨M,hM,hB⟩ := weightedAffineResponse_tail_bound hk 1 (-2) 0 0 (p + 1) (by linarith only [hp])
  have hp₀ := zero_lt_one.trans_le hp
  refine ⟨p * M,by positivity,?_⟩
  intro j hj d hd
  let a := 1 + j
  let b := 1 + 2 * j
  let f (u : ℝ) := weightedAffineResponse k 1 (-2) 0 0 u b p d
  have hD (u : ℝ) (hu : a ≤ u) :
      HasDerivAt f (-p * weightedAffineResponse k 1 (-2) 0 0 u b (p + 1) d) u := by
    apply weightedAffineResponse_base_deriv hk
    have h := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ b by unfold b; positivity)
    unfold a b at *
    linarith only [h,hu,hj]
  have hC : ContinuousOn f (Icc a (a + 1)) := fun x hx => (hD x hx.1).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ f (Ioo a (a + 1)) := fun x hx => (hD x hx.1.le).differentiableAt.differentiableWithinAt
  obtain ⟨x,hx,he⟩ := exists_deriv_eq_slope f (show a < a + 1 by linarith) hC hDiff
  rw [(hD x hx.1.le).deriv,add_sub_cancel_left,div_one] at he
  change ‖f (a + 1) - f a‖ ≤ _
  rw [← he,norm_mul,Real.norm_of_nonpos (neg_nonpos.mpr hp₀.le),neg_neg]
  exact (mul_le_mul_of_nonneg_left (hB j hj d hd x hx.1.le) hp₀.le).trans_eq (by ring)

theorem lowerNativeSite_dominated {k : ℕ} (hk : k ≤ 3) {p : ℝ} (hp : 1 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, ∀ d ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      ‖lowerNativeSite k p j d‖ ≤ M * (1 + (j : ℝ)) ^ (-2 : ℝ) := by
  obtain ⟨C,hC,hLeft⟩ := weightedAffineResponse_tail_bound hk (19 / 25 * p) (-(63 / 25) * p)
    (56 / 25 * p) (-(12 / 25) * p) (p + 1) (by linarith only [hp])
  obtain ⟨D,hD,hRight⟩ := weightedAffineResponse_tail_bound hk (6 / 25 * p) (-(12 / 25) * p)
    (-(6 / 25) * p) (12 / 25 * p) (p + 1) (by linarith only [hp])
  obtain ⟨E,hE,hDiff⟩ := nativeAffine_difference_bound hk hp
  refine ⟨C + D + E,by positivity,?_⟩
  intro j d hd
  let a : ℝ := 1 + j
  let b : ℝ := 1 + 2 * j
  let U := weightedAffineResponse k (19 / 25 * p) (-(63 / 25) * p) (56 / 25 * p)
    (-(12 / 25) * p) a b (p + 1) d
  let V := weightedAffineResponse k (6 / 25 * p) (-(12 / 25) * p) (-(6 / 25) * p)
    (12 / 25 * p) (a + 1) b (p + 1) d
  let W := weightedAffineResponse k 1 (-2) 0 0 (a + 1) b p d - weightedAffineResponse k 1 (-2) 0 0 a b p d
  have hEq : lowerNativeSite k p j d = U + V + W := by unfold lowerNativeSite U V W a b; ring
  rw [hEq]
  have hU := hLeft (j : ℝ) (Nat.cast_nonneg j) d hd a le_rfl
  have hV := hRight (j : ℝ) (Nat.cast_nonneg j) d hd (a + 1) (by unfold a; linarith)
  have hW := hDiff (j : ℝ) (Nat.cast_nonneg j) d hd
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hU hV)) hW)).trans_eq (by ring)

noncomputable def lowerNativeStream (k : ℕ) (p d : ℝ) : ℝ :=
  ∑' j : ℕ, lowerNativeSite k p j d

theorem lowerNativeStream_hasDerivAt {k : ℕ} (hk : k < 3) {p d : ℝ} (hp : 1 ≤ p)
    (hd : d ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    HasDerivAt (lowerNativeStream k p) (lowerNativeStream (k + 1) p d) d := by
  obtain ⟨M,hM,hBound⟩ := lowerNativeSite_dominated (show k ≤ 3 by omega) hp
  obtain ⟨K,hK,hDom⟩ := lowerNativeSite_dominated (show k + 1 ≤ 3 by omega) hp
  have hS (A : ℝ) : Summable (fun j : ℕ => A * (1 + (j : ℝ)) ^ (-2 : ℝ)) := by
    simpa only [Nat.cast_one] using (powerTail_summable (q := 2) (by norm_num) 1).mul_left A
  exact hasDerivAt_tsum_of_isPreconnected (hS K) isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun j x hx => lowerNativeSite_deriv hk (Nat.cast_nonneg j) (by linarith only [hx.2]))
    (fun j x hx => hDom j x (Ioo_subset_Icc_self hx)) hd
    (Summable.of_norm_bounded (hS M) (fun j => hBound j d (Ioo_subset_Icc_self hd))) hd

end ACS12.GammaMeasure
