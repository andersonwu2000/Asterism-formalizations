import ACS12.JointLowerCentralSign

/-! Uniform summability of the differentiated central expansion. -/
namespace ACS12.GammaMeasure

open Set Filter
open scoped Topology

private theorem affineResponse_uniform {k : ℕ} (hk : k ≤ 3) {A B C D a b q d : ℝ}
    (hA : |A| ≤ 3) (hB : |B| ≤ 3) (hC : |C| ≤ 3) (hD : |D| ≤ 3)
    (hd : |d| ≤ 1) (hb : 0 ≤ b) (hq : 0 ≤ q) (hy : 1 ≤ a - b * d) :
    ‖weightedAffineResponse k A B C D a b q d‖ ≤
      192 * (1 + b * (q + 2)) ^ 3 * (a - b * d) ^ (-q) := by
  let y := a - b * d
  let U := 1 + b * (q + 2)
  let M := U ^ 3 * y ^ (-q)
  let P₀ := A + B * d + C * d ^ 2 + D * d ^ 3
  let P₁ := B + 2 * C * d + 3 * D * d ^ 2
  let P₂ := 2 * C + 6 * D * d
  let P₃ := 6 * D
  let W₀ := y ^ (-q)
  let W₁ := b * q * y ^ (-q - 1)
  let W₂ := b ^ 2 * q * (q + 1) * y ^ (-q - 2)
  let W₃ := b ^ 3 * q * (q + 1) * (q + 2) * y ^ (-q - 3)
  have hU : 1 ≤ U := by unfold U; nlinarith only [mul_nonneg hb (show 0 ≤ q + 2 by linarith only [hq])]
  have hU₀ := zero_le_one.trans hU
  have hy₀ : 0 ≤ y := zero_le_one.trans hy
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg hU₀ _) (Real.rpow_nonneg hy₀ _)
  have hd₂ : |d| ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hd₃ : |d| ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg d) hd 3
  have hBd := mul_le_one₀ (by linarith only [hB] : |B| / 3 ≤ 1) (abs_nonneg d) hd
  have hBd' : |B| * |d| ≤ 3 := by nlinarith only [hBd]
  have hCd := mul_le_mul hC hd₂ (pow_nonneg (abs_nonneg d) _) (by norm_num : (0 : ℝ) ≤ 3)
  have hCd' := mul_le_mul hC hd (abs_nonneg d) (by norm_num : (0 : ℝ) ≤ 3)
  have hDd := mul_le_mul hD hd₃ (pow_nonneg (abs_nonneg d) _) (by norm_num : (0 : ℝ) ≤ 3)
  have hDd' := mul_le_mul hD hd₂ (pow_nonneg (abs_nonneg d) _) (by norm_num : (0 : ℝ) ≤ 3)
  have hDd'' := mul_le_mul hD hd (abs_nonneg d) (by norm_num : (0 : ℝ) ≤ 3)
  have h₀ : |P₀| ≤ 24 := by
    unfold P₀
    calc
      _ ≤ |A| + |B * d| + |C * d ^ 2| + |D * d ^ 3| :=
        (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by rw [abs_mul,abs_mul,abs_mul,abs_pow,abs_pow]; linarith only [hA,hBd',hCd,hDd]
  have h₁ : |P₁| ≤ 24 := by
    unfold P₁
    calc
      _ ≤ |B| + |2 * C * d| + |3 * D * d ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul,abs_pow,abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
        linarith only [hB,hCd',hDd']
  have h₂ : |P₂| ≤ 24 := by
    unfold P₂
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num)]
    linarith only [hC,hDd'']
  have h₃ : |P₃| ≤ 24 := by
    unfold P₃
    rw [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num)]
    linarith only [hD]
  have hBq (r : ℝ) (hr : 0 ≤ r) (hr₂ : r ≤ 2) : b * (q + r) ≤ U := by
    unfold U
    nlinarith only [mul_nonneg hb (show 0 ≤ 2 - r by linarith only [hr₂])]
  have h0 : |W₀| ≤ M := by
    unfold W₀ M
    rw [abs_of_nonneg (Real.rpow_nonneg hy₀ _)]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hy₀ _) (one_le_pow₀ hU)
  have h1 : |W₁| ≤ M := by
    have hQ := Real.rpow_le_rpow_of_exponent_le hy (show -q - 1 ≤ -q by linarith)
    have hU' := (pow_le_pow_right₀ hU (show (1 : ℕ) ≤ 3 by decide))
    rw [pow_one] at hU'
    unfold W₁ M
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul ((by simpa only [add_zero] using hBq 0 le_rfl (by norm_num) :
      b * q ≤ U).trans hU') hQ (Real.rpow_nonneg hy₀ _) (pow_nonneg hU₀ _)
  have h2 : |W₂| ≤ M := by
    have hQ := Real.rpow_le_rpow_of_exponent_le hy (show -q - 2 ≤ -q by linarith)
    have hU' := pow_le_pow_right₀ hU (show (2 : ℕ) ≤ 3 by decide)
    have hC' : b ^ 2 * q * (q + 1) ≤ U ^ 2 := by
      rw [show b ^ 2 * q * (q + 1) = (b * (q + 0)) * (b * (q + 1)) by ring,pow_two]
      exact mul_le_mul (hBq 0 le_rfl (by norm_num)) (hBq 1 zero_le_one (by norm_num)) (by positivity) hU₀
    unfold W₂ M
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hC'.trans hU') hQ (Real.rpow_nonneg hy₀ _) (pow_nonneg hU₀ _)
  have h3 : |W₃| ≤ M := by
    have hQ := Real.rpow_le_rpow_of_exponent_le hy (show -q - 3 ≤ -q by linarith)
    have hC' : b ^ 3 * q * (q + 1) * (q + 2) ≤ U ^ 3 := by
      rw [show b ^ 3 * q * (q + 1) * (q + 2) =
        (b * (q + 0)) * (b * (q + 1)) * (b * (q + 2)) by ring,pow_succ,pow_two]
      exact mul_le_mul (mul_le_mul (hBq 0 le_rfl (by norm_num)) (hBq 1 zero_le_one (by norm_num))
        (by positivity) hU₀) (hBq 2 (by norm_num) le_rfl) (by positivity) (mul_nonneg hU₀ hU₀)
    unfold W₃ M
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul hC' hQ (Real.rpow_nonneg hy₀ _) (pow_nonneg hU₀ _)
  have hTerm {x z : ℝ} (hx : |x| ≤ 24) (hz : |z| ≤ M) : |x * z| ≤ 24 * M := by
    rw [abs_mul]
    exact mul_le_mul hx hz (abs_nonneg _) (by norm_num)
  have hScale {x : ℝ} (hx : |x| ≤ 24 * M) {c : ℝ} (hc : 0 ≤ c) : |c * x| ≤ c * (24 * M) := by
    rw [abs_mul,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hx hc
  rw [Real.norm_eq_abs,mul_assoc]
  change _ ≤ 192 * M
  interval_cases k
  · rw [weightedAffineResponse_zero]
    exact (hTerm h₀ h0).trans (by linarith only [hM])
  · have hE : weightedAffineResponse 1 A B C D a b q d = P₁ * W₀ + P₀ * W₁ := by
      rw [weightedAffineResponse_first]; unfold P₀ P₁ W₀ W₁ y; ring
    rw [hE]
    have h := (abs_add_le _ _).trans (add_le_add (hTerm h₁ h0) (hTerm h₀ h1))
    exact h.trans (by linarith only [hM])
  · have hE : weightedAffineResponse 2 A B C D a b q d = P₂ * W₀ + 2 * (P₁ * W₁) + P₀ * W₂ := by
      rw [weightedAffineResponse_second]; unfold P₀ P₁ P₂ W₀ W₁ W₂ y; ring
    rw [hE]
    have h := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hTerm h₂ h0) (hScale (hTerm h₁ h1) (by norm_num : (0 : ℝ) ≤ 2))))
      (hTerm h₀ h2))
    exact h.trans (by linarith only [hM])
  · have hE : weightedAffineResponse 3 A B C D a b q d =
        P₃ * W₀ + 3 * (P₂ * W₁) + 3 * (P₁ * W₂) + P₀ * W₃ := by
      rw [weightedAffineResponse_third]; unfold P₀ P₁ P₂ P₃ W₀ W₁ W₂ W₃ y; ring
    rw [hE]
    have h := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hTerm h₃ h0) (hScale (hTerm h₂ h1) (by norm_num : (0 : ℝ) ≤ 3))))
      (hScale (hTerm h₁ h2) (by norm_num : (0 : ℝ) ≤ 3)))) (hTerm h₀ h3))
    exact h.trans (by linarith only [hM])

private theorem central_geometric_bound (n : ℕ) : ((n : ℝ) + 5) ^ 3 * (1 / 2 : ℝ) ^ n ≤ 125 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ (1 / 2 : ℝ)]
    have h₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hP : ((n : ℝ) + 1 + 5) ^ 3 * (1 / 2) ≤ ((n : ℝ) + 5) ^ 3 := by
      nlinarith only [h₀,sq_nonneg (n : ℝ),mul_nonneg h₀ (sq_nonneg (n : ℝ))]
    calc
      _ = (((n : ℝ) + 1 + 5) ^ 3 * (1 / 2)) * (1 / 2 : ℝ) ^ n := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hP (by positivity)).trans ih

private theorem lowerCentralResponse_dominated {k : ℕ} (hk : k ≤ 3) {p J : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hJ : 5 / 2 ≤ J) {d : ℝ}
    (hd : d ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (n : ℕ) :
    ‖lowerCentralResponse k p J n d‖ ≤ 24000 * (1 + 2 * J) ^ 3 := by
  let b := 2 * J
  let y := J + 1 - b * d
  let q := p + 1 + (n : ℝ)
  have hb : 0 ≤ b := by unfold b; linarith only [hJ]
  have hq : 0 ≤ q := by unfold q; linarith only [hp,Nat.cast_nonneg (α := ℝ) n]
  have hy : 2 ≤ y := by
    unfold y b
    have h := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 2 * J by linarith only [hJ])
    linarith only [h,hJ]
  have hd' : |d| ≤ 1 := abs_le.mpr ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
  have hC : ‖lowerCentralResponse k p J n d‖ ≤ 192 * (1 + b * (q + 2)) ^ 3 * y ^ (-q) := by
    unfold lowerCentralResponse
    split_ifs
    · let a := (n : ℝ) / ((n : ℝ) + 1)
      have ha : 0 ≤ a := by unfold a; positivity
      have ha₁ : a ≤ 1 := by unfold a; exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_right zero_le_one)
      apply affineResponse_uniform hk _ _ (by norm_num) (by norm_num) hd' hb hq
        ((by norm_num : (1 : ℝ) ≤ 2).trans hy)
      · rw [abs_of_nonneg ha]; linarith only [ha₁]
      · rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1 + 2 * a)]; linarith only [ha₁]
    · exact affineResponse_uniform hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd' hb hq
        ((by norm_num : (1 : ℝ) ≤ 2).trans hy)
  have hP : y ^ (-q) ≤ (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ y ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans hy)
        (by unfold q; linarith only [hp])
      _ ≤ (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hy (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ = _ := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_natCast,one_div,inv_pow]
  have hU : 1 + b * (q + 2) ≤ (1 + b) * ((n : ℝ) + 5) := by
    have h := mul_le_mul_of_nonneg_left (show q + 2 ≤ (n : ℝ) + 5 by unfold q; linarith only [hp₂]) hb
    nlinarith only [h,Nat.cast_nonneg (α := ℝ) n]
  have hB := mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + b * (q + 2)) hU 3)
    hP (Real.rpow_nonneg (by linarith only [hy]) _) (by positivity)
  refine hC.trans ?_
  calc
    _ ≤ 192 * (((1 + b) * ((n : ℝ) + 5)) ^ 3 * (1 / 2 : ℝ) ^ n) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = (192 * (1 + b) ^ 3) * (((n : ℝ) + 5) ^ 3 * (1 / 2 : ℝ) ^ n) := by rw [mul_pow]; ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (central_geometric_bound n)
        (show 0 ≤ 192 * (1 + b) ^ 3 by positivity) using 1
      unfold b
      ring


private noncomputable def lowerCentralStream (k : ℕ) (p J d : ℝ) : ℝ :=
  ∑' n, lowerCentralWeight p n * lowerCentralResponse k p J n d

private theorem lowerCentralStream_summable {k : ℕ} (hk : k ≤ 3) {p J d : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hJ : 5 / 2 ≤ J)
    (hd : d ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    Summable (fun n => lowerCentralWeight p n * lowerCentralResponse k p J n d) := by
  exact Summable.of_norm_bounded ((lowerCentralWeight_summable p).norm.mul_left (24000 * (1 + 2 * J) ^ 3))
    (fun n => by
      rw [norm_mul,mul_comm (24000 * (1 + 2 * J) ^ 3)]
      exact mul_le_mul_of_nonneg_left (lowerCentralResponse_dominated hk hp hp₂ hJ hd n) (norm_nonneg _))

private theorem lowerCentralStream_deriv {k : ℕ} (hk : k < 3) {p J d : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hJ : 5 / 2 ≤ J)
    (hd : d ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    HasDerivAt (lowerCentralStream k p J) (lowerCentralStream (k + 1) p J d) d := by
  exact hasDerivAt_tsum_of_isPreconnected
    ((lowerCentralWeight_summable p).norm.mul_left (24000 * (1 + 2 * J) ^ 3)) isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun n x hx => (lowerCentralResponse_deriv hk (by linarith only [hJ]) (by linarith only [hx.2]) n).const_mul _)
    (fun n x hx => by
      rw [norm_mul,mul_comm (24000 * (1 + 2 * J) ^ 3)]
      exact mul_le_mul_of_nonneg_left
        (lowerCentralResponse_dominated (show k + 1 ≤ 3 by omega) hp hp₂ hJ (Ioo_subset_Icc_self hx) n) (norm_nonneg _))
    hd (lowerCentralStream_summable (show k ≤ 3 by omega) hp hp₂ hJ (Ioo_subset_Icc_self hd)) hd

private theorem lowerNativeSite_eq_centralStream {k : ℕ} (hk : k ≤ 3) {p j : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hj : 2 ≤ j) :
    ∀ d ∈ Ioo (-(1 / 4) : ℝ) (1 / 4), lowerNativeSite k p j d = lowerCentralStream k p (j + 1 / 2) d := by
  induction k with
  | zero =>
    intro d hd
    have h := lowerNativeSite_central_hasSum (show 0 ≤ j by linarith only [hj])
      (show d < 1 / 2 by linarith only [hd.2]) (p := p)
    unfold lowerCentralStream
    simp_rw [lowerCentralResponse_zero]
    rw [← h.tsum_eq]
    apply tsum_congr
    intro n
    ring
  | succ k ih =>
    intro d hd
    have hK : k < 3 := by omega
    have hE : lowerNativeSite k p j =ᶠ[𝓝 d] lowerCentralStream k p (j + 1 / 2) := by
      filter_upwards [Ioo_mem_nhds hd.1 hd.2] with x hx
      exact ih (by omega) x hx
    have hD := (lowerCentralStream_deriv hK hp hp₂ (by linarith only [hj]) hd).congr_of_eventuallyEq hE
    have hN := lowerNativeSite_deriv (p := p) hK (show 0 ≤ j by linarith only [hj])
      (show d < 1 / 2 by linarith only [hd.2])
    exact hN.deriv.symm.trans hD.deriv

theorem lowerNativeSite_third_ge_centralBase {p j d : ℝ}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hj : 2 ≤ j) (hd : d ∈ Icc (0 : ℝ) (1 / 8)) :
    lowerCentralWeight p 0 * lowerCentralResponse 3 p (j + 1 / 2) 0 d +
      lowerCentralWeight p 1 * lowerCentralResponse 3 p (j + 1 / 2) 1 d ≤ lowerNativeSite 3 p j d := by
  let f (n : ℕ) := lowerCentralWeight p n * lowerCentralResponse 3 p (j + 1 / 2) n d
  have hd' : d ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hd.1],by linarith only [hd.2]⟩
  have hS : Summable f := lowerCentralStream_summable le_rfl hp hp₂ (by linarith only [hj]) (Ioo_subset_Icc_self hd')
  have hN (n : ℕ) : 0 ≤ f (n + 2) :=
    mul_nonneg (lowerCentralWeight_pos (zero_lt_one.trans_le hp) _).le
      (lowerCentralResponse_third_pos hp (by linarith only [hj]) hd (by omega)).le
  have hE := hS.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ,Finset.sum_range_one] at hE
  rw [lowerNativeSite_eq_centralStream le_rfl hp hp₂ hj d hd']
  change f 0 + f 1 ≤ ∑' n, f n
  rw [← hE]
  exact le_add_of_nonneg_right (tsum_nonneg hN)

end ACS12.GammaMeasure

